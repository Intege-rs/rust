#![allow(dead_code, unused)]

//╶───╴Our Passes╶───────────────────────────────────────────────────────────╴

mod flow;

// re-export them
pub(crate) use flow::FlowFlatten;

//╶───╴Obfuscation Seed╶─────────────────────────────────────────────────────╴

/// Gets the OBF_SEED environment variable
#[inline(always)]
fn seed_str() -> &'static str {
    use std::sync::OnceLock;
    static B: OnceLock<String> = OnceLock::<String>::new();
    B.get_or_init(||
        std::env::var("OBF_SEED")
            .unwrap_or_default())
        .as_str()
}

#[inline(always)]
fn is_obfuscation_enabled() -> bool {
    !seed_str().is_empty()
}

#[inline(always)]
fn seed_hashed() -> u64 {
    use std::sync::OnceLock;
    static B: OnceLock<u64> = OnceLock::<u64>::new();
    *B.get_or_init(||hash(seed_str().as_bytes()))
}

//╶───╴PRNG used for our obfuscation passes╶─────────────────────────────────╴

fn hash(stream: &[u8]) -> u64 {
    use rustc_data_structures::fx::FxHasher;
    use std::hash::Hasher;
    use std::io::Read;

    let mut hasher = FxHasher::default();
    hasher.write(stream);
    hasher.finish()
}

/// https://prng.di.unimi.it/xoshiro128plusplus.c
#[derive(Clone)]
pub(crate) struct PRNG(pub [u32;4]);

impl PRNG {

    pub(crate) fn from(hash: rustc_span::def_id::DefPathHash) -> Self {
        let lower = hash.0.to_smaller_hash().as_u64();
        let upper = seed_hashed();
        Self([
            (lower & 0xFFFFFFFF) as u32,
            (lower >> 32) as u32,
            (upper & 0xFFFFFFFF) as u32,
            (upper >> 32) as u32,
        ])
    }

    pub(crate) fn new(identifier: &[u8]) -> Self {

        let lower = hash(identifier);
        let upper = seed_hashed();

        Self([
            (lower & 0xFFFFFFFF) as u32,
            (lower >> 32) as u32,
            (upper & 0xFFFFFFFF) as u32,
            (upper >> 32) as u32,
        ])

    }

    pub(crate) fn next(&mut self) -> u32 {
        let r = (self.0[0] + self.0[3]).rotate_left(7);
        let t = self.0[1] << 9;
        self.0[2] ^= self.0[0];
        self.0[3] ^= self.0[1];
        self.0[1] ^= self.0[2];
        self.0[0] ^= self.0[3];
        self.0[2] ^= t;
        self.0[3] = self.0[3].rotate_left(11);
        r
    }

    /// This is the jump function for the generator. It is equivalent
    ///    to 2^64 calls to next(); it can be used to generate 2^64
    ///    non-overlapping subsequences for parallel computations.
    pub(crate) fn jump(&mut self) {
        const JUMP: [u32;4] = [ 0x8764000b, 0xf542d2d3, 0x6fa035c3, 0x77f2db5b ];
        let mut s = self.0.clone();

        for i in JUMP {
            for b in 0..32 {
                if (i & ( 1 << b )) != 0 {
                    s[0] ^= self.0[0];
                    s[1] ^= self.0[1];
                    s[2] ^= self.0[2];
                    s[3] ^= self.0[3];
                }
                self.next();
            }
        }

        self.0 = s;
    }

}

impl PRNG {

    pub(crate) fn new_bool(&mut self) -> bool {
        (self.next() & 1) != 0
    }

    pub(crate) fn range_usize(&mut self, r: std::ops::Range<usize>) -> usize {
        assert!(r.end < u32::MAX as usize);
        self.range( (r.start as u32) .. (r.end as u32) ) as usize
    }

    pub(crate) fn range(&mut self, r: std::ops::Range<u32>) -> u32 {
        (self.next() % r.end.saturating_sub(r.start) ) + r.start
    }

    pub(crate) fn shuffle<T: Sized>(&mut self, slice: &mut [T]) {
        if slice.len() <= 1 { return }
        for i in (0..slice.len() as u32) {
            slice.swap(i as usize, self.range(0..slice.len() as u32) as usize)
        }
    }

}

//╶───╴Utility╶──────────────────────────────────────────────────────────────╴
use rustc_middle::ty::TyCtxt;
use rustc_middle::mir::{SourceInfo, SourceScope};

const _SPAN: rustc_span::Span = rustc_span::DUMMY_SP;

/// blank source info to be used in our basic blocks
const _SOURCE: SourceInfo = SourceInfo {
    span: rustc_span::DUMMY_SP,
    scope: SourceScope::ZERO,
};

/// assembly and other things don't work in const functions, so we will filter them out here
pub(crate) fn is_non_const_func<'tcx>(tcx: TyCtxt<'tcx>, source: &rustc_middle::mir::MirSource<'tcx>) -> bool {
    use rustc_hir::{Constness, def::{DefKind, CtorKind}};
    use rustc_middle::ty::InstanceKind;
    let InstanceKind::Item(def) = &source.instance else { return false; };
    if tcx.constness(def) != Constness::NotConst { return false }
    matches!( tcx.def_kind(def),DefKind::Fn
        | DefKind::AssocFn
        | DefKind::Ctor(_, CtorKind::Fn)
        | DefKind::Closure)
}
