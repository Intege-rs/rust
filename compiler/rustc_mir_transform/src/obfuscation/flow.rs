use hashbrown::HashMap;
use itertools::Itertools;
use rustc_ast::Mutability;
use rustc_middle::mir::{BasicBlock, BasicBlockData, BasicBlocks, Body, ClearCrossCrate, Const, ConstOperand, LocalDecl, Operand, Place, Rvalue, SourceInfo, SourceScope, Statement, StatementKind, SwitchTargets, Terminator, TerminatorKind, UnwindAction};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use rustc_span::Span;
use crate::obfuscation::{_SOURCE, _SPAN};

const MIN_COMPLEXITY_THRESHOLD: usize = 100;

pub(crate) struct FlowFlatten;

impl<'tcx> crate::MirPass<'tcx> for FlowFlatten {

    fn is_enabled(&self, _sess: &Session) -> bool {
        super::is_obfuscation_enabled()
            && _sess.target_features.iter()
            .find(|f| f.as_str() == "obf_flatten")
            .is_some()
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {

        // this pass shouldn't run on const functions
        if !super::is_non_const_func(tcx, &body.source) { return; }

        let c = calc_complexity(&body.basic_blocks);
        if c <= MIN_COMPLEXITY_THRESHOLD {
            // function is not complex enough to be worth flow flattening
            return;
        }

        // pseudo random generator
        let mut prng = super::PRNG::from(tcx.def_path_hash(body.source.instance.def_id()));

        // the control variable for our switch block
        let ctrl_var = body.local_decls.push(LocalDecl {
            mutability: Mutability::Mut,
            local_info: ClearCrossCrate::Clear,
            ty: tcx.types.usize,
            user_ty: None,
            source_info: _SOURCE,
        });

        // creates an assignment statement that assigns a specific value to our control variable
        let assign_ctrl_var = |value: u64| {
            Statement::new(_SOURCE, StatementKind::Assign(Box::new((Place::from(ctrl_var), Rvalue::Use(Operand::Constant(
                Box::new(ConstOperand { span: _SPAN, user_ty: None, const_: Const::from_usize(tcx, value) })
            ))))))
        };

        let mut counter = 0;
        let blocks: HashMap<BasicBlock, usize> = HashMap::new();

        // insert our prelude block into the end of the list and swap it with the entrypoint
        let entrypoint = body.basic_blocks_mut()
            .push(BasicBlockData::new_stmts(vec![], None, false));
        body.basic_blocks_mut().swap(entrypoint, BasicBlock::from_usize(0));

        // oh boy!
        let lookup = {
            let mut blocks = body.basic_blocks_mut()
                // skip the first block, it should never have a precursor
                .iter_enumerated().skip(1)
                .filter(|(_, bbd)| (!bbd.is_cleanup))
                .map(|(bb,v)| bb)
                .collect::<Vec<BasicBlock>>();
            prng.shuffle(&mut blocks);
            blocks.iter().enumerate()
                .map(|(i, bb)| (*bb, i as u64))
                .collect::<HashMap<BasicBlock, u64>>()
        };

        // the default branch will be the last index for optimization reasons
        let default_branch = lookup.iter()
            .max_by_key(|(bb, i)| *i)
            .map(|(bb, _)| *bb)
            .unwrap_or(entrypoint);

        // build our switch case
        let switch_case = body.basic_blocks_mut().push(BasicBlockData::new(Some(Terminator {
            source_info: _SOURCE,
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from(ctrl_var)),
                targets: SwitchTargets::new(
                    lookup.iter().map(|(bb, i)| (*i as u128, *bb)),
                    default_branch,
                ),
            },
        }), false));

        // update the prelude block to set the control variable
        // and jump to our switch case
        let pbbd = body.basic_blocks_mut()
            .get_mut(BasicBlock::from_usize(0))
            .expect("Failed to get the prelude block");
        pbbd.statements.push(assign_ctrl_var(lookup[&entrypoint]));
        pbbd.terminator = Some(Terminator {
            source_info: _SOURCE,
            kind: TerminatorKind::Goto {
                target: switch_case,
            },
        });

        // kind of hacky, because we cannot insert into the body while we are reading it,
        // we will "pretend" we inserted blocks but actually insert them afterwards
        let mut insertion_debt = Vec::new();

        // this is the index that our newly inserted blocks will start at
        let insertion_start = switch_case + 1;

        walk_block_refs(body, true, |bb, bbr| {
            // don't replace variables that have already been set
            if bb >= switch_case || *bbr >= switch_case { return; }
            if let Some(bid) = lookup.get(bbr) {
                // point bbr to where the new block will be inserted
                *bbr = insertion_start + insertion_debt.len();
                insertion_debt.push(*bid);
            }
        });

        // now so that we don't crash/ice we need to pay off our debt
        for debt in insertion_debt {
            body.basic_blocks_mut().push(
                BasicBlockData::new_stmts(
                    vec![assign_ctrl_var(debt)],
                    Some(Terminator {
                        source_info: _SOURCE,
                        kind: TerminatorKind::Goto {
                            target: switch_case
                        },
                    }), false)
            );
        }

        // call the debug passes to re-order our blocks
        super::super::prettify::ReorderBasicBlocks.run_pass(tcx, body);
        super::super::prettify::ReorderLocals.run_pass(tcx, body);
    }

    fn is_required(&self) -> bool {
        true
    }
}

// simple complexity check so we don't run on small functions
fn calc_complexity<'tcx>(blocks: &BasicBlocks<'tcx>) -> usize {
    let mut count = 0;
    for block in blocks.iter() {
        count += 10 + block.statements.len(); // we count the terminator as an expression
    }
    count
}

/// ( Parent Block, Ref BasicBlock )
fn walk_block_refs(body: &mut Body<'_>, skip_cleanup: bool, mut func: impl FnMut(BasicBlock, &mut BasicBlock)) {
    for (bb, bbd) in body.basic_blocks_mut().iter_enumerated_mut() {
        let Some(terminator) = bbd.terminator.as_mut() else { continue };

        match &mut terminator.kind {
            TerminatorKind::Goto { target } => func(bb, target),
            TerminatorKind::SwitchInt { targets, .. } => {
                for x in targets.all_targets_mut() { func(bb, x) }
            }
            TerminatorKind::Drop { target, unwind, .. } => {
                if let UnwindAction::Cleanup(block) = unwind { if !skip_cleanup { func(bb, block) } }
                func(bb, target)
            }
            TerminatorKind::Call { target, unwind, .. } => {
                if let UnwindAction::Cleanup(block) = unwind { if !skip_cleanup { func(bb, block) } }
                if let Some(target) = target { func(bb, target) }
            }
            TerminatorKind::Assert { target, unwind, .. } => {
                if let UnwindAction::Cleanup(block) = unwind { if !skip_cleanup { func(bb, block) } }
                func(bb, target)
            }
            TerminatorKind::Yield { resume, drop, .. } => {
                if let Some(target) = drop { func(bb, target) }
                func(bb, resume)
            }
            TerminatorKind::FalseEdge { real_target, imaginary_target } => {
                func(bb, real_target);
                func(bb, imaginary_target)
            }
            TerminatorKind::FalseUnwind { real_target, unwind, .. } => {
                if let UnwindAction::Cleanup(block) = unwind { if !skip_cleanup { func(bb, block) } }
                func(bb, real_target)
            }
            TerminatorKind::InlineAsm { targets, unwind, .. } => {
                if let UnwindAction::Cleanup(block) = unwind { if !skip_cleanup { func(bb, block) } }
                for target in targets { func(bb, target) }
            }

            // These terminators do not reference other blocks
            TerminatorKind::UnwindResume => {}
            TerminatorKind::UnwindTerminate(_) => {}
            TerminatorKind::Return => {}
            TerminatorKind::Unreachable => {}
            TerminatorKind::TailCall { .. } => {}
            TerminatorKind::CoroutineDrop => {}
        }
    }
}