//! This module calculates precise information for which registers are "live" at each syntactic point of the IR. A register is "live" at some point in execution if its value may be used at or after that point.

use crate::compiler_types::{Map, Set};
use crate::ir::*;

/// Liveness information for an IR function.
#[derive(Clone, Debug)]
pub struct FunctionLiveness {
    /// Liveness information for each block of the function.
    pub blocks: Map<BlockId, BlockLiveness>,
}

impl FunctionLiveness {
    /// Pretty print function liveness information.
    pub fn pretty_print(&self) {
        let print_regs = |regs: &Set<Register>| {
            for (i, r) in regs.iter().enumerate() {
                if i != 0 {
                    print!(" ");
                }
                print!("{r}");
            }
            println!();
        };
        for (id, block) in &self.blocks {
            println!("block_{}:", id.0);
            print!("    start: ");
            print_regs(&block.start);
            for (i, inst) in block.insts.iter().enumerate() {
                print!("    inst{i}: ");
                print_regs(inst);
            }
        }
    }
}

/// Liveness information for a basic block.
#[derive(Clone, Debug)]
pub struct BlockLiveness {
    /// The set of live registers when this block begins execution.
    pub start: Set<Register>,
    /// The set of live registers after executing each instruction of this block.
    pub insts: Vec<Set<Register>>,
}

/// Calculate the liveness information for a function.
#[allow(clippy::assigning_clones)]
#[must_use]
pub fn calculate_liveness(f: &Function) -> FunctionLiveness {
    let start_map = calculate_start(f);
    let mut insts_map = Map::new();
    for &id in f.blocks.keys() {
        let block = f.blocks.get(&id).unwrap();
        let insts = &block.insts;
        if insts.is_empty() {
            insts_map.insert(id, vec![]);
            continue;
        }
        let mut insts_live: Vec<_> = (0..insts.len()).map(|_| Set::new()).collect();
        let mut last = Set::new();
        block.exit.visit_regs(|r| {
            last.insert(r);
        });
        for succ_id in block.successors() {
            last.extend(start_map.get(&succ_id).unwrap());
            let succ_block = f.blocks.get(&succ_id).unwrap();
            for inst in &succ_block.insts {
                let Inst::Store(_, StoreKind::Phi(regs)) = inst else {
                    continue;
                };
                last.insert(*regs.get(&id).unwrap());
            }
        }
        *insts_live.last_mut().unwrap() = last.clone();
        for (i, inst) in insts[1..].iter().enumerate().rev() {
            inst.visit_regs(|r, is_def| {
                if !is_def {
                    last.insert(r);
                }
            });
            // Remove all registers defined by this instruction.
            match inst {
                Inst::Store(def, _) => {
                    last.remove(def);
                }
                Inst::Call { returns, .. } => {
                    for def in returns {
                        last.remove(def);
                    }
                }
                Inst::Write(..) | Inst::Nop => {}
            }
            *insts_live.get_mut(i).unwrap() = last.clone();
        }
        insts_map.insert(id, insts_live);
    }
    assert_eq!(start_map.len(), insts_map.len());
    let blocks = start_map
        .into_iter()
        .zip(insts_map)
        .map(|((id1, start), (id2, insts))| {
            assert_eq!(id1, id2);
            let block = BlockLiveness { start, insts };
            (id1, block)
        })
        .collect();
    FunctionLiveness { blocks }
}

type Start = Map<BlockId, Set<Register>>;
fn calculate_start(f: &Function) -> Start {
    fn add(id: BlockId, r: Register, f: &Function, map: &mut Start) {
        if f.blocks[&id].defined_regs.contains(&r) || !map.get_mut(&id).unwrap().insert(r) {
            return;
        }
        for &pred in &f.predecessors[&id] {
            add(pred, r, f, map);
        }
    }
    let mut map: Start = f.blocks.keys().map(|&id| (id, Set::new())).collect();
    for (&id, block) in &f.blocks {
        for &r in &block.used_regs {
            add(id, r, f, &mut map);
        }
    }
    map
}
