use crate::compiler_types::{Map, Set};
use crate::ir::*;

#[rustfmt::skip] // rustfmt wants to split up longer lines.
pub const PASSES: &[(&str, fn(&mut Function))] = &[
    ("remove redundant writes", remove_redundant_writes),
    ("dead code elimination", dead_code_elimination),
    ("common subexpression elimination", common_subexpression_elimination),
];

pub fn optimize(ir: &mut Program) {
    let mut output = format!("{ir}");
    for (name, pass) in PASSES {
        for f in ir.functions.values_mut() {
            pass(f);
        }
        let new_output = format!("{ir}");
        // Yes, this is silly, but it works. What we should actually do is have each pass return whether it was able to optimize anything.
        if output == new_output {
            println!("{name}: no change");
        } else {
            output = new_output;
            println!("!! {name}:\n{output}");
        }
    }
}

pub fn remove_redundant_writes(f: &mut Function) {
    let mut stack_writes: Map<Register, Vec<(BlockId, usize)>> = f
        .blocks
        .values()
        .flat_map(|b| &b.insts)
        .filter_map(|inst| match inst {
            &Inst::Store(r, StoreKind::StackAlloc(_)) => Some(r),
            _ => None,
        })
        .map(|r| (r, vec![]))
        .collect();
    for (&block_id, block) in &f.blocks {
        for (i, inst) in block.insts.iter().enumerate() {
            let &Inst::Write(alloc, _) = inst else {
                continue;
            };
            if let Some(vec) = stack_writes.get_mut(&alloc) {
                vec.push((block_id, i));
            }
        }
    }
    for locs in stack_writes.values_mut() {
        locs.sort();
    }
    for (src, locs) in stack_writes {
        for (original_block_id, i) in locs {
            let mut closed = Set::new();
            let mut open = vec![BlockId::DUMMY];
            let mut is_used = false;
            'check: while let Some(block_id) = open.pop() {
                if !closed.insert(block_id) {
                    continue;
                }
                let insts = if block_id == BlockId::DUMMY {
                    &f.blocks.get(&original_block_id).unwrap().insts[i + 1..]
                } else if block_id == original_block_id {
                    &f.blocks.get(&original_block_id).unwrap().insts[..i]
                } else {
                    f.blocks.get(&block_id).unwrap().insts.as_ref()
                };
                let mut reached_end = block_id != original_block_id;
                for inst in insts {
                    match *inst {
                        Inst::Write(stack, _) if stack == src => {
                            reached_end = false;
                            break;
                        }
                        Inst::Store(_, StoreKind::Read(stack)) if stack == src => {
                            is_used = true;
                            break 'check;
                        }
                        _ => {}
                    }
                }
                if reached_end {
                    let block_id = if block_id == BlockId::DUMMY {
                        original_block_id
                    } else {
                        block_id
                    };
                    open.extend(f.blocks.get(&block_id).unwrap().successors());
                }
            }
            if !is_used {
                f.blocks.get_mut(&original_block_id).unwrap().insts[i] = Inst::Nop;
            }
        }
    }
}

pub fn dead_code_elimination(f: &mut Function) {
    let mut changed = true;
    while changed {
        changed = false;
        for block in f.blocks.values_mut() {
            block.gen_def_use();
        }
        let used: Set<_> = f
            .blocks
            .values()
            .flat_map(|b| &b.used_regs)
            .copied()
            .collect();
        for block in f.blocks.values_mut() {
            let old_len = block.insts.len();
            block.insts.retain(|inst| match inst {
                Inst::Store(r, _) => used.contains(r),
                Inst::Write(_, _) | Inst::Call { .. } => true,
                Inst::Nop => false,
            });
            changed |= block.insts.len() != old_len;
        }
    }
}

pub fn common_subexpression_elimination(f: &mut Function) {
    use StoreKind as Sk;
    fn visit(
        id: BlockId,
        children: &DominatorTree,
        blocks: &mut Map<BlockId, Block>,
        ancestor_subs: &mut Vec<Map<Sk, Register>>,
    ) {
        let block = blocks.get_mut(&id).unwrap();
        ancestor_subs.push(Map::new());
        for inst in &mut block.insts {
            let Inst::Store(r, sk) = inst else { continue };
            match sk {
                Sk::Int(..) | Sk::Phi(_) | Sk::UnaryOp(..) | Sk::BinOp(..) | Sk::Function(_) => {}
                | Sk::Read(_) // impure, performing CSE can erroneously erase a write
                | Sk::StackAlloc(_) // unique allocation, can't be copied
                | Sk:: Copy(_) // pointless to copy a copy
                => continue,
            }
            match ancestor_subs.iter().rev().find_map(|map| map.get(sk)) {
                Some(&r_sub) => *sk = Sk::Copy(r_sub),
                None => {
                    ancestor_subs.last_mut().unwrap().insert(sk.clone(), *r);
                }
            }
        }
        for (&id, child) in &children.children {
            visit(id, child, blocks, ancestor_subs);
        }
        ancestor_subs.pop().unwrap();
    }
    let dom_tree = DominatorTree::new(&f.blocks);
    visit(
        BlockId::ENTRY,
        dom_tree.children.get(&BlockId::ENTRY).unwrap(),
        &mut f.blocks,
        &mut vec![],
    );
}
