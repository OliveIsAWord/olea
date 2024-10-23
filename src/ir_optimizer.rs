use crate::compiler_types::{Map, Set};
use crate::ir::*;

pub fn remove_redundant_reads(f: &mut Function) {
    let mut stack_reads: Map<Register, Vec<(usize, usize)>> = f
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
            let &Inst::Store(_, StoreKind::Read(src)) = inst else {
                continue;
            };
            stack_reads.get_mut(&src).map(|vec| vec.push((block_id, i)));
        }
    }
    for locs in stack_reads.values_mut() {
        locs.sort();
    }
    for (src, locs) in stack_reads {
        for (original_block_id, i) in locs {
            let mut closed = Set::new();
            let mut open = vec![usize::MAX];
            let mut registers = Set::new();
            while let Some(block_id) = open.pop() {
                if !closed.insert(block_id) {
                    continue;
                }
                let insts = if block_id == usize::MAX {
                    &f.blocks.get(&original_block_id).unwrap().insts[..i]
                } else if block_id == original_block_id {
                    &f.blocks.get(&original_block_id).unwrap().insts[i + 1..]
                } else {
                    f.blocks.get(&block_id).unwrap().insts.as_ref()
                };
                let mut reached_beginning = block_id != original_block_id;
                for inst in insts.iter().rev() {
                    let r = match inst {
                        &Inst::Store(val, StoreKind::Read(prev_stack)) if prev_stack == src => val,
                        &Inst::Write(prev_stack, val) if prev_stack == src => val,
                        _ => continue,
                    };
                    registers.insert(r);
                    reached_beginning = false;
                    break;
                }
                if reached_beginning {
                    let block_id = if block_id == usize::MAX {
                        original_block_id
                    } else {
                        block_id
                    };
                    open.extend(f.predecessors.get(&block_id).unwrap().iter());
                }
            }
            match &mut f.blocks.get_mut(&original_block_id).unwrap().insts[i] {
                Inst::Store(_, x) => *x = StoreKind::Phi(registers),
                _ => unreachable!(),
            }
        }
    }
}

pub fn remove_redundant_writes(f: &mut Function) {
    let mut stack_writes: Map<Register, Vec<(usize, usize)>> = f
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
            stack_writes
                .get_mut(&alloc)
                .map(|vec| vec.push((block_id, i)));
        }
    }
    for locs in stack_writes.values_mut() {
        locs.sort();
    }
    for (src, locs) in stack_writes {
        for (original_block_id, i) in locs {
            let mut closed = Set::new();
            let mut open = vec![usize::MAX];
            let mut is_used = false;
            'check: while let Some(block_id) = open.pop() {
                if !closed.insert(block_id) {
                    continue;
                }
                let insts = if block_id == usize::MAX {
                    &f.blocks.get(&original_block_id).unwrap().insts[i + 1..]
                } else if block_id == original_block_id {
                    &f.blocks.get(&original_block_id).unwrap().insts[..i]
                } else {
                    f.blocks.get(&block_id).unwrap().insts.as_ref()
                };
                let mut reached_end = block_id != original_block_id;
                for inst in insts {
                    match inst {
                        &Inst::Write(stack, _) if stack == src => {
                            reached_end = false;
                            break;
                        }
                        &Inst::Store(_, StoreKind::Read(stack)) if stack == src => {
                            is_used = true;
                            break 'check;
                        }
                        _ => {}
                    }
                }
                if reached_end {
                    let block_id = if block_id == usize::MAX {
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
            println!(
                "defined: {:?}\nused: {:?}",
                block.defined_regs, block.used_regs
            );
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
                Inst::Write(_, _) | Inst::Jump(_) | Inst::CondJump(..) => true,
                Inst::Nop => false,
            });
            changed |= block.insts.len() != old_len;
        }
    }
}