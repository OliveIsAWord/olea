use crate::ir::*;
use std::collections::{HashMap, HashSet};

pub fn remove_redundant_reads(f: &mut Function) {
    let mut stack_reads: HashMap<Register, Vec<(usize, usize)>> = f
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
    println!("{stack_reads:?}");
    for (src, locs) in stack_reads {
        for (original_block_id, i) in locs {
            println!(
                "optimizing ({original_block_id}, {i}): {:?}",
                f.blocks.get_mut(&original_block_id).unwrap().insts[i]
            );
            let mut closed = HashSet::new();
            let mut open = vec![usize::MAX];
            let mut registers = HashSet::new();
            while let Some(block_id) = open.pop() {
                println!("open: {block_id} {open:?}");
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
    let mut stack_writes: HashMap<Register, Vec<(usize, usize)>> = f
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
    println!("{stack_writes:?}");
    for (src, locs) in stack_writes {
        for (original_block_id, i) in locs {
            println!(
                "optimizing ({original_block_id}, {i}): {:?}",
                f.blocks.get_mut(&original_block_id).unwrap().insts[i]
            );
            let mut closed = HashSet::new();
            let mut open = vec![usize::MAX];
            let mut is_used = false;
            'check: while let Some(block_id) = open.pop() {
                println!("open: {block_id} {open:?}");
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
                    println!("{inst:?}");
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
