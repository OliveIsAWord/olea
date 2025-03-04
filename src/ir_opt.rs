#![expect(dead_code, reason = "This code is unfinished.")]

use crate::compiler_prelude::*;
use crate::ir::*;

pub struct Pass {
    name: &'static str,
    on_function: fn(&mut Function),
}

impl Pass {
    /// Run a pass on a function
    pub fn run(&self, f: &mut Function) {
        eprintln!("running pass '{}'", self.name);
        (self.on_function)(f);
    }

    /// Run a pass on all functions in a program
    pub fn run_program(&self, p: &mut Program) {
        for f in p.functions.values_mut() {
            self.run(f);
        }
    }
}

enum Use<'a> {
    Inst(&'a Inst),
    Exit(&'a Exit),
}

// / return a vector of all uses of register
fn collect_uses(f: &Function, reg: Register) -> Vec<Use> {
    let mut uses = vec![];
    for block in f.blocks.values() {
        for inst in &block.insts {
            if inst.is_use(reg, true) {
                uses.push(Use::Inst(inst));
            }
        }
        if block.exit.is_use(reg) {
            uses.push(Use::Exit(&block.exit));
        }
    }
    uses
}

// enum UseMut<'a> {
//     Inst(&'a mut Inst),
//     Exit(&'a mut Exit),
// }

// /// return a vector of all uses of register
// fn collect_uses_mut(f: &mut Function, reg: Register) -> Vec<UseMut> {
//     let mut uses = vec![];
//     for (_, block) in f.blocks.iter_mut() {
//         for inst in block.insts.iter_mut() {
//             if inst.is_use(reg, true) {
//                 uses.push(UseMut::Inst(inst));
//             }
//         }
//         if block.exit.is_use(reg) {
//             uses.push(UseMut::Exit(&mut block.exit));
//         }
//     }
//     uses
// }

fn is_valid_candidate(f: &Function, reg: Register) -> bool {
    let uses = collect_uses(f, reg);

    // TODO: recognize returning the pointer as an invalid use

    for u in uses {
        match u {
            Use::Inst(u) => match u {
                // allowed to write to the pointer
                Inst::Write(ptr, val) => {
                    if *ptr != reg || *val == reg {
                        return false;
                    }
                }
                // allowed to read from the pointer
                Inst::Store(dst, StoreKind::Read(ptr)) => {
                    if *ptr != reg || *dst == reg {
                        return false;
                    }
                }
                // nothing else is allowed, since that would require using the
                // pointer as a value, so we cant take it out
                _ => return false,
            },
            Use::Exit(_) => return false,
        }
    }
    true
}

/// promote stack allocations to registers
pub const STACK_TO_REGISTER: Pass = Pass {
    name: "stack_to_register",
    on_function: stack_to_register_impl,
};

fn collect_stackallocs(f: &Function) -> Vec<Register> {
    let mut candidates: Vec<Register> = Vec::new();
    for block in f.blocks.values() {
        let mut subcandidates: Vec<Register> = block
            .insts
            .iter()
            .filter_map(|inst| match inst {
                Inst::Store(ptr, StoreKind::StackAlloc(_)) => Some(*ptr),
                _ => None,
            })
            .filter(|reg| is_valid_candidate(f, *reg))
            .collect();
        candidates.append(&mut subcandidates);
    }
    candidates
}

fn contains_write_to(block: &Block, var: Register) -> bool {
    block
        .insts
        .iter()
        .any(|i| matches!(i, Inst::Write(ptr, _) if *ptr == var))
}

fn phi_locations(f: &Function, stackallocs: &Vec<Register>) -> Map<Register, Set<BlockId>> {
    let locs = Map::new();

    for var in stackallocs {
        let written_blocks = f
            .blocks
            .iter()
            .filter(|(_, block)| contains_write_to(block, *var));

        let _blocks = written_blocks.clone();
    }

    locs
}

fn stack_to_register_impl(f: &mut Function) {
    // find stackallocs
    let stackallocs = collect_stackallocs(f);

    eprintln!("promotion candidates: {stackallocs:?}");

    // Write turns into Store(Copy)
    // Store(Read) turns into Store(Copy)

    // let block = f.blocks.get_mut(&BlockId::ENTRY).unwrap();

    // for candidate in candidates {
    //     let mut current_value = Register(u128::MAX);

    //     for inst in &mut block.insts {
    //         match inst {
    //             Inst::Write(ptr, val) if *ptr == candidate => {
    //                 current_value = *val;
    //                 *inst = Inst::Nop;
    //             }
    //             Inst::Store(def, StoreKind::Read(ptr)) if *ptr == candidate => {
    //                 assert!(
    //                     current_value.0 != u128::MAX,
    //                     "stack variable read before written"
    //                 );
    //                 *inst = Inst::Store(*def, StoreKind::Copy(current_value));
    //             }
    //             Inst::Store(def, StoreKind::StackAlloc(_)) if *def == candidate => {
    //                 *inst = Inst::Nop;
    //             }
    //             _ => {}
    //         }
    //     }
    // }
    // block.gen_def_use();
}

/// remove Nop instructions completely
pub const NOP_ELIMINATION: Pass = Pass {
    name: "nop_elimination",
    on_function: nop_elimination_impl,
};

fn nop_elimination_impl(f: &mut Function) {
    for block in f.blocks.values_mut() {
        block.insts.retain(|i| !matches!(i, Inst::Nop));
    }
}

/// evaluate constant expressions at compile-time.
pub const CONSTANT_PROPAGATION: Pass = Pass {
    name: "constant_propagation",
    on_function: constant_propagation_impl,
};

fn constant_propagation_impl(f: &mut Function) {
    type ConstMap = Map<Register, (i128, IntKind)>;
    let mut const_vals: ConstMap = Map::new();

    // if a constant eval can be done, do it, otherwise return None.
    let evaluate = |const_list: &ConstMap, sk: &StoreKind| -> Option<(i128, IntKind)> {
        let val = match *sk {
            StoreKind::Int(constant, kind) => (constant, kind),
            StoreKind::Copy(reg) => *const_list.get(&reg)?,
            StoreKind::UnaryOp(op, reg) => {
                let (x, kind) = *const_list.get(&reg)?;
                let val = match op {
                    UnaryOp::Neg => x.wrapping_neg(),
                };
                (val, kind)
            }
            StoreKind::BinOp(op, lhs, rhs) => {
                let (lhs, lhs_kind) = *const_list.get(&lhs)?;
                let (rhs, rhs_kind) = *const_list.get(&rhs)?;
                assert_eq!(lhs_kind, rhs_kind);
                let val = match op {
                    BinOp::Add => lhs.wrapping_add(rhs),
                    BinOp::Sub => lhs.wrapping_sub(rhs),
                    BinOp::Mul => lhs.wrapping_mul(rhs),
                    BinOp::Div => {
                        if rhs == 0 {
                            0 // TODO: we should probably properly handle this at some point
                        } else {
                            lhs.wrapping_div(rhs)
                        }
                    }
                    BinOp::BitAnd => lhs & rhs,
                    BinOp::BitOr => lhs | rhs,
                    BinOp::Shl => lhs.wrapping_shl(rhs as u32),
                    BinOp::Shr => lhs.wrapping_shr(rhs as u32),
                    BinOp::Cmp(cmp) => {
                        let b = match cmp {
                            Cmp::Lt => lhs < rhs,
                            Cmp::Le => lhs <= rhs,
                            Cmp::Eq => lhs == rhs,
                            Cmp::Ne => lhs != rhs,
                            Cmp::Gt => lhs > rhs,
                            Cmp::Ge => lhs >= rhs,
                        };
                        b.into()
                    }
                };
                (val, lhs_kind)
            }
            _ => return None,
        };
        Some(val)
    };

    // map possible registers to their constant evaluations
    // i dont like this, theres probably a better way to do this
    // works for now tho
    let mut keep_going = true;
    while keep_going {
        keep_going = false;
        for block in f.blocks.values_mut() {
            for inst in &mut block.insts {
                let Inst::Store(reg, sk) = inst else {
                    continue;
                };
                if const_vals.contains_key(reg) {
                    continue;
                }
                if let Some((const_val, int_kind)) = evaluate(&const_vals, sk) {
                    // eprintln!("map {} to constant {}", reg, const_val);
                    const_vals.insert(reg.to_owned(), (const_val, int_kind));
                    if !matches!(sk, StoreKind::Int(_, _)) {
                        keep_going = true;
                        *sk = StoreKind::Int(const_val, int_kind);
                    }
                }
            }
        }
    }
    // after we've done all the const evaluation we can, resolve any conditional jumps we can
    for block in f.blocks.values_mut() {
        match block.exit {
            Exit::Jump(_) | Exit::Return(_) => {}
            Exit::CondJump(cond, if_true, if_false) => {
                let Some(&(cond, _)) = const_vals.get(&cond) else {
                    continue;
                };
                let jump_to = if cond != 0 { if_true } else { if_false };
                block.exit = Exit::Jump(jump_to);
            }
        }
    }
}
