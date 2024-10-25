use crate::compiler_types::{Map, Set};
use crate::ir::*;

const NUM_REGISTERS: usize = 32;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StoreLoc {
    Register(u8),
    // Stack(u32),
}

impl StoreLoc {
    pub fn foo(self) -> String {
        match self {
            Self::Register(i) => format!("r{i}"),
        }
    }
    // stricter, must be syntactically dereferenceable
    pub fn bar(self) -> String {
        match self {
            Self::Register(i) => format!("r{i}"),
        }
    }
}

#[derive(Clone, Debug)]
struct RegAllocInfo {
    pub regs: Map<Register, StoreLoc>,
    pub local_locs: Map<Register, u32>,
    pub stack_size: u32,
}

fn reg_alloc(f: &Function) -> RegAllocInfo {
    let mut stack_size = 0;
    let local_locs: Map<Register, u32> = f
        .blocks
        .values()
        .flat_map(|b| &b.insts)
        .filter_map(|inst| match inst {
            Inst::Store(reg, StoreKind::StackAlloc(_ty)) => {
                let ret = Some((*reg, stack_size));
                stack_size += 4;
                ret
            }
            _ => None,
        })
        .collect();
    let mut regs = Map::new();
    // sort the registers because it looks nice
    let mut ir_regs: Vec<_> = f.tys.keys().copied().collect();
    ir_regs.sort();
    for (i, &reg) in ir_regs.iter().enumerate() {
        if i >= NUM_REGISTERS {
            todo!("stack allocation");
        }
        regs.insert(reg, StoreLoc::Register(i as u8));
    }
    RegAllocInfo {
        regs,
        local_locs,
        stack_size,
    }
}

// TODO: accept function name as additional argument
macro_rules! write_label {
    ($dst:expr, $($arg:tt)*) => {{
        use ::std::fmt::Write;
        let w: &mut String = &mut $dst;
        write!(w, $($arg)*).unwrap();
        w.push_str(":\n");
    }}
}

macro_rules! write_inst {
    ($dst:expr, $($arg:tt)*) => {{
        use ::std::fmt::Write;
        let w: &mut String = &mut $dst;
        w.push_str("    ");
        write!(w, $($arg)*).unwrap();
        w.push('\n');
    }}
}

pub fn gen_function(f: &Function) -> String {
    let mut code = String::new();
    let RegAllocInfo {
        regs,
        local_locs,
        stack_size,
    } = reg_alloc(f);
    let phi_map: Map<Register, (usize, Register)> = {
        let mut map = Map::new();
        let iter = f
            .blocks
            .iter()
            .flat_map(|(&id, b)| b.insts.iter().map(move |inst| (id, inst)));
        for (id, inst) in iter {
            match inst {
                Inst::Store(dst, StoreKind::Phi(regs)) => {
                    for &reg in regs {
                        map.insert(reg, (id, *dst));
                    }
                }
                _ => {}
            }
        }
        map
    };
    println!("{phi_map:?}");
    let function_name = "foo";
    let write_exit = |code: &mut String, returns: &[Register], prefix: &str| {
        write_inst!(*code, "{prefix}add rsp, {stack_size}");
        for r in returns {
            let r_reg = regs.get(r).unwrap().foo();
            write_inst!(*code, "{prefix}push {r_reg}");
        }
        write_inst!(*code, "{prefix}ret");
    };
    write_label!(code, "{function_name}_entry");
    write_inst!(code, "sub rsp, {}", stack_size);
    let mut indices: Set<usize> = f.blocks.keys().copied().collect();
    let mut i = 0;
    loop {
        assert!(indices.remove(&i));
        let block = f.blocks.get(&i).unwrap();
        let mut registers_to_merge = vec![];
        // TODO: this function and its usage is almost certainly wrong and/or bad
        let merge_phis = |code: &mut String, registers_to_merge: &[Register]| {
            for r in registers_to_merge.iter().rev() {
                let r_reg = regs.get(r).unwrap().foo();
                let (_, dst) = phi_map.get(r).unwrap();
                let dst_reg = regs.get(dst).unwrap().foo();
                write_inst!(*code, "mov {dst_reg}, {r_reg}");
            }
        };
        write_label!(code, "{function_name}_{i}");
        for inst in &block.insts {
            use StoreKind as Sk;
            match inst {
                Inst::Store(r, sk) => {
                    if phi_map.contains_key(r) {
                        registers_to_merge.push(*r);
                    }
                    let reg = regs.get(r).unwrap();
                    match sk {
                        Sk::StackAlloc(_) => {
                            write_inst!(code, "mov {}, rsp", reg.foo());
                            write_inst!(code, "add {}, {}", reg.foo(), local_locs.get(r).unwrap());
                        }
                        Sk::Int(int, _) => {
                            write_inst!(code, "mov {}, {int}", reg.foo());
                        }
                        Sk::Copy(src) => {
                            let src_reg = regs.get(src).unwrap();
                            write_inst!(code, "mov {}, {}", reg.foo(), src_reg.foo());
                        }
                        Sk::Read(src) => {
                            let src_reg = regs.get(src).unwrap();
                            write_inst!(code, "mov {}, [{}]", reg.foo(), src_reg.bar());
                        }
                        Sk::BinOp(op, lhs, rhs) => {
                            let lhs_reg = regs.get(lhs).unwrap();
                            let rhs_reg = regs.get(rhs).unwrap();
                            let op_mnemonic = match op {
                                BinOp::Add => "add",
                                BinOp::Sub => "sub",
                            };
                            write_inst!(code, "mov {}, {}", reg.foo(), lhs_reg.bar());
                            write_inst!(code, "{} {}, {}", op_mnemonic, reg.foo(), rhs_reg.bar());
                        }
                        Sk::Phi(_) => (),
                    }
                }
                Inst::Write(dst, src) => {
                    let dst_reg = regs.get(dst).unwrap();
                    let src_reg = regs.get(src).unwrap();
                    write_inst!(code, "mov [{}], {}", dst_reg.bar(), src_reg.foo());
                }
                Inst::Nop => write_inst!(code, "nop"),
            }
        }
        merge_phis(&mut code, &registers_to_merge);
        let next_i = match &block.exit {
            Exit::Jump(loc) => match loc {
                &JumpLocation::Block(jump_index) => {
                    if indices.contains(&jump_index) {
                        Some(jump_index)
                    } else {
                        write_inst!(code, "jmp {function_name}_{jump_index}");
                        None
                    }
                }
                JumpLocation::Return(regs) => {
                    write_exit(&mut code, regs, "");
                    None
                }
            },
            Exit::CondJump(cond, branch_true, branch_false) => {
                match cond {
                    Condition::NonZero(r) => {
                        let reg = regs.get(r).unwrap();
                        write_inst!(code, "cmp {}, 0", reg.foo());
                    }
                }
                let next_true = match branch_true {
                    &JumpLocation::Block(jump_index) => {
                        if indices.contains(&jump_index) {
                            Some(jump_index)
                        } else {
                            write_inst!(code, "ifnz jmp {function_name}_{jump_index}");
                            None
                        }
                    }
                    JumpLocation::Return(regs) => {
                        write_exit(&mut code, regs, "ifnz ");
                        None
                    }
                };
                let next_false = match branch_false {
                    &JumpLocation::Block(jump_index) => {
                        if next_true.is_none() && indices.contains(&jump_index) {
                            Some(jump_index)
                        } else {
                            write_inst!(code, "ifz jmp {function_name}_{jump_index}");
                            None
                        }
                    }
                    JumpLocation::Return(regs) => {
                        write_exit(&mut code, regs, "ifz ");
                        None
                    }
                };
                next_true.or(next_false)
            }
        };
        // obviously bad 2 lines of code
        if next_i.is_some() && indices.contains(&next_i.unwrap()) {
            i = next_i.unwrap();
        } else {
            match indices.iter().next() {
                Some(&next_i) => i = next_i,
                None => break,
            }
        }
    }
    code
}
