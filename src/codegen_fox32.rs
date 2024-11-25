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
    for (i, &reg) in f.tys.keys().enumerate() {
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

macro_rules! write_comment {
    ($dst:expr, $($arg:tt)*) => {{
        use ::std::fmt::Write;
        let w: &mut String = &mut $dst;
        w.push_str("; ");
        write!(w, $($arg)*).unwrap();
        w.push('\n');
    }}
}

pub fn gen_program(ir: &Program) -> String {
    let mut code = String::new();
    write_comment!(code, "Generated source code:");
    // TODO: this shouldn't be a hardcoded value
    if ir.functions.contains_key("main") {
        write_inst!(code, "jmp main");
    }
    for (name, f) in &ir.functions {
        let fn_output = gen_function(f, name);
        code.push_str(&fn_output);
        code.push('\n');
    }
    code
}

pub fn gen_function(f: &Function, function_name: &str) -> String {
    let mut code = String::new();
    let RegAllocInfo {
        regs,
        local_locs,
        stack_size,
    } = reg_alloc(f);
    let write_exit = |code: &mut String, returns: &[Register], prefix: &str| {
        write_inst!(*code, "{prefix}add rsp, {stack_size}");
        for r in returns {
            let r_reg = regs.get(r).unwrap().foo();
            write_inst!(*code, "{prefix}push {r_reg}");
        }
        write_inst!(*code, "{prefix}ret");
    };
    write_label!(code, "{function_name}_entry");
    write_inst!(code, "pop rfp");
    for arg in f.parameters.iter().rev() {
        let arg_reg = regs.get(arg).unwrap();
        write_inst!(code, "pop {}", arg_reg.foo());
    }
    write_inst!(code, "push rfp");
    write_inst!(code, "sub rsp, {}", stack_size);
    let mut indices: Set<BlockId> = f.blocks.keys().copied().collect();
    let mut i = BlockId::ENTRY;
    loop {
        use StoreKind as Sk;
        assert!(indices.remove(&i));
        let block = f.blocks.get(&i).unwrap();
        write_label!(code, "{function_name}_{}", i.0);
        for inst in &block.insts {
            match inst {
                Inst::Store(r, sk) => {
                    let reg = regs.get(r).unwrap();
                    match sk {
                        Sk::StackAlloc(_) => {
                            write_inst!(code, "mov {}, rsp", reg.foo());
                            write_inst!(code, "add {}, {}", reg.foo(), local_locs.get(r).unwrap());
                        }
                        Sk::Int(int) => {
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
                        Sk::UnaryOp(op, inner) => {
                            let inner_reg = regs.get(inner).unwrap();
                            let op_mnemonic = match op {
                                UnaryOp::Neg => "neg",
                            };
                            write_inst!(code, "mov {}, {}", reg.foo(), inner_reg.foo());
                            write_inst!(code, "{} {}", op_mnemonic, reg.foo());
                        }
                        Sk::BinOp(op, lhs, rhs) => {
                            let lhs_reg = regs.get(lhs).unwrap();
                            let rhs_reg = regs.get(rhs).unwrap();
                            let op_mnemonic = match op {
                                BinOp::Add => "add",
                                BinOp::Sub => "sub",
                                BinOp::Mul => "mul",
                            };
                            write_inst!(code, "mov {}, {}", reg.foo(), lhs_reg.foo());
                            write_inst!(code, "{} {}, {}", op_mnemonic, reg.foo(), rhs_reg.foo());
                        }
                        Sk::Function(name) => write_inst!(code, "mov {}, {name}", reg.foo()),
                        Sk::Phi(_) => (),
                    }
                }
                Inst::Write(dst, src) => {
                    let dst_reg = regs.get(dst).unwrap();
                    let src_reg = regs.get(src).unwrap();
                    write_inst!(code, "mov [{}], {}", dst_reg.bar(), src_reg.foo());
                }
                Inst::Call {
                    callee,
                    returns,
                    args,
                } => {
                    write_comment!(code, "begin function call");
                    write_comment!(code, "save register state");
                    for &r in regs.values().rev() {
                        if regs
                            .iter()
                            .any(|(&ir_reg, &loc)| returns.contains(&ir_reg) && r == loc)
                        {
                            continue;
                        }
                        match r {
                            StoreLoc::Register(_) => write_inst!(code, "push {}", r.foo()),
                        }
                    }
                    write_comment!(code, "pass arguments");
                    for r in args.iter().rev() {
                        let reg = regs.get(r).unwrap();
                        write_inst!(code, "push {}", reg.foo());
                    }
                    write_inst!(code, "call {callee}");
                    write_comment!(code, "get return values");
                    for r in returns {
                        let reg = regs.get(r).unwrap();
                        write_inst!(code, "pop {}", reg.foo());
                    }
                    write_comment!(code, "restore register state");
                    for &r in regs.values().rev() {
                        if regs
                            .iter()
                            .any(|(&ir_reg, &loc)| returns.contains(&ir_reg) && r == loc)
                        {
                            continue;
                        }
                        match r {
                            StoreLoc::Register(_) => write_inst!(code, "pop {}", r.foo()),
                        }
                    }
                    write_comment!(code, "end function call");
                }
                Inst::Nop => write_inst!(code, "nop"),
            }
        }
        let merge_phis = |code: &mut String, jump_index, prefix| {
            let jump_block = f.blocks.get(&jump_index).unwrap();
            for inst in &jump_block.insts {
                let Inst::Store(dst, Sk::Phi(srcs)) = inst else {
                    continue;
                };
                let src = srcs.get(&i).unwrap();
                let dst_reg = regs.get(dst).unwrap().foo();
                let src_reg = regs.get(src).unwrap().foo();
                write_inst!(*code, "{prefix}mov {dst_reg}, {src_reg}");
            }
        };
        let next_i = match &block.exit {
            Exit::Jump(loc) => match loc {
                &JumpLocation::Block(jump_index) => {
                    merge_phis(&mut code, jump_index, "");
                    if indices.contains(&jump_index) {
                        Some(jump_index)
                    } else {
                        write_inst!(code, "jmp {function_name}_{}", jump_index.0);
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
                        merge_phis(&mut code, jump_index, "ifnz ");
                        if indices.contains(&jump_index) {
                            Some(jump_index)
                        } else {
                            write_inst!(code, "ifnz jmp {function_name}_{}", jump_index.0);
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
                        merge_phis(&mut code, jump_index, "ifz ");
                        if next_true.is_none() && indices.contains(&jump_index) {
                            Some(jump_index)
                        } else {
                            write_inst!(code, "ifz jmp {function_name}_{}", jump_index.0);
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
