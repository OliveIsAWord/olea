use crate::compiler_types::{Map, Set, Str};
use crate::ir::*;
use crate::ir_liveness::{self, FunctionLiveness};

const NUM_REGISTERS: usize = 31;
const TEMP_REG: StoreLoc = StoreLoc::Register(31);

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum StoreLoc {
    Register(u8),
    Constant(Str),
    // Stack(u32),
}

impl StoreLoc {
    pub fn foo(&self) -> Str {
        match self {
            Self::Register(i) => format!("r{i}").into(),
            Self::Constant(c) => c.clone(),
        }
    }
    // stricter, must be syntactically dereferenceable
    pub fn bar(&self) -> Str {
        match self {
            Self::Register(i) => format!("r{i}").into(),
            Self::Constant(c) => c.clone(),
        }
    }
}

#[derive(Clone, Debug, Default)]
struct LivenessGraph {
    regs: Map<Register, Set<Register>>,
}

impl LivenessGraph {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn from_function_liveness(live: &FunctionLiveness) -> Self {
        let mut this = Self::new();
        live.blocks
            .values()
            .flat_map(|block_live| std::iter::once(&block_live.start).chain(&block_live.insts))
            .for_each(|set| this.insert_set(set));
        this
    }
    pub fn minmax(a: Register, b: Register) -> (Register, Register) {
        let min = a.min(b);
        let max = a.max(b);
        assert!(min != max, "inserted same register {a} {b}");
        (min, max)
    }
    pub fn get(&self, a: Register, b: Register) -> bool {
        let (min, max) = Self::minmax(a, b);
        self.regs.get(&min).map_or(false, |s| s.contains(&max))
    }
    pub fn insert(&mut self, a: Register, b: Register) {
        let (min, max) = Self::minmax(a, b);
        self.regs.entry(min).or_default().insert(max);
    }
    pub fn insert_set(&mut self, set: &Set<Register>) {
        for (i, &min) in set.iter().enumerate() {
            for &max in set.iter().skip(i + 1) {
                self.insert(min, max);
            }
        }
    }
}

#[derive(Clone, Debug)]
struct RegAllocInfo {
    pub regs: Map<Register, StoreLoc>,
    pub local_locs: Map<Register, u32>,
    pub stack_size: u32,
    pub liveness: FunctionLiveness,
}

fn reg_alloc(f: &Function) -> RegAllocInfo {
    let liveness = ir_liveness::calculate_liveness(f);
    let live_graph = LivenessGraph::from_function_liveness(&liveness);
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
    let mut regs: Map<Register, StoreLoc> = Map::new();
    let mut open: Set<_> = f.tys.keys().copied().collect();
    for block in f.blocks.values() {
        for inst in &block.insts {
            let Inst::Store(r, sk) = inst else {
                continue;
            };
            let constant_str = match sk {
                // cast from i128 to u32 because fox32asm doesn't support negative int literals
                #[allow(clippy::cast_sign_loss)]
                &StoreKind::Int(i) => (i as u32).to_string().into(),
                StoreKind::Function(name) => name.clone(),
                _ => continue,
            };
            open.remove(r);
            regs.insert(*r, StoreLoc::Constant(constant_str));
        }
    }
    let mut reg_counter = 0;
    while let Some(reg) = open.pop_first() {
        let store_loc = if reg_counter < NUM_REGISTERS {
            let x = StoreLoc::Register(reg_counter as u8);
            reg_counter += 1;
            x
        } else {
            todo!("stack spilling");
            // let x = StoreLoc::Stack(stack_size);
            // stack_size += 4;
            // x
        };
        regs.insert(reg, store_loc.clone());
        let mut shared = Set::new();
        shared.insert(reg);
        open.retain(|&fellow_reg| {
            if shared.iter().any(|&r| live_graph.get(r, fellow_reg)) {
                return true;
            }
            shared.insert(fellow_reg);
            regs.insert(fellow_reg, store_loc.clone());
            false
        });
    }
    RegAllocInfo {
        regs,
        local_locs,
        stack_size,
        liveness,
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

#[allow(unused_macros)]
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
    for (i, (name, f)) in ir.functions.iter().enumerate() {
        if i != 0 {
            code.push('\n');
        }
        let fn_output = gen_function(f, name);
        code.push_str(&fn_output);
    }
    code
}

pub fn gen_function(f: &Function, function_name: &str) -> String {
    let mut code = String::new();
    let RegAllocInfo {
        regs,
        local_locs,
        stack_size,
        liveness,
    } = reg_alloc(f);
    {
        let locs: Set<_> = regs.values().collect();
        for loc in locs {
            eprint!("{}:", loc.foo());
            for (r, r_loc) in &regs {
                if loc == r_loc {
                    eprint!(" {r}");
                }
            }
            eprintln!();
        }
    }
    let size_of_ir_value = |_| 4;
    write_label!(code, "{function_name}");
    if !f.parameters.is_empty() {
        write_inst!(code, "pop rfp");
        for arg in &f.parameters {
            match regs.get(arg).unwrap() {
                StoreLoc::Register(i) => write_inst!(code, "pop r{i}"),
                StoreLoc::Constant(_) => unreachable!(),
                // e @ StoreLoc::Stack(_) => todo!("function argument got assigned {e:?}"),
            }
        }
        write_inst!(code, "push rfp");
    }
    if stack_size != 0 {
        write_inst!(code, "sub rsp, {}", stack_size);
    }
    let mut indices: Set<BlockId> = f.blocks.keys().copied().collect();
    let mut i = BlockId::ENTRY;
    loop {
        use StoreKind as Sk;
        assert!(indices.remove(&i));
        let block = f.blocks.get(&i).unwrap();
        write_label!(code, "{function_name}_{}", i.0);
        for (inst_i, inst) in block.insts.iter().enumerate() {
            match inst {
                Inst::Store(r, sk) => {
                    let reg = regs.get(r).unwrap();
                    if matches!(reg, StoreLoc::Constant(_)) {
                        assert!(matches!(sk, Sk::Int(_) | Sk::Function(_)));
                        continue;
                    }
                    match sk {
                        Sk::StackAlloc(_) => {
                            write_inst!(code, "mov {}, rsp", reg.foo());
                            let stack_offset = *local_locs.get(r).unwrap();
                            if stack_offset != 0 {
                                write_inst!(code, "add {}, {}", reg.foo(), stack_offset);
                            }
                        }
                        Sk::Copy(src) => {
                            let src_reg = regs.get(src).unwrap();
                            if reg != src_reg {
                                write_inst!(code, "mov {}, {}", reg.foo(), src_reg.foo());
                            }
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
                            if reg != inner_reg {
                                write_inst!(code, "mov {}, {}", reg.foo(), inner_reg.foo());
                            }
                            write_inst!(code, "{} {}", op_mnemonic, reg.foo());
                        }
                        Sk::BinOp(op, lhs, rhs) => {
                            let lhs_reg = regs.get(lhs).unwrap();
                            let rhs_reg = regs.get(rhs).unwrap();
                            let arithmetic = |mnemonic| {
                                Box::new(move |code: &mut String| {
                                    if reg != lhs_reg {
                                        write_inst!(*code, "mov {}, {}", reg.foo(), lhs_reg.foo());
                                    }
                                    write_inst!(
                                        *code,
                                        "{mnemonic} {}, {}",
                                        reg.foo(),
                                        rhs_reg.foo(),
                                    );
                                }) as Box<dyn Fn(&mut String)>
                            };
                            let comparison = |condition| {
                                Box::new(move |code: &mut String| {
                                    write_inst!(*code, "cmp {}, {}", lhs_reg.foo(), rhs_reg.foo());
                                    // NOTE: This `mov` comes after the comparison because `reg` might be the same as `lhs_reg` or `rhs_reg` and we don't want to overwrite the value before the comparison.
                                    write_inst!(*code, "mov {}, 0", reg.foo());
                                    write_inst!(*code, "{condition} mov {}, 1", reg.foo());
                                })
                            };
                            let compile = match op {
                                BinOp::Add => arithmetic("add"),
                                BinOp::Sub => arithmetic("sub"),
                                BinOp::Mul => arithmetic("mul"),
                                BinOp::CmpLe => comparison("iflteq"),
                            };
                            compile(&mut code);
                        }
                        Sk::PtrOffset(lhs, rhs) => {
                            let lhs_reg = regs.get(lhs).unwrap();
                            let rhs_reg = regs.get(rhs).unwrap();
                            if reg != lhs_reg {
                                write_inst!(code, "mov {}, {}", reg.foo(), lhs_reg.foo());
                            }
                            write_inst!(code, "mov {}, {}", TEMP_REG.foo(), size_of_ir_value(lhs));
                            write_inst!(code, "mul {}, {}", TEMP_REG.foo(), rhs_reg.foo());
                            write_inst!(code, "add {}, {}", reg.foo(), TEMP_REG.foo());
                        }
                        Sk::Int(_) | Sk::Function(_) => unreachable!(
                            "register store should have been optimized as a constant literal"
                        ),
                        Sk::Phi(_) => (),
                        // _ => write_comment!(code, "TODO: {inst:?}"),
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
                    let saved: Set<_> = {
                        let mut saved: Set<_> = liveness.blocks[&i].insts[inst_i]
                            .iter()
                            .map(|r| regs.get(r).unwrap())
                            .collect();
                        for r in returns {
                            saved.remove(regs.get(r).unwrap());
                        }
                        saved
                    };
                    for &r in saved.iter().rev() {
                        match r {
                            StoreLoc::Register(_) => write_inst!(code, "push {}", r.foo()),
                            StoreLoc::Constant(_) => {}
                        }
                    }
                    for r in args.iter().rev() {
                        let reg = regs.get(r).unwrap();
                        write_inst!(code, "push {}", reg.foo());
                    }
                    let callee_reg = regs.get(callee).unwrap();
                    write_inst!(code, "call {}", callee_reg.foo());
                    for r in returns {
                        let reg = regs.get(r).unwrap();
                        write_inst!(code, "pop {}", reg.foo());
                    }
                    for r in saved {
                        match r {
                            StoreLoc::Register(_) => write_inst!(code, "pop {}", r.foo()),
                            StoreLoc::Constant(_) => {}
                        }
                    }
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
            Exit::Jump(loc) => {
                merge_phis(&mut code, *loc, "");
                if indices.contains(loc) {
                    Some(loc)
                } else {
                    write_inst!(code, "jmp {function_name}_{}", loc.0);
                    None
                }
            }
            Exit::CondJump(cond, branch_true, branch_false) => {
                match cond {
                    Condition::NonZero(r) => {
                        let reg = regs.get(r).unwrap();
                        write_inst!(code, "cmp {}, 0", reg.foo());
                    }
                }
                let next_true = {
                    merge_phis(&mut code, *branch_true, "ifnz ");
                    if indices.contains(branch_true) {
                        Some(branch_true)
                    } else {
                        write_inst!(code, "ifnz jmp {function_name}_{}", branch_true.0);
                        None
                    }
                };
                let next_false = {
                    merge_phis(&mut code, *branch_false, "ifz ");
                    if next_true.is_none() && indices.contains(branch_false) {
                        Some(branch_false)
                    } else {
                        write_inst!(code, "ifz jmp {function_name}_{}", branch_false.0);
                        None
                    }
                };
                next_true.or(next_false)
            }
            Exit::Return(returns) => {
                if stack_size != 0 {
                    write_inst!(code, "add rsp, {stack_size}");
                }
                if returns.is_empty() {
                    write_inst!(code, "ret");
                } else {
                    write_inst!(code, "pop rfp");
                    for r in returns {
                        let r_reg = regs.get(r).unwrap().foo();
                        write_inst!(code, "push {r_reg}");
                    }
                    write_inst!(code, "jmp rfp");
                }
                None
            }
        };
        // obviously bad 2 lines of code
        if next_i.is_some() && indices.contains(next_i.unwrap()) {
            i = *next_i.unwrap();
        } else {
            match indices.iter().next() {
                Some(&next_i) => i = next_i,
                None => break,
            }
        }
    }
    code
}
