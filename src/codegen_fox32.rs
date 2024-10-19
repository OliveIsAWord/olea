use crate::ir::*;
use std::collections::{HashMap, HashSet};

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
    pub regs: HashMap<Register, StoreLoc>,
    pub local_locs: HashMap<Register, u32>,
    pub stack_size: u32,
}

fn reg_alloc(f: &Function) -> RegAllocInfo {
    let mut stack_size = 0;
    let local_locs: HashMap<Register, u32> = f
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
    let mut regs = HashMap::new();
    for (i, (&reg, _ty)) in f.tys.iter().enumerate() {
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

/*
struct Sorterrr<'a, V> {
    map: &'a HashMap<usize, V>,
    next_index: usize,
    items_to_yield: usize,
}

impl<'a, V> Sorterrr<'a, V> {
    pub fn new(map: &'a HashMap<usize, V>) -> Self {
        Self {
            map,
            next_index: 0,
            items_to_yield: map.len(),
        }
    }
}

impl<'a, V> Iterator for Sorterrr<'a, V> {
    type Item = (usize, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        if self.items_to_yield == 0 {
            return None;
        }
        self.items_to_yield -= 1;
        loop {
            let i = self.next_index;
            self.next_index += 1;
            if let Some(v) = self.map.get(&i) {
                break Some((i, v));
            }
        }
    }
}
*/

pub fn gen_function(f: &Function) -> String {
    let mut code = String::new();
    let RegAllocInfo {
        regs,
        local_locs,
        stack_size,
    } = reg_alloc(f);
    let function_name = "foo";
    write_label!(code, "{function_name}_entry");
    write_inst!(code, "sub rsp, {}", stack_size);
    let mut indices: HashSet<usize> = f.blocks.keys().copied().collect();
    let mut i = 0;
    loop {
        assert!(indices.remove(&i));
        let block = f.blocks.get(&i).unwrap();
        write_label!(code, "{function_name}_{i}");
        let mut next_i = None;
        for inst in &block.insts {
            use StoreKind as Sk;
            match inst {
                Inst::Store(r, sk) => {
                    let reg = regs.get(r).unwrap();
                    match sk {
                        Sk::StackAlloc(_) => {
                            write_inst!(code, "mov {}, rsp", reg.foo());
                            write_inst!(code, "add {}, {}", reg.foo(), local_locs.get(r).unwrap());
                        }
                        Sk::Int(int, _) => {
                            write_inst!(code, "mov {}, {int}", reg.foo());
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
                        e @ Sk::Phi(..) => todo!("{e:?}"),
                    }
                }
                Inst::Write(dst, src) => {
                    let dst_reg = regs.get(dst).unwrap();
                    let src_reg = regs.get(src).unwrap();
                    write_inst!(code, "mov [{}], {}", dst_reg.bar(), src_reg.foo());
                }
                Inst::Jump(loc) => match loc {
                    &JumpLocation::Block(jump_index) => {
                        if indices.contains(&jump_index) {
                            assert_eq!(next_i, None);
                            next_i = Some(jump_index);
                        } else {
                            write_inst!(code, "jmp {function_name}_{jump_index}");
                        }
                    }
                },
                Inst::CondJump(cond, branch_true, branch_false) => {
                    match cond {
                        Condition::NonZero(r) => {
                            let reg = regs.get(r).unwrap();
                            write_inst!(code, "cmp {}, 0", reg.foo());
                        }
                    }
                    match branch_true {
                        &JumpLocation::Block(jump_index) => {
                            if indices.contains(&jump_index) {
                                assert_eq!(next_i, None);
                                next_i = Some(jump_index);
                            } else {
                                write_inst!(code, "ifnz jmp {function_name}_{jump_index}");
                            }
                        }
                    }
                    match branch_false {
                        &JumpLocation::Block(jump_index) => {
                            if next_i.is_none() && indices.contains(&jump_index) {
                                next_i = Some(jump_index);
                            } else {
                                write_inst!(code, "ifz jmp {function_name}_{jump_index}");
                            }
                        }
                    }
                }
            }
        }
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
