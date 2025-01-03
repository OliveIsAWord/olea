use crate::compiler_types::{Map, Set};
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
        for (_, f) in &mut p.functions {
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
    for (_, block) in f.blocks.iter() {
        for inst in block.insts.iter() {
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
    assert!(matches!(*f.tys.get(&reg).unwrap(), Ty::Pointer(_)));
    let uses = collect_uses(f, reg);

    // TODO: recognize returning the pointer as an invalid use

    for u in uses {
        match u {
            Use::Inst(u) => match u {
                // allowed to write to the pointer
                Inst::Write(loc, val) => {
                    // if *loc != reg || *val == reg {
                    //     return false;
                    // }
                    return *loc == reg && *val != reg
                }
                // allowed to read from the pointer
                Inst::Store(_, StoreKind::Read(_)) => {}
                // nothing else is allowed, since that would require using the
                // pointer as a value, so we cant take it out
                _ => return false
            }
            Use::Exit(_) => return false
        }
    }
    true
}

/// promote stack allocations to registers
pub const STACK_TO_REGISTER: Pass = Pass {
    name: "stack_to_register",
    on_function: stack_to_register_impl,
};

fn stack_to_register_impl(f: &mut Function) {
    assert!(f.blocks.len() == 1);
    
    let block = f.blocks.get(&BlockId::ENTRY).unwrap();
    // find stackallocs

    let candidates: Vec<Register> = block.insts.iter().filter_map(
        |inst| match inst {
            Inst::Store(ptr, StoreKind::StackAlloc(_)) => Some(*ptr),
            _ => None,
        }
    ).filter(
        |reg| is_valid_candidate(f, *reg)
    ).collect();

    println!("promotion candidates: {:?}\n", candidates);

    // Write turns into Store(Copy)
    // Store(Read) turns into Store(Copy)

    let block = f.blocks.get_mut(&BlockId::ENTRY).unwrap();

    for candidate in candidates {

        let mut current_value = Register(u128::MAX);

        for inst in block.insts.iter_mut() {
            match inst {
                Inst::Write(ptr, val) if *ptr == candidate => {
                    current_value = *val;
                    *inst = Inst::Nop;
                }
                Inst::Store(def, StoreKind::Read(ptr)) if *ptr == candidate => {
                    assert!(current_value.0 != u128::MAX, "stack variable read before written");
                    *inst = Inst::Store(*def, StoreKind::Copy(current_value));
                }
                Inst::Store(def, StoreKind::StackAlloc(_)) if *def == candidate => {
                    *inst = Inst::Nop;
                }
                _ => {}
            }
        }
    }
    block.gen_def_use();
}

/// remove Nop instructions completely
pub const NOP_ELIMINATION: Pass = Pass {
    name: "nop_elimination",
    on_function: nop_elimination_impl,
};

fn nop_elimination_impl(f: &mut Function) {
    for (_, block) in f.blocks.iter_mut() {
        block.insts.retain(|i| !matches!(i, Inst::Nop));
    }
}

pub const CONSTANT_PROPAGATION: Pass = Pass {
    name: "constant_propagation",
    on_function: constant_propagation_impl,
};

fn constant_propagation_impl(f: &mut Function) {
    // let mut worklist: Set<Register> = Set::new();

    for (blockid, block) in f.blocks.iter_mut() {
        for inst in block.insts.iter_mut() {
            
        }
    }
}