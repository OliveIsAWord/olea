use crate::compiler_types::{Map, Set};
use crate::ir::*;

// (sandwich): some shit

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
pub const STACK2REG: Pass = Pass {
    name: "stack2reg",
    on_function: stack2reg_function,
};

fn stack2reg_function(f: &mut Function) {
    assert!(f.blocks.len() == 1);
    
    let block = f.blocks.get(&BlockId::ENTRY).unwrap();
    // find stackallocs
    let candidates = block.insts.iter();

    let candidate_pairs: Vec<Register> = candidates.filter_map(
        |inst| match inst {
            Inst::Store(ptr, StoreKind::StackAlloc(_)) => Some(*ptr),
            _ => None,
        }
    ).filter(
        |reg| is_valid_candidate(f, *reg)
    ).collect();

    println!("promotion candidates: {:?}\n", candidate_pairs);

    // Write turns into Store(Copy)
    // Store(Read) turns into Store(Copy)

    let block = f.blocks.get_mut(&BlockId::ENTRY).unwrap();

    for candidate in candidate_pairs {

        let mut current_value = Register(0);

        for inst in block.insts.iter_mut() {
            match inst {
                Inst::Write(ptr, val) if *ptr == candidate => {
                    current_value = *val;
                    *inst = Inst::Nop;
                }
                Inst::Store(def, StoreKind::Read(ptr)) if *ptr == candidate => {
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
pub const NOPELIM: Pass = Pass {
    name: "nopelim",
    on_function: nopelim_function,
};

fn nopelim_function(f: &mut Function) {
    for (_, block) in f.blocks.iter_mut() {
        block.insts.retain(|i| !matches!(i, Inst::Nop));
    }
}

pub const CONSTPROP: Pass = Pass {
    name: "constprop",
    on_function: constprop_function,
};

fn constprop_function(f: &mut Function) {
    // let mut worklist: Set<Register> = Set::new();

    // for (blockid, block) in f.blocks.iter_mut() {
    //     for inst in block.insts.iter_mut() {
    //         match inst {
    //             Inst::Store(_, sk) => match sk {
    //                 StoreKind::Copy(input) => {
                        
    //                 }
    //             }
    //         }
    //     }
    // }
}