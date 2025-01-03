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

/// promote stack allocations to registers
pub const STACK2REG: Pass = Pass {
    name: "stack2reg",
    on_function: stack2reg_function,
};

/// return a vector of all uses of register
fn collect_uses(f: &Function, reg: Register) -> Vec<&Inst> {
    let mut uses = vec![];
    for (_, block) in f.blocks.iter() {
        for inst in block.insts.iter() {
            if inst.is_use(reg, true) {
                uses.push(inst);
            }
        }
    }
    uses
}

/// return a vector of all uses of register
fn collect_uses_mut(f: &mut Function, reg: Register) -> Vec<&mut Inst> {
    let mut uses = vec![];
    for (_, block) in f.blocks.iter_mut() {
        for inst in block.insts.iter_mut() {
            if inst.is_use(reg, true) {
                uses.push(inst);
            }
        }
    }
    uses
}

fn is_valid_candidate(f: &Function, reg: Register) -> bool {
    assert!(matches!(*f.tys.get(&reg).unwrap(), Ty::Pointer(_)));
    let uses = collect_uses(f, reg);

    // TODO: recognize returning the pointer as an invalid use

    for u in uses {
        match u {
            // allowed to write to the pointer
            Inst::Write(loc, val) => {
                if *loc != reg || *val == reg {
                    return false;
                }
            }
            // allowed to read from the pointer
            Inst::Store(_, StoreKind::Read(_)) => {}
            // nothing else is allowed, since that would require using the
            // pointer as a value, so we cant take it out
            _ => return false
        }
    }
    true
}

fn stack2reg_function(f: &mut Function) {
    assert!(f.blocks.len() == 1);
    let block = f.blocks.get(&BlockId::ENTRY).unwrap();
    // find stackallocs
    let candidates = block.insts.iter();

    let candidate_regs = candidates.filter_map(
        |inst| match inst {
            Inst::Store(ptr, StoreKind::StackAlloc(_)) => Some(ptr),
            _ => None,
        }
    );

    let candidate_regs = candidate_regs.filter(
        |reg| is_valid_candidate(f, **reg)
    );

    let x: Vec<&Register> = candidate_regs.collect();

    println!("{:?}", x);
}