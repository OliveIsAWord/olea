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

fn stack2reg_function(f: &mut Function) {

}