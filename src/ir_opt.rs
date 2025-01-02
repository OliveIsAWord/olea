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

    // run a pass on all functions in a program
    pub fn run_program(&self, p: &mut Program) {
        for (_, f) in &mut p.functions {
            self.run(f);
        }
    }

    pub const STACKPROM: Pass = Pass {
        name: "stackprom",
        on_function: stackprom_function,
    };
}

// // does A dominate B?
// fn dom(dt: &DominatorTree, A: BlockId, B: BlockId) -> bool {
//     if A == B {
//         return true;
//     }

//     // find node corresponding to block A

// }

// fn compute_frontier(dt: &DominatorTree, block: BlockId) {

// } 

fn stackprom_function(f: &mut Function) {
    assert!(f.blocks.len() == 1, "i dont wanna figure out how the dominator tree api works rn lmao");
}