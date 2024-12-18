use crate::ir::*;
use crate::ir_liveness::{calculate_liveness, FunctionLiveness};

struct Codegen<'a> {
    function: &'a Function,
    function_name: &'a str,
    live: &'a FunctionLiveness,
    buffer: &'a mut String,
}

impl Codegen<'_> {
    fn build(&mut self) {
        for &id in self.function.blocks.keys() {
            self.build_block(id);
        }
        todo!()
    }
    fn build_block(&mut self, id: BlockId) {}
}

pub fn gen_program(ir: &Program) -> String {
    let mut code = String::new();
    // write_comment!(code, "Generated source code:");
    for (name, f) in &ir.functions {
        gen_function(f, name, &mut code);
        code.push('\n');
    }
    code
}

pub fn gen_function(function: &Function, function_name: &str, buffer: &mut String) {
    let live = calculate_liveness(function);
    let mut gen = Codegen {
        function,
        function_name,
        live: &live,
        buffer,
    };
    gen.build();
}
