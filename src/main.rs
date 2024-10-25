mod ast;
mod codegen_fox32;
mod compiler_types;
mod ir;
mod ir_builder;
mod ir_optimizer;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let src = std::fs::read_to_string("example.olea")?;
    let st: ast::Program = serde_lexpr::from_str(&src)?;
    println!("{st:?}\n");
    let mut ir = ir_builder::build(&st);
    println!("{ir}\n");
    ir_optimizer::remove_redundant_reads(&mut ir);
    println!("removed redundant reads!\n{ir}\n");
    ir_optimizer::remove_redundant_writes(&mut ir);
    println!("removed redundant writes!\n{ir}\n");
    ir_optimizer::dead_code_elimination(&mut ir);
    println!("dead code elimination!\n{ir}\n");
    ir_optimizer::common_subexpression_elimination(&mut ir);
    println!("common subexpression elimination!\n{ir}\n");
    let code = codegen_fox32::gen_function(&ir);
    println!("; Generated source code:\n{code}");
    Ok(())
}
