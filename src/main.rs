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
    ir_optimizer::optimize(&mut ir);
    let code = codegen_fox32::gen_program(&ir);
    print!("{code}");
    Ok(())
}
