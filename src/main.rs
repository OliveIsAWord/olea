mod ast;
mod codegen_fox32;
mod ir;
mod ir_builder;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let src = std::fs::read_to_string("example.olea")?;
    let st: ast::Block = serde_lexpr::from_str(&src)?;
    println!("{st:?}\n");
    let mut builder = ir_builder::IrBuilder::new();
    builder.build_block(&st, false);
    let ir = builder.finish();
    println!("{ir:?}\n");
    let code = codegen_fox32::gen_function(&ir);
    println!("; Generated source code:\n{code}");
    Ok(())
}
