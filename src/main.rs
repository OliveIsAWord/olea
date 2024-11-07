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
    let mut output = format!("{ir}");
    println!("{output}\n");
    for (name, pass) in ir_optimizer::PASSES {
        pass(&mut ir);
        let new_output = format!("{ir}");
        // Yes, this is silly, but it works. What we should actually do is have each pass return whether it was able to optimize anything.
        if output == new_output {
            println!("{name}: no change");
        } else {
            output = new_output;
            println!("!! {name}:\n{output}\n");
        }
    }
    let code = codegen_fox32::gen_function(&ir);
    println!("; Generated source code:\n{code}");
    Ok(())
}
