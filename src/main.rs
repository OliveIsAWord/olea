#![allow(dead_code)]

mod arborist;
pub mod ast;
mod chumsky_types;
mod lexer;
mod ttree_visualize;
// mod parser;
//mod codegen_fox32;
mod compiler_types;
mod ir;
// mod ir_builder;
// mod ir_optimizer;

// use annotate_snippets::{Level, Renderer, Snippet};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // let error_renderer = Renderer::styled();
    let file_path = "example.olea";
    let src = std::fs::read_to_string(file_path)?;
    let tokens = lexer::tokenize(&src);
    // dbg!(tokens.has_error);
    /*
    for i in 0..tokens.len() {
        let lexer::Spanned {
            token,
            span: lexer::Span { start, len },
        } = tokens.get(i).unwrap();
        println!("{:?} {:?}", &src[start..start + len], token);
    }
    */
    let ttree = match arborist::arborize(&tokens) {
        Ok(x) => x,
        Err(()) => return Ok(()),
    };
    // println!("{ttree:#?}");
    ttree_visualize::visualize(&ttree, &src);
    Ok(())
}
