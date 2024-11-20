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

use annotate_snippets::{Level, Renderer, Snippet};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let error_renderer = Renderer::styled();
    let file_path = "example.olea";
    let src = std::fs::read_to_string(file_path)?;
    let tokens = lexer::tokenize(&src);
    // dbg!(tokens.has_error);
    let mut bleh = vec![];
    for i in 0..tokens.len() {
        let lexer::Spanned {
            token,
            span: lexer::Span { start, len },
        } = tokens.get(i).unwrap();
        // println!("{:?} {:?}", &src[start..start + len], token);
        bleh.push(ast::Spanned {
            kind: token,
            span: start..start + len,
        });
    }
    let ttree = match arborist::arborize(&bleh).into_result() {
        Ok(x) => x,
        Err(es) => {
            for e in &es {
                let title = format!("{e:?}");
                let message = Level::Error.title(&title).snippet(
                    Snippet::source(&src)
                        .origin(file_path)
                        .fold(true)
                        .annotation(Level::Error.span(e.span().clone())),
                );
                anstream::eprintln!("{}", error_renderer.render(message));
            }
            let title = format!(
                "could not compile due to {} previous error{}",
                es.len(),
                if es.len() == 1 { "" } else { "s" },
            );
            let message = Level::Error.title(&title);
            anstream::eprintln!("{}", error_renderer.render(message));
            return Ok(());
        }
    };
    // println!("{ttree:#?}");
    ttree_visualize::visualize(&ttree, &src);
    Ok(())
}
