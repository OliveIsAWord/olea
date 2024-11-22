#![allow(dead_code)]

mod arborist;
pub mod ast;
mod lexer;
mod parser;
mod ttree_visualize;
//mod codegen_fox32;
mod compiler_types;
mod ir;
// mod ir_builder;
// mod ir_optimizer;

use annotate_snippets::{Level, Message, Renderer, Snippet};
use std::process::ExitCode;

fn error(message: &str) {
    // Don't render message in bold, as is default.
    let error_renderer = Renderer::styled().emphasis(Default::default());
    let error = Level::Error.title(message);
    anstream::eprintln!("{}", error_renderer.render(error));
}

fn error_snippet(message: Message) {
    anstream::eprintln!("{}", Renderer::styled().render(message));
}

fn main() -> ExitCode {
    let args: Vec<_> = std::env::args().collect();
    if args.len() != 2 {
        error(&format!(
            "{} <file>",
            args.get(0).map_or(env!("CARGO_CRATE_NAME"), String::as_ref)
        ));
        return ExitCode::FAILURE;
    };
    let file_path = &args[1];
    let src = match std::fs::read_to_string(file_path) {
        Ok(x) => x,
        Err(e) => {
            // We can probably do better error reporting, especially for common errors like file not found.
            error(&format!("could not open `{file_path}`: {e}"));
            return ExitCode::FAILURE;
        }
    };
    println!("# Source code:\n{src}");
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
        Err(ast::Spanned { kind, span }) => {
            use arborist::ErrorKind as E;
            let title = match kind {
                E::Unexpected(c) => format!("unexpected {c:?}"),
                E::Expected(c) => format!("expected {c:?}"),
                E::Custom(msg) => msg.to_owned(),
            };
            error_snippet(
                Level::Error.title(&title).snippet(
                    Snippet::source(&src)
                        .origin(file_path)
                        .fold(true)
                        .annotation(Level::Error.span(span)),
                ),
            );
            return ExitCode::FAILURE;
        }
    };
    println!("# Token tree:");
    ttree_visualize::visualize(&ttree, &src);
    let ast = match parser::parse(&ttree, &src) {
        Ok(x) => x,
        Err(ast::Spanned { kind, span }) => {
            use parser::ErrorKind as E;
            let title = match kind {
                E::Custom(msg) => msg,
            };
            error_snippet(
                Level::Error.title(title).snippet(
                    Snippet::source(&src)
                        .origin(file_path)
                        .fold(true)
                        .annotation(Level::Error.span(span)),
                ),
            );
            return ExitCode::FAILURE;
        }
    };
    println!("#Syntax tree:\n{ast:?}");
    ExitCode::SUCCESS
}
