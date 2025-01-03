//! A compiler for the Olea programming language.

#![warn(missing_docs)]
#![allow(
    clippy::cast_possible_truncation,
    clippy::missing_panics_doc,
    clippy::option_if_let_else,
    clippy::similar_names,
    clippy::too_many_lines,
    clippy::type_complexity,
    clippy::wildcard_imports,
    clippy::cognitive_complexity
)]

mod arborist;
pub mod ast;
mod codegen_fox32;
pub mod compiler_types;
pub mod ir;
mod ir_builder;
mod ir_display;
pub mod ir_liveness;
// TODO: rewrite to account for `used_regs` not including phi arguments.
// mod ir_optimizer;
mod ir_opt;
mod lexer;
mod parser;
#[allow(dead_code)]
mod ttree_visualize;
mod typechecker;

use annotate_snippets::{renderer::Style, Level, Message, Renderer, Snippet};
use compiler_types::Spanned;
use std::process::ExitCode;

fn error(message: &str) {
    // Don't render message in bold, as is default.
    let error_renderer = Renderer::styled().emphasis(Style::default());
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
            args.first()
                .map_or(env!("CARGO_CRATE_NAME"), String::as_ref)
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
    eprintln!("# Source code:\n{src}");

    let tokens = lexer::tokenize(&src);
    /*
    dbg!(tokens.has_error);
    for i in 0..tokens.len() {
        let lexer::Spanned {
            token,
            span: lexer::Span { start, len },
        } = tokens.get(i).unwrap();
        eprintln!("{:?} {:?}", &src[start..start + len], token);
    }
    */

    let ttree = match arborist::arborize(&tokens) {
        Ok(x) => x,
        Err(Spanned { kind, span }) => {
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
    // eprintln!("# Token tree:");
    // ttree_visualize::visualize(&ttree, &src);
    // eprintln!();

    let ast = match parser::parse(&ttree, &src) {
        Ok(x) => x,
        Err(Spanned { kind, span }) => {
            let parser::ErrorKind::Custom(title) = kind;
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
    // eprintln!("#Syntax tree:\n{ast:?}\n");

    let mut ir = match ir_builder::build(&ast) {
        Ok(x) => x,
        Err(Spanned { kind, span }) => {
            use ir_builder::ErrorKind as E;
            let (title, note) = match kind {
                E::VariableNotFound(v) => (format!("could not find variable `{v}`"), None),
                E::DoesNotYield(span) => (
                    "this expression needs to yield a value but doesn't".to_string(),
                    Some(("required by this outer context".to_owned(), span)),
                ),
                E::CantAssignToConstant => ("Can't assign to constant".to_owned(), None),
            };
            let mut e = Snippet::source(&src)
                .origin(file_path)
                .fold(true)
                .annotation(Level::Error.span(span));
            if let Some((message, span)) = &note {
                e = e.annotation(Level::Info.span(span.clone()).label(message));
            }
            error_snippet(Level::Error.title(&title).snippet(e));
            return ExitCode::FAILURE;
        }
    };
    eprintln!("#IR:\n{ir}\n");

    match typechecker::typecheck(&ir) {
        Ok(()) => {}
        Err((fn_name, e)) => {
            use typechecker::ErrorKind as E;
            let fun = ir.functions.get(&fn_name).unwrap();
            let snippet = Snippet::source(&src).origin(file_path).fold(true);
            let (title, snippet): (String, _) = match e {
                E::NotPointer(reg) => (
                    format!(
                        "cannot dereference a value of type {}",
                        fun.tys.get(&reg).unwrap()
                    ),
                    snippet.annotation(Level::Error.span(fun.spans.get(&reg).unwrap().clone())),
                ),
                E::NotFunction(reg) => (
                    format!("expected function, got {}", fun.tys.get(&reg).unwrap()),
                    snippet.annotation(Level::Error.span(fun.spans.get(&reg).unwrap().clone())),
                ),
                E::Expected(reg, given_ty) => {
                    let span = fun.spans.get(&reg).unwrap().clone();
                    let reg_ty = fun.tys.get(&reg).unwrap();
                    (
                        format!("expected {given_ty}, got {reg_ty}"),
                        snippet.annotation(Level::Error.span(span)),
                    )
                }
            };
            error_snippet(Level::Error.title(&title).snippet(snippet));
            return ExitCode::FAILURE;
        }
    }

    eprintln!("#Optimizer phase");
    ir_opt::STACK2REG.run_program(&mut ir);
    ir_opt::NOPELIM.run_program(&mut ir);
    eprintln!("{ir}\n");

    for (name, f) in &ir.functions {
        let live = ir_liveness::calculate_liveness(f);
        eprintln!("{name}:");
        live.pretty_print();
    }
    eprintln!();

    let asm = codegen_fox32::gen_program(&ir);
    eprintln!("#Codegen");
    print!("{asm}");
    ExitCode::SUCCESS
}
