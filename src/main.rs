//! A compiler for the Olea programming language.

#![warn(missing_docs, clippy::allow_attributes_without_reason)]
#![allow(
    clippy::cast_possible_truncation,
    clippy::missing_panics_doc,
    clippy::option_if_let_else,
    clippy::similar_names,
    clippy::too_many_lines,
    clippy::type_complexity,
    clippy::wildcard_imports,
    clippy::cognitive_complexity,
    reason = "In the author's opinion, these lints are either too noisy or don't help correctness or sanity."
)]

mod arborist;
pub(crate) mod ast;
mod codegen_fox32;
pub(crate) mod compiler_types;
pub(crate) mod ir;
mod ir_builder;
mod ir_destructure;
mod ir_display;
pub mod ir_liveness;
mod ir_opt;
pub(crate) mod language_types;
mod lexer;
mod parser;
mod ttree_visualize;
mod typechecker;

use annotate_snippets::{Level, Message, Renderer, Snippet, renderer::Style};
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

/// A boolean flag indicating whether to output a detected error as a normal diagnostic or an internal compiler error.
#[derive(Copy, Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ErrorMode {
    /// A diagnostic indicating user error.
    User,
    /// A diagnostic indicating a bug in the compiler.
    Internal,
}

fn typecheck(ir: &ir::Program, src: &str, file_path: &str, error_mode: ErrorMode) -> bool {
    match typechecker::typecheck(ir) {
        Ok(()) => false,
        Err((fn_name, e)) => {
            use typechecker::ErrorKind as E;
            let fun = ir.functions.get(&fn_name).unwrap();
            let snippet = Snippet::source(src).origin(file_path).fold(true);
            let t = |r: ir::Register| ir.tys.format(fun.tys[&r]);
            let (title, snippet): (String, _) = match e {
                E::NotInt(reg) => (
                    format!("expected integer, got {}", t(reg)),
                    snippet.annotation(Level::Error.span(fun.spans.get(&reg).unwrap().clone())),
                ),
                E::NotPointer(reg) => (
                    format!("cannot dereference a value of type {}", t(reg),),
                    snippet.annotation(Level::Error.span(fun.spans.get(&reg).unwrap().clone())),
                ),
                E::NotFunction(reg) => (
                    format!("expected function, got {}", t(reg),),
                    snippet.annotation(Level::Error.span(fun.spans.get(&reg).unwrap().clone())),
                ),
                E::NotStruct(reg) => (
                    format!("type {} does not support field access", t(reg),),
                    snippet.annotation(Level::Error.span(fun.spans.get(&reg).unwrap().clone())),
                ),
                E::NoFieldNamed(reg, field) => (
                    format!("{} does not have field {field}", t(reg),),
                    snippet.annotation(Level::Error.span(fun.spans.get(&reg).unwrap().clone())),
                ),
                E::Expected(reg, given_ty) => (
                    format!("expected {given_ty}, got {}", t(reg)),
                    snippet.annotation(Level::Error.span(fun.spans.get(&reg).unwrap().clone())),
                ),
            };
            if error_mode == ErrorMode::Internal {
                eprint!("An internal compiler error occurred! ");
                eprintln!("An IR transformation has failed typechecking");
            }
            error_snippet(Level::Error.title(&title).snippet(snippet));
            true
        }
    }
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
    // eprintln!("# Source code:\n{src}");

    let tokens = lexer::tokenize(&src);

    /*
    dbg!(tokens.has_error);
    for i in 0..tokens.kinds.len() {
        let Spanned { kind, span } = tokens.get(i).unwrap();
        eprintln!("{:?} {:?} {:?}", &src[span.clone()], kind, span);
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
    if false {
        eprintln!("# Token tree:");
        ttree_visualize::visualize(&ttree, &src);
        eprintln!();
    }

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
                E::NotFound(kind, name) => (format!("could not find {kind} `{name}`"), None),
                E::NameConflict(kind, span) => (
                    format!("a {kind} with this name has already been defined"),
                    span.map(|span| ("previously defined here".to_owned(), span)),
                ),
                E::DoesNotYield(span) => (
                    "this expression needs to yield a value but doesn't".to_string(),
                    Some(("required by this outer context".to_owned(), span)),
                ),
                E::CantAssignToConstant => ("can't assign to constant".to_owned(), None),
                E::CantCastToTy(ty) => (format!("can't cast a value to type {ty}"), None),
                E::UnknownIntLiteralSuffix => ("unknown int literal suffix".to_owned(), None),
                E::InfiniteType(ty_names) => {
                    let s = match ty_names.len() {
                        0 => unreachable!(),
                        1 => format!("recursive type `{}` has infinite size", ty_names[0]),
                        2 => format!(
                            "recursive types `{}` and `{}` have infinite size",
                            ty_names[0], ty_names[1]
                        ),
                        _ => {
                            use std::fmt::Write;
                            let mut s = "recursive types ".to_owned();
                            for name in &ty_names[0..ty_names.len() - 1] {
                                _ = write!(s, "`{name}`, ");
                            }
                            _ = write!(s, "and `{}` have infinite size", ty_names.last().unwrap());
                            s
                        }
                    };
                    (s, None)
                }
                E::MissingArgs(fields, span) => {
                    const START: &str = "function call has missing argument";
                    let s = match fields.len() {
                        0 => unreachable!(),
                        1 => format!("{START} `{}`", fields[0]),
                        2 => format!("{START}s `{}` and `{}`", fields[0], fields[1]),
                        _ => {
                            use std::fmt::Write;
                            let mut s = format!("{START}s ");
                            for name in &fields[0..fields.len() - 1] {
                                _ = write!(s, "`{name}`, ");
                            }
                            _ = write!(s, "and `{}`", fields.last().unwrap());
                            s
                        }
                    };
                    let def = span.map(|span| ("struct defined here".to_owned(), span));
                    (s, def)
                }
                E::InvalidArgs(names) => {
                    let msg = match names.len() {
                        0 => panic!(),
                        1 => format!("invalid function argument `{}`", names[0]),
                        2 => format!(
                            "invalid function arguments `{}` and `{}`",
                            names[0], names[1]
                        ),
                        _ => {
                            use std::fmt::Write;
                            let mut s = "invalid function arguments ".to_owned();
                            for name in &names[0..names.len() - 1] {
                                _ = write!(s, "`{name}`, ");
                            }
                            _ = write!(s, "and `{}`", names.last().unwrap());
                            s
                        }
                    };
                    (msg, None)
                }
                E::BadPun => ("this expression can't be name punned".to_owned(), None),
                E::Todo(msg) => (format!("not yet implemented: {msg}"), None),
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
    // eprintln!("#IR:\n{ir}\n");
    if typecheck(&ir, &src, file_path, ErrorMode::User) {
        return ExitCode::FAILURE;
    }

    // eprintln!("#Desugaring phase");
    ir_destructure::destructure_program(&mut ir);
    // eprintln!("{ir}\n");
    if typecheck(&ir, &src, file_path, ErrorMode::Internal) {
        return ExitCode::FAILURE;
    }

    if false {
        eprintln!("#Optimizer phase");
        ir_opt::STACK_TO_REGISTER.run_program(&mut ir);
        ir_opt::CONSTANT_PROPAGATION.run_program(&mut ir);
        ir_opt::NOP_ELIMINATION.run_program(&mut ir);
        eprintln!("{ir}\n");
    }

    if true {
        /*
        for (name, f) in &ir.functions {
            let live = ir_liveness::calculate_liveness(f);
            eprintln!("{name}:");
            live.pretty_print();
        }
        eprintln!();
        */

        let asm = codegen_fox32::gen_program(&ir);
        // eprintln!("#Codegen");
        print!("{asm}");
    }
    ExitCode::SUCCESS
}
