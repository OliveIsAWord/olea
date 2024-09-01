use crate::lexer::{Iter, Span, Spanned, Token, Tokens, T};
use chumsky::extra::Full;
use chumsky::input::{Input, SpannedInput, Stream};
use chumsky::prelude::*;

#[derive(Clone, Debug)]
pub struct Program<Meta> {
    pub decls: Vec<Decl<Meta>>,
    pub meta: Meta,
}

#[derive(Clone, Debug)]
pub struct Decl<Meta> {
    pub kind: DeclKind<Meta>,
    pub meta: Meta,
}

#[derive(Clone, Debug)]
pub enum DeclKind<Meta> {
    Error,
    Function {
        name: String,
        parameters: Vec<(String, String)>,
        returns: Option<String>,
        body: Block<Meta>,
    },
}

#[derive(Clone, Debug)]
pub struct Block<Meta> {
    pub statements: Vec<Statement<Meta>>,
    pub meta: Meta,
}

#[derive(Clone, Debug)]
pub struct Statement<Meta> {
    pub kind: StatementKind<Meta>,
    pub meta: Meta,
}

#[derive(Clone, Debug)]
pub enum StatementKind<Meta> {
    Error,
    Expr(Expr<Meta>),
    // Decl(Decl<Meta>),
}

#[derive(Clone, Debug)]
pub struct Expr<Meta> {
    pub kind: ExprKind<Meta>,
    pub meta: Meta,
}

#[derive(Clone, Debug)]
pub enum ExprKind<Meta> {
    Error,
    Var(String),
    BinOp(BinOp, Box<Expr<Meta>>, Box<Expr<Meta>>),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum BinOp {
    Add,
    Mul,
}

// We should change the error type to `Cheap<Token, Span>` once we're confident there will be no parse errors.
type Extra<'a> = Full<Simple<'a, Token, Span>, &'a str, ()>;
type In<'a> = SpannedInput<Token, Span, Stream<Iter<'a>>>;

pub fn parse_program<'a>() -> impl Parser<'a, In<'a>, Program<Span>, Extra<'a>> {
    parse_decl()
        .repeated()
        .collect()
        .map_with(|decls, extra| Program {
            decls,
            meta: extra.span(),
        })
        .then_ignore(end())
}

pub fn parse_decl<'a>() -> impl Parser<'a, In<'a>, Decl<Span>, Extra<'a>> {
    parse_function().map_with(|kind, extra| Decl {
        kind,
        meta: extra.span(),
    })
}

pub fn parse_function<'a>() -> impl Parser<'a, In<'a>, DeclKind<Span>, Extra<'a>> {
    just(T::Fn)
        .ignore_then(parse_name())
        .then(parse_list(
            just(T::ParenOpen),
            just(T::ParenClose),
            parse_name().then(parse_name()),
        ))
        .then(just(T::ThinArrow).ignore_then(parse_name()).or_not())
        .then(parse_block())
        .map(|(((name, parameters), returns), body)| DeclKind::Function {
            name,
            parameters,
            returns,
            body,
        })
}

pub fn parse_block<'a>() -> impl Parser<'a, In<'a>, Block<Span>, Extra<'a>> {
    just(T::Colon).ignore_then(parse_list(empty(), empty(), parse_statement()).map_with(
        |statements, extra| Block {
            statements,
            meta: extra.span(),
        },
    ))
}

pub fn parse_statement<'a>() -> impl Parser<'a, In<'a>, Statement<Span>, Extra<'a>> {
    parse_expr(true).map_with(|expr, extra| Statement {
        kind: StatementKind::Expr(expr),
        meta: extra.span(),
    })
}

pub fn parse_expr<'a>(consume_newline: bool) -> impl Parser<'a, In<'a>, Statement<Span>, Extra<'a>> {
    todo()
}

pub fn parse_list<'a, E, P, P2, Awa>(
    open: P2,
    close: P2,
    elem: P,
) -> impl Parser<'a, In<'a>, Vec<E>, Extra<'a>>
where
    P2: Parser<'a, In<'a>, Awa, Extra<'a>>,
    P: Parser<'a, In<'a>, E, Extra<'a>>,
{
    let elems = elem.then_ignore(just(T::Newline)).repeated().collect();
    open.ignore_then(just(T::Newline))
        .ignore_then(just(T::Indent))
        .ignore_then(elems)
        .then_ignore(just(T::Dedent))
        .then_ignore(close)
}

pub fn parse_name<'a>() -> impl Parser<'a, In<'a>, String, Extra<'a>> {
    just(T::Name).map_with(|_, extra| {
        let src: &str = *extra.state();
        let span: Span = extra.span();
        src[span.start..span.start + span.len].to_owned()
    })
}

pub fn parse<'a>(tokens: &'a Tokens, mut src: &'a str) -> Program<Span> {
    let stream = Stream::from_iter(tokens.iter()).spanned(tokens.eof_span());
    parse_program().parse_with_state(stream, &mut src).unwrap()
}
