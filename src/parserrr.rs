#![allow(unused_imports)]

use crate::arborist::{Block, Item, PlainToken as P, TokenTree as Tt};
use crate::ast::*;
use crate::ast::{Span, Spanned};
use chumsky::input::{BorrowInput, Stream};
use chumsky::inspector::SimpleState;
use chumsky::prelude::*;

pub type Error<'a> = Rich<'a, Tt, Span>;
pub type Extra<'src> = extra::Full<Error<'src>, SimpleState<&'src str>, ()>;

/*
pub trait SpanHelper<'src, I, O> {
    fn spanned(self) -> impl Parser<'src, I, Spanned<O>, Extra<'src>> + Clone
    where
        Self: Parser<'src, I, O, Extra<'src>> + Sized + Clone,
        I: Input<'src, Token = Tt, Span = Span>,
    {
        self.map_with(move |kind, e| Spanned {
            kind,
            span: e.span(),
        })
    }
}

impl<'src, T, I, O> SpanHelper<'src, I, O> for T
where
    T: Parser<'src, I, O, Extra<'src>> + Clone,
    I: Input<'src, Token = Tt, Span = Span>,
{
}


fn j<'src, I>(token: P) -> impl Parser<'src, I, Span, Extra<'src>> + Clone
where
    I: Input<'src, Token = Tt, Span = Span>,
{
    just(Tt::Plain(token)).to_span()
}

fn name<'src, I>() -> impl Parser<'src, I, Name, Extra<'src>> + Clone
where
    I: Input<'src, Token = Tt, Span = Span>,
{
    j(P::Name)
        .map_with(|span, e| {
            #[allow(clippy::explicit_auto_deref)]
            // Mom, I found a false positive in clippy 0.1.78!
            let source: &str = *e.state();
            Name {
                kind: source[span.clone()].into(),
                span,
            }
        })
        .labelled("name")
}

fn decl<'src, I>() -> impl Parser<'src, I, Decl, Extra<'src>> + Clone
where
    I: Input<'src, Token = Tt, Span = Span>,
{
    j(P::Fn)
        .ignore_then(name())
        .then(todo())
        .then(todo())
        .then(todo())
        .map(|(((name, parameters), returns), body)| {
            DeclKind::Function(Function {
                name,
                parameters,
                returns,
                body,
            })
        })
        .spanned()
}
*/

fn block<'src, I1, I2, O>(
    p: impl Parser<'src, MadeInput<'src>, O, Extra<'src>> + Clone,
) -> impl Parser<'src, I2, Vec<O>, Extra<'src>> + Clone
where
    I2: Input<'src, Token = Tt, Span = Span> + BorrowInput<'src>,
{
    let group = select_ref!( Tt::IndentedBlock(b) => b.as_slice() );
    let itemer = select_ref!( b = e => make_input(e.span(), b) );
    p.nested_in(itemer).repeated().collect().nested_in(group)
}

type MadeInput<'src> =
    chumsky::input::MappedInput<Tt, Span, &'src [Spanned<Tt>], fn(&Spanned<Tt>) -> (&Tt, &Span)>;

fn make_input<'src>(eoi: Span, item: &'src Item) -> MadeInput {
    item.map(eoi, |Spanned { kind, span }| (kind, span))
}

pub fn parse<'src>(_block: &'src Block, _source: &'src str) -> ParseResult<Program, Error<'src>> {
    todo!()
}
