use crate::lexer::Token;
use chumsky::prelude::*;
type T = Token;
use crate::ast::{Span, Spanned};

pub type Error<'a> = Rich<'a, Token, Span>;
pub type Extra<'src> = extra::Full<Error<'src>, &'src str, ()>;

pub trait SpanHelper<'src, I, O> {
    fn spanned(self) -> impl Parser<'src, I, Spanned<O>, Extra<'src>> + Clone
    where
        Self: Parser<'src, I, O, Extra<'src>> + Sized + Clone,
        I: Input<'src, Token = Token, Span = Span>,
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
    I: Input<'src, Token = Token, Span = Span>,
{
}
