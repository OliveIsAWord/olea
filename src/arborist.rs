use crate::ast::{Span, Spanned};
use crate::chumsky_types::{Error, Extra, SpanHelper};
use crate::lexer::{ControlToken, PlainToken, Token};
use chumsky::input::{Input, Stream, ValueInput};
use chumsky::prelude::*;

type T = Token;
type C = ControlToken;
type P = PlainToken;
use Token::Control as Co;
use Token::Plain as Pl;

#[derive(Clone, Debug)]
pub enum TokenTree {
    Plain(PlainToken),
    Paren(Block),
    IndentedBlock(Block),
    ElseBlock(Block),
}

// Invariant: Item takes the form `(Plain | Paren)+ (IndentedBlock)? ElseBlock*`. Note that the Items for syntactically valid Olea programs take the form `(Plain | Paren)+ (IndentedBlock ElseBlock?)?`.
pub type Item = Vec<Spanned<TokenTree>>;
pub type Block = Vec<Item>;

macro_rules! parses {
    ($Output:ty) => {
        // `I` and `'src` are implicitly captured from the callsite. Is this bad??
        impl Parser<'src, I, $Output, Extra<'src>> + Clone
    }
}

fn block<'src, I>() -> parses!(Block)
where
    I: Input<'src, Token = Token, Span = Span> + ValueInput<'src>,
{
    recursive(|block| {
        let c = |t| just(Co(t));
        let plain = select! { Pl(t) => t }.map(TokenTree::Plain);
        let paren = block
            .clone()
            .delimited_by(c(C::ParenOpen), c(C::ParenClose))
            .map(TokenTree::Paren);
        let item_init = plain
            .or(paren)
            .spanned()
            .repeated()
            .at_least(1)
            .collect::<Item>();
        // let item_init = item_init.clone().then(just(C::Newline).ignore_then(item_init.));
        let indented_block = c(C::Colon)
            .ignore_then(
                c(C::Newline).ignore_then(block.clone().delimited_by(c(C::Indent), c(C::Dedent))),
            )
            .map(TokenTree::IndentedBlock)
            .spanned();
        let else_block = c(C::Else)
            .ignore_then(
                c(C::Colon)
                    .ignore_then(c(C::Newline))
                    .ignore_then(block.clone().delimited_by(c(C::Indent), c(C::Dedent))),
            )
            .map(TokenTree::ElseBlock)
            .spanned();
        let item = item_init
            .then(indented_block.or_not())
            .then(else_block.repeated().collect::<Item>())
            .map(|((mut meow, indented), else_blocks): ((Item, _), _)| {
                if let Some(indented) = indented {
                    meow.push(indented);
                }
                meow.extend(else_blocks);
                meow
            })
            .then_ignore(c(C::Newline).or_not());
        item.repeated().collect::<Block>()
    })
}

pub fn arborize(tokens: &[Spanned<Token>]) -> ParseResult<Block, Error> {
    let eoi_span: Span = tokens
        .last()
        .map_or(0..0, |Spanned { span, .. }| span.end..span.end);
    let input = Stream::from_iter(
        tokens
            .iter()
            .map(|Spanned { kind, span }| (*kind, span.clone())),
    )
    .spanned(eoi_span);
    block().parse(input)
}
