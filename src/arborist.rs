use crate::ast::{Span, Spanned};
pub use crate::lexer::PlainToken;
use crate::lexer::{self, ControlToken, Token, Tokens};

type T = Token;
type C = ControlToken;
type P = PlainToken;
use Token::Control as Co;
use Token::Plain as Pl;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TokenTree {
    Plain(PlainToken),
    Paren(Block, bool),
    IndentedBlock(Block),
    ElseBlock(Block),
}

use TokenTree as Tt;

// Invariant: Item takes the form `(Plain | Paren)+ (IndentedBlock ElseBlock?)?`.
pub type Item = Vec<Spanned<TokenTree>>;
// Invariant: Nonempty.
pub type Block = Vec<Item>;

#[derive(Clone, Debug)]
pub enum ErrorKind {
    Unexpected(ControlToken),
    Expected(ControlToken),
    Custom(&'static str),
}

pub type Error = Spanned<ErrorKind>;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Debug)]
struct Arborizer<'a> {
    tokens: &'a Tokens,
    i: usize,
}

impl Arborizer<'_> {
    fn peek(&self) -> Option<(Token, Span)> {
        self.tokens
            .get(self.i)
            .map(|lexer::Spanned { token, span }| (token, span.start..span.start + span.len))
    }
    fn next(&mut self) -> Option<(Token, Span)> {
        let token = self.peek()?;
        self.i += 1;
        Some(token)
    }
    fn consume_if(&mut self, expected: ControlToken) -> bool {
        let Some((token, _)) = self.peek() else {
            return false;
        };
        if token == Co(expected) {
            self.next().unwrap();
            true
        } else {
            false
        }
    }
    fn expect(&mut self, expected: ControlToken) -> Result<()> {
        if !self.consume_if(expected) {
            Err(Spanned {
                kind: ErrorKind::Expected(expected),
                span: self.get_span(),
            })
        } else {
            Ok(())
        }
    }
    fn get_span(&self) -> Span {
        if let Some((_, span)) = self.peek() {
            return span;
        }
        let span = self.tokens.eoi_span;
        span.start..span.start + span.len
    }
    fn get_previous_span(&self) -> Span {
        let span = self.tokens.get(self.i - 1).unwrap().span;
        span.start..span.start + span.len
    }
    fn unexpected(&self, token: ControlToken) -> Result<()> {
        Err(Spanned {
            kind: ErrorKind::Unexpected(token),
            span: self.get_previous_span(),
        })
    }
    fn err(&self, msg: &'static str) -> Result<()> {
        Err(Spanned {
            kind: ErrorKind::Custom(msg),
            span: self.get_previous_span(),
        })
    }
    // TODO: remove Spanned from the return type of this method?
    fn item(&mut self) -> Result<Option<Spanned<Item>>> {
        let mut item = vec![];
        let mut indented = false;
        // morally a `while ... else` loop
        let parse_indented: bool = loop {
            let Some((token, span)) = self.next() else {
                if item.is_empty() {
                    return Ok(None);
                }
                unreachable!("unexpected eof");
            };
            match token {
                Pl(t) => item.push(Spanned {
                    kind: Tt::Plain(t),
                    span,
                }),
                Co(C::Newline) => {
                    let got_indent = self.consume_if(C::Indent);
                    match (indented, got_indent) {
                        (false, false) => break false,
                        (false, true) => indented = true,
                        (true, false) => {
                            if self.consume_if(C::Dedent) {
                                break false;
                            }
                        }
                        (true, true) => self.err("cannot indent in an already indented item")?,
                    }
                }
                Co(C::ParenOpen) => {
                    // TODO: handle closing paren appearing before newline and dedent
                    let span_start = span.start;
                    let (inner, multi) = self.inner_block(false, Some(C::Comma))?;
                    self.expect(C::ParenClose)?;
                    let span_end = self.get_previous_span().end;
                    item.push(Spanned {
                        kind: Tt::Paren(inner, multi),
                        span: span_start..span_end,
                    });
                }
                Co(C::Colon) => break true,

                Co(t @ C::Indent) => self.unexpected(t)?,
                Co(C::Else) | Co(C::ParenClose) | Co(C::Dedent) | Co(C::Comma) => {
                    self.i -= 1;
                    break false;
                }
            }
        };
        if parse_indented {
            let span_start = self.get_span().start;
            let (inner, _) = self.inner_block(indented, None)?;
            let span_end = self.get_previous_span().end;
            item.push(Spanned {
                kind: Tt::IndentedBlock(inner),
                span: span_start..span_end,
            });
            if self.consume_if(C::Else) {
                let span_start = self.get_previous_span().start;
                // TODO: correctly parse ["else", newline, indent, ":"]
                let inner = if self.consume_if(C::Colon) {
                    self.inner_block(indented, None)?.0
                } else {
                    let single = self.item()?.expect("empty else block").kind;
                    vec![single]
                };
                let span_end = self.get_previous_span().end;
                item.push(Spanned {
                    kind: Tt::ElseBlock(inner),
                    span: span_start..span_end,
                });
            }
        }
        let item = if item.is_empty() {
            None
        } else {
            let span_start = item[0].span.start;
            let span_end = item.last().unwrap().span.end;
            Some(Spanned {
                kind: item,
                span: span_start..span_end,
            })
        };
        Ok(item)
    }
    fn inner_block(&mut self, skip_indent: bool, separator: Option<C>) -> Result<(Block, bool)> {
        let block = if self.consume_if(C::Newline) {
            if !skip_indent {
                self.expect(C::Indent)?;
            }
            let block = self.block()?;
            self.expect(C::Dedent)?;
            let multi = block.len() != 1;
            (block, multi)
        } else {
            let mut block = vec![];
            let mut has_separator = false;
            while let Some(Spanned { kind, .. }) = self.item()? {
                block.push(kind);
                if let Some(s) = separator {
                    if self.consume_if(s) {
                        has_separator = true;
                        let _ = self.consume_if(C::Newline);
                    }
                }
            }
            let multi = has_separator || block.len() != 1;
            (block, multi)
        };
        Ok(block)
    }
    fn block(&mut self) -> Result<Block> {
        let mut block = vec![];
        while let Some(item) = self.item()? {
            block.push(item);
        }
        if block.is_empty() {
            self.err("cannot have an empty block")?;
        }
        // assert!(!block.is_empty());
        Ok(block.into_iter().map(|x| x.kind).collect())
    }
    fn eof(&mut self) -> Result<()> {
        match self.next() {
            None => Ok(()),
            Some((t, _)) => match t {
                Pl(_) => unreachable!(),
                Co(c) => self.unexpected(c),
            },
        }
    }
}

pub fn arborize(tokens: &Tokens) -> Result<Block> {
    let mut arborizer = Arborizer { tokens, i: 0 };
    let block = arborizer.block()?;
    arborizer.eof().map(|()| block)
}
