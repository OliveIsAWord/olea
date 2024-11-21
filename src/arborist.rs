use crate::ast::{Span, Spanned};
use crate::lexer::{self, ControlToken, PlainToken, Token, Tokens};

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

use TokenTree as Tt;

// Invariant: Item takes the form `(Plain | Paren)+ (IndentedBlock ElseBlock?)?`.
pub type Item = Vec<Spanned<TokenTree>>;
// Invariant: Nonempty.
pub type Block = Vec<Item>;

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
    fn expect(&mut self, expected: ControlToken) {
        if !self.consume_if(expected) {
            panic!("expected {expected:?}");
        }
    }
    fn item(&mut self) -> Option<Spanned<Item>> {
        let mut item = vec![];
        let mut indented = false;
        // morally a `while ... else` loop
        let parse_indented: bool = loop {
            let Some((token, span)) = self.next() else {
                if item.is_empty() {
                    return None;
                }
                panic!("unexpected eof");
            };
            // println!("{token:?} {span:?}");
            match token {
                Pl(t) => item.push(Spanned {
                    kind: Tt::Plain(t),
                    span,
                }),
                Co(C::Newline) => {
                    if !indented && self.consume_if(C::Indent) {
                        indented = true;
                    } else {
                        break false;
                    }
                }
                Co(C::ParenOpen) => {
                    // TODO: handle closing paren appearing before newline and dedent
                    let Spanned { kind, span } = self.inner_block(false);
                    self.expect(C::ParenClose);
                    item.push(Spanned {
                        kind: Tt::Paren(kind),
                        span,
                    });
                }
                Co(C::Colon) => {
                    assert!(!item.is_empty(), "bad colon");
                    break true;
                }
                Co(C::Indent) => panic!("unexpected indent"),
                Co(C::Else) => panic!("else error"),
                Co(C::ParenClose) | Co(C::Dedent) => {
                    self.i -= 1;
                    break false;
                }
            }
        };
        if parse_indented {
            let Spanned { kind, span } = self.inner_block(indented);
            item.push(Spanned {
                kind: Tt::IndentedBlock(kind),
                span,
            });
            if self.consume_if(C::Else) {
                // TODO: correctly parse ["else", newline, indent, ":"]
                let Spanned { kind, span } = if self.consume_if(C::Colon) {
                    self.inner_block(false)
                } else {
                    let Spanned { kind, span } = self.item().expect("empty else block");
                    Spanned {
                        kind: vec![kind],
                        span,
                    }
                };
                item.push(Spanned {
                    kind: Tt::ElseBlock(kind),
                    span,
                });
            }
        } else if indented {
            self.expect(C::Dedent);
        }
        if item.is_empty() {
            None
        } else {
            let span_start = item[0].span.start;
            let span_end = item.last().unwrap().span.end;
            Some(Spanned {
                kind: item,
                span: span_start..span_end,
            })
        }
    }
    fn inner_block(&mut self, skip_indent: bool) -> Spanned<Block> {
        if self.consume_if(C::Newline) {
            if !skip_indent {
                self.expect(C::Indent);
            }
            let block = self.block();
            self.expect(C::Dedent);
            block
        } else {
            let Spanned { kind, span } = self.item().expect("empty block");
            Spanned {
                kind: vec![kind],
                span,
            }
        }
    }
    fn block(&mut self) -> Spanned<Block> {
        let mut block = vec![];
        while let Some(item) = self.item() {
            block.push(item);
        }
        assert!(!block.is_empty());
        let span = block[0].span.start..block.last().unwrap().span.end;
        Spanned {
            kind: block.into_iter().map(|x| x.kind).collect(),
            span,
        }
    }
}

pub fn arborize(tokens: &Tokens) -> Result<Block, ()> {
    let mut arborizer = Arborizer { tokens, i: 0 };
    Ok(arborizer.block().kind)
}
