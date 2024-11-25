use crate::compiler_types::{Span, Spanned};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum ControlToken {
    Newline,
    Indent,
    Dedent,
    Else,
    ParenOpen,
    ParenClose,
    Colon,
    Comma,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum PlainToken {
    Error,
    Name,
    Int,
    Fn,
    Let,
    If,
    While,
    // Block,
    // Dot,
    Equals,
    Plus,
    Minus,
    Asterisk,
    Hat,
    Pipe,
    // ThinArrow,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Token {
    Control(ControlToken),
    Plain(PlainToken),
}

type C = ControlToken;
type P = PlainToken;
use Token::Control as Co;
use Token::Plain as Pl;

impl From<ControlToken> for Token {
    fn from(value: ControlToken) -> Self {
        Co(value)
    }
}

impl From<PlainToken> for Token {
    fn from(value: PlainToken) -> Self {
        Pl(value)
    }
}

const ERR: Token = Pl(P::Error);

const KEYWORDS: &[(&str, Token)] = &[
    ("fn", Pl(P::Fn)),
    ("let", Pl(P::Let)),
    ("if", Pl(P::If)),
    ("else", Co(C::Else)),
    ("while", Pl(P::While)),
    // ("block", Pl(P::Block)),
];

const PUNCTUATION: &[(&str, Token)] = &[
    ("|>", Pl(P::Pipe)),
    // ("->", Pl(P::ThinArrow)),
    ("(", Co(C::ParenOpen)),
    (")", Co(C::ParenClose)),
    (":", Co(C::Colon)),
    (",", Co(C::Comma)),
    // (".", Pl(P::Dot)),
    ("=", Pl(P::Equals)),
    ("+", Pl(P::Plus)),
    ("-", Pl(P::Minus)),
    ("*", Pl(P::Asterisk)),
    ("^", Pl(P::Hat)),
];

/// # Invariants
/// `tokens` and `span` have the same length.
#[derive(Clone, Debug, Default)]
pub struct Tokens {
    pub kinds: Vec<Token>,
    pub spans: Vec<Span>,
    pub eoi_span: Span,
    pub has_error: bool,
}

impl Tokens {
    pub fn new(eoi_span: Span) -> Self {
        Self {
            eoi_span,
            ..Self::default()
        }
    }
    pub fn push(&mut self, token: Token, span: Span) {
        self.has_error |= matches!(token, ERR);
        self.kinds.push(token);
        self.spans.push(span);
    }
    pub fn get(&self, i: usize) -> Option<Spanned<Token>> {
        let kind = *self.kinds.get(i)?;
        let span = self.spans[i].clone();
        Some(Spanned { kind, span })
    }
}

struct View<'a> {
    pub src: &'a str,
    pub index: usize,
}

impl<'a> View<'a> {
    pub const fn new(src: &'a str) -> Self {
        Self { src, index: 0 }
    }

    fn peek(&self) -> Option<char> {
        self.src[self.index..self.src.len()].chars().next()
    }

    fn consume(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.index += c.len_utf8();
        Some(c)
    }

    fn consume_if(&mut self, predicate: fn(char) -> bool) -> Option<char> {
        let c = self.peek().filter(|&c| predicate(c))?;
        self.consume().unwrap();
        Some(c)
    }

    fn skip_while(&mut self, predicate: fn(char) -> bool) {
        while self.consume_if(predicate).is_some() {}
    }
}

pub fn tokenize(src_bytes: &str) -> Tokens {
    let mut src = View::new(src_bytes);
    let eoi_span = src_bytes.len()..src_bytes.len();
    let mut tokens = Tokens::new(eoi_span.clone());
    let mut indents: Vec<usize> = vec![];
    let mut was_newline = true;
    loop {
        if was_newline {
            was_newline = false;
            'do_indent: loop {
                let start = src.index;
                src.skip_while(|c| c == ' ');
                let indent = match src.peek() {
                    Some('\n') => {
                        src.consume().unwrap();
                        continue;
                    }
                    None => 0,
                    _ => src.index - start,
                };
                let mut has_dedented = false;
                loop {
                    use std::cmp::Ordering;
                    let last_indent = indents.last().copied().unwrap_or(0);
                    match indent.cmp(&last_indent) {
                        Ordering::Equal => break 'do_indent,
                        Ordering::Greater => {
                            // TODO: We might not want to start a new block here on an error.
                            indents.push(indent);
                            if has_dedented {
                                tokens.push(
                                    ERR,
                                    Span {
                                        start: start + indent,
                                        end: start + indent,
                                    },
                                );
                            } else {
                                tokens.push(
                                    Co(C::Indent),
                                    Span {
                                        start: start + last_indent,
                                        end: start + indent,
                                    },
                                );
                            };
                            break 'do_indent;
                        }
                        Ordering::Less => {
                            has_dedented = true;
                            indents.pop().unwrap();
                            let span = src.index..src.index;
                            tokens.push(Co(C::Dedent), span);
                        }
                    }
                }
            }
        }
        let start = src.index;
        let Some(c) = src.consume() else { break };
        let token = match c {
            c if c.is_ascii_alphabetic() => {
                src.skip_while(|c| c.is_ascii_alphabetic() || c.is_ascii_digit() || c == '_');
                let name = &src.src[start..src.index];
                let mut token = Pl(P::Name);
                for &(string, t) in KEYWORDS {
                    if name == string {
                        token = t;
                        break;
                    }
                }
                token
            }
            c if c.is_ascii_digit() => {
                src.skip_while(|c| c.is_ascii_digit() || c == '_');
                Pl(P::Int)
            }
            '\n' => {
                was_newline = true;
                Co(C::Newline)
            }
            _ => 'blk: {
                for &(string, token) in PUNCTUATION {
                    if src.src[src.index - 1..].starts_with(string) {
                        src.index += string.len() - 1;
                        break 'blk token;
                    }
                }
                Pl(P::Error)
            }
        };
        let span = Span {
            start,
            end: src.index,
        };
        tokens.push(token, span);
        if !was_newline {
            src.skip_while(|c| c == ' ');
        }
    }
    // this code feels hacky and is probably incorrect!
    if tokens
        .kinds
        .last()
        .is_some_and(|&t| t != Co(C::Newline) && t != Co(C::Dedent))
    {
        tokens.push(Co(C::Newline), eoi_span.clone());
    }
    for _ in indents {
        tokens.push(Co(C::Dedent), eoi_span.clone());
    }
    tokens
}
