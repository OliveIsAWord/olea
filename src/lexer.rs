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
    Block,
    Comma,
    Dot,
    Equals,
    Plus,
    Minus,
    Asterisk,
    Hat,
    ThinArrow,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Token {
    Control(ControlToken),
    Plain(PlainToken),
}

type T = Token;
type C = ControlToken;
type P = PlainToken;
use Token::Control as Co;
use Token::Plain as Pl;

impl Into<Token> for ControlToken {
    fn into(self) -> Token {
        Co(self)
    }
}

impl Into<Token> for PlainToken {
    fn into(self) -> Token {
        Pl(self)
    }
}

const ERR: Token = Pl(P::Error);

const KEYWORDS: &[(&str, Token)] = &[
    ("fn", Pl(P::Fn)),
    ("let", Pl(P::Let)),
    ("if", Pl(P::If)),
    ("else", Co(C::Else)),
    ("while", Pl(P::While)),
    ("block", Pl(P::Block)),
];

const PUNCTUATION: &[(&str, Token)] = &[
    ("->", Pl(P::ThinArrow)),
    ("(", Co(C::ParenOpen)),
    (")", Co(C::ParenClose)),
    (":", Co(C::Colon)),
    (",", Pl(P::Comma)),
    (".", Pl(P::Dot)),
    ("=", Pl(P::Equals)),
    ("+", Pl(P::Plus)),
    ("-", Pl(P::Minus)),
    ("*", Pl(P::Asterisk)),
    ("^", Pl(P::Hat)),
];

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Span {
    pub start: usize,
    pub len: usize,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Spanned {
    pub token: Token,
    pub span: Span,
}

/// # Invariants
/// `tokens` and `span` have the same length.
#[derive(Clone, Debug, Default)]
pub struct Tokens {
    pub kinds: Vec<Token>,
    pub spans: Vec<Span>,
    pub has_error: bool,
}

impl Tokens {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn push(&mut self, token: Token, span: Span) {
        self.has_error |= matches!(token, ERR);
        self.kinds.push(token);
        self.spans.push(span);
    }
    pub fn get(&self, i: usize) -> Option<Spanned> {
        let token = *self.kinds.get(i)?;
        let span = self.spans[i];
        Some(Spanned { token, span })
    }
    pub fn last(&self) -> Option<Spanned> {
        if self.is_empty() {
            None
        } else {
            Some(self.get(self.len() - 1).unwrap())
        }
    }
    pub fn len(&self) -> usize {
        self.kinds.len()
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
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
    let mut tokens = Tokens::new();
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
                                        len: 0,
                                    },
                                );
                            } else {
                                tokens.push(
                                    Co(C::Indent),
                                    Span {
                                        start: start + last_indent,
                                        len: indent - last_indent,
                                    },
                                );
                            };
                            break 'do_indent;
                        }
                        Ordering::Less => {
                            has_dedented = true;
                            indents.pop().unwrap();
                            let span = Span {
                                start: src.index,
                                len: 0,
                            };
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
            len: src.index - start,
        };
        tokens.push(token, span);
        if !was_newline {
            src.skip_while(|c| c == ' ');
        }
    }
    let end_span = Span {
        start: src.index,
        len: 0,
    };
    // this code feels hacky and is probably incorrect!
    if tokens
        .kinds
        .last()
        .is_some_and(|&t| t != Co(C::Newline) && t != Co(C::Dedent))
    {
        tokens.push(Co(C::Newline), end_span);
    }
    for _ in indents {
        tokens.push(Co(C::Dedent), end_span);
    }
    tokens
}
