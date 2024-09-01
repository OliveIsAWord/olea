use chumsky::span::Span as ChumskySpan;
use core::ops::Range;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Token {
    Error,
    Newline,
    Indent,
    Dedent,
    Name,
    Fn,
    ParenOpen,
    ParenClose,
    Colon,
    Plus,
    Times,
    ThinArrow,
}
pub type T = Token;

const KEYWORDS: &[(&str, Token)] = &[("fn", T::Fn)];

const PUNCTUATION: &[(&str, Token)] = &[
    ("(", T::ParenOpen),
    (")", T::ParenClose),
    (":", T::Colon),
    ("+", T::Plus),
    ("*", T::Times),
    ("->", T::ThinArrow),
];

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Span {
    pub start: usize,
    pub len: usize,
}

impl ChumskySpan for Span {
    type Context = ();
    type Offset = usize;
    fn new((): (), Range { start, end }: Range<usize>) -> Self {
        Span {
            start,
            len: end - start,
        }
    }
    fn context(&self) {}
    fn start(&self) -> usize {
        self.start
    }
    fn end(&self) -> usize {
        self.start + self.len
    }
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

use core::iter::{Copied, Zip};
use core::slice::Iter as SliceIter;

pub type Iter<'a> = Zip<Copied<SliceIter<'a, Token>>, Copied<SliceIter<'a, Span>>>;

impl Tokens {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn push(&mut self, token: Token, span: Span) {
        self.has_error |= matches!(token, T::Error);
        self.kinds.push(token);
        self.spans.push(span);
    }
    /*
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
    */
    pub fn iter(&self) -> Iter {
        self.kinds.iter().copied().zip(self.spans.iter().copied())
    }
    pub fn eof_span(&self) -> Span {
        let last_span = self
            .spans
            .last()
            .copied()
            .unwrap_or(Span { start: 0, len: 0 });
        Span {
            start: last_span.start + last_span.len,
            len: 0,
        }
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
                    let last_indent = indents.last().copied().unwrap_or(0);
                    use core::cmp::Ordering;
                    match indent.cmp(&last_indent) {
                        Ordering::Equal => break 'do_indent,
                        Ordering::Greater => {
                            // TODO: We might not want to start a new block here on an error.
                            indents.push(indent);
                            if has_dedented {
                                tokens.push(
                                    T::Error,
                                    Span {
                                        start: start + indent,
                                        len: 0,
                                    },
                                );
                            } else {
                                tokens.push(
                                    T::Indent,
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
                            tokens.push(T::Dedent, span);
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
                let mut token = T::Name;
                for &(string, t) in KEYWORDS {
                    if name == string {
                        token = t;
                        break;
                    }
                }
                token
            }
            '\n' => {
                was_newline = true;
                T::Newline
            }
            _ => 'blk: {
                for &(string, token) in PUNCTUATION {
                    if src.src[src.index - 1..].starts_with(string) {
                        src.index += string.len() - 1;
                        break 'blk token;
                    }
                }
                T::Error
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
    for _ in indents {
        let span = Span {
            start: src.index,
            len: 0,
        };
        tokens.push(T::Dedent, span);
    }
    tokens
}
