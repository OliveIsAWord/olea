use crate::compiler_prelude::{Span, Spanned};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum ControlToken {
    Newline,
    Indent,
    Dedent,
    Else,
    ParenOpen,
    ParenClose,
    SquareOpen,
    SquareClose,
    Colon,
    Comma,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum PlainToken {
    Error,
    Name,
    Int,
    String,
    As,
    If,
    Fn,
    Or,
    And,
    Let,
    Anon,
    Self_,
    Break,
    Const,
    Defer,
    While,
    Extern,
    Return,
    Struct,
    Continue,
    Dot,
    Equal,
    Plus,
    Minus,
    Asterisk,
    ForwardSlash,
    EqualEqual,
    NotEqual,
    LessThan,
    GreaterThan,
    LessThanEqual,
    GreaterThanEqual,
    Hat,
    At,
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
    ("as", Pl(P::As)),
    ("fn", Pl(P::Fn)),
    ("if", Pl(P::If)),
    ("or", Pl(P::Or)),
    ("and", Pl(P::And)),
    ("let", Pl(P::Let)),
    ("anon", Pl(P::Anon)),
    ("else", Co(C::Else)),
    ("self", Pl(P::Self_)),
    ("break", Pl(P::Break)),
    ("const", Pl(P::Const)),
    ("defer", Pl(P::Defer)),
    ("while", Pl(P::While)),
    ("extern", Pl(P::Extern)),
    ("return", Pl(P::Return)),
    ("struct", Pl(P::Struct)),
    ("continue", Pl(P::Continue)),
];

// NOTE: Because of how we lex these tokens, shorter tokens should be placed further in this list.
const PUNCTUATION: &[(&str, Token)] = &[
    ("<=", Pl(P::LessThanEqual)),
    (">=", Pl(P::GreaterThanEqual)),
    ("==", Pl(P::EqualEqual)),
    ("!=", Pl(P::NotEqual)),
    ("<", Pl(P::LessThan)),
    (">", Pl(P::GreaterThan)),
    ("(", Co(C::ParenOpen)),
    (")", Co(C::ParenClose)),
    ("[", Co(C::SquareOpen)),
    ("]", Co(C::SquareClose)),
    (":", Co(C::Colon)),
    (",", Co(C::Comma)),
    (".", Pl(P::Dot)),
    ("=", Pl(P::Equal)),
    ("+", Pl(P::Plus)),
    ("-", Pl(P::Minus)),
    ("*", Pl(P::Asterisk)),
    ("/", Pl(P::ForwardSlash)),
    ("^", Pl(P::Hat)),
    ("@", Pl(P::At)),
];

/// Is this character valid as the start of an identifier?
fn is_start(c: char) -> bool {
    c == '_' || c.is_ascii_alphabetic()
}

/// Is this character valid as the continuation of an identifier?
fn is_continued(c: char) -> bool {
    is_start(c) || c.is_ascii_digit()
}

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

    const fn normalize_cr(c: char) -> char {
        if c == '\r' { '\n' } else { c }
    }

    fn peek(&self) -> Option<char> {
        self.src[self.index..self.src.len()]
            .chars()
            .next()
            .map(Self::normalize_cr)
    }

    fn consume(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.index += c.len_utf8();
        Some(c)
    }

    fn consume_if(&mut self, predicate: impl FnOnce(char) -> bool) -> Option<char> {
        self.consume_map(|c| predicate(c).then_some(c))
    }

    fn consume_map<T>(&mut self, f: impl FnOnce(char) -> Option<T>) -> Option<T> {
        // Don't consume the next character unless it matches the predicate.
        let t = self.peek().and_then(f)?;
        self.consume().unwrap();
        Some(t)
    }

    fn skip_while(&mut self, predicate: fn(char) -> bool) {
        while self.consume_if(predicate).is_some() {}
    }

    fn find<T>(&mut self, mut f: impl FnMut(char) -> Option<T>) -> Option<T> {
        while let Some(c) = self.consume() {
            if let Some(t) = f(c) {
                return Some(t);
            }
        }
        None
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
                    Some('#') => {
                        src.skip_while(|c| c != '\n');
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
                                tokens.push(ERR, Span {
                                    start: start + indent,
                                    end: start + indent,
                                });
                            } else {
                                tokens.push(Co(C::Indent), Span {
                                    start: start + last_indent,
                                    end: start + indent,
                                });
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
            c if is_start(c) => {
                src.skip_while(is_continued);
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
                // capture the remaining digits as well as any suffix identifier
                src.skip_while(is_continued);
                Pl(P::Int)
            }
            '"' => {
                enum StringState {
                    End,
                    Error,
                    Escape,
                }
                use StringState as S;
                loop {
                    let state = src.find(|c| match c {
                        '"' => Some(S::End),
                        '\n' => Some(S::Error),
                        '\\' => Some(S::Escape),
                        _ => None,
                    });
                    match state {
                        Some(S::End) => break Pl(P::String),
                        Some(S::Escape) => _ = src.consume(),
                        Some(S::Error) | None => break Pl(P::Error),
                    }
                }
            }
            '\n' => {
                was_newline = true;
                Co(C::Newline)
            }
            '#' => {
                src.skip_while(|c| c != '\n');
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
