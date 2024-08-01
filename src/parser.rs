use crate::lexer::{Span, Spanned, Token, Tokens, T};

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

#[derive(Clone, Copy, Debug)]
struct Parser<'a> {
    tokens: &'a Tokens,
    src: &'a str,
    index: usize,
}

use std::sync::Mutex;
static AWA: Mutex<usize> = Mutex::new(0);

impl<'a> Parser<'a> {
    fn new(tokens: &'a Tokens, src: &'a str) -> Self {
        Self {
            tokens,
            src,
            index: 0,
        }
    }
    fn byte_position(&self) -> usize {
        match self.peek() {
            Some(s) => s.span.start,
            None => match self.tokens.last() {
                Some(s) => s.span.start + s.span.len,
                None => 0,
            },
        }
    }
    fn span_from_start(&self, start: usize) -> Span {
        let len = self.byte_position() - start;
        Span { start, len }
    }
    fn peek(&self) -> Option<Spanned> {
        let y = self.tokens.get(self.index);
        let mut x = AWA.lock().unwrap();
        if *x > 200 {
            panic!()
        } else {
            *x += 1
        }
        println!("mjau {y:?}");
        y
    }
    fn consume(&mut self) -> Option<Spanned> {
        let t = self.peek()?;
        self.index += 1;
        Some(t)
    }
    fn consume_if<F: Fn(Token) -> bool>(&mut self, predicate: F) -> Option<Spanned> {
        let t = self.peek()?;
        if predicate(t.token) {
            self.consume().unwrap();
            Some(t)
        } else {
            None
        }
    }
    fn consume_token(&mut self, token: Token) -> Option<Span> {
        self.consume_if(|t| t == token)
            .map(|Spanned { span, .. }| span)
    }
    fn parse_program(&mut self) -> Program<Span> {
        let mut decls = vec![];
        let start = self.byte_position();
        while self.peek().is_some() {
            decls.push(self.parse_decl());
            let _ = self.consume_token(T::Newline);
        }
        return Program {
            decls,
            meta: self.span_from_start(start),
        };
    }
    fn parse_decl(&mut self) -> Decl<Span> {
        let start = self.byte_position();
        let kind = 'kind: {
            if self.consume_if(|t| t == T::Fn).is_some() {
                let Some(name) = self.parse_name() else {
                    break 'kind DeclKind::Error;
                };
                if self.consume_token(T::ParenOpen).is_none() {
                    break 'kind DeclKind::Error;
                }
                let Some(Spanned {
                    token: block_begin, ..
                }) = self.consume()
                else {
                    break 'kind DeclKind::Error;
                };
                let parameters = match block_begin {
                    T::Newline => {
                        if self.consume_token(T::Indent).is_none() {
                            break 'kind DeclKind::Error;
                        }
                        let mut parameters = vec![];
                        loop {
                            let Some(pname) = self.parse_name() else {
                                break 'kind DeclKind::Error;
                            };
                            let Some(tname) = self.parse_name() else {
                                break 'kind DeclKind::Error;
                            };
                            parameters.push((pname, tname));
                            if self.consume_token(T::Newline).is_none() {
                                break 'kind DeclKind::Error;
                            }
                            if self.consume_token(T::Dedent).is_some() {
                                break;
                            }
                        }
                        if self.consume_token(T::ParenClose).is_none() {
                            break 'kind DeclKind::Error;
                        }
                        parameters
                    }
                    T::ParenClose => vec![],
                    _ => break 'kind DeclKind::Error,
                };
                // parse return type
                let returns = if self.consume_token(T::ThinArrow).is_some() {
                    let Some(rname) = self.parse_name() else {
                        break 'kind DeclKind::Error;
                    };
                    Some(rname)
                } else {
                    None
                };
                let body = self.parse_block();
                DeclKind::Function {
                    name,
                    parameters,
                    returns,
                    body,
                }
            } else {
                DeclKind::Error
            }
        };
        if matches!(kind, DeclKind::Error) {
            // TODO: actually skip to the next line/block
            self.consume();
        }
        Decl {
            kind,
            meta: self.span_from_start(start),
        }
    }
    fn parse_block(&mut self) -> Block<Span> {
        let start = self.byte_position();
        let statements = 'blk: {
            if self.consume_token(T::Colon).is_none() {
                break 'blk vec![];
            }
            if self.consume_token(T::Newline).is_none() {
                break 'blk vec![];
            }
            if self.consume_token(T::Indent).is_none() {
                break 'blk vec![];
            }
            let mut statements = vec![];
            while self.consume_token(T::Dedent).is_none() {
                statements.push(self.parse_statement())
            }
            statements
        };
        Block {
            statements,
            meta: self.span_from_start(start),
        }
    }
    fn parse_statement(&mut self) -> Statement<Span> {
        let start = self.byte_position();
        let expr = self.parse_expr();
        let _ = self.consume_token(T::Newline);
        let kind = StatementKind::Expr(expr);
        Statement {
            kind,
            meta: self.span_from_start(start),
        }
    }
    fn parse_expr(&mut self) -> Expr<Span> {
        self.parse_expr_with_precedence(0, false)
    }
    fn parse_expr_with_precedence(&mut self, p: u8, mut indent: bool) -> Expr<Span> {
        println!("parse_expr_with_precedence({p}, {indent})");
        let start = self.byte_position();
        let kind = 'kind: {
            let Some(var) = self.parse_name() else {
                break 'kind ExprKind::Error;
            };
            let mut expr = ExprKind::Var(var);
            loop {
                if self.consume_token(T::Newline).is_some() {
                    println!("    nl");
                    if self.consume_token(T::Indent).is_some() {
                        println!("    indent");
                        if indent {
                            todo!("multiple indents error");
                        } else {
                            indent = true;
                        }
                    }
                    println!("    and so {indent} {:?}", self.peek());
                    if !indent || self.consume_token(T::Dedent).is_some() {
                        println!("    ergo break");
                        break;
                    }
                    println!("    ergo onward");
                }
                let Some((op, lp, rp)) = self.peek().and_then(|v| get_infix_operator(v.token))
                else {
                    break;
                };
                println!("> {op:?} {lp} {rp}");
                if lp < p {
                    break;
                }
                let lhs = Expr {
                    kind: expr,
                    meta: self.span_from_start(start),
                };
                self.consume().unwrap();
                let rhs = self.parse_expr_with_precedence(rp, indent);
                expr = ExprKind::BinOp(op, Box::new(lhs), Box::new(rhs));
            }
            expr
        };
        println!("expr returning {kind:?}");
        Expr {
            kind,
            meta: self.span_from_start(start),
        }
    }
    fn parse_name(&mut self) -> Option<String> {
        let span = self.consume_token(T::Name)?;
        Some(self.src[span.start..span.start + span.len].to_owned())
    }
}

fn get_infix_operator(t: Token) -> Option<(BinOp, u8, u8)> {
    let x = match t {
        T::Plus => (BinOp::Add, 1, 2),
        T::Times => (BinOp::Mul, 3, 4),
        _ => return None,
    };
    Some(x)
}

pub fn parse(tokens: &Tokens, src: &str) -> Program<Span> {
    Parser::new(tokens, src).parse_program()
}
