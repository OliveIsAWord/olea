#![allow(clippy::range_plus_one)]

use crate::arborist::{self as a, PlainToken as P, TokenTree as Tt};
use crate::ast::*;
use crate::compiler_types::{Name, Span, Spanned};
use num_derive::FromPrimitive;
use num_traits::FromPrimitive;

type Error = Spanned<ErrorKind>;
type Result<T> = std::result::Result<T, Error>;
type Parsed<T> = Result<Option<T>>;

#[derive(Clone, Debug)]
pub enum ErrorKind {
    Custom(&'static str),
}

const fn err_span(message: &'static str, span: Span) -> Error {
    Error {
        span,
        kind: ErrorKind::Custom(message),
    }
}

#[derive(Clone, Copy, Debug, FromPrimitive, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
enum Level {
    Min = 0,
    Or = 1,
    And = 2,
    Equal = 3,
    Add = 4,
    Mul = 5,
    Prefix = 6,
    Postfix = 7,
    Max = 8,
}

impl Level {
    pub fn higher(self) -> Self {
        Self::from_u8(self as u8 + 1).expect("can't go higher than Level::Max")
    }
}

struct Parser<'src> {
    tokens: &'src [Spanned<Tt>],
    i: usize,
    source: &'src str,
    start_span: Span,
    end_span: Span,
}

impl<'src> Parser<'src> {
    fn peek(&self) -> Option<Spanned<&'src Tt>> {
        self.tokens
            .get(self.i)
            .map(|Spanned { kind, span }| Spanned {
                kind,
                span: span.clone(),
            })
    }
    fn next(&mut self) -> Option<Spanned<&'src Tt>> {
        let tt = self.peek()?;
        self.i += 1;
        Some(tt)
    }
    fn just(&mut self, token: P) -> Option<Span> {
        let Spanned { kind, span } = self.peek()?;
        if *kind == Tt::Plain(token) {
            self.next().unwrap();
            Some(span)
        } else {
            None
        }
    }
    fn get_previous_span(&self) -> Span {
        if self.i == 0 {
            self.start_span.clone()
        } else {
            self.tokens[self.i - 1].span.clone()
        }
    }
    fn get_span_checked(&self) -> Option<Span> {
        self.peek().map(|t| t.span)
    }
    fn get_span(&self) -> Span {
        self.get_span_checked()
            .unwrap_or_else(|| self.end_span.clone())
    }
    fn err(&self, message: &'static str) -> Error {
        err_span(message, self.get_span())
    }
    fn err_previous(&self, message: &'static str) -> Error {
        err_span(message, self.get_previous_span())
    }
    fn name(&mut self) -> Option<Name> {
        self.just(P::Name).map(|span| Name {
            kind: self.source[span.clone()].into(),
            span,
        })
    }
    fn int(&mut self) -> Option<(u64, Option<Name>)> {
        let span = self.just(P::Int)?;
        let mut src_str = &self.source[span.clone()];
        let original_len = src_str.len();
        let mut int: u64 = 0;
        while let Some(c) = src_str.chars().next() {
            match c {
                '_' => {}
                '0'..='9' => {
                    let digit = u64::from(c as u8 - b'0');
                    int = int.wrapping_mul(10).wrapping_add(digit);
                }
                _ => break,
            }
            src_str = &src_str[c.len_utf8()..];
        }
        let suffix = if src_str.is_empty() {
            None
        } else {
            let kind = src_str.into();
            let span = span.start + (original_len - src_str.len())..span.end;
            Some(Name { kind, span })
        };
        Some((int, suffix))
    }
    fn spanned<O>(&mut self, f: impl FnOnce(&mut Self) -> Result<O>) -> Result<Spanned<O>> {
        let span_start = self.get_span().start;
        f(self).map(|kind| {
            let span_end = self.get_previous_span().end;
            let span = span_start..span_end;
            Spanned { kind, span }
        })
    }
    fn spanned2<O>(&mut self, f: impl FnOnce(&mut Self) -> Parsed<O>) -> Parsed<Spanned<O>> {
        self.spanned(f)
            .map(|Spanned { kind, span }| kind.map(|kind| Spanned { kind, span }))
    }
    fn parse_item<O>(
        mut item_parser: impl FnMut(&mut Self) -> Result<O>,
        tokens: &'src a::Item,
        source: &'src str,
        start_span: Span,
        end_span: Span,
    ) -> Result<O> {
        let mut this = Self {
            tokens,
            i: 0,
            source,
            start_span,
            end_span,
        };
        let o = item_parser(&mut this)?;
        match this.get_span_checked() {
            Some(span) => Err(Spanned {
                kind: ErrorKind::Custom("expected end of item"),
                span,
            }),
            None => Ok(o),
        }
    }
    fn item<O>(
        &self,
        item_parser: impl FnMut(&mut Self) -> Result<O>,
        item: &'src a::Item,
        start_span: Span,
        end_span: Span,
    ) -> Result<O> {
        Self::parse_item(item_parser, item, self.source, start_span, end_span)
    }
    fn parse_block<O>(
        mut item_parser: impl FnMut(&mut Self) -> Result<O>,
        block: &'src a::Block,
        source: &'src str,
        start_span: Span,
        end_span: Span,
    ) -> Result<Vec<O>> {
        block
            .iter()
            .map(|tokens| {
                let mut this = Self {
                    tokens,
                    i: 0,
                    source,
                    start_span: start_span.clone(),
                    end_span: end_span.clone(),
                };
                let o = item_parser(&mut this)?;
                match this.get_span_checked() {
                    Some(span) => Err(Spanned {
                        kind: ErrorKind::Custom("expected end of item"),
                        span,
                    }),
                    None => Ok(o),
                }
            })
            .collect()
    }
    // These lifetimes are a little too strict, but it doesn't matter at all.
    fn block<O>(
        &self,
        item_parser: impl FnMut(&mut Self) -> Result<O>,
        block: &'src a::Block,
        start_span: Span,
        end_span: Span,
    ) -> Result<Vec<O>> {
        Self::parse_block(item_parser, block, self.source, start_span, end_span)
    }
    #[allow(clippy::unnecessary_wraps)]
    fn ty(&mut self) -> Parsed<Ty> {
        if let Some(fn_span) = self.just(P::Fn) {
            let Some(Spanned {
                kind: Tt::Paren(params, _),
                span,
            }) = self.peek()
            else {
                return Err(self.err("expected function type parameters"));
            };
            self.next().unwrap();
            let params = self.block(
                |this| {
                    this.ty()
                        .transpose()
                        .unwrap_or_else(|| Err(this.err("expected parameter type")))
                },
                params,
                span.start..span.start,
                span.end..span.end,
            )?;
            let returns = self.ty()?.map(Box::new);
            return Ok(Some(Spanned {
                kind: TyKind::Function(params, returns),
                span: fn_span.start..self.get_previous_span().end,
            }));
        }
        let Some(name) = self.name() else {
            return Ok(None);
        };
        let mut ty = if name.kind.as_ref() == "usize" {
            Ty {
                kind: TyKind::Int(IntKind::Usize),
                span: name.span,
            }
        } else if name.kind.as_ref() == "u8" {
            Ty {
                kind: TyKind::Int(IntKind::U8),
                span: name.span,
            }
        } else if name.kind.as_ref() == "int" {
            // simple error for legacy integer type name
            return Err(self.err_previous("unknown type `int`. Did you mean `usize`?"));
        } else {
            return Err(self.err_previous("unknown type"));
        };
        while let Some(deref_span) = self.just(P::Hat) {
            let span = ty.span.start..deref_span.end;
            ty = Ty {
                kind: TyKind::Pointer(Box::new(ty)),
                span,
            };
        }
        Ok(Some(ty))
    }
    fn param(&mut self) -> Result<(Name, Ty)> {
        let Some(name) = self.name() else {
            return Err(self.err("expected function parameter"));
        };
        let ty = self
            .ty()
            .transpose()
            .unwrap_or_else(|| Err(self.err("expected function parameter type")))?;
        Ok((name, ty))
    }
    fn expr(&mut self) -> Result<Expr> {
        self.expr_at(Level::Min)
    }
    fn expr_at(&mut self, level: Level) -> Result<Expr> {
        const BIN_OPS: &[(P, Level, BinOpKind)] = &[
            (P::LessThanEqual, Level::Equal, BinOpKind::CmpLe),
            (P::Plus, Level::Add, BinOpKind::Add),
            (P::Minus, Level::Add, BinOpKind::Sub),
            (P::Asterisk, Level::Mul, BinOpKind::Mul),
        ];
        const UNARY_OPS: &[(P, UnaryOpKind)] = &[(P::Minus, UnaryOpKind::Neg)];
        let span_start = self.get_span().start;
        let atom = if let Some(Spanned {
            kind: Tt::Paren(block, multi),
            span,
        }) = self.peek()
        {
            if *multi {
                return Err(self.err("tuples are not yet implemented"));
            }
            assert_eq!(block.len(), 1);
            self.next().unwrap();
            let start_span = span.start + 1..span.start + 1;
            let end_span = span.end - 1..span.end - 1;
            let expr = self.item(Self::expr, &block[0], start_span, end_span)?;
            ExprKind::Paren(Box::new(expr))
        } else if let Some(Spanned {
            kind: Tt::IndentedBlock(_),
            ..
        }) = self.peek()
        {
            let block = self.colon_block()?;
            ExprKind::Block(block)
        } else if let Some(name) = self.name() {
            ExprKind::Place(PlaceKind::Var(name))
        } else if let Some((int, suffix)) = self.int() {
            ExprKind::Int(int, suffix)
        } else if self.just(P::If).is_some() {
            let condition = self.expr()?;
            let then_block = self.colon_block()?;
            let else_block = self.else_block()?;
            ExprKind::If(Box::new(condition), then_block, else_block)
        } else if self.just(P::While).is_some() {
            let condition = self.expr()?;
            let body = self.colon_block()?;
            if matches!(
                self.peek(),
                Some(Spanned {
                    kind: Tt::ElseBlock(_),
                    ..
                })
            ) {
                return Err(self.err("else blocks for while loops not yet implemented"));
            }
            ExprKind::While(Box::new(condition), body)
        } else {
            let b = 'b: {
                let Some(Spanned {
                    kind: &Tt::Plain(token),
                    span,
                }) = self.next()
                else {
                    break 'b None;
                };
                let Some(kind) = UNARY_OPS
                    .iter()
                    .find_map(|&(t, k)| (t == token).then_some(k))
                else {
                    break 'b None;
                };
                if level > Level::Prefix {
                    // We will surely never hit this error path. We never call .expr() with a precedence level higher than Prefix.
                    return Err(self.err("this prefix operator's precedence is too low"));
                }
                let rhs = self.expr_at(Level::Prefix)?;
                Some(ExprKind::UnaryOp(UnaryOp { kind, span }, Box::new(rhs)))
            };
            b.ok_or_else(|| self.err_previous("unexpected token while parsing expression"))?
        };
        let mut e = Expr {
            kind: atom,
            span: span_start..self.get_previous_span().end,
        };
        // NOTE: These postfix operators have the highest precedence, so we skip the precedence level check and do this in a separate loop.
        loop {
            let span: Span;
            let kind: ExprKind;
            if let Some(deref_span) = self.just(P::Hat) {
                span = e.span.start..deref_span.end;
                kind = ExprKind::Place(PlaceKind::Deref(Box::new(e), deref_span));
            } else if let Some(ref_span) = self.just(P::At) {
                span = e.span.start..ref_span.end;
                let op = UnaryOp {
                    kind: UnaryOpKind::Ref,
                    span: ref_span,
                };
                kind = ExprKind::UnaryOp(op, Box::new(e));
            } else if self.just(P::As).is_some() {
                let Some(ty) = self.ty()? else {
                    return Err(self.err_previous("expected type after `as`"));
                };
                span = e.span.start..ty.span.end;
                kind = ExprKind::As(Box::new(e), ty);
            } else if let Some(Spanned {
                kind: Tt::Paren(args, _),
                span: args_span,
            }) = self.peek()
            {
                self.next().unwrap();
                let args = self.block(
                    Self::expr,
                    args,
                    args_span.start + 1..args_span.start + 1,
                    args_span.end - 1..args_span.end - 1,
                )?;
                span = e.span.start..args_span.end;
                kind = ExprKind::Call(Box::new(e), args);
            } else if let Some(Spanned {
                kind: Tt::Square(block, multi),
                span: index_span,
            }) = self.peek()
            {
                if *multi {
                    return Err(self.err("indexing cannot have multiple arguments"));
                }
                assert_eq!(block.len(), 1);
                self.next().unwrap();
                let start_span = index_span.start + 1..index_span.start + 1;
                let end_span = index_span.end - 1..index_span.end - 1;
                let expr = self.item(Self::expr, &block[0], start_span, end_span)?;
                span = e.span.start..index_span.end;
                kind = ExprKind::Place(PlaceKind::Index(Box::new(e), Box::new(expr), index_span));
            } else {
                break;
            }
            e = Expr { kind, span };
        }
        loop {
            let Some(Spanned {
                kind: Tt::Plain(kind),
                span,
            }) = self.peek()
            else {
                break;
            };
            let Some(&(_, op_level, op_kind)) = BIN_OPS.iter().find(|(op, _, _)| kind == op) else {
                break;
            };
            if op_level < level {
                break;
            }
            self.next().unwrap();
            let rhs = self.expr_at(op_level.higher())?;
            let op = BinOp {
                kind: op_kind,
                span,
            };
            let span = e.span.start..rhs.span.end;
            e = Expr {
                kind: ExprKind::BinOp(op, Box::new(e), Box::new(rhs)),
                span,
            };
        }
        // assignment
        if level <= Level::Min && self.just(P::Equals).is_some() {
            let rhs = self.expr()?;
            match e.kind {
                ExprKind::Place(p) => {
                    let lhs = Place {
                        kind: p,
                        span: e.span,
                    };
                    let span = lhs.span.start..rhs.span.end;
                    e = Expr {
                        kind: ExprKind::Assign(lhs, Box::new(rhs)),
                        span,
                    };
                }
                _ => return Err(err_span("cannot assign to this kind of expression", e.span)),
            }
        }
        Ok(e)
    }
    fn stmt(&mut self) -> Result<Stmt> {
        self.spanned(Self::stmt_kind)
    }
    fn stmt_kind(&mut self) -> Result<StmtKind> {
        if self.just(P::Let).is_some() {
            let name = self
                .name()
                .ok_or_else(|| self.err("expected name for let statement"))?;
            let ty = self.ty()?;
            if self.just(P::Equals).is_none() {
                return Err(self.err("expected `=` for let statement"));
            }
            let body = self.expr()?;
            Ok(StmtKind::Let(name, ty, body))
        } else {
            self.expr().map(StmtKind::Expr)
        }
    }
    fn colon_block(&mut self) -> Result<Block> {
        let Some(Spanned {
            kind: Tt::IndentedBlock(stmts),
            span,
        }) = self.peek()
        else {
            return Err(self.err("expected beginning of block"));
        };
        self.next().unwrap();
        let start_span = span.start + 1..span.start + 1;
        let end_span = span.end..span.end;
        self.block(Self::stmt, stmts, start_span, end_span)
            .map(Block)
    }
    fn else_block(&mut self) -> Parsed<Block> {
        let Some(Spanned {
            kind: Tt::ElseBlock(stmts),
            span,
        }) = self.peek()
        else {
            return Ok(None);
        };
        self.next().unwrap();
        let start_span = span.start + 4..span.start + 4;
        let end_span = span.end..span.end;
        self.block(Self::stmt, stmts, start_span, end_span)
            .map(|x| Some(Block(x)))
    }
    fn decl(&mut self) -> Parsed<Decl> {
        self.spanned2(Self::decl_kind)
    }
    #[allow(clippy::single_match_else)]
    fn decl_kind(&mut self) -> Parsed<DeclKind> {
        let Some(Spanned { kind, .. }) = self.next() else {
            return Ok(None);
        };
        let decl = match kind {
            Tt::Plain(P::Fn) => {
                let name = self
                    .name()
                    .ok_or_else(|| self.err("expected function name"))?;
                // use .peek() so we get the correct span for the error
                let Some(Spanned {
                    kind: Tt::Paren(params, _),
                    span,
                }) = self.peek()
                else {
                    return Err(self.err("expected paren list of function parameters"));
                };
                self.next().unwrap();
                let start_span = span.start + 1..span.start + 1;
                let end_span = span.end - 1..span.end - 1;
                let parameters = self.block(Self::param, params, start_span, end_span)?;
                let returns = self.ty()?;
                let body = self.colon_block()?;
                DeclKind::Function(Function {
                    name,
                    parameters,
                    returns,
                    body,
                })
            }
            Tt::Plain(P::Extern) => {
                self.just(P::Fn)
                    .ok_or_else(|| self.err("expected fn keyword after extern"))?;
                let name = self
                    .name()
                    .ok_or_else(|| self.err("expected extern function name"))?;
                let Some(Spanned {
                    kind: Tt::Paren(params, _),
                    span,
                }) = self.peek()
                else {
                    return Err(self.err("expected paren list of extern function parameters"));
                };
                self.next().unwrap();
                let start_span = span.start + 1..span.start + 1;
                let end_span = span.end - 1..span.end - 1;
                let parameters = self.block(
                    |this| {
                        this.ty().and_then(|x| {
                            x.ok_or_else(|| this.err("expected extern function parameter type"))
                        })
                    },
                    params,
                    start_span,
                    end_span,
                )?;
                let returns = self.ty()?;
                DeclKind::ExternFunction(ExternFunction {
                    name,
                    parameters,
                    returns,
                })
            }
            Tt::Plain(P::Struct) => {
                let name = self
                    .name()
                    .ok_or_else(|| self.err("expected struct name"))?;

                let Some(Spanned {
                    kind: Tt::IndentedBlock(struct_body),
                    span,
                }) = self.peek()
                else {
                    return Err(self.err("expected beginning of struct block"));
                };
                self.next().unwrap();
                let start_span = span.start + 1..span.start + 1;
                let end_span = span.end..span.end;
                let fields = self.block(Self::param, struct_body, start_span, end_span)?;
                DeclKind::Struct(Struct { name, fields })
            }
            _ => {
                self.i -= 1; // Hacky, I know.
                return Ok(None);
            }
        };
        Ok(Some(decl))
    }
    fn parse_program(block: &'src a::Block, source: &'src str) -> Result<Program> {
        let start_span = 0..0;
        let end_span = source.len()..source.len();
        Self::parse_block(
            |this| {
                this.decl().transpose().unwrap_or_else(|| {
                    Err(this.err("unexpected token while parsing top level declaration"))
                })
            },
            block,
            source,
            start_span,
            end_span,
        )
        .map(|decls| Program { decls })
    }
}

pub fn parse(block: &a::Block, source: &str) -> Result<Program> {
    Parser::parse_program(block, source)
}
