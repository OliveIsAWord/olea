use crate::arborist::{self as a, PlainToken as P, TokenTree as Tt};
use crate::ast::*;
use num_derive::FromPrimitive;
use num_traits::FromPrimitive;

type Error = Spanned<ErrorKind>;
type Result<T> = std::result::Result<T, Error>;
type Parsed<T> = Result<Option<T>>;

#[derive(Clone, Debug)]
pub enum ErrorKind {
    Custom(&'static str),
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
            Some(span.clone())
        } else {
            None
        }
    }
    fn get_previous_span(&self) -> Span {
        self.tokens[self.i - 1].span.clone()
    }
    fn get_span_checked(&self) -> Option<Span> {
        self.peek().map(|t| t.span)
    }
    fn get_span(&self) -> Span {
        let len = self.source.len();
        let eoi_span = len..len;
        self.get_span_checked().unwrap_or(eoi_span)
    }
    fn err(&self, message: &'static str) -> Error {
        Error {
            span: self.get_span(),
            kind: ErrorKind::Custom(message),
        }
    }
    fn name(&mut self) -> Option<Name> {
        self.just(P::Name).map(|span| Name {
            kind: self.source[span.clone()].into(),
            span,
        })
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
    fn block<O>(
        &self,
        mut item_parser: impl FnMut(&mut Self) -> Result<O>,
        block: &'src a::Block,
    ) -> Result<Vec<O>> {
        block
            .iter()
            .map(|tokens| {
                let mut this = Self {
                    tokens,
                    i: 0,
                    source: self.source,
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
    fn ty(&mut self) -> Result<Ty> {
        self.name()
            .and_then(|name| {
                if name.kind.as_ref() == "int" {
                    Some(Spanned {
                        kind: TyKind::Int,
                        span: name.span,
                    })
                } else {
                    None
                }
            })
            .ok_or_else(|| self.err("expected type"))
    }
    fn param(&mut self) -> Result<(Name, Ty)> {
        let Some(name) = self.name() else {
            return Err(self.err("expected function parameter"));
        };
        let ty = self.ty()?;
        Ok((name, ty))
    }
    fn expr(&mut self, level: Level) -> Result<Expr> {
        let span_start = self.get_span().start;
        let atom = if let Some(Spanned {
            kind: Tt::Paren(block),
            ..
        }) = self.peek()
        {
            self.next().unwrap();
            let mut exprs: Vec<_> = self.block(|this| this.expr(Level::Min), block)?;
            if exprs.len() != 1 {
                self.i -= 1;
                return Err(self.err("tuples are not yet implemented"));
            };
            let expr = exprs.pop().unwrap();
            ExprKind::Paren(Box::new(expr))
        } else if let Some(name) = self.name() {
            ExprKind::Place(PlaceKind::Var(name))
        } else if self.just(P::If).is_some() {
            let condition = self.expr(Level::Min)?;
            let then_block = self.colon_block()?;
            let else_block = self.else_block()?;
            ExprKind::If(Box::new(condition), then_block, else_block)
        } else {
            return Err(self.err("unexpected token while parsing expression"));
        };
        let mut e = Expr {
            kind: atom,
            span: span_start..self.get_previous_span().end,
        };
        loop {
            const OPS: &[(P, Level, BinOpKind)] = &[
                (P::Plus, Level::Add, BinOpKind::Add),
                (P::Asterisk, Level::Mul, BinOpKind::Mul),
            ];
            let Some(Spanned {
                kind: Tt::Plain(kind),
                span,
            }) = self.peek()
            else {
                break;
            };
            let Some(&(_, op_level, op_kind)) = OPS.iter().find(|(op, _, _)| kind == op) else {
                break;
            };
            if op_level < level {
                break;
            }
            self.next().unwrap();
            let rhs = self.expr(op_level.higher())?;
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
        Ok(e)
    }
    fn stmt(&mut self) -> Result<Stmt> {
        self.spanned(Self::stmt_kind)
    }
    fn stmt_kind(&mut self) -> Result<StmtKind> {
        if self.just(P::Let).is_some() {
            Err(self.err("todo: let statements"))
        } else {
            self.expr(Level::Min).map(StmtKind::Expr)
        }
    }
    fn colon_block(&mut self) -> Result<Block> {
        let Some(Spanned {
            kind: Tt::IndentedBlock(stmts),
            ..
        }) = self.peek()
        else {
            return Err(self.err("expected beginning of block"));
        };
        self.next().unwrap();
        self.block(Self::stmt, stmts).map(Block)
    }
    fn else_block(&mut self) -> Parsed<Block> {
        let Some(Spanned {
            kind: Tt::ElseBlock(stmts),
            ..
        }) = self.peek()
        else {
            return Ok(None);
        };
        self.next().unwrap();
        self.block(Self::stmt, stmts).map(|x| Some(Block(x)))
    }
    fn decl(&mut self) -> Parsed<Decl> {
        self.spanned2(Self::decl_kind)
    }
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
                    kind: Tt::Paren(params),
                    ..
                }) = self.peek()
                else {
                    return Err(self.err("expected paren list of function parameters"));
                };
                self.next().unwrap();
                let parameters = self.block(Self::param, params)?;
                let returns = self.just(P::ThinArrow).map(|_| self.ty()).transpose()?;
                let body = self.colon_block()?;
                DeclKind::Function(Function {
                    name,
                    parameters,
                    returns,
                    body,
                })
            }
            _ => {
                self.i -= 1; // Hacky, I know.
                return Ok(None);
            }
        };
        Ok(Some(decl))
    }
}

pub fn parse(block: &a::Block, source: &str) -> Result<Program> {
    let item = &block[0];
    let mut parser = Parser {
        tokens: item,
        i: 0,
        source,
    };
    parser.decl().map(|decl| Program {
        decls: decl.into_iter().collect(),
    })
}
