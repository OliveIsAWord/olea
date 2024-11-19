use crate::ast::*;
use crate::lexer::Token;
use chumsky::pratt::{infix, left, postfix};
use chumsky::prelude::*;
type T = Token;

type Error<'a> = Rich<'a, Token, Span>;
type R<'a, T> = ParseResult<T, Error<'a>>;
type Extra<'src> = extra::Full<Error<'src>, &'src str, ()>;

trait SpanHelper<'src, I, O> {
    fn spanned(self) -> impl Parser<'src, I, Spanned<O>, Extra<'src>> + Clone
    where
        Self: Parser<'src, I, O, Extra<'src>> + Sized + Clone,
        I: Input<'src, Token = Token, Span = Span>,
    {
        self.map_with(move |kind, e| Spanned {
            kind,
            span: e.span(),
        })
    }
}

impl<'src, T, I, O> SpanHelper<'src, I, O> for T
where
    T: Parser<'src, I, O, Extra<'src>> + Clone,
    I: Input<'src, Token = Token, Span = Span>,
{
}

fn name<'src, I>() -> impl Parser<'src, I, Name, Extra<'src>> + Clone
where
    I: Input<'src, Token = Token, Span = Span>,
{
    just(T::Name)
        .map_with(|_, e| {
            let span: Span = e.span();
            #[allow(clippy::explicit_auto_deref)]
            // Mom, I found a false positive in clippy 0.1.78!
            let source: &str = *e.state();
            Name {
                kind: source[span.clone()].into(),
                span,
            }
        })
        .labelled("name")
}

fn int<'src, I>() -> impl Parser<'src, I, u64, Extra<'src>> + Clone
where
    I: Input<'src, Token = Token, Span = Span>,
{
    just(T::Int)
        .try_map_with(|_, e| {
            let span: Span = e.span();
            #[allow(clippy::explicit_auto_deref)]
            let source: &str = *e.state();
            source[span.clone()]
                .parse()
                .map_err(|_| Rich::custom(span, "int too big"))
        })
        .labelled("name")
}

fn ty<'src, I>() -> impl Parser<'src, I, Ty, Extra<'src>> + Clone
where
    I: Input<'src, Token = Token, Span = Span>,
{
    name()
        .try_map(|name, span| {
            if name.kind.as_ref() == "int" {
                Ok(TyKind::Int)
            } else {
                Err(Rich::custom(span, "unknown type"))
            }
        })
        .spanned()
        .pratt((postfix(
            5,
            just(T::Hat).to_span(),
            |a: Ty, op_span: Span| {
                let span = a.span.start..op_span.end;
                Ty {
                    kind: TyKind::Pointer(Box::new(a)),
                    span,
                }
            },
        ),))
        .labelled("type")
}

fn expr<'src, I>() -> impl Parser<'src, I, Expr, Extra<'src>> + Clone
where
    I: Input<'src, Token = Token, Span = Span>,
{
    // glorified currying for pratt parsing
    macro_rules! binary {
        ($op:expr) => {{
            |a: Expr, op_span, b: Expr| {
                let span = a.span.start..b.span.end;
                Expr {
                    kind: ExprKind::BinOp(
                        BinOp {
                            kind: $op,
                            span: op_span,
                        },
                        Box::new(a),
                        Box::new(b),
                    ),
                    span,
                }
            }
        }};
    }
    use BinOpKind::*;
    recursive(|expr| {
        let atom = choice((
            name().map(|x| ExprKind::Place(PlaceKind::Var(x))),
            int().map(ExprKind::Int),
            expr.clone()
                .delimited_by(just(T::ParenOpen), just(T::ParenClose))
                .map(|e| ExprKind::Paren(Box::new(e))),
            just(T::If)
                .ignore_then(expr.clone())
                .then(block(expr.clone()))
                .then(just(T::Else).ignore_then(block(expr.clone())))
                .map(|((condition, then_block), else_block)| {
                    ExprKind::If(
                        Box::new(condition),
                        Box::new(then_block),
                        Box::new(else_block),
                    )
                }),
            just(T::While)
                .ignore_then(expr.clone())
                .then(block(expr.clone()))
                .map(|(condition, body)| ExprKind::While(Box::new(condition), Box::new(body))),
            just(T::Block)
                .ignore_then(block(expr.clone()))
                // Throw away the inner span so we can include `block` in the span
                .map(|x| x.kind),
        ))
        .spanned();
        let function_call = expr
            .clone()
            .separated_by(just(T::Comma))
            .allow_trailing()
            .collect()
            .delimited_by(just(T::ParenOpen), just(T::ParenClose))
            .spanned();
        let op = |k| just(k).to_span();
        atom.pratt((
            postfix(5, function_call, |e: Expr, Spanned { kind: args, span }| {
                let span = e.span.start..span.end;
                Expr {
                    kind: ExprKind::Call(Box::new(e), args),
                    span,
                }
            }),
            postfix(5, op(T::Hat), |a: Expr, op_span: Span| {
                let span = a.span.start..op_span.end;
                Expr {
                    kind: ExprKind::Place(PlaceKind::Deref(Box::new(a), op_span)),
                    span,
                }
            }),
            infix(left(4), op(T::Asterisk), binary!(Mul)),
            infix(left(3), op(T::Plus), binary!(Add)),
            infix(left(3), op(T::Minus), binary!(Sub)),
        ))
        .then(just(T::Equals).ignore_then(expr.clone()).or_not())
        .try_map(|(a, b), span| match b {
            None => Ok(a),
            Some(value) => match a.kind {
                ExprKind::Place(place) => Ok(Expr {
                    kind: ExprKind::Assign(
                        Place {
                            span: a.span,
                            kind: place,
                        },
                        Box::new(value),
                    ),
                    span,
                }),
                // FIXME: This error message annoyingly does not show up, seemingly. Chumsky bug?
                _ => Err(Rich::custom(
                    a.span,
                    "can't assign to this kind of expression",
                )),
            },
        })
    })
    .labelled("expression")
}

fn stmt<'src, I>(
    expr: impl Parser<'src, I, Expr, Extra<'src>> + Clone,
) -> impl Parser<'src, I, Stmt, Extra<'src>> + Clone
where
    I: Input<'src, Token = Token, Span = Span>,
{
    let let_stmt = just(T::Let)
        .ignore_then(name())
        .then(just(T::Colon).ignore_then(ty()))
        .then(just(T::Equals).ignore_then(expr.clone()))
        .map(|((var, ty), body)| StmtKind::Let(var, ty, body));
    choice((let_stmt, expr.map(StmtKind::Expr)))
        .spanned()
        .then_ignore(just(T::Newline))
        .labelled("statement")
}

fn block<'src, I>(
    expr: impl Parser<'src, I, Expr, Extra<'src>> + Clone,
) -> impl Parser<'src, I, Expr, Extra<'src>> + Clone
where
    I: Input<'src, Token = Token, Span = Span>,
{
    just(T::Colon)
        .ignore_then(just(T::Newline))
        .ignore_then(
            stmt(expr)
                .repeated()
                .collect()
                .delimited_by(just(T::Indent), just(T::Dedent).labelled("end of block")),
        )
        .map(|e| ExprKind::Block(Block(e)))
        .spanned()
}

fn function<'src, I>() -> impl Parser<'src, I, Function, Extra<'src>> + Clone
where
    I: Input<'src, Token = Token, Span = Span>,
{
    just(T::Fn)
        .ignore_then(name())
        .then(
            name()
                .then(ty())
                .separated_by(just(T::Comma))
                .allow_trailing()
                .collect()
                .delimited_by(just(T::ParenOpen), just(T::ParenClose)),
        )
        .then(just(T::ThinArrow).ignore_then(ty()).or_not())
        .then(block(expr()))
        .map(|(((name, parameters), returns), body)| Function {
            name,
            parameters,
            returns,
            body,
        })
        .labelled("function")
}

fn decl<'src, I>() -> impl Parser<'src, I, Decl, Extra<'src>> + Clone
where
    I: Input<'src, Token = Token, Span = Span>,
{
    function().map(DeclKind::Function).spanned()
}

fn program<'src, I>() -> impl Parser<'src, I, Program, Extra<'src>> + Clone
where
    I: Input<'src, Token = Token, Span = Span>,
{
    decl().repeated().collect().map(|decls| Program { decls })
}

pub fn parse<'src>(tokens: &'src [(Token, Span)], source: &'src str) -> R<'src, Program> {
    let eoi_span = tokens
        .last()
        .map_or(0..0, |(_, range)| range.end..range.end);
    let input = tokens.spanned(eoi_span);
    let mut state = source;
    program().parse_with_state(input, &mut state)
}
