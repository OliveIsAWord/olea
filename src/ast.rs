#![warn(missing_docs)]

//! The Olea abstract syntax tree module.
//!
//! The types in this module represent the syntactic forms that comprise the Olea grammar. We use a convention for each category of item of an enum `FooKind` representing the element itself, and a `Foo` which contains a `FooKind` as well as the source span of the element.

use crate::compiler_prelude::*;
use crate::language_types::IsAnon;

/// A full source program, made of a list of declarations.
#[derive(Clone, Debug)]
pub struct Program {
    /// The list of declarations.
    pub decls: Vec<Decl>,
}

/// See [`DeclKind`].
pub type Decl = Spanned<DeclKind>;

/// A declaration.
#[derive(Clone, Debug)]
pub enum DeclKind {
    /// See [`Function`].
    Function(Function),
    /// A reference to a callable function not defined in this program, to be linked after compilation terminates.
    ExternFunction(FunctionSignature),
    /// See [`Struct`].
    Struct(Struct),
    /// A constant declaration.
    Const(Name, Option<Ty>, Expr),
}

/// A named body of code that can be entered during execution.
#[derive(Clone, Debug)]
pub struct Function {
    /// The signature of the function.
    pub signature: FunctionSignature,
    /// The body of code that is executed when the function is called.
    pub body: Block,
}

/// The signature for a function, containing everything needed for program validation.
#[derive(Clone, Debug)]
pub struct FunctionSignature {
    /// The name of the function.
    pub name: Name,
    /// The optional first dummy parameter signalling the function cannot use `self` and cannot be called with method call notation.
    pub underscore_self: Option<Span>,
    /// The list of parameters and their types that the function accepts, as well as whether each parameter can be passed "anonymously" by position.
    pub parameters: Vec<(IsAnon, Name, Ty)>,
    /// The type of value the function returns, if any.
    pub returns: Option<Ty>,
}

/// A type declaration of a struct, a collection of fields.
#[derive(Clone, Debug)]
pub struct Struct {
    /// The name of the struct.
    pub name: Name,
    /// The fields of the struct.
    pub fields: Vec<(IsAnon, Name, Ty)>,
}

/// See [`TyKind`].
pub type Ty = Spanned<TyKind>;

/// A data type.
#[derive(Clone, Debug)]
pub enum TyKind {
    /// A type accessed by an identifier.
    Name(Name),
    /// A pointer to a value of a given type.
    Pointer(Box<Ty>),
    /// A contiguous collection of elements of a known length.
    Array(Box<Ty>, Box<Expr>),
    /// A function accepting and returning values of given types.
    Function(Vec<(IsAnon, Name, Ty)>, Option<Box<Ty>>),
}

/// See [`StmtKind`].
pub type Stmt = Spanned<StmtKind>;

/// A statement, a piece of code executed within a block.
// TODO: Allow decls in stmts.
#[derive(Clone, Debug)]
pub enum StmtKind {
    /// An expression whose yielded value, if any, is ignored (unless it is the final statement of a block). See [`ExprKind`].
    Expr(Expr),
    /// Store a value in a memory location.
    Assign(Place, Expr),
    /// A local variable declaration. This introduces a name which is bound to a value and can be accessed by all following statements in the block.
    Let(Name, Option<Ty>, Expr),
    Return(Option<Expr>),
    Break(Option<Expr>),
    Continue,
    Defer(Box<Stmt>),
}

/// See [`ExprKind`].
pub type Expr = Spanned<ExprKind>;

/// An expression, a piece of code which may yield a value when executed.
#[derive(Clone, Debug)]
pub enum ExprKind {
    /// An integer constant with an optional suffix, such as `42usize`.
    Int(u64, Option<Name>),
    /// A string literal.
    String(Str),
    /// An anonymous list of values.
    Tuple(Vec<Expr>),
    /// A calculation taking the value of one expression to yield another.
    UnaryOp(UnaryOp, Box<Expr>),
    /// A calculation taking the values of two expressions to yield another.
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    /// A comparison chain. Intuitively, the `operators` are interleaved between the `operands` as they appear in the syntax of the expression. Therefore, there must be one more element in `operands` than `operators`.
    Comparison {
        operands: Vec<Expr>,
        operators: Vec<Spanned<Cmp>>,
    },
    /// A cast of a value to a given type.
    As(Box<Expr>, Ty),
    /// An expression wrapped in parentheses.
    Paren(Box<Expr>),
    /// An "if" block composed of a condition and two branch bodies. The boolean condition is evaluated. If true, the first branch is evaluated. Otherise, the second branch is evaluated.
    If(Box<Expr>, Block, Option<Block>),
    /// A "while" loop. The condition and body expressions are evaluated repeatedly until the condition yields false.
    While(Box<Expr>, Block),
    /// See [`Block`].
    Block(Block),
    /// A function call, composed of a function and a list of arguments to pass to it.
    Call(Box<Expr>, Vec<FunctionArg>),
    /// A method call, composed of a receiver, a method name, a list of arguments, and the source location of the dot. Can take an implicit receiver.
    MethodCall(Option<Box<Expr>>, Name, Vec<FunctionArg>, Span),
    /// See [`PlaceKind`].
    Place(PlaceKind),
}

/// See [`FunctionArgKind`].
pub type FunctionArg = Spanned<FunctionArgKind>;

/// Every form that a value can be passed to a function.
#[derive(Clone, Debug)]
pub enum FunctionArgKind {
    /// Passed by name, e.g. `a: 42`.
    Named(Name, Block),
    /// Name-punned argument, e.g. `: a`.
    Punned(Block),
    /// Passed by position, e.g. `a`.
    Anon(Expr),
}

/// See [`PlaceKind`].
pub type Place = Spanned<PlaceKind>;

/// A "place expression", a category of expressions which are associated with a pointer to memory in which its value is stored. This distinction is relevant in so-called "place expression contexts", such as the left side of an assignment.
// TODO: Accept parens at the top level of place expressions, like Rust?
#[derive(Clone, Debug)]
pub enum PlaceKind {
    /// A variable.
    Var(Str),
    /// The `self` variable.
    Self_,
    /// An access of a value from an expression which yields a pointer. The second field contains the source span of the deref operator `^` itself.
    Deref(Box<Expr>, Span),
    /// An index operation, consisting of the indexee, the list of indices, and the span of the index (including square brackets). Note that multidimensional indexing is not yet supported.
    Index(Box<Expr>, Vec<Expr>, Span),
    /// A field of a struct value, and the span of the dot. Can take an implicit receiver.
    Field(Option<Box<Expr>>, Name, Span),
}

/// See [`UnaryOpKind`].
pub type UnaryOp = Spanned<UnaryOpKind>;

/// A kind of unary operation.
#[derive(Clone, Copy, Debug)]
pub enum UnaryOpKind {
    /// Two's complement negation.
    Neg,
    /// Taking the pointer of a value.
    Ref,
}

/// See [`BinOpKind`].
pub type BinOp = Spanned<BinOpKind>;

/// A kind of binary operation.
#[derive(Clone, Copy, Debug)]
pub enum BinOpKind {
    /// Two's complement addition.
    Add,
    /// Two's complement subtration.
    Sub,
    /// Two's complement unsigned multiplication.
    Mul,
    /// Unsigned division.
    Div,
    /// Short-circuiting boolean AND.
    And,
    /// Short-circuiting boolean OR.
    Or,
}

/// The different directions of comparison.
pub enum _Cmp {
    /// Equal.
    Eq,
    /// Not equal.
    Ne,
    /// Less than.
    Lt,
    /// Greater than.
    Gt,
    /// Less than or equal.
    Le,
    /// Greater than or equal.
    Ge,
}

/// A block, a list of statements that are executed in order. The block may yield the value of its last statement.
#[derive(Clone, Debug)]
pub struct Block(pub Vec<Stmt>);
