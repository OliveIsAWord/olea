use serde::{Deserialize, Serialize};
use crate::compiler_types::Str;

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Program {
    pub decls: Vec<Decl>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum Decl {
    // Constant(Constant),
    Function(Function),
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Constant {
    pub name: Str,
    pub value: u64,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Function {
    pub name: Str,
    pub parameters: Vec<(Str, Type)>,
    pub returns: Option<Type>,
    pub body: Block,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum Type {
    Int,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum Stmt {
    Let(Str, Type, Expr),
    Expr(Expr),
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum Expr {
    Int(u64),
    Var(Str),
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    While(Box<Expr>, Box<Expr>),
    Assign(Str, Box<Expr>),
    Block(Block),
    Call(Str, Vec<Expr>),
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum BinOp {
    Add,
    Sub,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Block(pub Vec<Stmt>);
