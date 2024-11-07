use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Program {
    pub decls: Vec<Decl>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum Decl {
    Constant(Constant),
    Function(Function),
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Constant {
    pub name: String,
    pub value: u64,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Function {
    pub name: String,
    pub parameters: Vec<(String, Type)>,
    pub returns: Option<Type>,
    pub body: Block,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum Type {
    Int,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum Stmt {
    Let(String, Type, Expr),
    Expr(Expr),
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum Expr {
    Int(u64),
    Var(String),
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    While(Box<Expr>, Box<Expr>),
    Assign(String, Box<Expr>),
    Block(Block),
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum BinOp {
    Add,
    Sub,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Block(pub Vec<Stmt>);
