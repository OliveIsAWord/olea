use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum Type {
    Int(u64),
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
