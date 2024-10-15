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
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum BinOp {
    Add,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Block(pub Vec<Stmt>);
