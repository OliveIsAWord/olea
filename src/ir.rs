use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct Function {
    pub blocks: HashMap<usize, Block>,
}

#[derive(Clone, Debug)]
pub struct Block {
    pub insts: Vec<Inst>,
}

#[derive(Clone, Debug)]
pub enum Inst {
    Store(Register, StoreKind),
    Write(Register, Register),
    Jump(JumpLocation),
    CondJump(Condition, JumpLocation, JumpLocation),
}

#[derive(Clone, Debug)]
pub enum StoreKind {
    Int(u128),
    // Copy(Register),
    Phi(Register, Register),
    BinOp(BinOp, Register, Register),
    StackAlloc(u128),
    Read(Register),
}

#[derive(Clone, Debug)]
pub enum BinOp {
    Add,
    Sub,
}

#[derive(Clone, Debug)]
pub enum Condition {
    // Always,
    NonZero(Register),
}

#[derive(Clone, Debug)]
pub enum JumpLocation {
    Block(usize),
    // Register(Register),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Register(pub u128);
