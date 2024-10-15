use crate::ast;
#[allow(clippy::wildcard_imports)]
// We can make these imports explicit when it's less likely to create churn.
use crate::ir::*;
use std::collections::HashMap;

/// This trait defines a helper method for transforming a `T` into an `Option<T>` with a postfix syntax.
trait ToSome {
    fn some(self) -> Option<Self>
    where
        Self: Sized;
}

impl<T> ToSome for T {
    fn some(self) -> Option<Self> {
        Some(self)
    }
}

#[derive(Clone, Debug)]
pub struct IrBuilder {
    current_block: Vec<Inst>,
    current_block_id: usize,
    next_block_id: usize,
    blocks: HashMap<usize, Block>,
    scopes: Vec<HashMap<String, Register>>,
    next_reg_id: u128,
}

impl IrBuilder {
    pub fn new() -> Self {
        Self {
            current_block: vec![],
            current_block_id: 0,
            next_block_id: 1,
            blocks: HashMap::new(),
            scopes: vec![HashMap::new()],
            next_reg_id: 0,
        }
    }

    pub fn build_block(&mut self, ast::Block(stmts): &ast::Block) -> Option<Register> {
        self.enter_scope();
        let mut last_stmt_return = None;
        for stmt in stmts {
            last_stmt_return = self.build_stmt(stmt);
        }
        self.exit_scope();
        last_stmt_return
    }

    fn build_stmt(&mut self, stmt: &ast::Stmt) -> Option<Register> {
        use ast::Stmt as S;
        match stmt {
            S::Let(name, _ty, body) => {
                let alloc_reg = self.new_var(name.clone());
                let value_reg = self.build_expr(body).unwrap();
                self.push_write(alloc_reg, value_reg);
                None
            }
            S::Expr(expr) => self.build_expr(expr),
        }
    }

    fn build_expr(&mut self, expr: &ast::Expr) -> Option<Register> {
        use ast::Expr as E;
        use StoreKind as Sk;
        match expr {
            &E::Int(i) => self.push_store(Sk::Int(i.into())).some(),
            E::BinOp(op, lhs, rhs) => {
                use ast::BinOp as A;
                use BinOp as B;
                let op_kind = match op {
                    A::Add => B::Add,
                    A::Sub => B::Sub,
                };
                let lhs_reg = self.build_expr(lhs).unwrap();
                let rhs_reg = self.build_expr(rhs).unwrap();
                self.push_store(Sk::BinOp(op_kind, lhs_reg, rhs_reg)).some()
            }
            E::Var(string) => {
                let var_reg = self.get_var(string);
                self.push_store(StoreKind::Read(var_reg)).some()
            }
            E::Assign(var, body) => {
                let value_reg = self.build_expr(body).unwrap();
                let var_reg = self.get_var(var);
                self.push_write(var_reg, value_reg);
                None
            }
            E::Block(b) => self.build_block(b),
            E::If(cond, then_body, else_body) => {
                let cond_reg = self.build_expr(cond).unwrap();
                let then_id = self.reserve_block_id();
                let else_id = self.reserve_block_id();
                let end_id = self.reserve_block_id();
                self.push_inst(Inst::CondJump(
                    Condition::NonZero(cond_reg),
                    JumpLocation::Block(then_id),
                    JumpLocation::Block(else_id),
                ));
                // compile both branches (todo: cond and then_body should share scope)
                let returns = [(then_id, then_body), (else_id, else_body)].map(|(id, body)| {
                    self.switch_to_new_block(id);
                    self.enter_scope();
                    let then_yield = self.build_expr(body);
                    self.push_jump_block(end_id);
                    self.exit_scope();
                    then_yield
                });
                self.switch_to_new_block(end_id);
                match returns {
                    [Some(then_reg), Some(else_reg)] => {
                        self.push_store(Sk::Phi(then_reg, else_reg)).some()
                    }
                    _ => None,
                }
            }
            E::While(cond, body) => {
                // jump to condition evaluation
                let cond_id = self.reserve_block_id();
                let body_id = self.reserve_block_id();
                let end_id = self.reserve_block_id();
                self.push_jump_block(cond_id);

                // condition evaluation, jump to either inner body or end of expression
                self.switch_to_new_block(cond_id);
                self.enter_scope(); // with code like `while x is Some(y): ...`, `y` should be accessible from the body
                let cond_reg = self.build_expr(cond).unwrap();
                self.push_inst(Inst::CondJump(
                    Condition::NonZero(cond_reg),
                    JumpLocation::Block(body_id),
                    JumpLocation::Block(end_id),
                ));

                // body evaluation, jump back to condition
                self.switch_to_new_block(body_id);
                self.build_expr(body);
                self.push_jump_block(cond_id);
                self.exit_scope();

                // continue evaluation after while loop
                self.switch_to_new_block(end_id);
                None
            }
        }
    }

    pub fn finish(mut self) -> Function {
        self.switch_to_new_block(420);
        assert_eq!(self.scopes.len(), 1);
        Function {
            blocks: self.blocks,
        }
    }

    fn enter_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn exit_scope(&mut self) {
        self.scopes.pop();
    }

    fn new_var(&mut self, name: String) -> Register {
        let reg = self.push_store(StoreKind::StackAlloc(69));
        self.scopes.last_mut().unwrap().insert(name, reg);
        reg
    }

    fn get_var(&mut self, name: &str) -> Register {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).copied())
            .expect("variable {name:?} not found")
    }

    fn push_write(&mut self, dst: Register, src: Register) {
        self.push_inst(Inst::Write(dst, src));
    }

    fn push_store(&mut self, sk: StoreKind) -> Register {
        let reg = self.new_reg();
        self.push_inst(Inst::Store(reg, sk));
        reg
    }

    fn push_jump_block(&mut self, id: usize) {
        self.push_inst(Inst::Jump(JumpLocation::Block(id)));
    }

    fn push_inst(&mut self, inst: Inst) {
        self.current_block.push(inst);
    }

    fn new_reg(&mut self) -> Register {
        let id = self.next_reg_id;
        self.next_reg_id = self
            .next_reg_id
            .checked_add(1)
            .expect("register allocation overflow");
        Register(id)
    }

    pub fn switch_to_new_block(&mut self, id: usize) {
        let block = Block {
            insts: std::mem::take(&mut self.current_block),
        };
        self.blocks.insert(self.current_block_id, block);
        self.current_block_id = id;
    }

    fn reserve_block_id(&mut self) -> usize {
        let id = self.next_block_id;
        self.next_block_id = self
            .next_block_id
            .checked_add(1)
            .expect("block allocation overflow");
        id
    }
}
