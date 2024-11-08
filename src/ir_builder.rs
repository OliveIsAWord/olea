use crate::ast;
use crate::compiler_types::Map;
#[allow(clippy::wildcard_imports)]
// We can make these imports explicit when it's less likely to create churn.
use crate::ir::*;

/// This trait defines a helper method for transforming a `T` into an `Option<T>` with a postfix syntax.
trait ToSome {
    fn some(self) -> Option<Self>
    where
        Self: Sized;

    fn some_if(self, condition: bool) -> Option<Self>
    where
        Self: Sized;
}

impl<T> ToSome for T {
    fn some(self) -> Option<Self> {
        Some(self)
    }

    fn some_if(self, condition: bool) -> Option<Self> {
        condition.then_some(self)
    }
}

fn unvoid_assert<T: std::fmt::Debug>(unvoid: bool, item: Option<T>) -> Option<T> {
    match (unvoid, &item) {
        (true, Some(_)) | (false, None) => (),
        (false, Some(_)) | (true, None) => {
            panic!("unvoid assert\nunvoid: {unvoid}\nitem: {item:?}")
        }
    }
    item
}

const fn to_ir_ty(ty: &ast::Type) -> Ty {
    use ast::Type as T;
    match ty {
        &T::Int => Ty::Int,
    }
}

#[derive(Clone, Debug)]
struct IrBuilder {
    parameters: Vec<Register>,
    current_block: Vec<Inst>,
    current_block_id: BlockId,
    next_block_id: usize,
    blocks: Map<BlockId, Block>,
    tys: Map<Register, Ty>,
    scopes: Vec<Map<String, Register>>,
    next_reg_id: u128,
}

impl IrBuilder {
    fn new() -> Self {
        Self {
            parameters: vec![],
            current_block: vec![],
            current_block_id: BlockId::ENTRY,
            next_block_id: BlockId::ENTRY.0 + 1,
            blocks: Map::new(),
            tys: Map::new(),
            scopes: vec![Map::new()],
            next_reg_id: 0,
        }
    }

    fn build_function(
        mut self,
        ast::Function {
            name: _,
            parameters,
            returns,
            body,
        }: &ast::Function,
    ) -> Function {
        for (p_name, p_ty) in parameters {
            let ir_ty = to_ir_ty(p_ty);
            let reg = self.new_reg(ir_ty.clone());
            self.parameters.push(reg);
            // Currently, we assume all variables are stack allocated, so we copy the argument to a stack allocation.
            let var_reg = self.new_var(p_name.clone(), ir_ty);
            self.push_write(var_reg, reg);
        }
        let reg = self.build_block(body, returns.is_some());
        let return_regs = if returns.is_some() {
            vec![reg.unwrap()]
        } else {
            assert_eq!(reg, None);
            vec![]
        };
        self.switch_to_new_block(
            Exit::Jump(JumpLocation::Return(return_regs)),
            BlockId::DUMMY,
        );
        assert_eq!(self.scopes.len(), 1);
        let f = Function::new(self.parameters, self.blocks, self.tys);
        f.type_check();
        f
    }

    fn build_block(&mut self, ast::Block(stmts): &ast::Block, unvoid: bool) -> Option<Register> {
        self.enter_scope();
        let mut last_stmt_return = None;
        for (i, stmt) in stmts.iter().enumerate() {
            let is_last = i == stmts.len() - 1;
            last_stmt_return = self.build_stmt(stmt, unvoid && is_last);
        }
        self.exit_scope();
        unvoid_assert(unvoid, last_stmt_return)
    }

    fn build_stmt(&mut self, stmt: &ast::Stmt, unvoid: bool) -> Option<Register> {
        use ast::Stmt as S;
        let reg = match stmt {
            S::Let(name, ty, body) => {
                let alloc_reg = self.new_var(name.clone(), to_ir_ty(ty));
                let value_reg = self.build_expr_unvoid(body);
                self.push_write(alloc_reg, value_reg);
                None
            }
            S::Expr(expr) => self.build_expr(expr, unvoid),
        };
        unvoid_assert(unvoid, reg)
    }

    fn build_expr_void(&mut self, expr: &ast::Expr) {
        assert_eq!(self.build_expr(expr, false), None);
    }

    fn build_expr_unvoid(&mut self, expr: &ast::Expr) -> Register {
        self.build_expr(expr, true).unwrap()
    }

    fn build_expr(&mut self, expr: &ast::Expr, unvoid: bool) -> Option<Register> {
        use ast::Expr as E;
        use StoreKind as Sk;
        let reg = match expr {
            &E::Int(i) => self.push_store(Sk::Int(i.into())).some_if(unvoid),
            E::BinOp(op, lhs, rhs) => {
                use ast::BinOp as A;
                use BinOp as B;
                let op_kind = match op {
                    A::Add => B::Add,
                    A::Sub => B::Sub,
                };
                let lhs_reg = self.build_expr_unvoid(lhs);
                let rhs_reg = self.build_expr_unvoid(rhs);
                self.push_store(Sk::BinOp(op_kind, lhs_reg, rhs_reg))
                    .some_if(unvoid)
            }
            E::Var(string) => {
                let var_reg = self.get_var(string);
                self.push_store(StoreKind::Read(var_reg)).some_if(unvoid)
            }
            E::Assign(var, body) => {
                let value_reg = self.build_expr_unvoid(body);
                let var_reg = self.get_var(var);
                self.push_write(var_reg, value_reg);
                None
            }
            E::Block(b) => self.build_block(b, unvoid),
            E::If(cond, then_body, else_body) => {
                let then_id = self.reserve_block_id();
                let else_id = self.reserve_block_id();
                let end_id = self.reserve_block_id();

                // evaluate condition, jump to either branch
                self.enter_scope();
                let cond_reg = self.build_expr_unvoid(cond);
                self.switch_to_new_block(
                    Exit::CondJump(
                        Condition::NonZero(cond_reg),
                        JumpLocation::Block(then_id),
                        JumpLocation::Block(else_id),
                    ),
                    then_id,
                );

                // evaluate true branch, jump to end
                let then_yield = self.build_expr(then_body, unvoid);
                let then_id = self.current_block_id;
                self.exit_scope();
                self.switch_to_new_block(Exit::Jump(JumpLocation::Block(end_id)), else_id);

                // evaluate false branch, jump to end
                self.enter_scope();
                let else_yield = self.build_expr(else_body, unvoid);
                let else_id = self.current_block_id;
                self.exit_scope();
                self.switch_to_new_block(Exit::Jump(JumpLocation::Block(end_id)), end_id);

                match (then_yield, else_yield) {
                    (Some(a), Some(b)) => {
                        let choices = [(then_id, a), (else_id, b)].into_iter().collect();
                        self.push_store(StoreKind::Phi(choices)).some()
                    }
                    _ => None,
                }
            }
            E::While(cond, body) => {
                // jump to condition evaluation
                let cond_id = self.reserve_block_id();
                let body_id = self.reserve_block_id();
                let end_id = self.reserve_block_id();
                self.switch_to_new_block(Exit::Jump(JumpLocation::Block(cond_id)), cond_id);

                // condition evaluation, jump to either inner body or end of expression
                self.enter_scope(); // with code like `while x is Some(y): ...`, `y` should be accessible from the body
                let cond_reg = self.build_expr_unvoid(cond);
                self.switch_to_new_block(
                    Exit::CondJump(
                        Condition::NonZero(cond_reg),
                        JumpLocation::Block(body_id),
                        JumpLocation::Block(end_id),
                    ),
                    body_id,
                );

                // body evaluation, jump back to condition
                self.build_expr_void(body);
                self.exit_scope();
                self.switch_to_new_block(Exit::Jump(JumpLocation::Block(cond_id)), end_id);

                // continue evaluation after while loop
                None
            }
        };
        // println!("unvoid {unvoid}\nexpr {expr:?}\nreg {reg:?}\n");
        unvoid_assert(unvoid, reg)
    }

    fn enter_scope(&mut self) {
        self.scopes.push(Map::new());
    }

    fn exit_scope(&mut self) {
        self.scopes.pop();
    }

    fn new_var(&mut self, name: String, ty: Ty) -> Register {
        let reg = self.push_store(StoreKind::StackAlloc(ty));
        self.scopes.last_mut().unwrap().insert(name, reg);
        reg
    }

    fn get_var(&mut self, name: &str) -> Register {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).copied())
            .unwrap_or_else(|| panic!("variable {name:?} not found"))
    }

    fn push_write(&mut self, dst: Register, src: Register) {
        self.push_inst(Inst::Write(dst, src));
    }

    fn push_store(&mut self, sk: StoreKind) -> Register {
        let reg = self.new_reg(sk.ty(&self.tys));
        self.push_inst(Inst::Store(reg, sk));
        reg
    }

    fn push_inst(&mut self, inst: Inst) {
        self.current_block.push(inst);
    }

    fn new_reg(&mut self, ty: Ty) -> Register {
        let reg = Register(self.next_reg_id);
        self.next_reg_id = self
            .next_reg_id
            .checked_add(1)
            .expect("register allocation overflow");
        self.tys.insert(reg, ty);
        reg
    }

    pub fn switch_to_new_block(&mut self, exit: Exit, id: BlockId) {
        let insts = std::mem::take(&mut self.current_block);
        let block = Block::new(insts, exit);
        self.blocks.insert(self.current_block_id, block);
        self.current_block_id = id;
    }

    fn reserve_block_id(&mut self) -> BlockId {
        let id = BlockId(self.next_block_id);
        self.next_block_id = self
            .next_block_id
            .checked_add(1)
            .expect("block allocation overflow");
        id
    }
}

pub fn build(program: &ast::Program) -> Program {
    let mut ir = Program {
        functions: Map::new(),
    };
    for decl in &program.decls {
        use ast::Decl as D;
        match decl {
            D::Function(fn_decl) => {
                let builder = IrBuilder::new();
                let function = builder.build_function(fn_decl);
                ir.functions.insert(fn_decl.name.clone(), function);
            }
        }
    }
    ir
}
