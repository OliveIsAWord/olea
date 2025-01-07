use crate::ast;
use crate::compiler_types::{Map, Name, Span, Spanned, Str};
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

pub enum ErrorKind {
    NotFound(&'static str, Str),
    NameConflict(&'static str, Option<Span>),
    DoesNotYield(Span),
    CantAssignToConstant,
    UnknownIntLiteralSuffix,
    CantCastToTy(Ty),
    #[allow(dead_code)]
    Todo(&'static str),
}

type Error = Spanned<ErrorKind>;
type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Debug)]
struct IrBuilder<'a> {
    parameters: Vec<Register>,
    current_block: Vec<Inst>,
    current_block_id: BlockId,
    next_block_id: usize,
    blocks: Map<BlockId, Block>,
    tys: Map<Register, Ty>,
    spans: Map<Register, Span>,
    scopes: Vec<Map<Str, Register>>,
    next_reg_id: u128,
    function_tys: &'a Map<Str, (Vec<Ty>, Option<Ty>)>,
    defined_tys: &'a DefinedTys,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MaybeVar {
    // A register containing the value we're accessing.
    Constant(Register),
    // A register containing a pointer to the value we're accessing.
    Variable(Register),
}

#[derive(Clone, Debug)]
struct DefinedTys {
    tys: Map<Str, (Ty, Option<Span>)>,
}

impl DefinedTys {
    fn build_ty(&self, ty: &ast::Ty) -> Result<Ty> {
        use ast::TyKind as T;
        match &ty.kind {
            T::Name(name) => match self.tys.get(&name.kind) {
                Some((ty, _)) => Ok(ty.clone()),
                None => Err(Error {
                    kind: ErrorKind::NotFound("type", name.kind.clone()),
                    span: ty.span.clone(),
                }),
            },
            T::Pointer(inner) => self.build_ty(inner).map(Box::new).map(Ty::Pointer),
            T::Function(params, returns) => {
                let params = params
                    .iter()
                    .map(|t| self.build_ty(t))
                    .collect::<Result<_>>()?;
                let returns = returns
                    .iter()
                    .map(|t| self.build_ty(t))
                    .collect::<Result<_>>()?;
                Ok(Ty::Function(params, returns))
            }
        }
    }
}

impl<'a> IrBuilder<'a> {
    fn new(function_tys: &'a Map<Str, (Vec<Ty>, Option<Ty>)>, defined_tys: &'a DefinedTys) -> Self {
        Self {
            parameters: vec![],
            current_block: vec![],
            current_block_id: BlockId::ENTRY,
            next_block_id: BlockId::ENTRY.0 + 1,
            blocks: Map::new(),
            tys: Map::new(),
            spans: Map::new(),
            scopes: vec![Map::new()],
            next_reg_id: 0,
            function_tys,
            defined_tys,
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
    ) -> Result<Function> {
        for (p_name, p_ty) in parameters {
            let ir_ty = self.build_ty(p_ty)?;
            let reg = self.new_reg(ir_ty.clone(), p_name.span.clone());
            self.parameters.push(reg);
            // Currently, we assume all variables are stack allocated, so we copy the argument to a stack allocation.
            let var_reg = self.new_var(p_name.clone(), ir_ty);
            self.push_write(var_reg, reg);
        }
        let return_regs = if let Some(returns) = returns.as_ref() {
            vec![self.build_block_unvoid(body, returns.span.clone())?]
        } else {
            self.build_block(body, false)?;
            vec![]
        };
        self.switch_to_new_block(Exit::Return(return_regs), BlockId::DUMMY);
        assert_eq!(self.scopes.len(), 1);
        Ok(Function::new(
            self.parameters,
            self.blocks,
            self.tys,
            self.spans,
            self.next_reg_id,
        ))
    }

    fn build_block_unvoid(&mut self, block: &ast::Block, outer: Span) -> Result<Register> {
        let r = self.build_block(block, true)?;
        r.ok_or_else(|| Error {
            kind: ErrorKind::DoesNotYield(outer),
            span: block.0.last().unwrap().span.clone(),
        })
    }

    fn build_block(
        &mut self,
        ast::Block(stmts): &ast::Block,
        unvoid: bool,
    ) -> Result<Option<Register>> {
        self.enter_scope();
        let mut last_stmt_return = None;
        for (i, stmt) in stmts.iter().enumerate() {
            let is_last = i == stmts.len() - 1;
            last_stmt_return = self.build_stmt(stmt, unvoid && is_last)?;
        }
        self.exit_scope();
        Ok(last_stmt_return)
    }

    fn build_stmt(&mut self, stmt: &ast::Stmt, unvoid: bool) -> Result<Option<Register>> {
        use ast::StmtKind as S;
        let ast::Stmt { kind, span } = stmt;
        let span = span.clone();
        let reg = match kind {
            S::Let(name, ty, body) => {
                let value_reg = self.build_expr_unvoid(body, span)?;
                let alloc_ty = match ty {
                    Some(t) => self.build_ty(t)?,
                    None => self.tys.get(&value_reg).unwrap().clone(),
                };
                let alloc_reg = self.new_var(name.clone(), alloc_ty);
                self.push_write(alloc_reg, value_reg);
                None
            }
            S::Expr(expr) => self.build_expr(expr, unvoid)?,
        };
        Ok(reg)
    }

    fn build_expr_unvoid(&mut self, expr: &ast::Expr, outer: Span) -> Result<Register> {
        let reg = self.build_expr(expr, true)?;
        match reg {
            Some(r) => Ok(r),
            None => Err(Error {
                kind: ErrorKind::DoesNotYield(outer),
                span: expr.span.clone(),
            }),
        }
    }

    fn build_expr(&mut self, expr: &ast::Expr, unvoid: bool) -> Result<Option<Register>> {
        use ast::ExprKind as E;
        use StoreKind as Sk;
        let ast::Expr { kind, span } = expr;
        let span = span.clone();
        // let span2 = span.clone(); // maybe if i write enough of these, Rust 2024 will make it Copy
        let reg = match kind {
            E::Place(kind) => match self.build_place(kind, span.clone())? {
                MaybeVar::Variable(place_reg) => self
                    .push_store(StoreKind::Read(place_reg), span)
                    .some_if(unvoid),
                MaybeVar::Constant(value_reg) => Some(value_reg),
            },
            // NOTE: We're implicitly checking and evaluating the place expression first, but typechecking currently has to check the value expression first. Should we change our order here?
            E::Assign(place, value) => {
                let MaybeVar::Variable(place_reg) =
                    self.build_place(&place.kind, place.span.clone())?
                else {
                    return Err(Error {
                        kind: ErrorKind::CantAssignToConstant,
                        span,
                    });
                };
                let value_reg = self.build_expr_unvoid(value, span)?;
                self.push_write(place_reg, value_reg);
                None
            }
            E::Int(int, suffix) => {
                let int_ty = if let Some(suffix) = suffix {
                    match suffix.kind.as_ref() {
                        "usize" => IntKind::Usize,
                        "u8" => IntKind::U8,
                        _ => {
                            return Err(Error {
                                kind: ErrorKind::UnknownIntLiteralSuffix,
                                span: suffix.span.clone(),
                            });
                        }
                    }
                } else {
                    IntKind::Usize
                };
                self.push_store(Sk::Int((*int).into(), int_ty), span).some()
            }
            E::UnaryOp(op, e) => {
                use ast::UnaryOpKind as A;
                use UnaryOp as B;
                match op.kind {
                    A::Neg => {
                        let reg = self.build_expr_unvoid(e, span.clone())?;
                        self.push_store(Sk::UnaryOp(B::Neg, reg), span)
                            .some_if(unvoid)
                    }
                    A::Ref => {
                        let maybe_var = match &e.kind {
                            E::Place(kind) => self.build_place(kind, span)?,
                            _ => MaybeVar::Constant(self.build_expr_unvoid(e, span)?),
                        };
                        match maybe_var {
                            MaybeVar::Variable(v) => Some(v),
                            MaybeVar::Constant(c) => {
                                let r = self.push_store(
                                    Sk::StackAlloc(self.tys.get(&c).unwrap().clone()),
                                    e.span.clone(),
                                );
                                self.push_write(r, c);
                                Some(r)
                            }
                        }
                    }
                }
            }
            E::BinOp(op, lhs, rhs) => {
                use ast::BinOpKind as A;
                use BinOp as B;
                let op_kind = match op.kind {
                    A::Add => B::Add,
                    A::Sub => B::Sub,
                    A::Mul => B::Mul,
                    A::CmpLe => B::CmpLe,
                };
                let lhs_reg = self.build_expr_unvoid(lhs, span.clone())?;
                let rhs_reg = self.build_expr_unvoid(rhs, span.clone())?;
                self.push_store(Sk::BinOp(op_kind, lhs_reg, rhs_reg), span)
                    .some_if(unvoid)
            }
            E::As(value, ty) => {
                let value_reg = self.build_expr_unvoid(value, span.clone())?;
                let ir_ty = self.build_ty(ty)?;
                let kind = match ir_ty {
                    Ty::Int(k) => k,
                    t => {
                        return Err(Error {
                            kind: ErrorKind::CantCastToTy(t),
                            // Should we annotate the span of the type or the entire `as` expression?
                            span: ty.span.clone(),
                        });
                    }
                };
                self.push_store(Sk::IntCast(value_reg, kind), span).some()
            }
            // NOTE: When building Paren and Block, we forget their spans, which means subsequent error diagnostics will only ever point to the inner expression. Is this good or bad? We could change this by creating a Copy of the inner register, assigning the copy the outer span.
            E::Paren(inner) => self.build_expr(inner.as_ref(), unvoid)?,
            E::Block(b) => self.build_block(b, unvoid)?,
            E::If(cond, then_body, else_body) => {
                let then_id = self.reserve_block_id();
                let end_id = self.reserve_block_id();
                let else_id = if else_body.is_some() {
                    self.reserve_block_id()
                } else {
                    end_id
                };

                // evaluate condition, jump to either branch
                self.enter_scope();
                let cond_reg = self.build_expr_unvoid(cond, span.clone())?;
                self.switch_to_new_block(
                    Exit::CondJump(Condition::NonZero(cond_reg), then_id, else_id),
                    then_id,
                );

                // evaluate true branch, jump to end
                let then_yield = self.build_block(then_body, unvoid)?;
                self.exit_scope();
                let then_id = self.current_block_id;
                self.switch_to_new_block(Exit::Jump(end_id), else_id);

                // evaluate false branch, jump to end
                let else_yield = else_body
                    .as_ref()
                    .map(|e| {
                        self.enter_scope();
                        let else_yield = self.build_block(e, unvoid)?;
                        self.exit_scope();
                        let else_id = self.current_block_id;
                        self.switch_to_new_block(Exit::Jump(end_id), end_id);
                        Ok(else_yield.map(|e| (e, else_id)))
                    })
                    .transpose()?
                    .flatten();

                match (then_yield, else_yield) {
                    (Some(a), Some((b, else_id))) => {
                        let choices = [(then_id, a), (else_id, b)].into_iter().collect();
                        self.push_store(StoreKind::Phi(choices), span).some()
                    }
                    _ => None,
                }
            }
            E::While(cond, body) => {
                // jump to condition evaluation
                let cond_id = self.reserve_block_id();
                let body_id = self.reserve_block_id();
                let end_id = self.reserve_block_id();
                self.switch_to_new_block(Exit::Jump(cond_id), cond_id);

                // condition evaluation, jump to either inner body or end of expression
                self.enter_scope(); // with code like `while x is Some(y): ...`, `y` should be accessible from the body
                let cond_reg = self.build_expr_unvoid(cond, span)?;
                self.switch_to_new_block(
                    Exit::CondJump(Condition::NonZero(cond_reg), body_id, end_id),
                    body_id,
                );

                // body evaluation, jump back to condition
                self.build_block(body, true)?;
                self.exit_scope();
                self.switch_to_new_block(Exit::Jump(cond_id), end_id);

                // continue evaluation after while loop
                None
            }
            E::Call(callee, args) => {
                let callee = self.build_expr_unvoid(callee, span.clone())?;
                let returns: Vec<_> = match self.tys.get(&callee).unwrap() {
                    Ty::Function(_, returns) => {
                        assert!(matches!(returns.len(), 0 | 1));
                        // somewhat silly clone because we need mutable access to `self` for `new_reg`.
                        returns
                            .clone()
                            .into_iter()
                            .map(|ty| self.new_reg(ty, span.clone()))
                            .collect()
                    }
                    Ty::Int(_) | Ty::Pointer(_) | Ty::Struct(_) => {
                        // dummy return
                        vec![self.new_reg(Ty::Int(IntKind::Usize), span.clone())]
                    }
                };
                let return_reg = returns.first().copied();
                let args = args
                    .iter()
                    .map(|arg| self.build_expr_unvoid(arg, span.clone()))
                    .collect::<Result<_>>()?;
                self.push_inst(Inst::Call {
                    callee,
                    args,
                    returns,
                });
                return_reg
            }
        };
        // println!("unvoid {unvoid}\nexpr {expr:?}\nreg {reg:?}\n");
        Ok(reg)
    }
    // This function returns a MaybeVar because not all syntactic place expressions are semantic place expressions. For example, we can't assign a value to a function. Different code paths we expect a place expression will have to properly handle these cases.
    fn build_place(&mut self, kind: &ast::PlaceKind, span: Span) -> Result<MaybeVar> {
        use ast::PlaceKind as Pk;
        match kind {
            Pk::Var(name) => self
                .get_var(name)
                .map(MaybeVar::Variable)
                .or_else(|| {
                    self.function_tys
                        .contains_key(&name.kind)
                        .then(|| self.push_store(StoreKind::Function(name.kind.clone()), span))
                        .map(MaybeVar::Constant)
                })
                .ok_or_else(|| Error {
                    kind: ErrorKind::NotFound("variable", name.kind.clone()),
                    span: name.span.clone(),
                }),
            Pk::Deref(e, _) => self.build_expr_unvoid(e, span).map(MaybeVar::Variable),
            Pk::Index(indexee, index, index_span) => {
                let indexee_reg = self.build_expr_unvoid(indexee, span.clone())?;
                let index_reg = self.build_expr_unvoid(index, index_span.clone())?;
                let indexed_reg =
                    self.push_store(StoreKind::PtrOffset(indexee_reg, index_reg), span);
                Ok(MaybeVar::Variable(indexed_reg))
            }
            Pk::Field(struct_value, field) => {
                let struct_reg = self.build_expr_unvoid(struct_value, span.clone())?;
                let field_ptr_reg =
                    self.push_store(StoreKind::FieldOffset(struct_reg, field.kind.clone()), span);
                Ok(MaybeVar::Variable(field_ptr_reg))
            }
        }
    }

    fn enter_scope(&mut self) {
        self.scopes.push(Map::new());
    }

    fn exit_scope(&mut self) {
        self.scopes.pop();
    }

    fn build_ty(&self, ty: &ast::Ty) -> Result<Ty> {
        self.defined_tys.build_ty(ty)
    }

    fn new_var(&mut self, name: Name, ty: Ty) -> Register {
        let reg = self.push_store(StoreKind::StackAlloc(ty), name.span);
        self.scopes.last_mut().unwrap().insert(name.kind, reg);
        reg
    }

    fn get_var(&self, name: &Name) -> Option<Register> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name.kind.as_ref()).copied())
    }

    fn push_write(&mut self, dst: Register, src: Register) {
        self.push_inst(Inst::Write(dst, src));
    }

    fn push_store(&mut self, sk: StoreKind, span: Span) -> Register {
        let ty = self.guess_ty(&sk);
        let reg = self.new_reg(ty, span);
        self.push_inst(Inst::Store(reg, sk));
        reg
    }
    pub fn guess_ty(&self, sk: &StoreKind) -> Ty {
        const DUMMY_TY: Ty = Ty::Int(IntKind::U8);
        use StoreKind as Sk;
        let t = |r| self.tys.get(r).unwrap().clone();
        match sk {
            &Sk::Int(_, kind) | &Sk::IntCast(_, kind) => Ty::Int(kind),
            Sk::Phi(regs) => t(regs.first_key_value().expect("empty phi").1),
            Sk::BinOp(_, lhs, _rhs) => t(lhs),
            Sk::PtrOffset(ptr, _) => t(ptr),
            Sk::FieldOffset(r, field) => {
                let Ty::Pointer(value) = t(r) else {
                    println!("foo");
                    return DUMMY_TY;
                };
                let Ty::Struct(fields) = value.as_ref() else {
                    println!("foofoo");
                    return DUMMY_TY;
                };
                fields
                    .iter()
                    .find_map(|(name, ty)| {
                        (name == field).then(|| Ty::Pointer(Box::new(ty.clone())))
                    })
                    .unwrap_or(DUMMY_TY)
            }
            Sk::StackAlloc(ty) => Ty::Pointer(Box::new(ty.clone())),
            Sk::Copy(r) | Sk::UnaryOp(UnaryOp::Neg, r) => t(r),
            Sk::Read(r) => match self.tys.get(r).unwrap() {
                Ty::Pointer(inner) => inner.as_ref().clone(),
                Ty::Int(_) | Ty::Function(..) | Ty::Struct(_) => DUMMY_TY,
            },
            Sk::Function(name) => {
                let (args, returns) = self
                    .function_tys
                    .get(name)
                    .expect("constructed function instruction to unknown function")
                    .clone();
                Ty::Function(args, returns.into_iter().collect())
            }
        }
    }

    fn push_inst(&mut self, inst: Inst) {
        self.current_block.push(inst);
    }

    fn new_reg(&mut self, ty: Ty, span: Span) -> Register {
        let reg = Register(self.next_reg_id);
        self.next_reg_id = self
            .next_reg_id
            .checked_add(1)
            .expect("register allocation overflow");
        self.tys.insert(reg, ty);
        self.spans.insert(reg, span);
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

pub fn build(program: &ast::Program) -> Result<Program> {
    use ast::DeclKind as D;
    let mut function_tys = Map::new();
    let mut defined_tys = DefinedTys {
        tys: Map::from([
            ("u8".into(), (Ty::Int(IntKind::U8), None)),
            ("usize".into(), (Ty::Int(IntKind::Usize), None)),
        ]),
    };
    // collect struct types
    // currently we only accept forward declarations of structs (bad). fixing this in the general case requires a pervasive rewrite of the IR type system.
    for ast::Decl { kind, span: _ } in &program.decls {
        match kind {
            D::Function(_) | D::ExternFunction(_) => {}
            D::Struct(ast::Struct { name, fields }) => {
                let mut ir_fields: Vec<(Str, Ty)> = Vec::with_capacity(fields.len());
                let mut names = Map::new();
                for (field_name, field_ty) in fields {
                    let ty = defined_tys.build_ty(field_ty)?;
                    ir_fields.push((field_name.kind.clone(), ty));
                    if let Some(previous_span) =
                        names.insert(field_name.kind.clone(), field_name.span.clone())
                    {
                        return Err(Error {
                            kind: ErrorKind::NameConflict("field", Some(previous_span)),
                            span: field_name.span.clone(),
                        });
                    }
                }
                let ty = Ty::Struct(ir_fields);
                let name_span = name.span.clone();
                // check if another ty in the same scope has the same name
                let maybe_clash = defined_tys
                    .tys
                    .insert(name.kind.clone(), (ty, name_span.some()));
                if let Some((_, previous_span)) = maybe_clash {
                    return Err(Error {
                        kind: ErrorKind::NameConflict("type", previous_span),
                        span: name.span.clone(),
                    });
                }
            }
        }
    }
    for ast::Decl { kind, span: _ } in &program.decls {
        match kind {
            D::Function(ast::Function {
                name,
                parameters,
                returns,
                body: _,
            }) => {
                function_tys.insert(
                    name.kind.clone(),
                    (
                        parameters
                            .iter()
                            .map(|arg| defined_tys.build_ty(&arg.1))
                            .collect::<Result<_>>()?,
                        returns
                            .as_ref()
                            .map(|ret| defined_tys.build_ty(ret))
                            .transpose()?,
                    ),
                );
            }
            D::ExternFunction(ast::ExternFunction {
                name,
                parameters,
                returns,
            }) => {
                function_tys.insert(
                    name.kind.clone(),
                    (
                        parameters
                            .iter()
                            .map(|arg| defined_tys.build_ty(arg))
                            .collect::<Result<_>>()?,
                        returns
                            .as_ref()
                            .map(|ret| defined_tys.build_ty(ret))
                            .transpose()?,
                    ),
                );
            }
            D::Struct(_) => {}
        }
    }
    let mut functions = Map::new();
    for decl in &program.decls {
        match &decl.kind {
            D::Function(fn_decl) => {
                let builder = IrBuilder::new(&function_tys, &defined_tys);
                let function = builder.build_function(fn_decl)?;
                functions.insert(fn_decl.name.kind.clone(), function);
            }
            D::ExternFunction(_) | D::Struct(_) => {}
        }
    }
    let function_tys = function_tys
        .into_iter()
        .map(|(name, (params, returns))| (name, (params, returns.into_iter().collect())))
        .collect();
    Ok(Program {
        functions,
        function_tys,
    })
}
