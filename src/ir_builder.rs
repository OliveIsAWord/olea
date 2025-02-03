use crate::ast;
use crate::compiler_types::{Map, Name, Set, Span, Spanned, Str};
use crate::ir::*;

const INT_TYPES: &[(&str, IntKind)] = &[
    ("u8", IntKind::U8),
    ("u16", IntKind::U16),
    ("u32", IntKind::U32),
    ("usize", IntKind::Usize),
];

enum OleaTy {
    Int(IntKind),
    Pointer(Arc<Self>),
    Function(Arc<[Self]>, Option<Arc<Self>>),
}

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
    CantCastToTy(String),
    InfiniteType(Vec<Str>),
    NotStruct(Str),
    MissingFields(Vec<Str>, Option<Span>),
    #[allow(
        dead_code,
        reason = "This variant is often used sporadically and temporarily, and only serves to give better diagnostics in the presence of future language direction. It may come in and out of use over the lifetime of the compiler."
    )]
    Todo(&'static str),
}

type Error = Spanned<ErrorKind>;
type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
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
    program_tys: &'a mut TyMap,
    function_tys: &'a Map<Str, (Vec<Ty>, Option<Ty>)>,
    defined_tys: &'a DefinedTys,
    dummy_ty: Ty,
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
    fn build_ty(&self, ty: &ast::Ty, program_tys: &mut TyMap) -> Result<Ty> {
        use ast::TyKind as T;
        match &ty.kind {
            T::Name(name) => match self.tys.get(&name.kind) {
                Some(&(ty, _)) => Ok(ty),
                None => Err(Error {
                    kind: ErrorKind::NotFound("type", name.kind.clone()),
                    span: ty.span.clone(),
                }),
            },
            T::Pointer(inner) => {
                let inner_kind = self.build_ty(inner, program_tys)?;
                Ok(program_tys.insert(TyKind::Pointer(inner_kind)))
            }
            T::Function(params, returns) => {
                let params = params
                    .iter()
                    .map(|t| self.build_ty(t, program_tys))
                    .collect::<Result<_>>()?;
                let returns = returns
                    .iter()
                    .map(|t| self.build_ty(t, program_tys))
                    .collect::<Result<_>>()?;
                Ok(program_tys.insert(TyKind::Function(params, returns)))
            }
        }
    }
}

impl<'a> IrBuilder<'a> {
    fn new(
        function_tys: &'a Map<Str, (Vec<Ty>, Option<Ty>)>,
        defined_tys: &'a DefinedTys,
        program_tys: &'a mut TyMap,
    ) -> Self {
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
            dummy_ty: program_tys.insert(TyKind::Int(IntKind::U8)),
            function_tys,
            defined_tys,
            program_tys,
        }
    }

    fn build_function(
        mut self,
        ast::Function { signature, body }: &ast::Function,
    ) -> Result<Function> {
        let ast::FunctionSignature {
            name: _,
            parameters,
            returns,
        } = signature;
        for (p_name, p_ty) in parameters {
            let ir_ty = self.build_ty(p_ty)?;
            let reg = self.new_reg(ir_ty, p_name.span.clone());
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
                    None => self.tys[&value_reg],
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
        use StoreKind as Sk;
        use ast::ExprKind as E;
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
                    INT_TYPES
                        .iter()
                        .find_map(|(name, int_kind)| (**name == *suffix.kind).then_some(*int_kind))
                        .ok_or_else(|| Error {
                            kind: ErrorKind::UnknownIntLiteralSuffix,
                            span: suffix.span.clone(),
                        })?
                } else {
                    IntKind::Usize
                };
                self.push_store(Sk::Int((*int).into(), int_ty), span).some()
            }
            E::Struct(name, fields) => {
                const DUMMY_REG: Register = Register(u128::MAX);
                let mut evaled_fields: Map<Str, (Span, Register)> = Map::new();
                for (field, expr) in fields {
                    if let Some((prev_span, _)) = evaled_fields.get(&field.kind) {
                        return Err(Error {
                            kind: ErrorKind::NameConflict("struct field", prev_span.clone().some()),
                            span: field.span.clone(),
                        });
                    }
                    let evaled = self.build_expr_unvoid(expr, span.clone())?;
                    evaled_fields.insert(field.kind.clone(), (field.span.clone(), evaled));
                }
                let Some((struct_ty, struct_span)) = self.defined_tys.tys.get(&name.kind) else {
                    return Err(Error {
                        kind: ErrorKind::NotFound("struct type", name.kind.clone()),
                        span: name.span.clone(),
                    });
                };
                let TyKind::Struct {
                    name: type_name,
                    fields: type_fields,
                } = &self.program_tys[*struct_ty]
                else {
                    return Err(Error {
                        kind: ErrorKind::NotStruct(name.kind.clone()),
                        span: name.span.clone(),
                    });
                };
                assert_eq!(&name.kind, type_name);
                let mut filled_fields: Vec<(Str, Register)> = type_fields
                    .iter()
                    .map(|(name, _)| (name.clone(), DUMMY_REG))
                    .collect();
                for (name, (span, r)) in evaled_fields {
                    let Some(dummy_r) = filled_fields
                        .iter_mut()
                        .find_map(|(field_name, r)| (&name == field_name).then_some(r))
                    else {
                        return Err(Error {
                            kind: ErrorKind::NotFound("struct field", name),
                            span,
                        });
                    };
                    *dummy_r = r;
                }
                let missing_fields: Vec<_> = filled_fields
                    .iter()
                    .filter(|(_, r)| *r == DUMMY_REG)
                    .map(|(name, _)| name.clone())
                    .collect();
                if !missing_fields.is_empty() {
                    return Err(Error {
                        kind: ErrorKind::MissingFields(missing_fields, struct_span.clone()),
                        span,
                    });
                }
                self.push_store(
                    Sk::Struct {
                        name: name.kind.clone(),
                        fields: filled_fields,
                    },
                    span,
                )
                .some()
            }
            E::UnaryOp(op, e) => {
                use UnaryOp as B;
                use ast::UnaryOpKind as A;
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
                                let r =
                                    self.push_store(Sk::StackAlloc(self.tys[&c]), e.span.clone());
                                self.push_write(r, c);
                                Some(r)
                            }
                        }
                    }
                }
            }
            E::BinOp(op, lhs, rhs) => {
                use BinOp as B;
                use ast::BinOpKind as A;
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
                match self.program_tys[ir_ty] {
                    TyKind::Int(kind) => self.push_store(Sk::IntCast(value_reg, kind), span).some(),
                    TyKind::Pointer(kind) => {
                        self.push_store(Sk::PtrCast(value_reg, kind), span).some()
                    }
                    ref t => {
                        return Err(Error {
                            kind: ErrorKind::CantCastToTy(self.program_tys.format_kind(t)),
                            span: ty.span.clone(),
                        });
                    }
                }
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
                let returns: Vec<_> = match &self.program_tys[self.tys[&callee]] {
                    TyKind::Function(_, returns) => {
                        assert!(matches!(returns.len(), 0 | 1));
                        // somewhat silly clone because we need mutable access to `self` for `new_reg`.
                        returns
                            .clone()
                            .into_iter()
                            .map(|ty| self.new_reg(ty, span.clone()))
                            .collect()
                    }
                    _ => {
                        // dummy return
                        vec![self.new_reg(self.dummy_ty, span.clone())]
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

    fn build_ty(&mut self, ty: &ast::Ty) -> Result<Ty> {
        self.defined_tys.build_ty(ty, self.program_tys)
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
    pub fn guess_ty(&mut self, sk: &StoreKind) -> Ty {
        use StoreKind as Sk;
        let dummy_ty = self.dummy_ty;
        let t = |r| *self.tys.get(r).unwrap();
        match sk {
            &Sk::Int(_, kind) | &Sk::IntCast(_, kind) => self.program_tys.insert(TyKind::Int(kind)),
            &Sk::PtrCast(_, kind) => self.program_tys.insert(TyKind::Pointer(kind)),
            Sk::Phi(regs) => t(regs.first_key_value().expect("empty phi").1),
            Sk::BinOp(_, lhs, _rhs) => t(lhs),
            Sk::PtrOffset(ptr, _) => t(ptr),
            Sk::FieldOffset(r, field) => {
                let TyKind::Pointer(value) = self.program_tys[t(r)] else {
                    return dummy_ty;
                };
                let TyKind::Struct { fields, .. } = &self.program_tys[value] else {
                    return dummy_ty;
                };
                fields
                    .clone()
                    .into_iter()
                    .find_map(|(name, ty)| {
                        (&name == field).then(|| self.program_tys.insert(TyKind::Pointer(ty)))
                    })
                    .unwrap_or(dummy_ty)
            }
            &Sk::StackAlloc(ty) => self.program_tys.insert(TyKind::Pointer(ty)),
            Sk::Copy(r) | Sk::UnaryOp(UnaryOp::Neg, r) => t(r),
            Sk::Read(r) => match self.program_tys[self.tys[r]] {
                TyKind::Pointer(inner) => inner,
                _ => dummy_ty,
            },
            Sk::Function(name) => {
                let (args, returns) = self
                    .function_tys
                    .get(name)
                    .expect("constructed function instruction to unknown function")
                    .clone();
                self.program_tys
                    .insert(TyKind::Function(args, returns.into_iter().collect()))
            }
            Sk::Struct { name, .. } => self.defined_tys.tys[name].0,
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
    let mut program_tys = TyMap::new();
    // Global type construction first pass: register all type names in `defined_tys`. Type declarations can reference structs declared after themselves, even cyclically.
    let mut defined_tys = DefinedTys {
        tys: INT_TYPES
            .iter()
            .map(|&(name, int_kind)| {
                (
                    name.into(),
                    (program_tys.insert(TyKind::Int(int_kind)), None),
                )
            })
            .collect(),
    };
    for ast::Decl { kind, span: _ } in &program.decls {
        match kind {
            D::Function(_) | D::ExternFunction(_) => {}
            D::Struct(ast::Struct { name, fields: _ }) => {
                let maybe_clash = defined_tys.tys.insert(
                    name.kind.clone(),
                    (program_tys.reserve(), name.span.clone().some()),
                );
                if let Some((_, previous_span)) = maybe_clash {
                    return Err(Error {
                        kind: ErrorKind::NameConflict("type", previous_span),
                        span: name.span.clone(),
                    });
                }
            }
        }
    }
    // Global type construction second pass: fill out actual type information we skipped in the first pass.
    // also track value size dependencies to detect and reject infinite size types
    // this is a map from named types to the named types this type stores by value, as well as a span for diagnostics
    let mut value_cycles: Map<Str, (Span, Vec<Str>)> = Map::new();
    for ast::Decl { kind, span: _ } in &program.decls {
        match kind {
            D::Function(_) | D::ExternFunction(_) => {}
            D::Struct(ast::Struct { name, fields }) => {
                use ast::TyKind as Tk;
                let mut ir_fields: Vec<(Str, Ty)> = Vec::with_capacity(fields.len());
                let mut names = Map::new();
                let mut fields_stored_by_value = vec![];
                for (field_name, field_ty) in fields {
                    let ty = defined_tys.build_ty(field_ty, &mut program_tys)?;
                    ir_fields.push((field_name.kind.clone(), ty));
                    if let Some(previous_span) =
                        names.insert(field_name.kind.clone(), field_name.span.clone())
                    {
                        return Err(Error {
                            kind: ErrorKind::NameConflict("field", Some(previous_span)),
                            span: field_name.span.clone(),
                        });
                    }
                    // does this field store a possibly recursive type by value?
                    match &field_ty.kind {
                        Tk::Pointer(_) | Tk::Function(_, _) => {}
                        Tk::Name(name) => fields_stored_by_value.push(name.kind.clone()),
                    }
                }
                let kind = TyKind::Struct {
                    name: name.kind.clone(),
                    fields: ir_fields,
                };
                let ty_index = defined_tys.tys[&name.kind].0;
                program_tys.insert_at(ty_index, kind);
                // register this struct in the cycle graph
                value_cycles.insert(
                    name.kind.clone(),
                    (name.span.clone(), fields_stored_by_value),
                );
            }
        }
    }
    // detect infinite size types
    {
        // each item on the stack is a visited type and all the types it is going to visit
        let mut stack: Vec<(&Str, &[Str])> = vec![];
        // all the types we know don't form infinite size loops
        let mut closed: Set<Str> = Set::new();
        for (name, (_, fields)) in &value_cycles {
            stack.push((name, fields));
            while let Some((_, fields)) = stack.last_mut() {
                let Some(field) = fields.first() else {
                    let (old_field, _) = stack.pop().unwrap();
                    closed.insert(old_field.clone());
                    continue;
                };
                *fields = &fields[1..];
                if closed.contains(field) {
                    continue;
                }
                for (i, (prior, _)) in stack.iter().enumerate().rev() {
                    if field == *prior {
                        let cycle = stack[i..].iter().map(|&(n, _)| n.clone()).collect();
                        return Err(Error {
                            kind: ErrorKind::InfiniteType(cycle),
                            span: value_cycles[*prior].0.clone(),
                        });
                    }
                }
                if let Some((_, recursive_fields)) = value_cycles.get(field) {
                    stack.push((field, recursive_fields));
                } else {
                    closed.insert(field.clone());
                }
            }
        }
        drop(value_cycles);
    }
    let mut function_tys = Map::new();
    for ast::Decl { kind, span: _ } in &program.decls {
        let mut build_ty = |t| defined_tys.build_ty(t, &mut program_tys);
        match kind {
            D::Function(ast::Function { signature, .. }) | D::ExternFunction(signature) => {
                let ast::FunctionSignature {
                    name,
                    parameters,
                    returns,
                } = signature;
                function_tys.insert(
                    name.kind.clone(),
                    (
                        parameters
                            .iter()
                            .map(|(_, t)| build_ty(t))
                            .collect::<Result<_>>()?,
                        returns.as_ref().map(build_ty).transpose()?,
                    ),
                );
            }
            D::Struct(_) => {}
        }
    }
    let function_tys = function_tys;
    let mut functions = Map::new();
    for decl in &program.decls {
        match &decl.kind {
            D::Function(fn_decl) => {
                let builder = IrBuilder::new(&function_tys, &defined_tys, &mut program_tys);
                let function = builder.build_function(fn_decl)?;
                functions.insert(fn_decl.signature.name.kind.clone(), function);
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
        tys: program_tys,
    })
}
