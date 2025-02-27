use crate::ast;
use crate::compiler_prelude::*;
use crate::ir::*;
use StoreKind as Sk;

const INT_TYS: &[(&str, IntKind)] = &[
    ("u8", IntKind::U8),
    ("u16", IntKind::U16),
    ("u32", IntKind::U32),
    ("usize", IntKind::Usize),
];

const OTHER_TYS: &[(&str, TyKind)] = &[("bool", TyKind::Bool)];

fn get_int_kind_from_suffix(suffix: &Name) -> Result<IntKind> {
    INT_TYS
        .iter()
        .find_map(|&(name, int_kind)| (*name == *suffix.kind).then_some(int_kind))
        .ok_or_else(|| Error {
            kind: ErrorKind::UnknownIntLiteralSuffix,
            span: suffix.span.clone(),
        })
}

/// This trait defines a helper method for transforming a `T` into an `Option<T>` with a postfix syntax.
trait ToSome: Sized {
    fn some(self) -> Option<Self>;
    fn some_if(self, condition: bool) -> Option<Self>;
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
    MissingArgs(Vec<Str>, Option<Span>),
    InvalidArgs(Vec<Str>),
    BadPun,
    IllFormedComparison,
    NoSelf(Option<Span>),
    NotMethod,
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
    self_reg: Option<Register>,
    underscore_self: Option<Span>,
    next_reg_id: u128,
    static_values: &'a mut Map<Str, Value>,
    program_tys: &'a mut TyMap,
    function_tys: &'a Map<Str, Ty>,
    constants: &'a Map<Str, Value>,
    defined_tys: &'a DefinedTys,
    dummy_ty: Ty,
}

#[must_use]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MaybeVar {
    /// A register containing the value we're accessing.
    Constant(Register),
    /// A register containing a pointer to the value we're accessing.
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
            T::Array(inner, count) => {
                let inner_kind = self.build_ty(inner, program_tys)?;
                let ValueKind::Usize(count) = eval_const(count)? else {
                    return Err(todo("const eval type error", count.span.clone()));
                };
                Ok(program_tys.insert(TyKind::Array(inner_kind, count.into())))
            }
            T::Function(underscore_self, params, returns) => self.build_function_ty(
                underscore_self.is_none(),
                params,
                returns.as_ref().map(|v| &**v),
                program_tys,
            ),
        }
    }
    fn build_function_ty(
        &self,
        has_self: bool,
        params: &[(IsAnon, Name, ast::Ty)],
        returns: Option<&ast::Ty>,
        program_tys: &mut TyMap,
    ) -> Result<Ty> {
        let ir_params: IndexMap<_, _> = params
            .iter()
            .map(|(is_anon, name, t)| {
                self.build_ty(t, program_tys)
                    .map(|t| (name.kind.clone(), (*is_anon, t)))
            })
            .collect::<Result<_>>()?;
        if params.len() != ir_params.len() {
            for name in ir_params.keys() {
                let mut prev_span = None;
                for (_, n, _) in params {
                    let span = n.span.clone();
                    if &n.kind == name {
                        if let Some(prev_span) = prev_span.clone() {
                            return Err(Error {
                                kind: ErrorKind::NameConflict(
                                    "function parameter",
                                    Some(prev_span),
                                ),
                                span,
                            });
                        }
                        prev_span = Some(span);
                    }
                }
            }
            unreachable!()
        }
        let returns = returns
            .iter()
            .map(|t| self.build_ty(t, program_tys))
            .collect::<Result<_>>()?;
        Ok(program_tys.insert(TyKind::Function {
            has_self,
            params: ir_params,
            returns,
        }))
    }
}

fn eval_const(expr: &ast::Expr) -> Result<ValueKind> {
    use ast::ExprKind as E;
    match &expr.kind {
        E::Int(i, suffix) => {
            let n = u128::from(*i);
            let kind = match suffix {
                Some(suffix) => get_int_kind_from_suffix(suffix)?,
                None => IntKind::Usize,
            };
            let value = match kind {
                IntKind::U8 => ValueKind::U8(n as _),
                IntKind::U16 => ValueKind::U16(n as _),
                IntKind::U32 => ValueKind::U32(n as _),
                IntKind::Usize => ValueKind::Usize(n as _),
            };
            Ok(value)
        }
        _ => Err(todo(
            "const evaluation. Try using a plain integer literal instead!",
            expr.span.clone(),
        )),
    }
}

impl<'a> IrBuilder<'a> {
    fn new(
        function_tys: &'a Map<Str, Ty>,
        constants: &'a Map<Str, Value>,
        defined_tys: &'a DefinedTys,
        static_values: &'a mut Map<Str, Value>,
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
            self_reg: None,
            underscore_self: None,
            next_reg_id: 0,
            dummy_ty: program_tys.insert(TyKind::Int(IntKind::U8)),
            function_tys,
            constants,
            defined_tys,
            static_values,
            program_tys,
        }
    }

    fn build_function(
        mut self,
        ast::Function { signature, body }: &ast::Function,
    ) -> Result<Function> {
        let ast::FunctionSignature {
            name,
            underscore_self,
            parameters,
            returns,
        } = signature;
        self.underscore_self = underscore_self.clone();
        let TyKind::Function {
            params: ir_params, ..
        } = self.program_tys[self.function_tys[&name.kind]].clone()
        else {
            unreachable!();
        };
        for (i, ((_, p_name, _), (_, (_, ir_ty)))) in zip(parameters, ir_params).enumerate() {
            let reg = self.new_reg(ir_ty, p_name.span.clone());
            self.parameters.push(reg);
            // Currently, we assume all variables are stack allocated, so we copy the argument to a stack allocation.
            let var_reg = self.new_var(p_name.clone(), ir_ty);
            self.push_write(var_reg, reg);
            if i == 0 && underscore_self.is_none() {
                self.self_reg = Some(var_reg);
            }
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

    fn build_struct_constructor(mut self, ast::Struct { name, fields }: &ast::Struct) -> Function {
        let ty = self.defined_tys.tys[&name.kind].0;
        let TyKind::Struct {
            fields: ir_fields, ..
        } = self.program_tys[ty].clone()
        else {
            unreachable!();
        };
        let mut parameters: Map<&str, Register> = Map::new();
        let field_args = zip(&ir_fields, fields)
            .map(|((name, ty), ast_field)| {
                let span = ast_field.1.span.clone();
                let reg = self.new_reg(*ty, span);
                parameters.insert(name, reg);
                reg
            })
            .collect();
        self.parameters.extend(parameters.values());
        let struct_reg = self.push_store(
            Sk::Struct {
                ty,
                fields: field_args,
            },
            name.span.clone(),
        );
        self.switch_to_new_block(Exit::Return(vec![struct_reg]), BlockId::DUMMY);
        Function::new(
            self.parameters,
            self.blocks,
            self.tys,
            self.spans,
            self.next_reg_id,
        )
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
            S::Expr(expr) => self.build_expr(expr, unvoid)?,
            // NOTE: We're implicitly checking and evaluating the place expression first, but typechecking currently has to check the value expression first. Should we change our order here?
            S::Assign(place, value) => {
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
            S::Continue => return Err(todo("continue", span)),
            S::Return(_e) => return Err(todo("return", span)),
            S::Break(_e) => return Err(todo("break", span)),
            S::Defer(_e) => return Err(todo("defer", span)),
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
        let ast::Expr { kind, span } = expr;
        let span = span.clone();
        // let span2 = span.clone(); // maybe if i write enough of these, Rust 2024 will make it Copy
        let reg = match kind {
            E::Place(kind) => {
                let maybe_var = self.build_place(kind, span.clone())?;
                self.maybe_var_to_value(maybe_var, span).some()
            }
            E::Int(int, suffix) => {
                let int_ty = suffix
                    .as_ref()
                    .map_or(Ok(IntKind::Usize), get_int_kind_from_suffix)?;
                self.push_store(Sk::Int((*int).into(), int_ty), span).some()
            }
            E::String(string) => {
                let bytes: Vec<_> = string.bytes().chain(Some(0)).map(ValueKind::U8).collect();
                let u8_ty = self.program_tys.insert(TyKind::Int(IntKind::U8));
                let array_ty = self
                    .program_tys
                    .insert(TyKind::Array(u8_ty, bytes.len().try_into().unwrap()));
                let value = Value {
                    kind: ValueKind::Array(bytes),
                    ty: array_ty,
                };
                let static_name = Str::from(format!("__olea_string_{}", self.static_values.len()));
                self.static_values.insert(static_name.clone(), value);
                let pointer_to_byte_array = self.push_store(Sk::Static(static_name), span.clone());
                self.push_store(Sk::PtrCast(pointer_to_byte_array, u8_ty), span)
                    .some()
            }
            E::Tuple(items) => {
                let _regs = items
                    .iter()
                    .map(|item| self.build_expr_unvoid(item, span.clone()))
                    .collect::<Result<Vec<_>>>()?;
                return Err(todo("tuples", span));
            }
            E::UnaryOp(op, e) => {
                use UnaryOp as B;
                use ast::UnaryOpKind as A;
                let op_span = op.span.clone();
                match op.kind {
                    A::Neg => {
                        let reg = self.build_expr_unvoid(e, op_span)?;
                        self.push_store(Sk::UnaryOp(B::Neg, reg), span)
                            .some_if(unvoid)
                    }
                    A::Ref => self.build_expr_ref(e, op_span)?.some(),
                }
            }
            E::BinOp(op, lhs, rhs) => {
                use BinOp as B;
                use ast::BinOpKind as A;
                let mut arithmetic = |op_kind| {
                    let lhs_reg = self.build_expr_unvoid(lhs, span.clone())?;
                    let rhs_reg = self.build_expr_unvoid(rhs, span.clone())?;
                    let result =
                        self.push_store(Sk::BinOp(op_kind, lhs_reg, rhs_reg), span.clone());
                    Ok(result)
                };
                let result = match op.kind {
                    A::Add => arithmetic(B::Add)?,
                    A::Sub => arithmetic(B::Sub)?,
                    A::Mul => arithmetic(B::Mul)?,
                    A::Div => arithmetic(B::Div)?,
                    A::And => {
                        let lhs_reg = self.build_expr_unvoid(lhs, span.clone())?;
                        let lhs_id = self.current_block_id;
                        let end_id = self.reserve_block_id();
                        let continue_id = self.reserve_block_id();
                        self.switch_to_new_block(
                            Exit::CondJump(lhs_reg, continue_id, end_id),
                            continue_id,
                        );
                        let rhs_reg = self.build_expr_unvoid(rhs, span.clone())?;
                        let rhs_id = self.current_block_id;
                        self.switch_to_new_block(Exit::Jump(end_id), end_id);
                        let phi_map = [(lhs_id, lhs_reg), (rhs_id, rhs_reg)].into_iter().collect();
                        self.push_store(Sk::Phi(phi_map), span)
                    }
                    A::Or => {
                        let lhs_reg = self.build_expr_unvoid(lhs, span.clone())?;
                        let lhs_id = self.current_block_id;
                        let end_id = self.reserve_block_id();
                        let continue_id = self.reserve_block_id();
                        self.switch_to_new_block(
                            Exit::CondJump(lhs_reg, end_id, continue_id),
                            continue_id,
                        );
                        let rhs_reg = self.build_expr_unvoid(rhs, span.clone())?;
                        let rhs_id = self.current_block_id;
                        self.switch_to_new_block(Exit::Jump(end_id), end_id);
                        let phi_map = [(lhs_id, lhs_reg), (rhs_id, rhs_reg)].into_iter().collect();
                        self.push_store(Sk::Phi(phi_map), span)
                    }
                };
                Some(result)
            }
            E::Comparison {
                operands: ast_operands,
                operators,
            } => {
                let mut operands = ast_operands.iter();
                let unvoid_span = operators[0].span.clone();
                let end_id = self.reserve_block_id();
                let mut phi_map = Map::new();
                let mut lhs = self.build_expr_unvoid(operands.next().unwrap(), unvoid_span)?;
                // these two booleans track the well-formedness of the comparison chain
                let mut less_ok = true;
                let mut greater_ok = true;
                for (i, (rhs, op)) in zip(operands, operators).enumerate() {
                    let valid = match op.kind {
                        Cmp::Eq => true,
                        Cmp::Lt | Cmp::Le => {
                            greater_ok = false;
                            less_ok
                        }
                        Cmp::Gt | Cmp::Ge => {
                            less_ok = false;
                            greater_ok
                        }
                        Cmp::Ne => {
                            let b = less_ok && greater_ok;
                            less_ok = false;
                            greater_ok = false;
                            b
                        }
                    };
                    if !valid {
                        return Err(Error {
                            kind: ErrorKind::IllFormedComparison,
                            span: op.span.clone(),
                        });
                    }
                    let rhs = self.build_expr_unvoid(rhs, op.span.clone())?;
                    let span = ast_operands[i].span.start..ast_operands[i + 1].span.end;
                    let cmp_result =
                        self.push_store(Sk::BinOp(BinOp::Cmp(op.kind), lhs, rhs), span);
                    let current_id = self.current_block_id;
                    phi_map.insert(current_id, cmp_result);
                    if i + 2 == ast_operands.len() {
                        // tail comparison
                        self.switch_to_new_block(Exit::Jump(end_id), end_id);
                    } else {
                        let continue_id = self.reserve_block_id();
                        self.switch_to_new_block(
                            Exit::CondJump(cmp_result, continue_id, end_id),
                            continue_id,
                        );
                        lhs = rhs;
                    }
                }
                self.push_store(Sk::Phi(phi_map), span).some()
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
                self.switch_to_new_block(Exit::CondJump(cond_reg, then_id, else_id), then_id);

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
                        self.push_store(Sk::Phi(choices), span).some()
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
                self.switch_to_new_block(Exit::CondJump(cond_reg, body_id, end_id), body_id);

                // body evaluation, jump back to condition
                self.build_block(body, true)?;
                self.exit_scope();
                self.switch_to_new_block(Exit::Jump(cond_id), end_id);

                // continue evaluation after while loop
                None
            }
            E::Call(callee, args) => {
                let callee = self.build_expr_unvoid(callee, span.clone())?;
                self.build_function_call(callee, args, None, span)?
            }
            E::MethodCall(receiver, method_name, args, dot_span) => {
                let receiver_span;
                let receiver = if let Some(receiver) = receiver {
                    receiver_span = receiver.span.clone();
                    self.build_expr_unvoid(receiver, method_name.span.clone())?
                } else {
                    receiver_span = dot_span.clone();
                    let r = self.get_self(receiver_span.clone())?;
                    self.push_store(Sk::Read(r), receiver_span.clone())
                };
                let f = self.get_var(&method_name.kind, method_name.span.clone(), "function")?;
                let f = self.maybe_var_to_value(f, method_name.span.clone());
                self.build_function_call(f, args, Some((receiver, receiver_span)), span)?
            }
        };
        // eprintln!("unvoid {unvoid}\nexpr {expr:?}\nreg {reg:?}\n");
        Ok(reg)
    }
    // This function returns a MaybeVar because not all syntactic place expressions are semantic place expressions. For example, we can't assign a value to a function. Different code paths we expect a place expression will have to properly handle these cases.
    fn build_place(&mut self, kind: &ast::PlaceKind, span: Span) -> Result<MaybeVar> {
        use ast::PlaceKind as Pk;
        match kind {
            Pk::Var(name) => self.get_var(name, span, "variable"),
            Pk::Self_ => self.get_self(span).map(MaybeVar::Variable),
            Pk::Deref(e, deref_span) => self
                .build_expr_unvoid(e, deref_span.clone())
                .map(MaybeVar::Variable),
            Pk::Index(indexee, indices, index_span) => {
                let indexee_reg = self.build_expr_unvoid(indexee, index_span.clone())?;
                let index_regs = indices
                    .iter()
                    .map(|index| self.build_expr_unvoid(index, index_span.clone()))
                    .collect::<Result<Vec<_>>>()?;
                if index_regs.len() != 1 {
                    return Err(todo("multidimensional indexing", index_span.clone()));
                }
                let index_reg = index_regs[0];
                let access = vec![PtrOffset::Index(RegisterOrConstant::Register(index_reg))];
                let span = indexee.span.start..index_span.end;
                let indexed_reg = self.push_store(Sk::PtrOffset(indexee_reg, access), span);
                Ok(MaybeVar::Variable(indexed_reg))
            }
            Pk::Field(struct_value, field, dot_span) => {
                let span;
                let struct_reg = if let Some(struct_value) = struct_value {
                    span = struct_value.span.clone();
                    self.build_expr_ref(struct_value, span.clone())?
                } else {
                    span = dot_span.clone();
                    self.get_self(span.clone())?
                };
                let access = vec![PtrOffset::Field(field.kind.clone())];
                let span = span.start..field.span.end;
                let field_ptr_reg = self.push_store(Sk::PtrOffset(struct_reg, access), span);
                Ok(MaybeVar::Variable(field_ptr_reg))
            }
        }
    }

    /// Build an expression and return a pointer to its value. If it's a place expression, this will be a pointer to its memory region. Otherwise, this will create a new stack allocation and return a pointer to that.
    fn build_expr_ref(&mut self, expr: &ast::Expr, span: Span) -> Result<Register> {
        let maybe_var = match &expr.kind {
            ast::ExprKind::Place(kind) => self.build_place(kind, span.clone())?,
            _ => MaybeVar::Constant(self.build_expr_unvoid(expr, span)?),
        };
        let r = match maybe_var {
            MaybeVar::Variable(r) => r,
            MaybeVar::Constant(c) => {
                let r = self.push_store(Sk::StackAlloc(self.tys[&c]), expr.span.clone());
                self.push_write(r, c);
                r
            }
        };
        Ok(r)
    }

    fn maybe_var_to_value(&mut self, maybe_var: MaybeVar, span: Span) -> Register {
        match maybe_var {
            MaybeVar::Variable(place_reg) => self.push_store(Sk::Read(place_reg), span),
            MaybeVar::Constant(value_reg) => value_reg,
        }
    }

    fn build_constant(&mut self, value: &Value, span: Span) -> Register {
        let mut int =
            |v: i128, int_kind: IntKind| self.push_store(Sk::Int(v, int_kind), span.clone());
        match value.kind {
            ValueKind::Bool(b) => self.push_store(Sk::Bool(b), span),
            ValueKind::U8(v) => int(v.into(), IntKind::U8),
            ValueKind::U16(v) => int(v.into(), IntKind::U16),
            ValueKind::U32(v) => int(v.into(), IntKind::U32),
            ValueKind::Usize(v) => int(v.into(), IntKind::Usize),
            ValueKind::Array(_) => todo!("array const eval"),
        }
    }

    fn build_function_call(
        &mut self,
        callee: Register,
        args: &[ast::FunctionArg],
        mut receiver: Option<(Register, Span)>,
        span: Span,
    ) -> Result<Option<Register>> {
        let TyKind::Function {
            params,
            returns,
            has_self,
        } = self.program_tys[self.tys[&callee]].clone()
        else {
            // if we need to do anything important after this big `match`, perhaps we should replace this with a named break
            // add a dummy instruction to defer the error to typechecking
            self.push_inst(Inst::Call {
                callee,
                args: vec![],
                returns: vec![],
            });
            return Ok(Some(callee));
        };
        let (mut evaled_args, evaled_anon) = self.build_function_arguments(args, span.clone())?;
        let mut evaled_anon = evaled_anon.into_iter();
        if receiver.is_some() && (!has_self || params.is_empty()) {
            return Err(Error {
                kind: ErrorKind::NotMethod,
                span,
            });
        }
        let mut missing_args = vec![];
        let args = params
            .iter()
            .map(|(name, (is_anon, _))| {
                // if we have a receiver, use it as the first argument
                if let Some((r, _)) = receiver.take() {
                    return r;
                }
                // if there was an argument with the name of this parameter...
                if let Some((_, r)) = evaled_args.shift_remove(name) {
                    return r;
                }
                let is_anon = bool::from(is_anon);
                // if this function has an anon parameter and the caller provided an anon argument...
                if let Some(Some(r)) = is_anon.then(|| evaled_anon.next()) {
                    return r;
                }
                // otherwise, add this parameter name to the list of missing arguments
                let missing = if is_anon {
                    format!("anon {name}").into()
                } else {
                    name.clone()
                };
                missing_args.push(missing);
                Register(u128::MAX)
            })
            .collect();
        if !missing_args.is_empty() {
            return Err(Error {
                kind: ErrorKind::MissingArgs(missing_args, None),
                span,
            });
        }
        if !evaled_args.is_empty() {
            return Err(Error {
                kind: ErrorKind::InvalidArgs(evaled_args.into_keys().collect()),
                span,
            });
        }
        assert!(returns.len() < 2);
        let return_reg = returns
            .first()
            .map(|&return_ty| self.new_reg(return_ty, span));
        self.push_inst(Inst::Call {
            callee,
            returns: return_reg.into_iter().collect(),
            args,
        });
        Ok(return_reg)
    }

    // use `IndexMap` so that an "invalid args" error is in the same order as the argument list
    fn build_function_arguments(
        &mut self,
        args: &[ast::FunctionArg],
        span: Span,
    ) -> Result<(IndexMap<Str, (Span, Register)>, Vec<Register>)> {
        let mut evaled_args: IndexMap<Str, (Span, Register)> = IndexMap::new();
        let mut evaled_anon: Vec<Register> = vec![];
        for arg in args {
            use ast::FunctionArgKind as Arg;
            use indexmap::map::Entry::{Occupied, Vacant};
            let (name, body) = match &arg.kind {
                Arg::Named(name, body) => (name.clone(), body),
                Arg::Punned(body) => (Self::pun(body)?, body),
                Arg::Anon(expr) => {
                    let reg = self.build_expr_unvoid(expr, span.clone())?;
                    evaled_anon.push(reg);
                    continue;
                }
            };
            let entry = match evaled_args.entry(name.kind.clone()) {
                Occupied(e) => {
                    return Err(Error {
                        kind: ErrorKind::NameConflict(
                            "function argument",
                            e.get().0.clone().some(),
                        ),
                        span: name.span,
                    });
                }
                Vacant(e) => e,
            };
            let r = self.build_block_unvoid(body, name.span.clone())?;
            entry.insert((name.span.clone(), r));
        }
        Ok((evaled_args, evaled_anon))
    }

    fn pun(block: &ast::Block) -> Result<Name> {
        use ast::{ExprKind, PlaceKind};
        let last = block.0.last().unwrap();
        let err = Err(Error {
            kind: ErrorKind::BadPun,
            span: last.span.clone(),
        });
        let ast::StmtKind::Expr(e) = &last.kind else {
            return err;
        };
        let name = match &e.kind {
            ExprKind::Place(PlaceKind::Var(name)) => Name {
                kind: name.clone(),
                span: e.span.clone(),
            },
            ExprKind::Place(PlaceKind::Field(_, name, _)) => name.clone(),
            _ => return err,
        };
        Ok(name)
    }

    fn get_self(&mut self, span: Span) -> Result<Register> {
        let Some(r) = self.self_reg else {
            return Err(Error {
                kind: ErrorKind::NoSelf(self.underscore_self.clone()),
                span: span.clone(),
            });
        };
        Ok(self.push_store(Sk::Copy(r), span))
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
        let reg = self.push_store(Sk::StackAlloc(ty), name.span);
        self.scopes.last_mut().unwrap().insert(name.kind, reg);
        reg
    }

    fn get_var(&mut self, name: &Str, span: Span, kind: &'static str) -> Result<MaybeVar> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name.as_ref()).copied())
            .map(|reg| {
                let r = self.push_store(Sk::Copy(reg), span.clone());
                MaybeVar::Variable(r)
            })
            .or_else(|| {
                self.function_tys
                    .contains_key(name)
                    .then(|| self.push_store(Sk::Function(name.clone()), span.clone()))
                    .map(MaybeVar::Constant)
            })
            .or_else(|| {
                self.constants.get(name).map(|value| {
                    let r = self.build_constant(value, span.clone());
                    MaybeVar::Constant(r)
                })
            })
            .ok_or_else(|| Error {
                kind: ErrorKind::NotFound(kind, name.clone()),
                span,
            })
    }

    fn push_write(&mut self, dst: Register, src: Register) {
        self.push_inst(Inst::Write(dst, src));
    }

    fn push_store(&mut self, sk: Sk, span: Span) -> Register {
        let ty = self.guess_ty(&sk);
        let reg = self.new_reg(ty, span);
        self.push_inst(Inst::Store(reg, sk));
        reg
    }
    pub fn guess_ty(&mut self, sk: &Sk) -> Ty {
        let dummy_ty = self.dummy_ty;
        let t = |r| *self.tys.get(r).unwrap();
        match sk {
            Sk::Bool(_) | Sk::BinOp(BinOp::Cmp(_), ..) => self.program_tys.insert(TyKind::Bool),
            &Sk::Int(_, kind) | &Sk::IntCast(_, kind) => self.program_tys.insert(TyKind::Int(kind)),
            &Sk::PtrCast(_, kind) => self.program_tys.insert(TyKind::Pointer(kind)),
            Sk::Phi(regs) => t(regs.first_key_value().expect("empty phi").1),
            Sk::BinOp(BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div, lhs, _rhs) => t(lhs),
            Sk::PtrOffset(ptr, accesses) => {
                assert_eq!(accesses.len(), 1);
                let access = &accesses[0];
                let TyKind::Pointer(mut pointee_ty) = self.program_tys[t(ptr)] else {
                    return dummy_ty;
                };
                match access {
                    PtrOffset::Index(_) => {
                        if let TyKind::Array(item, _count) = self.program_tys[pointee_ty] {
                            pointee_ty = item;
                        }
                    }
                    PtrOffset::Field(field) => {
                        let TyKind::Struct { fields, .. } = &self.program_tys[pointee_ty] else {
                            return dummy_ty;
                        };
                        let Some(item) = fields
                            .iter()
                            .find_map(|(name, &ty)| (name == field).then_some(ty))
                        else {
                            return dummy_ty;
                        };
                        pointee_ty = item;
                    }
                }
                self.program_tys.insert(TyKind::Pointer(pointee_ty))
            }
            &Sk::StackAlloc(ty) => self.program_tys.insert(TyKind::Pointer(ty)),
            Sk::Copy(r) | Sk::UnaryOp(UnaryOp::Neg, r) => t(r),
            Sk::Read(r) => match self.program_tys[self.tys[r]] {
                TyKind::Pointer(inner) => inner,
                _ => dummy_ty,
            },
            Sk::Function(name) => self.function_tys[name],
            Sk::Static(name) => {
                let inner = self.static_values[name].ty;
                self.program_tys.insert(TyKind::Pointer(inner))
            }
            &Sk::Struct { ty, .. } => ty,
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

#[allow(
    dead_code,
    reason = "This diagnostic is often used sporadically and temporarily, and only serves to give better diagnostics in the presence of future language direction or in-development features. It may come in and out of use over the lifetime of the compiler."
)]
const fn todo(message: &'static str, span: Span) -> Error {
    Error {
        kind: ErrorKind::Todo(message),
        span,
    }
}

pub fn build(program: &ast::Program) -> Result<Program> {
    use ast::DeclKind as D;
    let mut program_tys = TyMap::new();
    // Global type construction first pass: register all type names in `defined_tys`. Type declarations can reference structs declared after themselves, even cyclically.
    let mut defined_tys = DefinedTys {
        tys: {
            let int_tys = INT_TYS
                .iter()
                .map(|&(name, int_kind)| (name, TyKind::Int(int_kind)));
            let other_tys = OTHER_TYS.iter().cloned();
            int_tys
                .chain(other_tys)
                .map(|(name, ty_kind)| (name.into(), (program_tys.insert(ty_kind), None)))
                .collect()
        },
    };
    let bool_ty = program_tys.insert(TyKind::Bool);
    let mut constants: Map<Str, Value> = [
        ("true", Value {
            kind: ValueKind::Bool(true),
            ty: bool_ty,
        }),
        ("false", Value {
            kind: ValueKind::Bool(true),
            ty: bool_ty,
        }),
    ]
    .into_iter()
    .map(|(name, value)| (name.into(), value))
    .collect();
    for ast::Decl { kind, span: _ } in &program.decls {
        match kind {
            D::Function(_) | D::ExternFunction(_) | D::Const(..) => {}
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
    let mut value_cycles: IndexMap<Str, (Span, Vec<Str>)> = IndexMap::new();
    for ast::Decl { kind, span: _ } in &program.decls {
        match kind {
            D::Function(_) | D::ExternFunction(_) => {}
            D::Struct(ast::Struct { name, fields }) => {
                use ast::TyKind as Tk;
                let mut ir_fields: IndexMap<Str, Ty> = IndexMap::with_capacity(fields.len());
                let mut names = Map::new();
                let mut fields_stored_by_value = vec![];
                for (_is_anon, field_name, field_ty) in fields {
                    fn recursively_stores(field_kind: &ast::TyKind) -> Option<Str> {
                        // does this field store a possibly recursive type by value?
                        match &field_kind {
                            Tk::Pointer(_) | Tk::Function { .. } => None,
                            Tk::Name(name) => Some(name.kind.clone()),
                            Tk::Array(item_ty, _count) => {
                                // Open question: Do we consider arrays of length 0? Rust has an open issue for it: https://github.com/rust-lang/rust/issues/11924
                                recursively_stores(&item_ty.kind)
                            }
                        }
                    }
                    let ty = defined_tys.build_ty(field_ty, &mut program_tys)?;
                    ir_fields.insert(field_name.kind.clone(), ty);
                    if let Some(previous_span) =
                        names.insert(field_name.kind.clone(), field_name.span.clone())
                    {
                        return Err(Error {
                            kind: ErrorKind::NameConflict("field", Some(previous_span)),
                            span: field_name.span.clone(),
                        });
                    }
                    fields_stored_by_value.extend(recursively_stores(&field_ty.kind));
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
            D::Const(name, ty_annotation, body) => {
                let value_kind = eval_const(body)?;
                let ty_kind = match value_kind {
                    ValueKind::Bool(_) => TyKind::Bool,
                    ValueKind::U8(_) => TyKind::Int(IntKind::U8),
                    ValueKind::U16(_) => TyKind::Int(IntKind::U16),
                    ValueKind::U32(_) => TyKind::Int(IntKind::U32),
                    ValueKind::Usize(_) => TyKind::Int(IntKind::Usize),
                    ValueKind::Array(_) => todo!("array const eval"),
                };
                let ty = program_tys.insert(ty_kind);
                let value = Value {
                    kind: value_kind,
                    ty,
                };
                if let Some(ty_annotation) = ty_annotation {
                    let declared_ty = defined_tys.build_ty(ty_annotation, &mut program_tys)?;
                    if !program_tys.equals(ty, declared_ty) {
                        return Err(todo("const eval type error", ty_annotation.span.clone()));
                    }
                }
                constants.insert(name.kind.clone(), value);
            }
        }
    }
    // detect infinite size types
    {
        // each item on the stack is a visited type and all the types it is going to visit
        let mut stack: IndexMap<&Str, &[Str]> = IndexMap::new();
        // all the types we know don't form infinite size loops
        let mut closed: Set<&Str> = Set::new();
        for (name, (_, fields)) in &value_cycles {
            stack.insert(name, fields);
            while let Some((_, fields)) = stack.last_mut() {
                let Some(field) = fields.first() else {
                    let (old_field, _) = stack.pop().unwrap();
                    closed.insert(old_field);
                    continue;
                };
                *fields = &fields[1..];
                if closed.contains(field) {
                    continue;
                }
                if let Some((i, prior, _)) = stack.get_full(field) {
                    let cycle = stack.as_slice()[i..].keys().copied().cloned().collect();
                    return Err(Error {
                        kind: ErrorKind::InfiniteType(cycle),
                        span: value_cycles[*prior].0.clone(),
                    });
                }
                if let Some((_, recursive_fields)) = value_cycles.get(field) {
                    stack.insert(field, recursive_fields);
                } else {
                    closed.insert(field);
                }
            }
        }
        drop(value_cycles);
    }
    let mut function_tys: Map<Str, Ty> = Map::new();
    for ast::Decl { kind, .. } in &program.decls {
        let (name, ty) = match kind {
            D::Const(..) => continue,
            D::Function(ast::Function { signature, .. }) | D::ExternFunction(signature) => {
                let ast::FunctionSignature {
                    name,
                    underscore_self, // TODO
                    parameters,
                    returns,
                } = signature;
                let ty = defined_tys.build_function_ty(
                    underscore_self.is_none(),
                    parameters,
                    returns.as_ref(),
                    &mut program_tys,
                )?;
                (name, ty)
            }
            D::Struct(ast::Struct {
                name,
                fields: ast_fields,
            }) => {
                let struct_ty = defined_tys.tys[&name.kind].0;
                let TyKind::Struct { fields, .. } = &program_tys[struct_ty] else {
                    unreachable!(
                        "struct has non-struct type: {struct_ty} {}",
                        program_tys.format(struct_ty)
                    );
                };
                let params = zip(ast_fields, fields)
                    .map(|(&(is_anon, _, _), (name, &ty))| (name.clone(), (is_anon, ty)))
                    .collect();
                // We arbitrarily decide that constructor functions can be called as methods. This seems fine enough, and is especially nice for wrapper types.
                let constructor_ty = TyKind::Function {
                    has_self: true,
                    params,
                    returns: vec![struct_ty],
                };
                let ty = program_tys.insert(constructor_ty);
                (name, ty)
            }
        };
        if function_tys.contains_key(&name.kind) {
            let prev_span = program
                .decls
                .iter()
                .find_map(|ast::Decl { kind, .. }| {
                    let prev_name = match kind {
                        D::Const(..) => return None,
                        D::Function(ast::Function { signature, .. })
                        | D::ExternFunction(signature) => &signature.name,
                        D::Struct(ast::Struct { name, .. }) => name,
                    };
                    (name.kind == prev_name.kind).then(|| prev_name.span.clone())
                })
                .unwrap();
            return Err(Error {
                kind: ErrorKind::NameConflict("top level declaration", Some(prev_span)),
                span: name.span.clone(),
            });
        }
        function_tys.insert(name.kind.clone(), ty);
    }
    let function_tys = function_tys;
    let mut functions = Map::new();
    let mut static_values = Map::new();
    for decl in &program.decls {
        match &decl.kind {
            D::ExternFunction(_) | D::Const(..) => {}
            D::Function(fn_decl) => {
                let builder = IrBuilder::new(
                    &function_tys,
                    &constants,
                    &defined_tys,
                    &mut static_values,
                    &mut program_tys,
                );
                let function = builder.build_function(fn_decl)?;
                functions.insert(fn_decl.signature.name.kind.clone(), function);
            }
            D::Struct(s) => {
                let builder = IrBuilder::new(
                    &function_tys,
                    &constants,
                    &defined_tys,
                    &mut static_values,
                    &mut program_tys,
                );
                let function = builder.build_struct_constructor(s);
                functions.insert(s.name.kind.clone(), function);
            }
        }
    }
    Ok(Program {
        functions,
        function_tys,
        static_values,
        tys: program_tys,
    })
}
