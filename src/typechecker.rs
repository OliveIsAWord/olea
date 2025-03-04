use crate::compiler_prelude::*;
use crate::ir::*;

#[derive(Clone, Debug)]
pub enum ErrorKind {
    /// We performed an integer operation on a non-integer.
    NotInt(Register),
    /// We dereferenced a register of a non-pointer type.
    NotPointer(Register),
    /// We wrote a value through a const pointer.
    MutateThroughConstPointer(Register),
    /// We wrote a value to an immutable variable.
    MutateConstVariable(Register),
    /// We cast a const pointer to a mut pointer.
    CantCastPointerToMut(Register),
    /// We tried to mutably reference an immutable variable.
    MutRefToConstVariable(Register),
    /// We tried to use the deref operator on a multi-item pointer.
    CantDerefMultiPointer(Register),
    /// We tried to use the index operator on a single-item pointer to a type that wasn't an array.
    CantIndexSinglePointer(Register),
    /// We called a register of a non-function type.
    NotFunction(Register),
    /// We accessed a field of a non-struct type.
    NotStruct(Ty, Register),
    /// We accessed a non-existent field of a struct.
    NoFieldNamed(Register, Str),
    /// The register has one type but we expected another.
    Expected(Register, String),
}

type Error = (Str, ErrorKind);
type Result<T = ()> = std::result::Result<T, Error>;

type Tys = Map<Register, Ty>;

#[derive(Debug)]
struct TypeChecker<'a> {
    ty_map: &'a TyMap,
    function_tys: &'a Map<Str, Ty>,
    static_values: &'a Map<Str, Value>,
    return_tys: &'a [Ty],
    tys: &'a Tys,
    name: &'a Str,
    variable_set: &'a Set<Register>,
}

impl<'a> TypeChecker<'a> {
    fn t(&self, r: Register) -> &'a TyKind {
        &self.ty_map[self.tys[&r]]
    }
    fn err(&self, r: Register, kind: &TyKind) -> Result {
        Err((
            self.name.clone(),
            ErrorKind::Expected(r, self.ty_map.format_kind(kind)),
        ))
    }
    fn expect(&self, r: Register, kind: &TyKind) -> Result {
        if self.ty_map.equals_kind(self.t(r), kind) {
            Ok(())
        } else {
            self.err(r, kind)
        }
    }
    fn int(&self, r: Register) -> Result<IntKind> {
        match self.t(r) {
            &TyKind::Int(k) => Ok(k),
            _ => Err((self.name.clone(), ErrorKind::NotInt(r))),
        }
    }
    fn pointer(&self, r: Register) -> Result<Pointer> {
        match self.t(r) {
            &TyKind::Pointer(p) => Ok(p),
            _ => Err((self.name.clone(), ErrorKind::NotPointer(r))),
        }
    }
    fn infer_storekind(&self, sk: &StoreKind) -> Result<TyKind> {
        use StoreKind as Sk;
        let ty = match *sk {
            Sk::Bool(_) => TyKind::Bool,
            Sk::Int(_, kind) => TyKind::Int(kind),
            Sk::Struct { ty, ref fields } => {
                let ty_kind = &self.ty_map[ty];
                let TyKind::Struct {
                    fields: real_fields,
                    ..
                } = ty_kind
                else {
                    unreachable!()
                };
                for (&ty, &r) in zip(real_fields.values(), fields) {
                    self.expect(r, &self.ty_map[ty])?;
                }
                ty_kind.clone()
            }
            Sk::IntCast(int, kind) => {
                self.int(int)?;
                TyKind::Int(kind)
            }
            // A pointer cast returns a value of the provided pointer type, but we must assure the operand is itself a pointer and that we're not casting away a const.
            Sk::PtrCast(pointer, cast_to) => {
                let Pointer {
                    inner: _,
                    kind: _,
                    is_mut,
                } = self.pointer(pointer)?;
                if is_mut == IsMut::Const && cast_to.is_mut == IsMut::Mut {
                    let kind = if self.variable_set.contains(&pointer) {
                        ErrorKind::MutRefToConstVariable(pointer)
                    } else {
                        ErrorKind::CantCastPointerToMut(pointer)
                    };
                    return Err((self.name.clone(), kind));
                }
                TyKind::Pointer(cast_to)
            }
            Sk::Copy(r) => self.t(r).clone(),
            Sk::BinOp(op, lhs, rhs) => {
                match op {
                    BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::Div
                    | BinOp::BitAnd
                    | BinOp::BitOr
                    | BinOp::Cmp(_) => (),
                }
                let lhs_int = self.int(lhs)?;
                let rhs_int = self.int(rhs)?;
                if lhs_int != rhs_int {
                    self.err(rhs, &TyKind::Int(lhs_int))?;
                }
                if matches!(op, BinOp::Cmp(_)) {
                    TyKind::Bool
                } else {
                    TyKind::Int(lhs_int)
                }
            }
            Sk::PtrOffset(pointer, ref accesses) => {
                let Pointer {
                    mut inner,
                    mut kind,
                    is_mut,
                } = self.pointer(pointer)?;
                for access in accesses {
                    match *access {
                        PtrOffset::Index(index) => {
                            inner = match kind {
                                PointerKind::Multi => inner,
                                PointerKind::Single => {
                                    if let TyKind::Array(item, _count) = self.ty_map[inner] {
                                        item
                                    } else {
                                        return Err((
                                            self.name.clone(),
                                            ErrorKind::CantIndexSinglePointer(pointer),
                                        ));
                                    }
                                }
                            };
                            kind = PointerKind::Single;
                            if let RegisterOrConstant::Register(index) = index {
                                self.expect(index, &TyKind::Int(IntKind::Usize))?;
                            }
                        }
                        PtrOffset::Field(ref field) => {
                            let TyKind::Struct { fields, .. } = &self.ty_map[inner] else {
                                return Err((
                                    self.name.clone(),
                                    ErrorKind::NotStruct(inner, pointer),
                                ));
                            };
                            inner = *fields.get(field).ok_or_else(|| {
                                (
                                    self.name.clone(),
                                    ErrorKind::NoFieldNamed(pointer, field.clone()),
                                )
                            })?;
                        }
                    }
                }
                TyKind::Pointer(Pointer {
                    inner,
                    kind,
                    is_mut,
                })
            }
            Sk::UnaryOp(UnaryOp::Neg, rhs) => {
                let kind = self.int(rhs)?;
                TyKind::Int(kind)
            }
            Sk::StackAlloc(inner) => TyKind::Pointer(Pointer {
                inner,
                kind: PointerKind::Single,
                is_mut: IsMut::Mut,
            }),
            Sk::Read(src) => {
                let Pointer {
                    inner,
                    kind,
                    is_mut: _,
                } = self.pointer(src)?;
                match kind {
                    PointerKind::Single => {}
                    PointerKind::Multi => {
                        return Err((self.name.clone(), ErrorKind::CantDerefMultiPointer(src)));
                    }
                }
                self.ty_map[inner].clone()
            }
            Sk::Phi(ref rs) => {
                let mut rs = rs.values().copied();
                let ty = self.t(rs.next().expect("empty phi"));
                for r in rs {
                    self.expect(r, ty)?;
                }
                ty.clone()
            }
            Sk::Function(ref name) => self.ty_map[self.function_tys[name.as_ref()]].clone(),
            Sk::Static(ref name) => {
                let inner = self.static_values[name.as_ref()].ty;
                let is_mut = IsMut::Const; // TODO: mutable statics
                TyKind::Pointer(Pointer {
                    inner,
                    kind: PointerKind::Single,
                    is_mut,
                })
            }
        };
        Ok(ty)
    }
    fn visit_inst(&self, inst: &Inst) -> Result {
        // eprintln!("visit {inst:?}");
        match inst {
            &Inst::Store(r, ref sk) => {
                let got = self.infer_storekind(sk)?;
                self.expect(r, &got)
            }
            &Inst::Write(dst, src) => {
                let Pointer {
                    inner,
                    kind,
                    is_mut,
                } = self.pointer(dst)?;
                // it's times like these i wish we reported multiple errors
                match kind {
                    PointerKind::Single => {}
                    PointerKind::Multi => {
                        return Err((self.name.clone(), ErrorKind::CantDerefMultiPointer(dst)));
                    }
                }
                if is_mut == IsMut::Const {
                    let kind = if self.variable_set.contains(&dst) {
                        ErrorKind::MutateConstVariable(dst)
                    } else {
                        ErrorKind::MutateThroughConstPointer(dst)
                    };
                    return Err((self.name.clone(), kind));
                }
                self.expect(src, &self.ty_map[inner])
            }
            Inst::Nop => Ok(()),
            Inst::Call {
                callee,
                args,
                returns,
            } => {
                let callee = *callee;
                let TyKind::Function {
                    has_self: _,
                    params: fn_params,
                    returns: fn_returns,
                } = self.t(callee)
                else {
                    return Err((self.name.clone(), ErrorKind::NotFunction(callee)));
                };
                for (&(_, expected), &r) in zip(fn_params.values(), args) {
                    self.expect(r, &self.ty_map[expected])?;
                }
                for (&expected, &r) in zip(fn_returns, returns) {
                    self.expect(r, &self.ty_map[expected])?;
                }
                Ok(())
            }
        }
    }

    fn visit_block(&self, block: &Block) -> Result {
        for inst in &block.insts {
            self.visit_inst(inst)?;
        }
        match &block.exit {
            Exit::Jump(_) => Ok(()),
            &Exit::CondJump(r, _, _) => self.expect(r, &TyKind::Bool),
            Exit::Return(regs) => {
                if regs.len() != self.return_tys.len() {
                    // The IR lowering phase will always produce functions with 0 or 1 returns, and it checks that all paths return the appropriate number of values. This code path will only run when typechecking transformed IR, namely after lowering IR types to machine-friendly types.
                    todo!("proper error diagnostic for wrong number of returns");
                }
                for (&r, &ty) in zip(regs, self.return_tys) {
                    self.expect(r, &self.ty_map[ty])?;
                }
                Ok(())
            }
        }
    }
    fn visit_function(
        f: &'a Function,
        name: &'a Str,
        function_tys: &'a Map<Str, Ty>,
        static_values: &'a Map<Str, Value>,
        ty_map: &'a TyMap,
        variable_set: &'a Set<Register>,
    ) -> Result {
        let TyKind::Function {
            has_self: _,
            params: param_tys,
            returns: return_tys,
        } = &ty_map[function_tys[name]]
        else {
            unreachable!();
        };
        let this = Self {
            ty_map,
            function_tys,
            static_values,
            return_tys,
            tys: &f.tys,
            name,
            variable_set,
        };
        for (&r, &(_, ty)) in zip(&f.parameters, param_tys.values()) {
            this.expect(r, &ty_map[ty])?;
        }
        for block in f.blocks.values() {
            this.visit_block(block)?;
        }
        Ok(())
    }
}

pub fn typecheck(program: &Program) -> Result {
    // eprintln!("{:?}", program.tys);
    for (fn_name, f) in &program.functions {
        /*
        eprintln!("typechecking {fn_name}");
        for (r, ty) in &f.tys {
            eprintln!("  {r} {ty}");
        }
        */
        TypeChecker::visit_function(
            f,
            fn_name,
            &program.function_tys,
            &program.static_values,
            &program.tys,
            &f.variables,
        )?;
    }
    Ok(())
}
