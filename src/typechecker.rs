use crate::compiler_types::{IndexMap, Map, Str};
use crate::ir::*;

#[derive(Clone, Debug)]
pub enum ErrorKind {
    /// We performed an integer operation on a non-integer.
    NotInt(Register),
    /// We dereferenced a register of a non-pointer type.
    NotPointer(Register),
    /// We called a register of a non-function type.
    NotFunction(Register),
    /// We accessed a field of a non-struct type.
    NotStruct(Register),
    /// We accessed a non-existent field of a struct.
    NoFieldNamed(Register, Str),
    /// The register has one type but we expected another.
    Expected(Register, String),
}

type Error = (Str, ErrorKind);
type Result<T = ()> = std::result::Result<T, Error>;

type Tys = Map<Register, Ty>;
type FunctionTys<'a> = &'a Map<Str, (IndexMap<Str, (IsAnon, Ty)>, Vec<Ty>)>;

#[derive(Debug)]
struct TypeChecker<'a> {
    ty_map: &'a TyMap,
    function_tys: FunctionTys<'a>,
    return_tys: &'a [Ty],
    tys: &'a Tys,
    name: &'a str,
}

impl<'a> TypeChecker<'a> {
    fn t(&self, r: Register) -> &'a TyKind {
        &self.ty_map[self.tys[&r]]
    }
    fn err(&self, r: Register, kind: &TyKind) -> Result {
        Err((
            self.name.into(),
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
            _ => Err((self.name.into(), ErrorKind::NotInt(r))),
        }
    }
    fn pointer(&self, r: Register) -> Result<&'a TyKind> {
        match self.t(r) {
            &TyKind::Pointer(inner) => Ok(&self.ty_map[inner]),
            _ => Err((self.name.into(), ErrorKind::NotPointer(r))),
        }
    }
    fn infer_storekind(&self, sk: &StoreKind) -> Result<TyKind> {
        use StoreKind as Sk;
        let ty = match *sk {
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
                assert_eq!(fields.len(), real_fields.len());
                real_fields
                    .values()
                    .zip(fields)
                    .try_for_each(|(&ty, &r)| self.expect(r, &self.ty_map[ty]))?;
                ty_kind.clone()
            }
            Sk::IntCast(int, kind) => {
                self.int(int)?;
                TyKind::Int(kind)
            }
            Sk::PtrCast(pointer, kind) => {
                self.pointer(pointer)?;
                TyKind::Pointer(kind)
            }
            Sk::Copy(r) => self.t(r).clone(),
            Sk::BinOp(op, lhs, rhs) => {
                match op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::CmpLe => (),
                }
                let lhs_int = self.int(lhs)?;
                let rhs_int = self.int(rhs)?;
                if lhs_int != rhs_int {
                    self.err(rhs, &TyKind::Int(lhs_int))?;
                }
                TyKind::Int(lhs_int)
            }
            Sk::PtrOffset(pointer, ref accesses) => {
                let &TyKind::Pointer(mut pointee) = self.t(pointer) else {
                    return Err((self.name.into(), ErrorKind::NotPointer(pointer)));
                };
                for access in accesses {
                    match *access {
                        PtrOffset::Index(index) => {
                            self.expect(index, &TyKind::Int(IntKind::Usize))?;
                            if let TyKind::Array(item, _count) = self.ty_map[pointee] {
                                pointee = item;
                            }
                        }
                        PtrOffset::Field(ref field) => {
                            let TyKind::Struct { fields, .. } = &self.ty_map[pointee] else {
                                return Err((self.name.into(), ErrorKind::NotStruct(pointer)));
                            };
                            pointee = fields
                                .iter()
                                .find_map(|(name, &ty)| (name == field).then_some(ty))
                                .ok_or_else(|| {
                                    (
                                        self.name.into(),
                                        ErrorKind::NoFieldNamed(pointer, field.clone()),
                                    )
                                })?;
                        }
                    }
                }
                TyKind::Pointer(pointee)
            }
            /*
            Sk::FieldOffset(r, ref field) => {
            }
            */
            Sk::UnaryOp(UnaryOp::Neg, rhs) => {
                let kind = self.int(rhs)?;
                TyKind::Int(kind)
            }
            Sk::StackAlloc(inner) => TyKind::Pointer(inner),
            Sk::Read(src) => self.pointer(src)?.clone(),
            Sk::Phi(ref rs) => {
                let mut rs = rs.values().copied();
                let ty = self.t(rs.next().expect("empty phi"));
                for r in rs {
                    self.expect(r, ty)?;
                }
                ty.clone()
            }
            Sk::Function(ref name) => {
                let (params, returns) = self.function_tys.get(name.as_ref()).expect("function get");
                TyKind::Function(params.clone(), returns.clone())
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
                let inner = self.pointer(dst)?;
                self.expect(src, inner)
            }
            Inst::Nop => Ok(()),
            Inst::Call {
                callee,
                args,
                returns,
            } => {
                let callee = *callee;
                let TyKind::Function(fn_params, fn_returns) = self.t(callee) else {
                    return Err((self.name.into(), ErrorKind::NotFunction(callee)));
                };
                assert_eq!(fn_params.len(), args.len());
                for (&(_, expected), &r) in fn_params.values().zip(args) {
                    self.expect(r, &self.ty_map[expected])?;
                }
                for (&expected, &r) in fn_returns.iter().zip(returns) {
                    self.expect(r, &self.ty_map[expected])?;
                }
                Ok(())
            }
        }
    }
    // fn visit_jump_loc(&self, loc: &JumpLocation) -> Result {
    //     match loc {
    //         JumpLocation::Block(_) => Ok(()),
    //         JumpLocation::Return(regs) => {
    //             if regs.len() != self.return_tys.len() {
    //                 // The IR lowering phase will always produce functions with 0 or 1 returns, and it checks that all paths return the appropriate number of values. This code path will only run when typechecking transformed IR, namely after lowering IR types to machine-friendly types.
    //                 todo!("proper error diagnostic for wrong number of returns");
    //             }
    //             regs.iter()
    //                 .zip(self.return_tys)
    //                 .try_for_each(|(&r, ty)| self.expect(r, ty))
    //         }
    //     }
    // }
    fn visit_block(&self, block: &Block) -> Result {
        for inst in &block.insts {
            self.visit_inst(inst)?;
        }
        match &block.exit {
            Exit::Jump(_) => Ok(()),
            Exit::CondJump(cond, _, _) => match cond {
                &Condition::NonZero(r) => self.int(r).map(|_| ()),
            },
            Exit::Return(regs) => {
                if regs.len() != self.return_tys.len() {
                    // The IR lowering phase will always produce functions with 0 or 1 returns, and it checks that all paths return the appropriate number of values. This code path will only run when typechecking transformed IR, namely after lowering IR types to machine-friendly types.
                    todo!("proper error diagnostic for wrong number of returns");
                }
                regs.iter()
                    .zip(self.return_tys)
                    .try_for_each(|(&r, &ty)| self.expect(r, &self.ty_map[ty]))
            }
        }
    }
    fn visit_function(
        f: &'a Function,
        name: &'a str,
        function_tys: FunctionTys<'a>,
        ty_map: &'a TyMap,
    ) -> Result {
        let return_tys = &function_tys.get(name).unwrap().1;
        let this = Self {
            ty_map,
            function_tys,
            return_tys,
            tys: &f.tys,
            name,
        };
        assert_eq!(
            f.parameters.len(),
            function_tys[name].0.len(),
            "mismatch in parameter count"
        );
        f.parameters
            .iter()
            .zip(function_tys[name].0.values())
            .try_for_each(|(&r, &(_, ty))| this.expect(r, &ty_map[ty]))?;
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
        TypeChecker::visit_function(f, fn_name, &program.function_tys, &program.tys)?;
    }
    Ok(())
}
