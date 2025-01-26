use crate::compiler_types::{Map, Str};
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
type FunctionTys<'a> = &'a Map<Str, (Vec<Ty>, Vec<Ty>)>;

#[derive(Debug)]
struct TypeChecker<'a> {
    ty_map: &'a TyMap,
    function_tys: FunctionTys<'a>,
    return_tys: &'a [Ty],
    tys: &'a Tys,
    name: &'a str,
}

impl<'a> TypeChecker<'a> {
    /*
    fn expect(&self, r: Register, ty: &'a Ty) -> Result {
        Self::expect_ty(self.tys.get_mut(&r).unwrap(), ty)
            .ok_or_else(|| self.err(ErrorKind::Expected(r, ty.clone())))
    }
    fn expect_ty(dst: &mut Ty, ty: &Ty) -> Option<()> {
        if dst == ty {
            Some(())
        } else {
            None
        }
    }
    */
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
        if self.t(r) == kind {
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
            Sk::IntCast(int, kind) => {
                self.int(int)?;
                TyKind::Int(kind)
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
            Sk::PtrOffset(lhs, rhs) => {
                self.pointer(lhs)?;
                self.expect(rhs, &TyKind::Int(IntKind::Usize))?;
                self.t(lhs).clone()
            }
            Sk::FieldOffset(r, ref field) => {
                let TyKind::Struct { fields, .. } = self.pointer(r)? else {
                    return Err((self.name.into(), ErrorKind::NotStruct(r)));
                };
                fields
                    .iter()
                    .find_map(|(name, ty)| (name == field).then_some(TyKind::Pointer(*ty)))
                    .ok_or_else(|| (self.name.into(), ErrorKind::NoFieldNamed(r, field.clone())))?
            }
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
        match inst {
            &Inst::Store(r, ref sk) => {
                let expected = self.t(r);
                let got = self.infer_storekind(sk)?;
                if *expected == got {
                    Ok(())
                } else {
                    self.err(r, &got)
                }
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
                match self.t(*callee) {
                    TyKind::Function(..) => {}
                    _ => return Err((self.name.into(), ErrorKind::NotFunction(*callee))),
                }
                let arg_tys = args.iter().map(|r| self.tys[r]).collect();
                let return_tys = returns.iter().map(|r| self.tys[r]).collect();
                let fn_ty = TyKind::Function(arg_tys, return_tys);
                self.expect(*callee, &fn_ty)
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
        for i in f.cfg.dom_iter() {
            let block = f.blocks.get(&i).unwrap();
            this.visit_block(block)?;
        }
        Ok(())
    }
}

pub fn typecheck(program: &Program) -> Result {
    eprintln!("{:?}", program.tys);
    for (fn_name, f) in &program.functions {
        /*
        println!("typechecking {fn_name}");
        for (r, ty) in &f.tys {
            println!("  {r} {ty}");
        }
        */
        TypeChecker::visit_function(f, fn_name, &program.function_tys, &program.tys)?;
    }
    Ok(())
}
