use crate::compiler_types::{Map, Str};
use crate::ir::*;

#[derive(Clone, Debug)]
pub enum ErrorKind {
    // We dereferenced a register of a non-pointer type.
    NotPointer(Register),
    // The register has one type but we expected another.
    Expected(Register, Ty),
}

type Error = (Str, ErrorKind);
type Result<T = ()> = std::result::Result<T, Error>;

type Tys = Map<Register, Ty>;
type Blocks = Map<BlockId, Block>;

#[derive(Debug)]
struct TypeChecker<'a> {
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
    fn t(&self, r: Register) -> &'a Ty {
        self.tys.get(&r).expect("register with no type")
    }
    fn err(&self, r: Register, ty: Ty) -> Result {
        Err((self.name.into(), ErrorKind::Expected(r, ty)))
    }
    fn expect(&self, r: Register, ty: &'a Ty) -> Result {
        if self.t(r) == ty {
            Ok(())
        } else {
            self.err(r, ty.clone())
        }
    }
    fn pointer(&self, r: Register) -> Result<&'a Ty> {
        match self.t(r) {
            Ty::Pointer(inner) => Ok(inner.as_ref()),
            Ty::Int | Ty::Function(..) => Err((self.name.into(), ErrorKind::NotPointer(r))),
        }
    }
    fn infer_storekind(&self, sk: &StoreKind) -> Result<Ty> {
        use StoreKind as Sk;
        let ty = match sk {
            Sk::Int(_) => Ty::Int,
            &Sk::Copy(r) => self.t(r).clone(),
            &Sk::BinOp(op, lhs, rhs) => {
                match op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul => (),
                }
                self.expect(lhs, &Ty::Int)?;
                self.expect(rhs, &Ty::Int)?;
                Ty::Int
            }
            &Sk::UnaryOp(UnaryOp::Neg, rhs) => {
                self.expect(rhs, &Ty::Int)?;
                Ty::Int
            }
            Sk::StackAlloc(inner) => Ty::Pointer(Box::new(inner.clone())),
            &Sk::Read(src) => self.pointer(src)?.clone(),
            Sk::Phi(rs) => {
                let mut rs = rs.values().copied();
                let ty = self.t(rs.next().expect("empty phi"));
                for r in rs {
                    self.expect(r, ty)?;
                }
                ty.clone()
            }
        };
        Ok(ty)
    }
    fn visit_inst(&self, inst: &Inst) -> Result {
        match inst {
            Inst::Store(r, sk) => {
                let expected = self.t(*r);
                let got = self.infer_storekind(sk)?;
                if *expected == got {
                    Ok(())
                } else {
                    Err((self.name.into(), ErrorKind::Expected(*r, got)))
                }
            }
            &Inst::Write(dst, src) => {
                let inner = self.pointer(dst)?;
                self.expect(src, inner)
            }
            Inst::Nop => Ok(()),
            e @ Inst::Call{..} => todo!("{e:?}"),
        }
    }
    fn visit_block(&self, block: &Block) -> Result {
        for inst in &block.insts {
            self.visit_inst(inst)?;
        }
        Ok(())
    }
    fn visit_function(f: &'a Function, name: &'a str) -> Result {
        let this = Self { tys: &f.tys, name };
        for i in f.dominator_tree.iter() {
            let block = f.blocks.get(&i).unwrap();
            this.visit_block(block)?;
        }
        Ok(())
    }
}

pub fn typecheck(program: &mut Program) -> Result {
    for (fn_name, f) in &mut program.functions {
        // println!("typechecking {fn_name}");
        TypeChecker::visit_function(f, fn_name)?;
    }
    Ok(())
}
