use crate::compiler_types::{Map, Str};
use crate::ir::*;

#[derive(Clone, Debug)]
pub enum ErrorKind {
    // We dereferenced a register of a non-pointer type.
    NotPointer(Register),
    // We called a register of a non-function type.
    NotFunction(Register),
    // The register has one type but we expected another.
    Expected(Register, Ty),
}

type Error = (Str, ErrorKind);
type Result<T = ()> = std::result::Result<T, Error>;

type Tys = Map<Register, Ty>;
type Blocks = Map<BlockId, Block>;
// NOTE: This can be changed to take 2 lifetime parameters. Also, we can AsRef the value type into something like `(&'a [Ty], &'a [Ty])` if need be.
type FunctionTys<'a> = &'a Map<&'a str, &'a (Vec<Ty>, Vec<Ty>)>;

#[derive(Debug)]
struct TypeChecker<'a> {
    function_tys: FunctionTys<'a>,
    returns: &'a [Ty],
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
            Sk::Function(name) => {
                let (params, returns) = self.function_tys.get(name.as_ref()).expect("function get");
                Ty::Function(params.clone(), returns.clone())
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
            Inst::Call {
                callee,
                args,
                returns,
            } => {
                match self.t(*callee) {
                    Ty::Function(..) => {}
                    Ty::Int | Ty::Pointer(_) => {
                        return Err((self.name.into(), ErrorKind::NotFunction(*callee)))
                    }
                }
                let arg_tys = args.iter().map(|&r| self.t(r).clone()).collect();
                let return_tys = returns.iter().map(|&r| self.t(r).clone()).collect();
                let fn_ty = Ty::Function(arg_tys, return_tys);
                self.expect(*callee, &fn_ty)
            }
        }
    }
    fn visit_jump_loc(&self, loc: &JumpLocation) -> Result {
        match loc {
            JumpLocation::Block(_) => Ok(()),
            JumpLocation::Return(regs) => {
                if regs.len() != self.returns.len() {
                    // The IR lowering phase will always produce functions with 0 or 1 returns, and it checks that all paths return the appropriate number of values. This code path will only run when typechecking transformed IR, namely after lowering IR types to machine-friendly types.
                    todo!("proper error diagnostic for wrong number of returns");
                }
                regs.iter()
                    .zip(self.returns)
                    .map(|(&r, ty)| self.expect(r, ty))
                    .collect()
            }
        }
    }
    fn visit_block(&self, block: &Block) -> Result {
        for inst in &block.insts {
            self.visit_inst(inst)?;
        }
        match &block.exit {
            Exit::Jump(loc) => self.visit_jump_loc(loc),
            Exit::CondJump(cond, loc1, loc2) => {
                match cond {
                    Condition::NonZero(_) => {}
                }
                self.visit_jump_loc(loc1)?;
                self.visit_jump_loc(loc2)
            }
        }
    }
    fn visit_function(f: &'a Function, name: &'a str, function_tys: FunctionTys<'a>) -> Result {
        let returns = &function_tys.get(name).unwrap().1;
        let this = Self {
            function_tys,
            returns,
            tys: &f.tys,
            name,
        };
        for i in f.dominator_tree.iter() {
            let block = f.blocks.get(&i).unwrap();
            this.visit_block(block)?;
        }
        Ok(())
    }
}

pub fn typecheck(program: &mut Program) -> Result {
    let function_tys = program
        .functions
        .iter()
        .map(|(name, f)| (name.as_ref(), &f.function_ty))
        .collect();
    for (fn_name, f) in &program.functions {
        println!("typechecking {fn_name}");
        for (r, ty) in &f.tys {
            println!("  {r} {ty}");
        }
        TypeChecker::visit_function(f, fn_name, &function_tys)?;
    }
    Ok(())
}
