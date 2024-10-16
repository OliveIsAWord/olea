use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct Function {
    pub blocks: HashMap<usize, Block>,
    pub tys: HashMap<Register, Ty>,
}

impl Function {
    pub fn type_check(&self) {
        let tys = &self.tys;
        self.blocks
            .values()
            .flat_map(|b| &b.insts)
            .for_each(|i| i.type_check(tys));
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ty {
    Int(u64),
    Pointer(Box<Self>),
}

#[derive(Clone, Debug)]
pub struct Block {
    pub insts: Vec<Inst>,
}

#[derive(Clone, Debug)]
pub enum Inst {
    Store(Register, StoreKind),
    Write(Register, Register),
    Jump(JumpLocation),
    CondJump(Condition, JumpLocation, JumpLocation),
}

impl Inst {
    fn type_check(&self, tys: &HashMap<Register, Ty>) {
        let ty_of = |r| tys.get(r).unwrap();
        match self {
            Self::Store(r, sk) => assert_eq!(ty_of(r), &sk.ty(tys)),
            Self::Write(dst, src) => match ty_of(dst) {
                Ty::Pointer(inner) => assert_eq!(inner.as_ref(), ty_of(src)),
                e => panic!("typeck error: attempted to Write to {dst:?} of type {e:?}"),
            },
            Self::Jump(location) => match location {
                JumpLocation::Block(_) => (),
            },
            Self::CondJump(condition, _branch1, _branch2) => {
                match condition {
                    Condition::NonZero(r) => match ty_of(r) {
                        Ty::Int(_) | Ty::Pointer(_) => (),
                    },
                }
                // TODO: any sort of JumpLocation checking?
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum StoreKind {
    Int(u128, u64),
    // Copy(Register),
    Phi(Vec<Register>),
    BinOp(BinOp, Register, Register),
    StackAlloc(Ty),
    Read(Register),
}

impl StoreKind {
    pub fn ty(&self, tys: &HashMap<Register, Ty>) -> Ty {
        let all = |regs: &[Register]| {
            let (first, rest) = (regs[0], &regs[1..]);
            let ty = tys.get(&first).unwrap();
            for reg in rest {
                assert_eq!(tys.get(reg).unwrap(), ty);
            }
            ty.clone()
        };
        match self {
            &Self::Int(_, width) => Ty::Int(width),
            Self::Phi(regs) => all(regs),
            &Self::BinOp(_, lhs, rhs) => all(&[lhs, rhs]),
            Self::StackAlloc(ty) => Ty::Pointer(Box::new(ty.clone())),
            Self::Read(r) => match tys.get(r).unwrap() {
                Ty::Pointer(inner) => inner.as_ref().clone(),
                e => panic!("typeck error: attempted to Read from {r:?} of type {e:?}"),
            },
        }
    }
}

#[derive(Clone, Debug)]
pub enum BinOp {
    Add,
    Sub,
}

#[derive(Clone, Debug)]
pub enum Condition {
    // Always,
    NonZero(Register),
}

#[derive(Clone, Debug)]
pub enum JumpLocation {
    Block(usize),
    // Register(Register),
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Register(pub u128);
