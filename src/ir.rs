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
    pub fn iter(&self) -> impl Iterator<Item = (usize, &Block)> {
        let blocks = self
            .blocks
            .iter()
            .filter_map(|(&i, block)| if i == 0 { None } else { Some((i, block)) });
        Some(0)
            .into_iter()
            .map(|i| (i, self.blocks.get(&i).unwrap()))
            .chain(blocks)
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
                JumpLocation::Return(_) => (), // TODO
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
    Return(Vec<Register>),
    // Register(Register),
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Register(pub u128);

impl std::fmt::Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "r{}", self.0)
    }
}

impl std::fmt::Display for JumpLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Self::Block(i) => write!(f, "block_{i}"),
            Self::Return(regs) => write!(f, "Return({regs:?})"),
        }
    }
}

impl std::fmt::Display for Condition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Self::NonZero(r) => write!(f, "NonZero({r})"),
        }
    }
}

impl std::fmt::Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        for (i, block) in self.iter() {
            if i != 0 {
                writeln!(f)?;
            }
            write!(f, "block_{i}:")?;
            for inst in &block.insts {
                write!(f, "\n    ")?;
                match inst {
                    Inst::Store(r, sk) => {
                        use StoreKind as Sk;
                        write!(f, "{r} = ")?;
                        match sk {
                            Sk::StackAlloc(ty) => write!(f, "StackAlloc({ty:?})"),
                            Sk::Int(i, ty) => write!(f, "{i}_u{ty}"),
                            Sk::Read(r) => write!(f, "*{r}"),
                            Sk::BinOp(op, lhs, rhs) => write!(
                                f,
                                "{lhs} {} {rhs}",
                                match op {
                                    BinOp::Add => "+",
                                    BinOp::Sub => "-",
                                }
                            ),
                            Sk::Phi(regs) => {
                                write!(f, "Phi(")?;
                                for (i, reg) in regs.iter().enumerate() {
                                    if i != 0 {
                                        write!(f, ", ")?;
                                    }
                                    write!(f, "{reg}")?;
                                }
                                write!(f, ")")
                            }
                        }
                    }
                    Inst::Write(dst, src) => write!(f, "*{dst} = {src}"),
                    Inst::Jump(loc) => write!(f, "Jump {loc}"),
                    Inst::CondJump(cond, loc_true, loc_false) => {
                        write!(f, "Jump if {cond} then {loc_true} else {loc_false}")
                    }
                }?;
            }
        }
        Ok(())
    }
}
