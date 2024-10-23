use crate::compiler_types::{Map, Set};

#[derive(Clone, Debug)]
pub struct Function {
    pub blocks: Map<usize, Block>,
    pub predecessors: Map<usize, Set<usize>>,
    pub tys: Map<Register, Ty>,
}

impl Function {
    pub fn new(blocks: Map<usize, Block>, tys: Map<Register, Ty>) -> Self {
        let mut this = Function {
            blocks,
            tys,
            predecessors: Map::new(),
        };
        this.gen_predecessors();
        this
    }
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
    pub fn gen_predecessors(&mut self) {
        let mut p: Map<_, _> = self.blocks.keys().map(|&id| (id, Set::new())).collect();
        for (&id, block) in &self.blocks {
            for succ_id in block.successors() {
                p.get_mut(&succ_id).unwrap().insert(id);
            }
        }
        self.predecessors = p;
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
    pub defined_regs: Set<Register>,
    pub used_regs: Set<Register>,
}

impl Block {
    pub fn new(insts: Vec<Inst>) -> Self {
        let mut this = Block {
            insts,
            defined_regs: Set::new(),
            used_regs: Set::new(),
        };
        this.gen_def_use();
        this
    }
    pub fn successors(&self) -> impl Iterator<Item = usize> {
        let mut ids = vec![];
        let mut add = |loc: &JumpLocation| match loc {
            JumpLocation::Return(_) => {}
            &JumpLocation::Block(succ_id) => {
                ids.push(succ_id);
            }
        };
        match self.insts.last().unwrap() {
            Inst::Jump(loc) => add(loc),
            Inst::CondJump(_, loc1, loc2) => {
                add(loc1);
                add(loc2);
            }
            _ => unreachable!(),
        }
        ids.into_iter()
    }
    pub fn gen_def_use(&mut self) {
        let mut def = Set::new();
        let mut used = Set::new();
        self.visit_regs(|&mut r, is_def| {
            if is_def {
                def.insert(r);
            } else {
                used.insert(r);
            }
        });
        self.defined_regs = def;
        self.used_regs = used;
    }
    pub fn visit_regs<F: FnMut(&mut Register, bool)>(&mut self, mut f: F) {
        for inst in &mut self.insts {
            use StoreKind as Sk;
            match inst {
                Inst::Store(r, sk) => {
                    f(r, true);
                    match sk {
                        Sk::BinOp(_, r1, r2) => {
                            f(r1, false);
                            f(r2, false);
                        }
                        Sk::Read(r) => {
                            f(r, false);
                        }
                        Sk::Phi(regs) => {
                            let mut new_regs: Vec<_> = regs.iter().copied().collect();
                            for r in &mut new_regs {
                                f(r, false)
                            }
                            *regs = new_regs.into_iter().collect();
                        }
                        Sk::Int(..) | Sk::StackAlloc(_) => {}
                    }
                }
                Inst::Write(r1, r2) => {
                    f(r1, false);
                    f(r2, false);
                }
                Inst::CondJump(cond, ..) => match cond {
                    Condition::NonZero(r) => f(r, false),
                },
                Inst::Jump(_) | Inst::Nop => {}
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum Inst {
    Store(Register, StoreKind),
    Write(Register, Register),
    Jump(JumpLocation),
    CondJump(Condition, JumpLocation, JumpLocation),
    Nop,
}

impl Inst {
    fn type_check(&self, tys: &Map<Register, Ty>) {
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
            Self::Nop => {}
        }
    }
}

#[derive(Clone, Debug)]
pub enum StoreKind {
    Int(u128, u64),
    // Copy(Register),
    Phi(Set<Register>),
    BinOp(BinOp, Register, Register),
    StackAlloc(Ty),
    Read(Register),
}

impl StoreKind {
    pub fn ty(&self, tys: &Map<Register, Ty>) -> Ty {
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
            Self::Phi(regs) => all(&regs.iter().copied().collect::<Vec<_>>()), // TODO silly and bad
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
                    Inst::Nop => write!(f, "Nop"),
                }?;
            }
        }
        Ok(())
    }
}
