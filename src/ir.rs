use crate::compiler_types::{Map, Set};

/// A body of code accepts and yields some registers.
#[derive(Clone, Debug)]
pub struct Function {
    /// The basic blocks of code comprising this function.
    pub blocks: Map<BlockId, Block>,
    /// The blocks that can directly jump to a given block.
    pub predecessors: Map<BlockId, Set<BlockId>>,
    /// The data type of values stored in each register.
    pub tys: Map<Register, Ty>,
}

impl Function {
    pub fn new(blocks: Map<BlockId, Block>, tys: Map<Register, Ty>) -> Self {
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
        for Block { exit, .. } in self.blocks.values() {
            exit.type_check(tys);
        }
    }
    /// Returns an iterator over the blocks and their IDs of the function. The first item is always the entry block.
    pub fn iter(&self) -> impl Iterator<Item = (BlockId, &Block)> {
        // NOTE: This relies on block 0 being first because of BTreeSet and the sort order of blocks
        self.blocks.iter().map(|(&id, block)| (id, block))
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

/// The type of any value operated on.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Ty {
    /// An integer.
    Int,
    /// A pointer into memory storing a value of a given type.
    Pointer(Box<Self>),
}

/// A basic block, as in a block of code with one entrance and one exit where each instruction is executed in sequence exactly once before another block executes or the function returns.
#[derive(Clone, Debug)]
pub struct Block {
    /// A sequence of instructions that are executed in order.
    pub insts: Vec<Inst>,
    /// The direction of control flow after all instructions of this block have been executed.
    pub exit: Exit,
    /// The set of all registers defined (and then assigned) by this block.
    pub defined_regs: Set<Register>,
    /// The set of all registers directly used by this block.
    pub used_regs: Set<Register>,
}

impl Block {
    pub fn new(insts: Vec<Inst>, exit: Exit) -> Self {
        let mut this = Block {
            insts,
            exit,
            defined_regs: Set::new(),
            used_regs: Set::new(),
        };
        this.gen_def_use();
        this
    }
    pub fn successors(&self) -> impl Iterator<Item = BlockId> {
        self.exit.successors()
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
                        Sk::Read(r) | Sk::Copy(r) => {
                            f(r, false);
                        }
                        Sk::Phi(regs) => {
                            for r in regs.values_mut() {
                                f(r, false);
                            }
                        }
                        Sk::Int(..) | Sk::StackAlloc(_) => {}
                    }
                }
                Inst::Write(r1, r2) => {
                    f(r1, false);
                    f(r2, false);
                }
                Inst::Nop => {}
            }
        }
        match &mut self.exit {
            Exit::Jump(branch) => branch.visit_regs(|r| f(r, false)),
            Exit::CondJump(cond, branch1, branch2) => {
                match cond {
                    Condition::NonZero(r) => f(r, false),
                }
                branch1.visit_regs(|r| f(r, false));
                branch2.visit_regs(|r| f(r, false));
            }
        }
    }
}

/// An operation within a block.
#[derive(Clone, Debug)]
pub enum Inst {
    /// Define a register and assign it a value.
    Store(Register, StoreKind),
    /// Write to a pointer with a value.
    Write(Register, Register),
    /// Do nothing.
    Nop,
}

impl Inst {
    fn type_check(&self, tys: &Map<Register, Ty>) {
        let ty_of = |r| tys.get(r).unwrap();
        match self {
            Self::Store(r, sk) => assert_eq!(ty_of(r), &sk.ty(tys)),
            Self::Write(dst, src) => match ty_of(dst) {
                Ty::Pointer(inner) => assert_eq!(inner.as_ref(), ty_of(src)),
                e @ Ty::Int => panic!("typeck error: attempted to Write to {dst:?} of type {e:?}"),
            },
            Self::Nop => {}
        }
    }
}

/// A method of calculating a value to store in a register.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum StoreKind {
    /// An integer constant.
    Int(u128),
    /// A copy of another register's value.
    Copy(Register),
    /// A choice of values based on the immediately preceding block.
    Phi(Map<BlockId, Register>),
    /// An operation on the value of two registers.
    BinOp(BinOp, Register, Register),
    /// A pointer to a unique allocation for a value of a given type.
    StackAlloc(Ty),
    /// A read access through a pointer to memory.
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
            &Self::Int(_) => Ty::Int,
            Self::Phi(regs) => all(&regs.values().copied().collect::<Vec<_>>()), // TODO silly and bad
            &Self::BinOp(_, lhs, rhs) => all(&[lhs, rhs]),
            Self::StackAlloc(ty) => Ty::Pointer(Box::new(ty.clone())),
            Self::Copy(r) => tys.get(r).unwrap().clone(),
            Self::Read(r) => match tys.get(r).unwrap() {
                Ty::Pointer(inner) => inner.as_ref().clone(),
                e @ Ty::Int => panic!("typeck error: attempted to Read from {r:?} of type {e:?}"),
            },
        }
    }
}

/// A logic or arithmetic operation taking two values and yielding one.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum BinOp {
    /// Addition.
    Add,
    /// Subtraction.
    Sub,
}

/// The direction of control flow after all instructions of a block have been executed.
#[derive(Clone, Debug)]
pub enum Exit {
    /// Direct control flow to a single, static location.
    Jump(JumpLocation),
    /// Direct control flow to one of two locations based on some runtime condition.
    CondJump(Condition, JumpLocation, JumpLocation),
}

impl Exit {
    pub fn type_check(&self, tys: &Map<Register, Ty>) {
        let ty_of = |r| tys.get(r).unwrap();
        match self {
            Self::Jump(location) => match location {
                JumpLocation::Block(_) => (),
                JumpLocation::Return(_) => (), // TODO
            },
            Self::CondJump(condition, _branch1, _branch2) => {
                match condition {
                    Condition::NonZero(r) => match ty_of(r) {
                        Ty::Int | Ty::Pointer(_) => (),
                    },
                }
                // TODO: any sort of JumpLocation checking?
            }
        }
    }
    pub fn successors(&self) -> impl Iterator<Item = BlockId> {
        let mut ids = vec![];
        let mut add = |loc: &JumpLocation| match loc {
            JumpLocation::Return(_) => {}
            &JumpLocation::Block(succ_id) => {
                ids.push(succ_id);
            }
        };
        match self {
            Self::Jump(loc) => add(loc),
            Self::CondJump(_, loc1, loc2) => {
                add(loc1);
                add(loc2);
            }
        }
        ids.into_iter()
    }
}

/// A runtime condition to determine which of two control flow paths to take.
#[derive(Clone, Debug)]
pub enum Condition {
    /// Take the first branch if the register contains a non-zero value, meaning:
    /// - An integer not equal to zero.
    /// - A pointer whose address is not equal to zero.
    NonZero(Register),
}

/// The behavior of a branch of execution.
#[derive(Clone, Debug)]
pub enum JumpLocation {
    /// Execution continues to another block.
    Block(BlockId),
    /// Execution terminates, yielding a list of values.
    Return(Vec<Register>),
}

impl JumpLocation {
    pub fn visit_regs<F: FnMut(&mut Register)>(&mut self, mut f: F) {
        match self {
            Self::Block(_) => {}
            Self::Return(regs) => {
                for r in regs {
                    f(r);
                }
            }
        }
    }
}

/// A named location which stores a value.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Register(pub u128);

/// An identifier for a block unique within the function.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BlockId(pub usize);

impl BlockId {
    pub const ENTRY: Self = Self(0);
    pub const DUMMY: Self = Self(usize::MAX);

    pub fn is_entry(self) -> bool {
        self.0 == 0
    }
}

impl std::fmt::Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "%{}", self.0)
    }
}

impl std::fmt::Display for BlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "block_{}", self.0)
    }
}

impl std::fmt::Display for JumpLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Self::Block(b) => write!(f, "{b}"),
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

impl std::fmt::Display for Exit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Self::Jump(loc) => write!(f, "Jump {loc}"),
            Self::CondJump(cond, loc_true, loc_false) => {
                write!(f, "Jump if {cond} then {loc_true} else {loc_false}")
            }
        }
    }
}

impl std::fmt::Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        for (id, block) in self.iter() {
            if !id.is_entry() {
                writeln!(f)?;
            }
            write!(f, "{id}:")?;
            for inst in &block.insts {
                write!(f, "\n    ")?;
                match inst {
                    Inst::Store(r, sk) => {
                        use StoreKind as Sk;
                        write!(f, "{r} = ")?;
                        match sk {
                            Sk::StackAlloc(ty) => write!(f, "StackAlloc({ty:?})"),
                            Sk::Int(i) => write!(f, "{i}"),
                            Sk::Copy(r) => write!(f, "{r}"),
                            Sk::Read(r) => write!(f, "{r}*"),
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
                                for (i, (id, reg)) in regs.iter().enumerate() {
                                    if i != 0 {
                                        write!(f, ", ")?;
                                    }
                                    write!(f, "{id}: {reg}")?;
                                }
                                write!(f, ")")
                            }
                        }
                    }
                    Inst::Write(dst, src) => write!(f, "{dst}* = {src}"),
                    Inst::Nop => write!(f, "Nop"),
                }?;
            }
            write!(f, "\n    {}", block.exit)?;
        }
        Ok(())
    }
}
