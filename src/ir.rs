use crate::compiler_types::{Map, Set, Span, Str};

/// A full or partial program.
#[derive(Clone, Debug)]
pub struct Program {
    /// The functions composing this program.
    pub functions: Map<Str, Function>,
}

impl Program {
    /*
    pub fn type_check(&self) {
        for (_name, f) in &self.functions {
            f.type_check();
        }
    }
    */
}

/// A body of code accepts and yields some registers.
#[derive(Clone, Debug)]
pub struct Function {
    /// The types of the parameters.
    pub param_tys: Vec<Ty>,
    /// The types of the returned values.
    pub return_tys: Vec<Ty>,
    /// A list of registers containing the input values in order at the start of the function's execution.
    pub parameters: Vec<Register>,
    /// The basic blocks of code comprising this function.
    pub blocks: Map<BlockId, Block>,
    /// The data type of values stored in each register.
    pub tys: Map<Register, Ty>,
    /// The corresponding source location of each register.
    pub spans: Map<Register, Span>,
    /// The blocks that can directly jump to a given block.
    pub predecessors: Map<BlockId, Set<BlockId>>,
    /// The dominator tree
    pub dominator_tree: DominatorTree,
}

impl Function {
    pub fn new(
        param_tys: Vec<Ty>,
        return_tys: Vec<Ty>,
        parameters: Vec<Register>,
        blocks: Map<BlockId, Block>,
        tys: Map<Register, Ty>,
        spans: Map<Register, Span>,
    ) -> Self {
        let dominator_tree = DominatorTree::new(&blocks);
        let mut this = Self {
            param_tys,
            return_tys,
            parameters,
            blocks,
            tys,
            spans,
            predecessors: Map::new(),
            dominator_tree,
        };
        this.gen_predecessors();
        this
    }
    /*
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
    */
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
    fn display_with_name(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        name: &str,
    ) -> Result<(), std::fmt::Error> {
        for (id, block) in self.iter() {
            if !id.is_entry() {
                writeln!(f)?;
            }
            write!(f, "{name}_{}:", id.0)?;
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
                            Sk::Read(r) => write!(f, "{r}^"),
                            Sk::UnaryOp(op, inner) => write!(
                                f,
                                "{}{inner}",
                                match op {
                                    UnaryOp::Neg => "-",
                                }
                            ),
                            Sk::BinOp(op, lhs, rhs) => write!(
                                f,
                                "{lhs} {} {rhs}",
                                match op {
                                    BinOp::Add => "+",
                                    BinOp::Sub => "-",
                                    BinOp::Mul => "*",
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
                            Sk::Function(name) => write!(f, "{name}"),
                        }
                    }
                    Inst::Write(dst, src) => write!(f, "{dst}^ = {src}"),
                    Inst::Call {
                        callee,
                        returns,
                        args,
                    } => {
                        write!(f, "[")?;
                        for (i, r) in returns.iter().enumerate() {
                            if i != 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{r}")?;
                        }
                        write!(f, "] = {callee}(")?;
                        for (i, r) in args.iter().enumerate() {
                            if i != 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{r}")?;
                        }
                        write!(f, ")")
                    }
                    Inst::Nop => write!(f, "Nop"),
                }?;
            }
            write!(f, "\n    {}", block.exit)?;
        }
        Ok(())
    }
}

/// The type of any value operated on.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Ty {
    /// An integer.
    Int,
    /// A pointer into memory storing a value of a given type.
    Pointer(Box<Self>),
    /// A function pointer accepting and returning some values.
    Function(Vec<Self>, Vec<Self>),
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
        let mut this = Self {
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
                        Sk::UnaryOp(_, r) => f(r, false),
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
                        Sk::Int(..) | Sk::StackAlloc(_) | Sk::Function(_) => {}
                    }
                }
                Inst::Write(r1, r2) => {
                    f(r1, false);
                    f(r2, false);
                }
                Inst::Call {
                    callee,
                    returns,
                    args,
                } => {
                    f(callee, false);
                    for r in returns {
                        f(r, true);
                    }
                    for r in args {
                        f(r, false);
                    }
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
    /// Execute a function, passing the values in a list of registers as arguments and storing return values in a list of registers.
    Call {
        callee: Register,
        returns: Vec<Register>,
        args: Vec<Register>,
    },
    /// Do nothing.
    Nop,
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
    /// An operation on the value of one register.
    UnaryOp(UnaryOp, Register),
    /// An operation on the value of two registers.
    BinOp(BinOp, Register, Register),
    /// A pointer to a unique allocation for a value of a given type.
    StackAlloc(Ty),
    /// A read access through a pointer to memory.
    Read(Register),
    /// The pointer to a function.
    Function(Str),
}

/// A logic or arithmetic operation taking and yielding one value.
#[derive(Copy, Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum UnaryOp {
    /// Negation.
    Neg,
}

/// A logic or arithmetic operation taking two values and yielding one.
#[derive(Copy, Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum BinOp {
    /// Addition.
    Add,
    /// Subtraction.
    Sub,
    /// Multiplication.
    Mul,
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
    /// - A function whose address is not equal to zero (so all of them?).
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

    pub const fn is_entry(self) -> bool {
        self.0 == 0
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DominatorTree {
    pub children: Map<BlockId, Self>,
}

impl DominatorTree {
    pub fn new(blocks: &Map<BlockId, Block>) -> Self {
        let mut this = Self {
            children: blocks
                .keys()
                .map(|&id| {
                    (
                        id,
                        Self {
                            children: Map::new(),
                        },
                    )
                })
                .collect(),
        };
        this.make_immediate(blocks);
        this
    }
    fn make_immediate(&mut self, blocks: &Map<BlockId, Block>) {
        fn traverse_except(blocks: &Map<BlockId, Block>, except: BlockId) -> Set<BlockId> {
            let mut unreachable: Set<_> =
                blocks.keys().copied().filter(|&id| id != except).collect();
            let mut open = vec![BlockId::ENTRY];
            while let Some(id) = open.pop() {
                if unreachable.remove(&id) {
                    open.extend(blocks.get(&id).unwrap().successors());
                }
            }
            unreachable
        }
        let mut closed = Set::new();
        // TODO: this is an unlovely quadratic loop. if this is a problem, fix it or change algorithms
        while let Some(child_id) = self
            .children
            .keys()
            .copied()
            .find(|child_id| !closed.contains(child_id))
        {
            closed.insert(child_id);
            let mut new_children = traverse_except(blocks, child_id)
                .into_iter()
                .filter_map(|dommed_id| self.children.remove_entry(&dommed_id))
                .collect();
            self.children
                .get_mut(&child_id)
                .unwrap()
                .children
                .append(&mut new_children);
        }
        for child in self.children.values_mut() {
            child.make_immediate(blocks);
        }
    }
    pub fn visit(&self, mut f: impl FnMut(BlockId)) {
        self.visit_inner(&mut f);
    }
    fn visit_inner(&self, f: &mut impl FnMut(BlockId)) {
        for (&id, children) in &self.children {
            f(id);
            children.visit_inner(f);
        }
    }
    pub fn iter(&self) -> impl Iterator<Item = BlockId> + '_ {
        // obviously it's bad to allocate a vec for this, but it's our little secret.
        // the lifetime bound (i think) lets us change this to something better if need be
        let mut ids = vec![];
        self.visit(|id| ids.push(id));
        ids.into_iter()
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

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Self::Int => write!(f, "int"),
            Self::Pointer(inner) => write!(f, "{inner}^"),
            Self::Function(params, returns) => {
                write!(f, "fn(")?;
                for (i, param) in params.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{param}")?;
                }
                write!(f, ")")?;
                match returns.len() {
                    0 => Ok(()),
                    1 => write!(f, " {}", returns[0]),
                    _ => {
                        write!(f, " {{")?;
                        for (i, ret) in returns.iter().enumerate() {
                            if i != 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{ret}")?;
                        }
                        write!(f, "}}")
                    }
                }
            }
        }
    }
}

impl std::fmt::Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.display_with_name(f, "block")
    }
}

impl std::fmt::Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        for (name, function) in &self.functions {
            function.display_with_name(f, name)?;
            write!(f, "\n\n")?;
        }
        Ok(())
    }
}
