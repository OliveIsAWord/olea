//! The Olea intermediate representation, a low level language that consists of [SSA](https://en.wikipedia.org/wiki/Static_single-assignment_form) registers and [basic blocks](https://en.wikipedia.org/wiki/Basic_block).

use crate::compiler_types::{Map, Set, Span, Str};

/// A full or partial program.
#[derive(Clone, Debug)]
pub struct Program {
    /// The functions composing this program.
    pub functions: Map<Str, Function>,
    /// The type signature of every function including extern functions.
    pub function_tys: Map<Str, (Vec<Ty>, Vec<Ty>)>,
}

/// A body of code accepts and yields some registers.
#[derive(Clone, Debug)]
pub struct Function {
    /// A list of registers containing the input values in order at the start of the function's execution.
    pub parameters: Vec<Register>,
    /// The basic blocks of code comprising this function.
    pub blocks: Map<BlockId, Block>,
    /// The data type of values stored in each register.
    pub tys: Map<Register, Ty>,
    /// The corresponding source location of each register.
    pub spans: Map<Register, Span>,
    /// Information about the control flow graph.
    pub cfg: Cfg,
    /// Next register ID.
    pub next_register: u128,
}

/// Information about the control flow graph,
/// including successors, predecessors, and dominance
#[derive(Clone, Debug)]
pub struct Cfg {
    /// Map directly from BlockId to CfgNodes
    pub map: Map<BlockId, CfgNode>,
}

/// Information about the control flow graph.
impl Cfg {
    /// build a CFG out of a set of blocks.
    pub fn new(blocks: &Map<BlockId, Block>) -> Self {
        let mut cfg = Cfg {
            map: Map::<BlockId, CfgNode>::new(),
        };

        // build nodes
        for (id, _) in blocks {
            cfg.map.insert(*id, CfgNode::new(*id));
        }

        // build edges
        for (id, block) in blocks {
            // we have to do this in separate loops unfortunately cause mutable borrowing
            for succ in block.successors() {
                let succ_node = cfg.map.get_mut(&succ).unwrap();
                succ_node.predecessors.insert(*id);
            }
            let block_node = cfg.map.get_mut(id).unwrap();
            for succ in block.successors() {
                block_node.successors.insert(succ);
            }
        }

        // build dominator tree
        // TODO: actually build a reasonable dominator tree rather than this sad, totally naive approximation where every other block is a child of the entry block.
        // build edges
        for id in blocks.keys() {
            let parent = if id.is_entry() {
                None
            } else {
                Some(BlockId::ENTRY)
            };
            cfg.map.get_mut(id).unwrap().immediate_dominator = parent;
        }
        cfg.map
            .get_mut(&BlockId::ENTRY)
            .unwrap()
            .dominates
            .extend(blocks.keys().copied().filter(|id| !id.is_entry()));
        cfg
    }

    /// Access every block ID in the dominator tree such that a given block is visited before any of the blocks it strictly dominates.
    pub fn dom_visit(&self, mut f: impl FnMut(BlockId)) {
        self.dom_visit_inner(BlockId::ENTRY, &mut f);
    }
    fn dom_visit_inner(&self, id: BlockId, f: &mut impl FnMut(BlockId)) {
        f(id);
        let children = &self.map.get(&id).unwrap().dominates;
        for child in children {
            self.dom_visit_inner(*child, f);
        }
    }
    /// Get the block IDs of this dominator tree in visiting order.
    pub fn dom_iter(&self) -> impl Iterator<Item = BlockId> + '_ {
        // (sandwich): this is pretty much lifted from og DominatorTree

        // obviously it's bad to allocate a vec for this, but it's our little secret.
        // the lifetime bound (i think) lets us change this to something better if need be
        let mut ids = vec![];
        self.dom_visit(|id| ids.push(id));
        ids.into_iter()
    }
}

/// A node in the CFG
#[derive(Clone, Debug)]
pub struct CfgNode {
    /// Associated block id.
    pub id: BlockId,
    /// Dominance tree parent
    pub immediate_dominator: Option<BlockId>,
    /// Dominance tree children
    pub dominates: Set<BlockId>,

    /// Blocks that can jump here
    pub predecessors: Set<BlockId>,
    /// Blocks that this block can jump to
    pub successors: Set<BlockId>,
}

impl CfgNode {
    /// Construct a CFG node.
    pub fn new(id: BlockId) -> Self {
        Self {
            id,
            immediate_dominator: None,
            dominates: Set::new(),
            predecessors: Set::new(),
            successors: Set::new(),
        }
    }
}

impl Function {
    /// Construct a function.
    #[must_use]
    pub fn new(
        parameters: Vec<Register>,
        blocks: Map<BlockId, Block>,
        tys: Map<Register, Ty>,
        spans: Map<Register, Span>,
        next_register: u128,
    ) -> Self {
        let cfg = Cfg::new(&blocks);
        let this = Self {
            parameters,
            blocks,
            tys,
            spans,
            cfg,
            next_register,
        };
        this
    }
    /// Returns an iterator over the blocks and their IDs of the function. The first item is always the entry block.
    pub fn iter(&self) -> impl Iterator<Item = (BlockId, &Block)> {
        // NOTE: This relies on block 0 being first because of BTreeSet and the sort order of blocks
        self.blocks.iter().map(|(&id, block)| (id, block))
    }

    /// create a new register.
    pub fn new_reg(&mut self) -> Register {
        self.next_register += 1;
        Register(self.next_register - 1)
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
    /// Construct a block.
    #[must_use]
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
    /// Get all the blocks this block can jump to.
    pub fn successors(&self) -> impl Iterator<Item = BlockId> {
        self.exit.successors()
    }
    /// Update the sets of used and defined registers.
    pub fn gen_def_use(&mut self) {
        let mut def = Set::new();
        let mut used = Set::new();
        self.visit_regs(|r, is_def| {
            if is_def {
                def.insert(r);
            } else {
                used.insert(r);
            }
        });
        self.defined_regs = def;
        self.used_regs = used;
    }
    /// Access every register instance of this block with an additional parameter signalling whether this is the definition of the register, not including phi arguments.
    pub fn visit_regs<F: FnMut(Register, bool)>(&self, mut f: F) {
        for inst in &self.insts {
            inst.visit_regs(&mut f);
        }
        self.exit.visit_regs(|r| f(r, false));
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
        /// The register containing the function.
        callee: Register,
        /// The list of registers that store the function's returned values.
        returns: Vec<Register>,
        /// The list of registers whose values are passed as arguments to the function.
        args: Vec<Register>,
    },
    /// Do nothing.
    Nop,
}

impl Inst {
    /// Access every register instance of this instruction with an additional parameter signalling whether this is the definition of the register, not including phi arguments.
    pub fn visit_regs<F: FnMut(Register, bool)>(&self, mut f: F) {
        use StoreKind as Sk;
        match self {
            Self::Store(r, sk) => {
                f(*r, true);
                match sk {
                    &Sk::UnaryOp(_, r) => f(r, false),
                    &Sk::BinOp(_, r1, r2) | &Sk::PtrOffset(r1, r2) => {
                        f(r1, false);
                        f(r2, false);
                    }
                    &Sk::Read(r) | &Sk::Copy(r) => {
                        f(r, false);
                    }
                    Sk::Phi(_) => (), // Don't visit phi node arguments because they conceptually live in the predecessor block.
                    Sk::Int(_) | Sk::StackAlloc(_) | Sk::Function(_) => {}
                }
            }
            &Self::Write(r1, r2) => {
                f(r1, false);
                f(r2, false);
            }
            Self::Call {
                callee,
                returns,
                args,
            } => {
                f(*callee, false);
                for &r in returns {
                    f(r, true);
                }
                for &r in args {
                    f(r, false);
                }
            }
            Self::Nop => {}
        }
    }

    /// Does this instruction define a certain register?
    pub fn is_def(&self, reg: Register) -> bool {
        match self {
            Self::Store(r, _) => *r == reg,
            Self::Call {
                callee: _,
                returns,
                args: _,
            } => returns.iter().any(|r| *r == reg),
            _ => false,
        }
    }

    /// Does this instruction use a certain register?
    pub fn is_use(&self, reg: Register, count_phi: bool) -> bool {
        use StoreKind as Sk;
        match self {
            Self::Store(_, sk) => match sk {
                &Sk::BinOp(_, r1, r2) | &Sk::PtrOffset(r1, r2) => r1 == reg || r2 == reg,
                &Sk::UnaryOp(_, r) | &Sk::Read(r) | &Sk::Copy(r) => r == reg,
                Sk::Phi(srcs) => count_phi && srcs.iter().any(|(_, r)| *r == reg),
                Sk::Int(_) | Sk::StackAlloc(_) | Sk::Function(_) => false,
            },
            &Self::Write(r1, r2) => r1 == reg || r2 == reg,
            Self::Call {
                callee: _,
                returns: _,
                args,
            } => args.iter().any(|r| *r == reg),
            Self::Nop => false,
        }
    }
}

/// A method of calculating a value to store in a register.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum StoreKind {
    /// An integer constant.
    Int(i128),
    /// A copy of another register's value.
    Copy(Register),
    /// A choice of values based on the immediately preceding block.
    Phi(Map<BlockId, Register>),
    /// An operation on the value of one register.
    UnaryOp(UnaryOp, Register),
    /// An operation on the value of two registers.
    BinOp(BinOp, Register, Register),
    /// A pointer offset from the first register by a number of elements according to the second register. Equivalent to `r1[r2]@`.
    PtrOffset(Register, Register),
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
    /// Unsigned multiplication.
    Mul,
    /// Less-than-or-equal-to comparison.
    CmpLe,
}

/// The direction of control flow after all instructions of a block have been executed.
#[derive(Clone, Debug)]
pub enum Exit {
    /// Direct control flow to a single, static location.
    Jump(BlockId),
    /// Direct control flow to one of two locations based on some runtime condition.
    CondJump(Condition, BlockId, BlockId),
    /// Execution terminates, yielding a list of values.
    Return(Vec<Register>),
}

impl Exit {
    /// Does this exit use a certain register?
    pub fn is_use(&self, reg: Register) -> bool {
        match self {
            Self::CondJump(Condition::NonZero(r), _, _) => *r == reg,
            Self::Return(regs) => regs.iter().any(|r| *r == reg),
            _ => false,
        }
    }
    /// Get all the blocks this exit can jump to.
    pub fn successors(&self) -> impl Iterator<Item = BlockId> {
        let mut ids = vec![];
        match self {
            Self::Jump(loc) => ids.push(*loc),
            Self::CondJump(_, loc1, loc2) => {
                ids.push(*loc1);
                ids.push(*loc2);
            }
            _ => {}
        }
        ids.into_iter()
    }
    /// Access every register usage of this block exit.
    pub fn visit_regs<F: FnMut(Register)>(&self, mut f: F) {
        match self {
            Self::Jump(_) => {}
            Self::CondJump(cond, _, _) => match cond {
                &Condition::NonZero(r) => f(r),
            },
            Self::Return(regs) => {
                for &r in regs {
                    f(r);
                }
            }
        }
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

/// A named location which stores a value.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Register(pub u128);

/// An identifier for a block unique within the function.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BlockId(pub usize);

impl BlockId {
    /// The ID of the block first executed when calling a function.
    pub const ENTRY: Self = Self(0);
    /// A placeholder ID which does not correspond to a block.
    pub const DUMMY: Self = Self(usize::MAX);

    /// Check if this ID is the entry ID.
    #[must_use]
    pub const fn is_entry(self) -> bool {
        self.0 == 0
    }
}
