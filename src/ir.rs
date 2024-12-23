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
    /// The blocks that can directly jump to a given block.
    pub predecessors: Map<BlockId, Set<BlockId>>,
    /// The dominator tree of this function. See [`DominatorTree`].
    pub dominator_tree: DominatorTree,
}

impl Function {
    /// Construct a function.
    #[must_use]
    pub fn new(
        parameters: Vec<Register>,
        blocks: Map<BlockId, Block>,
        tys: Map<Register, Ty>,
        spans: Map<Register, Span>,
    ) -> Self {
        let dominator_tree = DominatorTree::new(&blocks);
        let mut this = Self {
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
    /// Returns an iterator over the blocks and their IDs of the function. The first item is always the entry block.
    pub fn iter(&self) -> impl Iterator<Item = (BlockId, &Block)> {
        // NOTE: This relies on block 0 being first because of BTreeSet and the sort order of blocks
        self.blocks.iter().map(|(&id, block)| (id, block))
    }
    /// Traverse the control flow graph to update the mapping of immediate predecessors for each block.
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
                    &Sk::BinOp(_, r1, r2) => {
                        f(r1, false);
                        f(r2, false);
                    }
                    &Sk::Read(r) | &Sk::Copy(r) => {
                        f(r, false);
                    }
                    Sk::Phi(_) => (), // Don't visit phi node arguments because they conceptually live in the predecessor block.
                    Sk::Int(..) | Sk::StackAlloc(_) | Sk::Function(_) => {}
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
    /// Get all the blocks this exit can jump to.
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
    /// Access every register usage of this block exit.
    pub fn visit_regs<F: FnMut(Register)>(&self, mut f: F) {
        match self {
            Self::Jump(branch) => branch.visit_regs(f),
            Self::CondJump(cond, branch1, branch2) => {
                match *cond {
                    Condition::NonZero(r) => f(r),
                }
                branch1.visit_regs(&mut f);
                branch2.visit_regs(f);
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

/// The behavior of a branch of execution.
#[derive(Clone, Debug)]
pub enum JumpLocation {
    /// Execution continues to another block.
    Block(BlockId),
    /// Execution terminates, yielding a list of values.
    Return(Vec<Register>),
}

impl JumpLocation {
    /// Access every register this jump location uses.
    pub fn visit_regs<F: FnMut(Register)>(&self, mut f: F) {
        match self {
            Self::Block(_) => {}
            Self::Return(regs) => {
                for &r in regs {
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

/// A [dominator tree](https://en.wikipedia.org/wiki/Dominator_(graph_theory)), a tree of blocks where a block's ancestors are all the blocks that must execute before it.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DominatorTree {
    /// The tree of blocks.
    pub children: Map<BlockId, Self>,
}

impl DominatorTree {
    /// Construct a dominator tree.
    #[must_use]
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
    /// Access every block ID in the dominator tree such that a given block is visited before any of the blocks it strictly dominates.
    pub fn visit(&self, mut f: impl FnMut(BlockId)) {
        self.visit_inner(&mut f);
    }
    fn visit_inner(&self, f: &mut impl FnMut(BlockId)) {
        for (&id, children) in &self.children {
            f(id);
            children.visit_inner(f);
        }
    }
    /// Get the block IDs of this dominator tree in visiting order.
    pub fn iter(&self) -> impl Iterator<Item = BlockId> + '_ {
        // obviously it's bad to allocate a vec for this, but it's our little secret.
        // the lifetime bound (i think) lets us change this to something better if need be
        let mut ids = vec![];
        self.visit(|id| ids.push(id));
        ids.into_iter()
    }
}
