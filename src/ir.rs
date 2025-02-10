//! The Olea intermediate representation, a low level language that consists of [SSA](https://en.wikipedia.org/wiki/Static_single-assignment_form) registers and [basic blocks](https://en.wikipedia.org/wiki/Basic_block).

use crate::compiler_types::{IndexMap, Map, Set, Span, Str};
pub use crate::language_types::IsAnon;

/// A full or partial program.
#[derive(Clone, Debug)]
pub struct Program {
    /// The functions composing this program.
    pub functions: Map<Str, Function>,
    /// The type signature of every function including extern functions.
    pub function_tys: Map<Str, (IndexMap<Str, (IsAnon, Ty)>, Vec<Ty>)>,
    /// All the types used in this program, indexed by `Ty`s.
    pub tys: TyMap,
}

/// The storage for all the types used in a program.
#[derive(Clone, Debug, Default)]
pub struct TyMap {
    /// The storage structure mapping type indexes to type data.
    pub(crate) inner: Map<Ty, TyKind>,
    /// A counter for the next type index to return.
    next_ty: u128,
}

impl TyMap {
    /// Construct a new [`TyMap`]
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Get a type immutably.
    #[must_use]
    pub fn get(&self, index: Ty) -> Option<&TyKind> {
        self.inner.get(&index)
    }

    // /// Get a type mutably.
    // pub fn get_mut(&mut self, ty: Ty) -> Option<&mut TyKind> {
    //     self.inner.get_mut(&ty)
    // }

    /// Reserve a type id for future use;
    pub fn reserve(&mut self) -> Ty {
        let reserved = self.next_ty;
        self.next_ty += 1;
        Ty(reserved)
    }

    /// Insert a new type and get the index to it.
    pub fn insert(&mut self, kind: TyKind) -> Ty {
        let index = self.reserve();
        self.insert_at(index, kind);
        index
    }

    /// Insert a new type with a previously reserved id.
    pub fn insert_at(&mut self, index: Ty, kind: TyKind) {
        if let Some(previous) = self.get(index) {
            panic!(
                "inserted two types at the same id\n  id: {index}\n  type 1: {previous}\n  type 2: {kind}"
            )
        }
        self.inner.insert(index, kind);
    }

    /// Format a type as a string through its id.
    #[must_use]
    pub fn format(&self, index: Ty) -> String {
        self.format_kind(&self[index])
    }

    /// Format a type as a string.
    #[must_use]
    pub fn format_kind(&self, kind: &TyKind) -> String {
        // yeah this is bad
        match kind {
            TyKind::Int(size) => size.to_string(),
            &TyKind::Pointer(inner) => format!("{}^", self.format(inner)),
            TyKind::Function(params, returns) => {
                let mut string = "fn(".to_owned();
                for (i, (name, (is_anon, ty))) in params.iter().enumerate() {
                    if i != 0 {
                        string.push_str(", ");
                    }
                    if is_anon.into() {
                        string.push_str("anon ");
                    }
                    string.push_str(name);
                    string.push_str(": ");
                    string.push_str(&self.format(*ty));
                }
                string.push(')');
                match returns.len() {
                    0 => {}
                    1 => {
                        string.push(' ');
                        string.push_str(&self.format(returns[0]));
                    }
                    2.. => {
                        string.push('{');
                        for (i, &ret) in returns.iter().enumerate() {
                            if i != 0 {
                                string.push_str(", ");
                            }
                            string.push_str(&self.format(ret));
                        }
                        string.push('}');
                    }
                }
                string
            }
            TyKind::Struct { name, .. } => name.as_ref().into(),
        }
    }

    /// Are the types behind these two ids structurally equal?
    #[must_use]
    pub fn equals(&self, a: Ty, b: Ty) -> bool {
        self.equals_kind(&self[a], &self[b])
    }

    /// Are these two types structurally equal?
    #[must_use]
    pub fn equals_kind(&self, a: &TyKind, b: &TyKind) -> bool {
        use TyKind as T;
        // exhaustiveness check; if this errors then you should probably update this function!
        match a {
            T::Int(_) | T::Pointer(_) | T::Function(..) | T::Struct { .. } => {}
        }
        match (a, b) {
            (T::Int(a), T::Int(b)) => a == b,
            (&T::Pointer(a), &T::Pointer(b)) => self.equals(a, b),
            (T::Function(a_params, a_returns), T::Function(b_params, b_returns)) => {
                if a_params.len() != b_params.len() || a_returns.len() != b_returns.len() {
                    return false;
                }
                for ((a_name, (a_is_anon, a_ty)), (b_name, (b_is_anon, b_ty))) in
                    a_params.iter().zip(b_params)
                {
                    if a_is_anon != b_is_anon || a_name != b_name || !self.equals(*a_ty, *b_ty) {
                        return false;
                    }
                }
                for (&a, &b) in a_returns.iter().zip(b_returns) {
                    if !self.equals(a, b) {
                        return false;
                    }
                }
                true
            }
            (T::Struct { name: a, .. }, T::Struct { name: b, .. }) => a == b,
            _ => false,
        }
    }
}

impl std::ops::Index<Ty> for TyMap {
    type Output = TyKind;
    fn index(&self, index: Ty) -> &TyKind {
        self.get(index).expect("no type found")
    }
}

// impl std::ops::IndexMut<Ty> for TyMap {
//     fn index_mut(&self, index: Ty) -> TyKind {
//         self.get_mut(index).expect("no type found")
//     }
// }

/// A body of code that accepts and yields some registers.
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

/// Information about the control flow graph, including successors, predecessors, and dominance.
#[derive(Clone, Debug)]
pub struct Cfg {
    /// Map directly from [`BlockId`] to [`CfgNodes`].
    pub map: Map<BlockId, CfgNode>,
}

/// Information about the control flow graph.
impl Cfg {
    /// Build a control flow graph out of a set of blocks.
    #[must_use]
    pub fn new(blocks: &Map<BlockId, Block>) -> Self {
        let mut cfg = Self { map: Map::new() };

        // build nodes
        for &id in blocks.keys() {
            cfg.map.insert(id, CfgNode::new(id));
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
        cfg.build_domtree();

        // build dominance frontiers
        // cfg.build_dom_frontiers();

        cfg
    }

    /// Use the Lengauer-Tarjan algorithm to create a dominator tree.
    #[expect(
        clippy::items_after_statements,
        reason = "This code needs rewriting anyways."
    )]
    pub fn build_domtree(&mut self) {
        // TODO: add a special case that skips all of this when a single-block function is found

        // these can be turned into arrays, but they can be maps for now.
        // the original algorithm calls for computing predecessors too, but we do that already.
        #[derive(Debug, Default)]
        struct LtInfo {
            parent: Map<BlockId, BlockId>,        // pre-order parent
            semi: Map<BlockId, usize>,            // semidominator helper
            vertex: Map<usize, BlockId>,          // block id from pre-order index
            bucket: Map<BlockId, Set<BlockId>>,   // set of blocks whos semidominator is the key
            forest_parent: Map<BlockId, BlockId>, // intermediate forest used in steps 2 and 3
            n: usize,                             // number of blocks
        }
        // initialize lengauer-tarjan info
        let mut lt = LtInfo::default();
        for v in self.map.keys() {
            lt.bucket.insert(*v, Set::new());
        }

        // step 1: run pre-order traversal
        // let mut n = 0;
        fn dfs(lt: &mut LtInfo, cfg: &Cfg, v: BlockId) {
            lt.n += 1;
            lt.semi.insert(v, lt.n);
            lt.vertex.insert(lt.n, v);
            let x = &cfg.map.get(&v).unwrap().successors;
            for w in x {
                if !lt.semi.contains_key(w) {
                    lt.parent.insert(*w, v);
                    dfs(lt, cfg, *w);
                }
            }
        }
        dfs(&mut lt, self, BlockId::ENTRY);

        fn link(lt: &mut LtInfo, parent: BlockId, child: BlockId) {
            lt.forest_parent.insert(child, parent);
        }

        fn eval(lt: &LtInfo, v: BlockId) -> BlockId {
            if !lt.forest_parent.contains_key(&v) {
                return v;
            }

            let mut u = v;
            let mut candidate = u;
            while lt.forest_parent.contains_key(&candidate) {
                if lt.semi[&candidate] < lt.semi[&u] {
                    u = candidate;
                }
                candidate = lt.forest_parent[&candidate];
            }
            u
        }

        for i in (2usize..=lt.n).rev() {
            let w = lt.vertex[&i];
            // step 2
            for v in &self.map[&w].predecessors {
                let u = eval(&lt, *v);
                if lt.semi[&u] < lt.semi[&w] {
                    lt.semi.insert(w, lt.semi[&u]);
                }
            }
            // add w to bucket(vertex(semi(w)))
            let bucket_semi_w = lt.bucket.get_mut(&lt.vertex[&lt.semi[&w]]).unwrap();
            bucket_semi_w.insert(w);
            let parent_w = lt.parent[&w];
            link(&mut lt, parent_w, w);

            // step 3
            for v in &lt.bucket[&lt.parent[&w]] {
                let u = eval(&lt, *v);
                let dom = if lt.semi[&u] < lt.semi[&w] {
                    u
                } else {
                    lt.parent[&w]
                };
                self.map.get_mut(&u).unwrap().immediate_dominator = Some(dom);
            }
        }
        // step 4
        for i in 2..=lt.n {
            let w: BlockId = lt.vertex[&i];
            let dom_w = self.map[&w].immediate_dominator.unwrap(); // if this unwrap fails, something bad has happened
            if dom_w != lt.vertex[&lt.semi[&w]] {
                let dom_dom_w = self
                    .map
                    .get_mut(&dom_w)
                    .unwrap()
                    .immediate_dominator
                    .unwrap();
                self.map.get_mut(&w).unwrap().immediate_dominator = Some(dom_dom_w);
            }
        }
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
    /// Get the [`BlockId`]s of this dominator tree in visiting order.
    pub fn dom_iter(&self) -> impl Iterator<Item = BlockId> + '_ {
        // (sandwich): this is pretty much lifted from og DominatorTree

        // obviously it's bad to allocate a vec for this, but it's our little secret.
        // the lifetime bound (i think) lets us change this to something better if need be
        let mut ids = vec![];
        self.dom_visit(|id| ids.push(id));
        ids.into_iter()
    }

    // pub fn build_dom_frontiers(&mut self) {
    //     for n in self.map.values_mut() {
    //         self.build_dom_frontier(n);
    //     }
    // }

    fn _build_dom_frontier(&self, n: &mut CfgNode) {
        for (block_id, block_node) in &self.map {
            if !self.dom(n.id, *block_id) {
                continue;
            }

            for succ in &block_node.successors {
                if !self.strict_dom(n.id, *succ) {
                    n.dom_frontier.insert(*succ);
                    break;
                }
            }
        }
    }

    /// Is N strictly dominated by D?
    #[must_use]
    pub fn strict_dom(&self, d: BlockId, mut n: BlockId) -> bool {
        while self.map[&n].immediate_dominator.is_some() {
            n = self.map[&n].immediate_dominator.unwrap();
            if n == d {
                return true;
            }
        }
        false
    }

    /// Is N dominated by D?
    #[must_use]
    pub fn dom(&self, d: BlockId, mut n: BlockId) -> bool {
        if n == d {
            return true;
        }
        while self.map[&n].immediate_dominator.is_some() {
            n = self.map[&n].immediate_dominator.unwrap();
            if n == d {
                return true;
            }
        }
        false
    }
}

/// A node in the [`Cfg`].
#[derive(Clone, Debug)]
pub struct CfgNode {
    /// Associated block ID.
    pub id: BlockId,
    /// Dominator tree parent (or `None` if this is the entry block).
    pub immediate_dominator: Option<BlockId>,
    /// Dominator tree children.
    pub dominates: Set<BlockId>,
    /// Blocks that can jump to this block.
    pub predecessors: Set<BlockId>,
    /// Blocks that this block can jump to.
    pub successors: Set<BlockId>,
    /// Dominance frontier.
    pub dom_frontier: Set<BlockId>,
}

impl CfgNode {
    /// Construct a CFG node.
    #[must_use]
    pub const fn new(id: BlockId) -> Self {
        Self {
            id,
            immediate_dominator: None,
            dominates: Set::new(),
            predecessors: Set::new(),
            successors: Set::new(),
            dom_frontier: Set::new(),
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
        Self {
            parameters,
            blocks,
            tys,
            spans,
            cfg,
            next_register,
        }
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

/// An index into the program level type storage.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
// I'd prefer not to have this field public but it's needed for `ir_display`.
pub struct Ty(pub(crate) u128);

/// The type of any value operated on.
#[derive(Clone, Debug)]
pub enum TyKind {
    /// An integer.
    Int(IntKind),
    /// A pointer into memory storing a value of a given type.
    Pointer(Ty),
    /// A function pointer accepting and returning some values.
    Function(IndexMap<Str, (IsAnon, Ty)>, Vec<Ty>),
    /// A named collection of named values.
    Struct {
        /// The name of the struct type.
        name: Str,
        /// The fields of the struct type.
        fields: Vec<(Str, Ty)>,
    },
}

/// The sizes an integer type can be.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum IntKind {
    /// Machine word-sized.
    Usize,
    /// 8 bits.
    U8,
    /// 16 bits.
    U16,
    /// 32 bits.
    U32,
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
                match *sk {
                    Sk::UnaryOp(_, r)
                    | Sk::IntCast(r, _)
                    | Sk::PtrCast(r, _)
                    | Sk::Read(r)
                    | Sk::Copy(r)
                    | Sk::FieldOffset(r, _) => f(r, false),
                    Sk::BinOp(_, r1, r2) | Sk::PtrOffset(r1, r2) => {
                        f(r1, false);
                        f(r2, false);
                    }
                    Sk::Phi(_) => (), // Don't visit phi node arguments because they conceptually live in the predecessor block.
                    Sk::Int(..) | Sk::StackAlloc(_) | Sk::Function(_) => {}
                    Sk::Struct {
                        ref fields,
                        name: _,
                    } => {
                        for &(_, value) in fields {
                            f(value, false);
                        }
                    }
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
    #[must_use]
    pub fn is_def(&self, reg: Register) -> bool {
        match self {
            Self::Store(r, _) => *r == reg,
            Self::Call {
                callee: _,
                returns,
                args: _,
            } => returns.iter().any(|r| *r == reg),
            Self::Write(..) | Self::Nop => false,
        }
    }

    /// Does this instruction use a certain register?
    #[must_use]
    pub fn is_use(&self, reg: Register, count_phi: bool) -> bool {
        use StoreKind as Sk;
        match self {
            Self::Store(_, sk) => match *sk {
                Sk::BinOp(_, r1, r2) | Sk::PtrOffset(r1, r2) => r1 == reg || r2 == reg,
                Sk::UnaryOp(_, r)
                | Sk::IntCast(r, _)
                | Sk::PtrCast(r, _)
                | Sk::Read(r)
                | Sk::Copy(r)
                | Sk::FieldOffset(r, _) => r == reg,
                Sk::Phi(ref srcs) => count_phi && srcs.iter().any(|(_, r)| *r == reg),
                Sk::Int(..) | Sk::StackAlloc(_) | Sk::Function(_) => false,
                Sk::Struct {
                    ref fields,
                    name: _,
                } => fields.iter().any(|&(_, r)| r == reg),
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
    Int(i128, IntKind),
    /// A struct constant.
    Struct {
        /// The name of the struct type.
        name: Str,
        /// The name and provided value for each field.
        fields: Vec<(Str, Register)>,
    },
    /// A copy of another register's value.
    Copy(Register),
    /// A choice of values based on the immediately preceding block.
    Phi(Map<BlockId, Register>),
    /// An operation on the value of one register.
    UnaryOp(UnaryOp, Register),
    /// An operation on the value of two registers.
    BinOp(BinOp, Register, Register),
    /// Casting an integer value to another integer type.
    IntCast(Register, IntKind),
    /// Casting an pointer inner type to a different type.
    PtrCast(Register, Ty),
    /// A pointer offset from the first register by a number of elements according to the second register. Equivalent to `r1[r2]@`.
    PtrOffset(Register, Register),
    /// A pointer offset to a field of the pointed struct.
    FieldOffset(Register, Str),
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
    #[must_use]
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
            Self::Return(_) => {}
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
