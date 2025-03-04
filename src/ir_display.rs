use crate::compiler_prelude::*;
use crate::ir::*;
use std::fmt::{Display, Formatter, Result, Write};

const DISPLAY_TYS: bool = false;

impl Display for Program {
    fn fmt(&self, f: &mut Formatter) -> Result {
        for (i, (name, function)) in self.functions.iter().enumerate() {
            if i != 0 {
                write!(f, "\n\n")?;
            }
            self.fmt_function(name, function, &mut *f)?;
        }
        Ok(())
    }
}

impl Program {
    fn fmt_function(&self, name: &str, function: &Function, f: &mut impl Write) -> Result {
        let Function {
            parameters,
            blocks,
            tys: _,
            spans: _,
            variables: _,
            cfg: _,
            next_register: _,
        } = function;
        let TyKind::Function {
            has_self,
            params: ref param_tys,
            ref returns,
        } = self.tys[self.function_tys[name]]
        else {
            unreachable!()
        };
        self.tys.fmt_function_signature(
            has_self,
            param_tys,
            returns,
            Some((name, parameters)),
            &mut *f,
        )?;
        write!(f, ": ")?;
        for (&id, block) in blocks {
            writeln!(f)?;
            self.fmt_block(name, function, id, block, &mut *f)?;
        }
        Ok(())
    }
    fn fmt_block(
        &self,
        name: &str,
        function: &Function,
        id: BlockId,
        block: &Block,
        f: &mut impl Write,
    ) -> Result {
        let Block {
            insts,
            exit,
            defined_regs: _,
            used_regs: _,
        } = block;
        self.fmt_block_id(name, id, &mut *f)?;
        writeln!(f, ":")?;
        for inst in insts {
            write!(f, "    ")?;
            self.fmt_inst(function, inst, &mut *f)?;
            writeln!(f)?;
        }
        write!(f, "    ")?;
        self.fmt_exit(name, exit, &mut *f)
    }
    fn fmt_inst(&self, function: &Function, inst: &Inst, f: &mut impl Write) -> Result {
        match *inst {
            Inst::Nop => write!(f, "nop"),
            Inst::Store(r, ref sk) => {
                write!(f, "{r}")?;
                if DISPLAY_TYS {
                    write!(f, ": ")?;
                    self.fmt_ty(function.tys[&r], &mut *f)?;
                }
                write!(f, " = ")?;
                self.fmt_store_kind(sk, &mut *f)
            }
            Inst::Write(dst, src) => {
                write!(f, "{dst}^ = {src}")
            }
            Inst::Call {
                ref returns,
                callee,
                ref args,
            } => {
                write!(f, "[")?;
                {
                    let mut comma = false;
                    for r in returns {
                        if comma {
                            write!(f, ", ")?;
                        }
                        comma = true;
                        write!(f, "{r}")?;
                    }
                }
                write!(f, "] = {callee}(")?;
                {
                    let mut comma = false;
                    for a in args {
                        if comma {
                            write!(f, ", ")?;
                        }
                        comma = true;
                        write!(f, "{a}")?;
                    }
                }
                write!(f, ")")
            }
        }
    }
    fn fmt_store_kind(&self, sk: &StoreKind, f: &mut impl Write) -> Result {
        use StoreKind as Sk;
        match *sk {
            Sk::Bool(b) => write!(f, "{b}"),
            Sk::Int(i, kind) => write!(f, "{i}_{kind}"),
            Sk::Struct { ty, ref fields } => {
                let TyKind::Struct {
                    ref name,
                    fields: ref declared_fields,
                } = self.tys[ty]
                else {
                    unreachable!();
                };
                write!(f, "{name}(")?;
                let mut comma = false;
                for (r, name) in zip(fields, declared_fields.keys()) {
                    if comma {
                        write!(f, ", ")?;
                    }
                    comma = true;
                    write!(f, "{name}: {r}")?;
                }
                write!(f, ")")
            }
            Sk::Copy(r) => write!(f, "{r}"),
            Sk::Phi(ref preds) => {
                write!(f, "phi(")?;
                let mut comma = false;
                for (&id, &r) in preds {
                    if comma {
                        write!(f, ", ")?;
                    }
                    comma = false;
                    write!(f, "{}: {r}", id.0)?;
                }
                write!(f, ")")
            }
            Sk::UnaryOp(op, r) => match op {
                UnaryOp::Neg => write!(f, "-{r}"),
            },
            Sk::BinOp(op, lhs, rhs) => {
                let op = match op {
                    BinOp::Add => "+",
                    BinOp::Sub => "-",
                    BinOp::Mul => "*",
                    BinOp::Div => "/",
                    BinOp::BitAnd => "&",
                    BinOp::BitOr => "|",
                    BinOp::Shl => "<<",
                    BinOp::Shr => ">>",
                    BinOp::Cmp(Cmp::Lt) => "<",
                    BinOp::Cmp(Cmp::Le) => "<=",
                    BinOp::Cmp(Cmp::Eq) => "==",
                    BinOp::Cmp(Cmp::Ne) => "!=",
                    BinOp::Cmp(Cmp::Gt) => ">",
                    BinOp::Cmp(Cmp::Ge) => ">=",
                };
                write!(f, "{lhs} {op} {rhs}")
            }
            Sk::IntCast(r, kind) => write!(f, "{r} as {kind}"),
            Sk::PtrCast(r, ptr) => {
                write!(f, "{r} as ")?;
                self.tys.fmt_kind(&TyKind::Pointer(ptr), &mut *f)
            }
            Sk::PtrOffset(r, ref offsets) => {
                write!(f, "{r}")?;
                for offset in offsets {
                    write!(f, "{offset}")?;
                }
                Ok(())
            }
            Sk::StackAlloc(ty) => {
                write!(f, "alloca ")?;
                self.fmt_ty(ty, &mut *f)
            }
            Sk::Read(r) => write!(f, "{r}^"),
            Sk::Function(ref name) | Sk::Static(ref name) => write!(f, "{name}"),
        }
    }
    fn fmt_exit(&self, name: &str, exit: &Exit, f: &mut impl Write) -> Result {
        match *exit {
            Exit::Jump(id) => {
                write!(f, "goto ")?;
                self.fmt_block_id(name, id, &mut *f)
            }
            Exit::CondJump(r, then_id, else_id) => {
                write!(f, "if {r} goto ")?;
                self.fmt_block_id(name, then_id, &mut *f)?;
                write!(f, "else goto ")?;
                self.fmt_block_id(name, else_id, &mut *f)
            }
            Exit::Return(ref returns) => {
                write!(f, "return")?;
                let mut comma = false;
                for r in returns {
                    if comma {
                        write!(f, ", ")?;
                    } else {
                        write!(f, " ")?;
                        comma = true;
                    }
                    write!(f, "{r}")?;
                }
                Ok(())
            }
        }
    }
    fn fmt_block_id(&self, name: &str, id: BlockId, f: &mut impl Write) -> Result {
        write!(f, "{name}_{}", id.0)
    }
    fn fmt_ty(&self, ty: Ty, f: &mut impl Write) -> Result {
        self.tys.fmt_ty(ty, f)
    }
}

impl TyMap {
    pub fn ty_to_string(&self, index: Ty) -> String {
        self.kind_to_string(&self[index])
    }
    pub fn kind_to_string(&self, kind: &TyKind) -> String {
        let mut buffer = String::new();
        self.fmt_kind(kind, &mut buffer).unwrap();
        buffer
    }
    pub fn fmt_ty(&self, index: Ty, f: &mut impl Write) -> Result {
        self.fmt_kind(&self[index], f)
    }

    pub fn fmt_kind(&self, kind: &TyKind, f: &mut impl Write) -> Result {
        match kind {
            TyKind::Bool => write!(f, "bool"),
            TyKind::Int(size) => write!(f, "{size}"),
            &TyKind::Pointer(Pointer {
                inner,
                kind,
                is_mut,
            }) => {
                self.fmt_ty(inner, &mut *f)?;
                match kind {
                    PointerKind::Single => write!(f, "^")?,
                    PointerKind::Multi => write!(f, "[^]")?,
                }
                match is_mut {
                    IsMut::Mut => write!(f, "mut"),
                    IsMut::Const => Ok(()),
                }
            }
            TyKind::Function {
                has_self,
                params,
                returns,
            } => self.fmt_function_signature(*has_self, params, returns, None, &mut *f),
            TyKind::Struct { name, .. } => write!(f, "{name}"),
            &TyKind::Array(item, count) => {
                self.fmt_ty(item, &mut *f)?;
                write!(f, "[{count}]")
            }
        }
    }
    fn fmt_function_signature(
        &self,
        has_self: bool,
        params: &IndexMap<Str, (IsAnon, Ty)>,
        returns: &[Ty],
        maybe: Option<(&str, &[Register])>,
        f: &mut impl Write,
    ) -> Result {
        let (maybe_name, maybe_params) = maybe.unzip();
        write!(f, "fn")?;
        if let Some(name) = maybe_name {
            write!(f, " {name}")?;
        }
        write!(f, "(")?;
        let mut comma = false;
        if has_self {
            write!(f, "_")?;
            comma = true;
        }
        let mut param_regs = maybe_params.map(|p| p.iter());
        for ty in params {
            if comma {
                write!(f, ", ")?;
            }
            comma = true;
            if let Some(regs) = &mut param_regs {
                write!(f, "{} = ", regs.next().unwrap())?;
            }
            self.fmt_function_parameter(ty, &mut *f)?;
        }
        write!(f, ")")?;
        self.fmt_returns(returns, &mut *f)
    }
    fn fmt_function_parameter(
        &self,
        (p_name, &(is_anon, p_ty)): (&Str, &(IsAnon, Ty)),
        f: &mut impl Write,
    ) -> Result {
        if is_anon == IsAnon::Anon {
            write!(f, "anon ")?;
        }
        write!(f, "{p_name}: ")?;
        self.fmt_ty(p_ty, &mut *f)
    }
    fn fmt_returns(&self, returns: &[Ty], f: &mut impl Write) -> Result {
        match returns.len() {
            0 => Ok(()),
            1 => {
                write!(f, " ")?;
                self.fmt_ty(returns[0], f)
            }
            _ => {
                write!(f, " {{")?;
                self.fmt_ty(returns[0], &mut *f)?;
                for &r in &returns[1..] {
                    self.fmt_ty(r, &mut *f)?;
                }
                write!(f, "}}")
            }
        }
    }
}

impl Display for Register {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "%{}", self.0)
    }
}

impl Display for PtrOffset {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            Self::Field(field) => write!(f, ".{field}"),
            Self::Index(RegisterOrConstant::Register(i)) => write!(f, "[{i}]"),
            Self::Index(RegisterOrConstant::Constant(i)) => write!(f, "[{i}]"),
        }
    }
}

impl Display for IntKind {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let name = match self {
            Self::Usize => "usize",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
        };
        write!(f, "{name}")
    }
}

impl Display for Cfg {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "digraph CFG {{")?;
        for (index, node) in &self.map {
            for succ in &node.successors {
                write!(f, "    \"n{}\" -> \"n{}\"", index.0, succ.0)?;
            }
        }
        write!(f, "}}")?;

        write!(f, "digraph DomTree {{")?;
        for (index, node) in &self.map {
            let Some(parent) = &node.immediate_dominator else {
                continue;
            };
            write!(f, "    \"n{}\" -> \"n{}\"", parent.0, index.0)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}
