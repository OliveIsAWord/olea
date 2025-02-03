// This code is bad!

use crate::ir::*;
use std::fmt::{Display, Formatter, Result};

type F<'a, 'b> = &'a mut Formatter<'b>;

const DISPLAY_TYS: bool = false;

struct SepBy<'a, T, U: ?Sized>(T, &'a U);
impl<T, U> Display for SepBy<'_, T, U>
where
    T: Clone + IntoIterator<Item: Display>,
    U: Display + ?Sized,
{
    fn fmt(&self, f: F) -> Result {
        for (i, item) in self.0.clone().into_iter().enumerate() {
            if i != 0 {
                write!(f, "{}", self.1)?;
            }
            write!(f, "{item}")?;
        }
        Ok(())
    }
}

struct Commas<T>(T);
impl<T> Display for Commas<T>
where
    T: Clone + IntoIterator<Item: Display>,
{
    fn fmt(&self, f: F) -> Result {
        write!(f, "{}", SepBy(self.0.clone(), ", "))
    }
}

struct WithTy<'a, T: ?Sized>(&'a T, &'a Ty);
impl<T: Display + ?Sized> Display for WithTy<'_, T> {
    fn fmt(&self, f: F) -> Result {
        write!(f, "{}", self.0)?;
        if DISPLAY_TYS {
            write!(f, " {}", self.1)?;
        }
        Ok(())
    }
}

// explicit Clone and Copy impls to avoid enforcing that T is Clone or Copy
impl<T> Clone for WithTy<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for WithTy<'_, T> {}

struct Returns<T>(T);
impl<T> Display for Returns<T>
where
    T: Clone + IntoIterator<Item: Display>,
{
    fn fmt(&self, f: F) -> Result {
        let oops: Vec<_> = self.0.clone().into_iter().collect();
        match oops.len() {
            0 => Ok(()),
            1 => write!(f, "{}", oops[0]),
            _ => write!(f, "{{{}}}", Commas(&oops)),
        }
    }
}

struct ReturnsSpace<T>(T);
impl<T> Display for ReturnsSpace<T>
where
    T: Clone + IntoIterator<Item: Display>,
{
    fn fmt(&self, f: F) -> Result {
        let returns = format!("{}", Returns(self.0.clone()));
        if returns.is_empty() {
            Ok(())
        } else {
            write!(f, " {returns}")
        }
    }
}

trait DisplayWithName {
    fn fmt_with_name(&self, f: F, name: &str) -> Result;
    fn with_name<'a>(&'a self, name: &'a str) -> impl Display + 'a
    where
        Self: Sized,
    {
        struct WithName<'a, T>(&'a T, &'a str);
        impl<T: DisplayWithName> Display for WithName<'_, T> {
            fn fmt(&self, f: F) -> Result {
                self.0.fmt_with_name(f, self.1)
            }
        }
        WithName(self, name)
    }
}

impl DisplayWithName for BlockId {
    fn fmt_with_name(&self, f: F, name: &str) -> Result {
        write!(f, "{name}_{}", self.0)
    }
}

impl DisplayWithName for Exit {
    fn fmt_with_name(&self, f: F, name: &str) -> Result {
        match self {
            Self::Jump(loc) => write!(f, "goto {}", loc.with_name(name)),
            Self::CondJump(cond, loc_true, loc_false) => write!(
                f,
                "if {cond}: goto {} else goto {}",
                loc_true.with_name(name),
                loc_false.with_name(name)
            ),
            Self::Return(regs) => write!(f, "return{}", ReturnsSpace(regs)),
        }
    }
}

impl DisplayWithName for Function {
    fn fmt_with_name<'a>(&'a self, f: F, name: &str) -> Result {
        let reg_def = |r: &'a Register| WithTy(r, self.tys.get(r).unwrap());
        write!(
            f,
            "fn {name}({})",
            Commas(self.parameters.iter().map(reg_def)),
        )?;
        for (id, block) in self.iter() {
            write!(f, "\n{}:", id.with_name(name))?;
            for inst in &block.insts {
                write!(f, "\n    ")?;
                match inst {
                    Inst::Store(r, sk) => {
                        use StoreKind as Sk;
                        write!(f, "{} = ", reg_def(r))?;
                        match sk {
                            Sk::StackAlloc(ty) => write!(f, "StackAlloc({ty})"),
                            Sk::Int(i, kind) => write!(f, "{i}_{kind}"),
                            Sk::Copy(r) => write!(f, "{r}"),
                            Sk::Read(r) => write!(f, "{r}^"),
                            Sk::UnaryOp(op, inner) => write!(f, "{}{inner}", match op {
                                UnaryOp::Neg => "-",
                            }),
                            Sk::BinOp(op, lhs, rhs) => write!(f, "{lhs} {} {rhs}", match op {
                                BinOp::Add => "+",
                                BinOp::Sub => "-",
                                BinOp::Mul => "*",
                                BinOp::CmpLe => "<=",
                            }),
                            Sk::IntCast(inner, ty) => write!(f, "{inner} as {ty}"),
                            Sk::PtrCast(pointer, ty) => write!(f, "{pointer} as {ty}^"),
                            Sk::PtrOffset(lhs, rhs) => write!(f, "{lhs}[{rhs}]@"),
                            Sk::FieldOffset(inner, field) => write!(f, "{inner}.{field}@"),
                            Sk::Phi(regs) => write!(
                                f,
                                "Phi({})",
                                Commas(
                                    regs.iter()
                                        .map(|(id, r)| format!("{}: {r}", id.with_name(name)))
                                )
                            ),

                            Sk::Function(name) => write!(f, "{name}"),
                            Sk::Struct { name, fields } => {
                                write!(f, "struct {name}(")?;
                                for (i, (field, val)) in fields.iter().enumerate() {
                                    if i != 0 {
                                        write!(f, ", ")?;
                                    }
                                    write!(f, "{field}: {val}")?;
                                }
                                write!(f, ")")
                            }
                        }
                    }
                    Inst::Write(dst, src) => write!(f, "{dst}^ = {src}"),
                    Inst::Call {
                        callee,
                        returns,
                        args,
                    } => write!(
                        f,
                        "[{}] = {callee}({})",
                        Returns(returns.iter().map(reg_def)),
                        Commas(args)
                    ),
                    Inst::Nop => write!(f, "Nop"),
                }?;
            }
            write!(f, "\n    {}", block.exit.with_name(name))?;
        }
        Ok(())
    }
}

impl Display for Register {
    fn fmt(&self, f: F) -> Result {
        write!(f, "%{}", self.0)
    }
}

impl Display for Condition {
    fn fmt(&self, f: F) -> Result {
        match self {
            Self::NonZero(r) => write!(f, "NonZero({r})"),
        }
    }
}

impl Display for Program {
    fn fmt(&self, f: F) -> Result {
        for (i, (name, function)) in self.functions.iter().enumerate() {
            if i != 0 {
                write!(f, "\n\n")?;
            }
            write!(f, "{}", function.with_name(name))?;
        }
        Ok(())
    }
}

impl Display for Ty {
    fn fmt(&self, f: F) -> Result {
        write!(f, "ty_{}", self.0)
    }
}

impl Display for TyKind {
    fn fmt(&self, f: F) -> Result {
        match self {
            Self::Int(kind) => write!(f, "{kind}"),
            Self::Pointer(inner) => write!(f, "{inner}^"),
            Self::Function(params, returns) => {
                write!(
                    f,
                    "fn({}){}",
                    Commas(params.iter().map(|(name, ty)| format!("{name}: {ty}"))),
                    ReturnsSpace(returns)
                )
            }
            Self::Struct { name, .. } => {
                write!(f, "{name}")
            }
        }
    }
}

impl Display for IntKind {
    fn fmt(&self, f: F) -> Result {
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
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
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
