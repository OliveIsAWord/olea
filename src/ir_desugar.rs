//! An IR stage deconstructing struct values into its individual fields.

// TODO: Desugar function types with struct arguments/returns.

use crate::compiler_types::{Map, Set, Str};
use crate::ir::*;

type StructFields = Map<Register, (Ty, Vec<Str>)>;

fn make_struct_fields(fields: &[(Str, Ty)], next_register: &mut u128) -> StructFields {
    fn visit(
        this: &mut StructFields,
        prefix: &[Str],
        fields: &[(Str, Ty)],
        next_register: &mut u128,
    ) {
        for (field, ty) in fields {
            let mut path = prefix.to_vec();
            path.push(field.clone());
            match ty {
                // Types that don't need desugaring
                Ty::Int(_) | Ty::Pointer(_) | Ty::Function { .. } => {
                    let r = Register(*next_register);
                    *next_register += 1;
                    this.insert(r, (ty.clone(), path));
                }
                Ty::Struct(child_fields) => {
                    visit(this, &path, child_fields, next_register);
                }
            }
        }
    }
    let mut this = StructFields::new();
    visit(&mut this, &[], fields, next_register);
    this
}

pub fn desugar_program(program: &mut Program) {
    let Program {
        functions,
        function_tys,
    } = program;
    for f in functions.values_mut() {
        desugar_function(f);
    }
    for (params, returns) in function_tys.values_mut() {
        desugar_ty_vec(params);
        desugar_ty_vec(returns);
    }
}

pub fn desugar_function(f: &mut Function) {
    let struct_regs: Map<Register, StructFields> = f
        .tys
        .iter()
        .filter_map(|(&r, ty)| match ty {
            Ty::Struct(fields) => Some((r, make_struct_fields(fields, &mut f.next_register))),
            Ty::Int(_) | Ty::Pointer(_) | Ty::Function { .. } => None,
        })
        .collect();
    for (r, fields) in &struct_regs {
        eprintln!("{r}:");
        for (r, (ty, accesses)) in fields {
            eprintln!("    {r}: {accesses:?} {ty}");
        }
    }
    let Function {
        parameters,
        blocks,
        tys,
        spans,
        cfg: _, // does not contain registers
        next_register,
    } = f;

    desugar_vec(&struct_regs, parameters);
    for block in blocks.values_mut() {
        desugar_block(&struct_regs, block, tys, next_register);
    }
    for (r, fields) in &struct_regs {
        // NOTE: `desugar_block` relies on getting the type of `r`
        tys.remove(r);
        let span = spans.remove(r).unwrap();
        for (&field_r, (field_ty, _)) in fields {
            tys.insert(field_r, field_ty.clone());
            spans.insert(field_r, span.clone());
        }
    }
    for ty in tys.values_mut() {
        desugar_ty(ty);
    }
}

fn desugar_block(
    struct_regs: &Map<Register, StructFields>,
    block: &mut Block,
    tys: &mut Map<Register, Ty>,
    next_register: &mut u128,
) {
    let Block {
        insts,
        exit,
        defined_regs,
        used_regs,
    } = block;
    for (r, fields) in struct_regs {
        let desugar_set = |set: &mut Set<Register>| {
            set.remove(r);
            set.extend(fields.keys());
        };
        desugar_set(defined_regs);
        desugar_set(used_regs);
    }
    // sanity check function: it would be a type error for this register to be a struct
    let do_not_visit = |r: Register| {
        assert!(
            !struct_regs.contains_key(&r),
            "found struct register {r} in condition"
        );
    };
    match exit {
        Exit::Jump(_) => {}
        Exit::CondJump(cond, _, _) => match cond {
            Condition::NonZero(r) => do_not_visit(*r),
        },
        Exit::Return(regs) => desugar_vec(struct_regs, regs),
    }
    let mut i = 0;
    while let Some(inst) = insts.get_mut(i) {
        use StoreKind as Sk;
        i += 1;
        match inst {
            Inst::Nop => {}
            Inst::Call {
                callee,
                returns,
                args,
            } => {
                do_not_visit(*callee);
                desugar_vec(struct_regs, returns);
                desugar_vec(struct_regs, args);
            }
            &mut Inst::Write(dst, src) => {
                let Some(fields) = struct_regs.get(&src) else {
                    continue;
                };
                i -= 1;
                insts.remove(i);
                for (&r, (_, accesses)) in fields {
                    let mut ptr = dst;
                    let mut ty = tys[&src].clone();
                    for access in accesses {
                        ty = {
                            let Ty::Struct(fields) = ty else {
                                unreachable!();
                            };
                            fields
                                .into_iter()
                                .find_map(|(name, ty)| (&name == access).then_some(ty))
                                .unwrap()
                        };
                        let new_ptr = Register(*next_register);
                        *next_register += 1;
                        tys.insert(new_ptr, Ty::Pointer(Box::new(ty.clone())));
                        insts.insert(
                            i,
                            Inst::Store(new_ptr, Sk::FieldOffset(ptr, access.clone())),
                        );
                        i += 1;
                        ptr = new_ptr;
                    }
                    insts.insert(i, Inst::Write(ptr, r));
                    i += 1;
                }
            }
            &mut Inst::Store(r, ref mut sk) => {
                if let Sk::StackAlloc(ty) = sk {
                    eprintln!("before: {ty}");
                    desugar_ty(ty);
                    eprintln!("after:  {ty}");
                }
                let Some(fields) = struct_regs.get(&r) else {
                    continue;
                };
                match sk {
                    // we could `do_not_visit` all of these, but that would be annoying
                    Sk::Int(..)
                    | Sk::IntCast(..)
                    | Sk::PtrOffset(..)
                    | Sk::FieldOffset(..)
                    | Sk::StackAlloc(_)
                    | Sk::Function(_)
                    | Sk::UnaryOp(UnaryOp::Neg, _)
                    | Sk::BinOp(BinOp::Add | BinOp::Mul | BinOp::Sub | BinOp::CmpLe, _, _) => {
                        unreachable!("illegal op on struct during destructuring: {inst:?}")
                    }
                    Sk::Copy(copied) => {
                        let copied_fields = &struct_regs[copied];
                        i -= 1;
                        insts.remove(i);
                        let rs_to = fields.iter().map(|(&r, _)| r);
                        let rs_from = copied_fields.iter().map(|(&r, _)| r);
                        for (r_to, r_from) in rs_to.zip(rs_from) {
                            insts.insert(i, Inst::Store(r_to, Sk::Copy(r_from)));
                            i += 1;
                        }
                    }
                    Sk::Phi(_) => {
                        i -= 1;
                        // we need this to avoid double borrowing
                        let Inst::Store(_, Sk::Phi(preds)) = insts.remove(i) else {
                            unreachable!()
                        };
                        for (&r, (_, name)) in fields {
                            let field_preds = preds
                                .iter()
                                .map(|(&k, v)| {
                                    (
                                        k,
                                        struct_regs[v]
                                            .iter()
                                            .find_map(|(&r2, (_, name2))| {
                                                (name == name2).then_some(r2)
                                            })
                                            .unwrap(),
                                    )
                                })
                                .collect();
                            insts.insert(i, Inst::Store(r, Sk::Phi(field_preds)));
                            i += 1;
                        }
                    }
                    &mut Sk::Read(src) => {
                        i -= 1;
                        insts.remove(i);
                        for (&r2, (_, accesses)) in fields {
                            let mut ptr = src;
                            let mut ty = tys[&r].clone();
                            for access in accesses {
                                ty = {
                                    let Ty::Struct(fields) = ty else {
                                        unreachable!();
                                    };
                                    fields
                                        .into_iter()
                                        .find_map(|(name, ty)| (&name == access).then_some(ty))
                                        .unwrap()
                                };
                                let new_ptr = Register(*next_register);
                                *next_register += 1;
                                tys.insert(new_ptr, Ty::Pointer(Box::new(ty.clone())));
                                insts.insert(
                                    i,
                                    Inst::Store(new_ptr, Sk::FieldOffset(ptr, access.clone())),
                                );
                                i += 1;
                                ptr = new_ptr;
                            }
                            insts.insert(i, Inst::Store(r2, Sk::Read(ptr)));
                            i += 1;
                        }
                    }
                }
            }
        }
    }
}

fn desugar_ty(ty: &mut Ty) {
    match ty {
        Ty::Int(_) => {}
        Ty::Pointer(ty) => desugar_ty(ty),
        Ty::Function(params, returns) => {
            desugar_ty_vec(params);
            desugar_ty_vec(returns);
        }
        Ty::Struct(fields) => {
            for (_, ty) in fields {
                desugar_ty(ty);
            }
        }
    }
}

fn desugar_ty_vec(tys: &mut Vec<Ty>) {
    let mut i = 0;
    while let Some(ty) = tys.get_mut(i) {
        i += 1;
        match ty {
            Ty::Int(_) => {}
            Ty::Pointer(ty) => desugar_ty(ty),
            Ty::Function(params, returns) => {
                desugar_ty_vec(params);
                desugar_ty_vec(returns);
            }
            Ty::Struct(_) => {
                i -= 1;
                let old_i = i;
                let Ty::Struct(fields) = tys.remove(i) else {
                    unreachable!();
                };
                for (_, ty) in fields {
                    tys.insert(i, ty);
                    i += 1;
                }
                i = old_i; // yeah this sucks
            }
        }
    }
}

fn desugar_vec(struct_regs: &Map<Register, StructFields>, regs: &mut Vec<Register>) {
    // we could probably write some unsafe code here if this becomes a bottleneck
    let mut i = 0;
    while i < regs.len() {
        if let Some(fields) = struct_regs.get(&regs[i]) {
            regs.remove(i);
            for &reg in fields.keys() {
                regs.insert(i, reg);
                i += 1;
            }
        } else {
            i += 1;
        }
    }
}
