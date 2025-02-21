//! An IR stage deconstructing aggregate types into its individual "base" types.

use crate::compiler_types::{IndexMap, Map, Set, Str};
use crate::ir::*;

type StructFields = Map<Register, (Ty, Vec<PtrOffset>)>;

fn make_struct_fields(
    fields: &IndexMap<Str, Ty>,
    next_register: &mut u128,
    ty_map: &TyMap,
) -> StructFields {
    fn visit(
        this: &mut StructFields,
        prefix: &[PtrOffset],
        fields: &IndexMap<Str, Ty>,
        next_register: &mut u128,
        ty_map: &TyMap,
    ) {
        for (field, &ty) in fields {
            let mut path = prefix.to_vec();
            path.push(PtrOffset::Field(field.clone()));
            match &ty_map[ty] {
                // Types that don't need destructuring
                TyKind::Int(_) | TyKind::Pointer(_) | TyKind::Function { .. }
                | TyKind::Array(..) // TODO
                => {
                    let r = Register(*next_register);
                    *next_register += 1;
                    this.insert(r, (ty, path));
                }
                TyKind::Struct {
                    fields: child_fields,
                    ..
                } => {
                    visit(this, &path, child_fields, next_register, ty_map);
                }
            }
        }
    }
    let mut this = StructFields::new();
    visit(&mut this, &[], fields, next_register, ty_map);
    this
}

pub fn destructure_program(program: &mut Program) {
    let Program {
        functions,
        function_tys,
        tys,
    } = program;
    for f in functions.values_mut() {
        destructure_function(f, tys);
    }
    // For each `Vec<Ty>` (params and returns), we need to expand any struct `Ty` into a list of its fields.
    _ = function_tys;
    /* TODO
    for (params, returns) in function_tys.values_mut() {
        destructure_struct_in_params(params, tys);
        destructure_struct_in_returns(returns, tys);
    }
    */
    // 1. for each ty in the ty map
    #[expect(clippy::needless_collect, reason = "False positive")]
    for ty in tys.inner.keys().copied().collect::<Vec<_>>() {
        let kind = tys.inner.get_mut(&ty).unwrap();
        // 2. if it's a function, mem::take its params and returns
        if let TyKind::Function(params, returns) = kind {
            use std::mem::take;
            let mut params = take(params);
            let mut returns = take(returns);
            destructure_struct_in_params(&mut params, tys);
            destructure_struct_in_returns(&mut returns, tys);
            tys.inner.insert(ty, TyKind::Function(params, returns));
        }
        // pass it to destructure_ty_vec (which no longer has to be recursive) maybe call it destructure_struct_in_function_signature
    }

    // dsifs:
    // 1. for each ty
    // 2. if struct, expand to fields and retape
}

pub fn destructure_function(f: &mut Function, ty_map: &mut TyMap) {
    let struct_regs: Map<Register, StructFields> = f
        .tys
        .iter()
        .filter_map(|(&r, &ty)| match &ty_map[ty] {
            TyKind::Struct { fields, .. } => {
                Some((r, make_struct_fields(fields, &mut f.next_register, ty_map)))
            }
            TyKind::Int(_) | TyKind::Pointer(_) | TyKind::Function { .. }
            | TyKind::Array(..) // TODO
            => None,
        })
        .collect();
    /*
    for (r, fields) in &struct_regs {
        eprintln!("{r}:");
        for (r, (ty, accesses)) in fields {
            eprintln!("    {r}: {accesses:?} {ty}");
        }
    }
    */
    let Function {
        parameters,
        blocks,
        tys,
        spans,
        cfg: _, // does not contain registers
        next_register,
    } = f;

    destructure_vec(&struct_regs, parameters);
    for block in blocks.values_mut() {
        destructure_block(&struct_regs, block, tys, next_register, ty_map);
    }
    for (r, fields) in &struct_regs {
        // NOTE: `destructure_block` relies on getting the type of `r`
        tys.remove(r);
        let span = spans.remove(r).unwrap();
        for (&field_r, (field_ty, _)) in fields {
            tys.insert(field_r, *field_ty);
            spans.insert(field_r, span.clone());
        }
    }
}

fn destructure_block(
    struct_regs: &Map<Register, StructFields>,
    block: &mut Block,
    tys: &mut Map<Register, Ty>,
    next_register: &mut u128,
    ty_map: &mut TyMap,
) {
    let Block {
        insts,
        exit,
        defined_regs,
        used_regs,
    } = block;
    for (r, fields) in struct_regs {
        let destructure_set = |set: &mut Set<Register>| {
            set.remove(r);
            set.extend(fields.keys());
        };
        destructure_set(defined_regs);
        destructure_set(used_regs);
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
        Exit::Return(regs) => destructure_vec(struct_regs, regs),
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
                destructure_vec(struct_regs, returns);
                destructure_vec(struct_regs, args);
            }
            &mut Inst::Write(dst, src) => {
                let Some(fields) = struct_regs.get(&src) else {
                    continue;
                };
                i -= 1;
                insts.remove(i);
                for (&field_r, &(ty, ref accesses)) in fields {
                    let new_ptr = Register(*next_register);
                    *next_register += 1;
                    let ty = ty_map.insert(TyKind::Pointer(ty));
                    tys.insert(new_ptr, ty);
                    let accesses = accesses.iter().cloned().collect();
                    insts.insert(i, Inst::Store(new_ptr, Sk::PtrOffset(dst, accesses)));
                    i += 1;
                    insts.insert(i, Inst::Write(new_ptr, field_r));
                    i += 1;
                }
            }
            &mut Inst::Store(r, ref mut sk) => {
                let Some(fields) = struct_regs.get(&r) else {
                    continue;
                };
                match sk {
                    // we could `do_not_visit` all of these, but that would be annoying
                    Sk::Int(..)
                    | Sk::IntCast(..)
                    | Sk::PtrCast(..)
                    | Sk::PtrOffset(..)
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
                    Sk::Struct { .. } => {
                        i -= 1;
                        let Inst::Store(
                            _,
                            Sk::Struct {
                                fields: literal_fields,
                                ..
                            },
                        ) = insts.remove(i)
                        else {
                            unreachable!();
                        };
                        let mut fields = fields.keys().copied();
                        let mut add_copy = |from_reg| {
                            let r = fields.next().unwrap();
                            insts.insert(i, Inst::Store(r, Sk::Copy(from_reg)));
                            i += 1;
                        };
                        for literal_reg in literal_fields {
                            if let Some(inner_fields) = struct_regs.get(&literal_reg) {
                                for &inner_reg in inner_fields.keys() {
                                    add_copy(inner_reg);
                                }
                            } else {
                                add_copy(literal_reg);
                            }
                        }
                        assert_eq!(fields.next(), None);
                    }
                    &mut Sk::Read(src) => {
                        i -= 1;
                        insts.remove(i);
                        for (&field_r, &(ty, ref accesses)) in fields {
                            let new_ptr = Register(*next_register);
                            *next_register += 1;
                            let ty = ty_map.insert(TyKind::Pointer(ty));
                            tys.insert(new_ptr, ty);
                            let accesses = accesses.iter().cloned().collect();
                            insts.insert(i, Inst::Store(new_ptr, Sk::PtrOffset(src, accesses)));
                            i += 1;
                            insts.insert(i, Inst::Store(field_r, Sk::Read(new_ptr)));
                            i += 1;
                        }
                    }
                }
            }
        }
    }
}

fn destructure_struct_in_params(ty_list: &mut IndexMap<Str, (IsAnon, Ty)>, ty_map: &TyMap) {
    let mut i = 0;
    while let Some((_, &(is_anon, ty))) = ty_list.get_index(i) {
        match &ty_map[ty] {
            TyKind::Struct { fields, .. } => {
                let (name, _) = ty_list.shift_remove_index(i).unwrap();
                let mut field_i = i;
                for (field_name, field_ty) in fields {
                    let new_name = format!("{name}.{field_name}").into();
                    ty_list.shift_insert(field_i, new_name, (is_anon, *field_ty));
                    field_i += 1;
                }
            }
            _ => i += 1,
        }
    }
}

fn destructure_struct_in_returns(ty_list: &mut Vec<Ty>, ty_map: &TyMap) {
    let mut i = 0;
    while let Some(&ty) = ty_list.get(i) {
        match &ty_map[ty] {
            TyKind::Struct { fields, .. } => {
                ty_list.remove(i);
                let mut field_i = i;
                for &field_ty in fields.values() {
                    ty_list.insert(field_i, field_ty);
                    field_i += 1;
                }
            }
            _ => i += 1,
        }
    }
}

fn destructure_vec(struct_regs: &Map<Register, StructFields>, regs: &mut Vec<Register>) {
    // we could write some unsafe code here if this becomes a bottleneck
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
