use crate::compiler_prelude::*;
use crate::ir::*;

type DestructedTys = Map<Ty, Vec<(Vec<PtrOffset>, Ty)>>;
type DestructedRegs = Map<Register, (Ty, Vec<Register>)>;

pub fn destructure_program(program: &mut Program) {
    let Program {
        functions,
        function_tys: _,
        static_values: _,
        tys,
    } = program;

    let destructed_tys: DestructedTys = {
        let mut ty_clusters = Map::<Ty, Vec<(PtrOffset, Ty)>>::new();
        for (&ty, kind) in &tys.inner {
            let cluster = match kind {
                TyKind::Bool | TyKind::Int(_) | TyKind::Pointer(_) | TyKind::Function(..) => {
                    continue;
                }
                TyKind::Struct { fields, .. } => fields
                    .iter()
                    .map(|(name, &ty)| (PtrOffset::Field(name.clone()), ty))
                    .collect(),
                &TyKind::Array(inner_ty, count) => (0..count)
                    .map(|i| (PtrOffset::Index(RegisterOrConstant::Constant(i)), inner_ty))
                    .collect(),
            };
            ty_clusters.insert(ty, cluster);
        }
        fn visit(
            ty: Ty,
            prefix: &mut Vec<PtrOffset>,
            ty_clusters: &Map<Ty, Vec<(PtrOffset, Ty)>>,
            scalars: &mut Vec<(Vec<PtrOffset>, Ty)>,
        ) {
            match ty_clusters.get(&ty) {
                None => scalars.push((prefix.clone(), ty)),
                Some(branches) => {
                    for &(ref offset, ty) in branches {
                        prefix.push(offset.clone());
                        visit(ty, prefix, ty_clusters, scalars);
                        prefix.pop();
                    }
                }
            };
        }
        ty_clusters
            .keys()
            .map(|&ty| {
                let mut scalars = vec![];
                visit(ty, &mut vec![], &ty_clusters, &mut scalars);
                (ty, scalars)
            })
            .collect()
    };

    for (a, b) in &destructed_tys {
        eprintln!("{a} {{");
        for b in b {
            eprintln!(" , {b:?}");
        }
        eprintln!("}}");
    }

    for kind in tys.inner.values_mut() {
        let TyKind::Function(params, returns) = kind else {
            continue;
        };
        assert!(returns.len() <= 1, "idempotence hole");
        if let Some(&return_ty) = returns.get(0) {
            if let Some(scalars) = destructed_tys.get(&return_ty) {
                returns.clear();
                returns.extend(scalars.iter().map(|(_, t)| t));
            }
        }
        let old_params = std::mem::take(params);
        *params = old_params
            .into_iter()
            .flat_map(|(name, (is_anon, ty))| match destructed_tys.get(&ty) {
                None => vec![(name, (is_anon, ty))],
                Some(scalars) => scalars
                    .iter()
                    .map(|&(ref accesses, ty)| {
                        let mut name = name.to_string();
                        for access in accesses {
                            use std::fmt::Write;
                            write!(&mut name, "{access}").unwrap();
                        }
                        (name.into(), (is_anon, ty))
                    })
                    .collect(),
            })
            .collect();
    }

    for f in functions.values_mut() {
        visit_function(f, tys, &destructed_tys);
    }
}
fn visit_function(f: &mut Function, ty_map: &mut TyMap, destructed_tys: &DestructedTys) {
    let Function {
        parameters,
        blocks,
        tys,
        spans,
        cfg: _,
        next_register,
    } = f;
    let mut destructed_regs: DestructedRegs = Map::new();
    for (&r, &ty) in tys.iter() {
        let Some(scalars) = destructed_tys.get(&ty) else {
            continue;
        };
        let scalar_regs = scalars.iter().map(|_| {
            let new_register = Register(*next_register);
            *next_register += 1;
            new_register
        });
        destructed_regs.insert(r, (ty, scalar_regs.collect()));
    }
    for (&r, (ty, scalars)) in &destructed_regs {
        tys.remove(&r).unwrap();
        let span = spans.remove(&r).unwrap();
        for (&scalar, &(_, scalar_ty)) in zip(scalars, &destructed_tys[ty]) {
            tys.insert(scalar, scalar_ty);
            spans.insert(scalar, span.clone());
        }
    }
    destructure_registers(parameters, &destructed_regs);
    for block in blocks.values_mut() {
        visit_block(
            block,
            ty_map,
            destructed_tys,
            &destructed_regs,
            tys,
            next_register,
        );
    }
}

fn visit_block(
    block: &mut Block,
    ty_map: &mut TyMap,
    destructed_tys: &DestructedTys,
    destructed_regs: &DestructedRegs,
    tys: &mut Map<Register, Ty>,
    next_register: &mut u128,
) {
    let Block {
        insts,
        exit,
        defined_regs,
        used_regs,
    } = block;
    for (r, (_, scalars)) in destructed_regs {
        let visit = |set: &mut Set<_>| {
            if set.remove(r) {
                set.extend(scalars);
            }
        };
        visit(defined_regs);
        visit(used_regs);
    }
    // sanity check function: it would be a type error for this register to be a struct
    let do_not_visit = |r: Register| {
        assert!(
            !destructed_regs.contains_key(&r),
            "found struct register {r} in condition"
        );
    };
    match exit {
        Exit::Jump(_) => {}
        Exit::CondJump(r, _, _) => do_not_visit(*r),
        Exit::Return(regs) => destructure_registers(regs, destructed_regs),
    }
    let get = |r: Register| -> Option<(&[_], &[_])> {
        let (old_ty, scalar_regs) = destructed_regs.get(&r)?;
        let fields = &destructed_tys[old_ty];
        Some((scalar_regs.as_ref(), fields.as_ref()))
    };
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
                destructure_registers(returns, destructed_regs);
                destructure_registers(args, destructed_regs);
            }
            &mut Inst::Write(dst, src) => {
                let Some((scalar_regs, fields)) = get(src) else {
                    continue;
                };
                i -= 1;
                insts.remove(i);
                for (&scalar, &(ref accesses, ty)) in zip(scalar_regs, fields) {
                    let new_ptr = Register(*next_register);
                    *next_register += 1;
                    let ty = ty_map.insert(TyKind::Pointer(ty));
                    tys.insert(new_ptr, ty);
                    let accesses = accesses.clone();
                    insts.insert(i, Inst::Store(new_ptr, Sk::PtrOffset(dst, accesses)));
                    i += 1;
                    insts.insert(i, Inst::Write(new_ptr, scalar));
                    i += 1;
                }
            }
            &mut Inst::Store(r, ref mut sk) => {
                let Some((scalar_regs, fields)) = get(r) else {
                    continue;
                };
                match sk {
                    // we could `do_not_visit` all of these, but that would be annoying
                    Sk::Bool(_)
                    | Sk::Int(..)
                    | Sk::IntCast(..)
                    | Sk::PtrCast(..)
                    | Sk::PtrOffset(..)
                    | Sk::StackAlloc(_)
                    | Sk::Function(_)
                    | Sk::Static(_)
                    | Sk::UnaryOp(UnaryOp::Neg, _)
                    | Sk::BinOp(BinOp::Add | BinOp::Mul | BinOp::Sub | BinOp::Cmp(_), _, _) => {
                        unreachable!("illegal op on struct during destructuring: {inst:?}")
                    }
                    &mut Sk::Copy(copied) => {
                        let (copied_regs, _) = get(copied).unwrap();
                        i -= 1;
                        insts.remove(i);
                        for (&r_to, &r_from) in zip(scalar_regs, copied_regs) {
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
                        let pred_scalars: Vec<(BlockId, &[Register])> = preds
                            .into_iter()
                            .map(|(id, r)| (id, get(r).unwrap().0))
                            .collect();
                        for (pred_i, &scalar) in scalar_regs.iter().enumerate() {
                            let field_preds = pred_scalars
                                .iter()
                                .map(|&(id, rs)| (id, rs[pred_i]))
                                .collect();
                            insts.insert(i, Inst::Store(scalar, Sk::Phi(field_preds)));
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
                        let mut literal_fields = literal_fields.clone();
                        destructure_registers(&mut literal_fields, destructed_regs);
                        for (&to, from) in zip(scalar_regs, literal_fields) {
                            insts.insert(i, Inst::Store(to, Sk::Copy(from)));
                            i += 1;
                        }
                    }
                    &mut Sk::Read(src) => {
                        i -= 1;
                        insts.remove(i);
                        for (&field_r, &(ref accesses, ty)) in zip(scalar_regs, fields) {
                            let new_ptr = Register(*next_register);
                            *next_register += 1;
                            let ty = ty_map.insert(TyKind::Pointer(ty));
                            tys.insert(new_ptr, ty);
                            let accesses = accesses.clone();
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

fn destructure_registers(regs: &mut Vec<Register>, destructed_regs: &DestructedRegs) {
    *regs = destructure_registers_cloned(regs, destructed_regs);
}

fn destructure_registers_cloned(
    regs: &[Register],
    destructed_regs: &DestructedRegs,
) -> Vec<Register> {
    regs.iter()
        .flat_map(|&r| match destructed_regs.get(&r) {
            None => vec![r],
            Some((_, rs)) => rs.clone(), // bad clone
        })
        .collect()
}
