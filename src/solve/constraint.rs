use crate::priv_prelude::*;

#[derive(Clone)]
pub struct Constraint {
    pub unique_tm: Tm,
    pub proof: Scope<Tm>,
}

impl Constraint {
    pub fn map_all(
        constraints: Vec<(usize, Constraint)>,
        ctx_len: usize,
        mut func: impl FnMut(usize, &Tm, Scope<Tm>, Tm) -> Tm,
    ) -> Vec<(usize, Constraint)> {
        constraints
        .into_iter()
        .map(|(index, Constraint { unique_tm, proof })| {
            let proof = Scope::make(ctx_len, |tm| {
                func(index, &unique_tm, proof, tm)
            });
            (index, Constraint { unique_tm, proof })
        })
        .collect()
    }

    pub fn merge(
        ctx: &mut Vec<Ty>,
        mut constraints_0: Vec<(usize, Constraint)>,
        mut constraints_1: Vec<(usize, Constraint)>,
        eliminated: &mut Usages,
    ) -> Result<Vec<(usize, Constraint)>, Uninhabited> {
        loop {
            if constraints_1.is_empty() {
                break Ok(constraints_0);
            }

            let mut new_constraints_0 = Vec::new();
            let mut new_constraints_1 = Vec::new();
            for (index, which) in merge_enumerated(constraints_0, constraints_1) {
                let (constraint_0, constraint_1) = match which {
                    Which::Left(constraint) | Which::Right(constraint) => {
                        new_constraints_0.push((index, constraint));
                        continue;
                    },
                    Which::Both(constraint_0, constraint_1) => {
                        (constraint_0, constraint_1)
                    },
                };
                let Constraint { unique_tm: unique_tm_0, proof: proof_0 } = constraint_0;
                let Constraint { unique_tm: unique_tm_1, proof: proof_1 } = constraint_1;

                let var_ty = ctx[index].clone();
                if let Some(unique_tm) = Unify::unify(
                    ctx, var_ty.clone(), unique_tm_0.clone(), unique_tm_1.clone(),
                ) {
                    new_constraints_0.push((index, Constraint { unique_tm, proof: proof_0 }));
                    continue;
                }

                let equal_ty = Ty::equal(
                    var_ty.clone(),
                    unique_tm_0.clone(),
                    unique_tm_1.clone(),
                );
                let transitively_eq = Scope::make(ctx.len(), |tm| {
                    proof_0
                    .bind(tm.clone())
                    .symmetry(
                        var_ty.clone(),
                        Tm::var(index),
                    )
                    .transitivity(
                        proof_1.bind(tm),
                        var_ty.clone(),
                        unique_tm_0.clone(),
                        unique_tm_1.clone(),
                    )
                });

                match solve::simplify::simplify_equal(
                    ctx,
                    index,
                    &equal_ty,
                    &var_ty,
                    &unique_tm_0,
                    &unique_tm_1,
                ) {
                    Err(Uninhabited { tags, proof }) => {
                        let proof = Scope::make(ctx.len(), |tm| {
                            proof.bind(transitively_eq.bind(tm))
                        });
                        return Err(Uninhabited { tags, proof });
                    },
                    Ok(Simplification {
                        new_ty: _,
                        iso: equals_iso,
                        constraints: equals_constraints,
                        eliminated: equals_eliminated,
                    }) => {
                        let equals_fwd = equals_iso.fwd;
                        new_constraints_1.extend(
                            equals_constraints
                            .into_iter()
                            .map(|(index, Constraint { unique_tm, proof })| {
                                let proof = Scope::make(ctx.len(), |tm| {
                                    let eq = transitively_eq.clone().bind(tm);
                                    proof.bind(equals_fwd.clone().bind(eq))
                                });
                                (index, Constraint { unique_tm, proof })
                            })
                        );
                        eliminated.or_assign(&equals_eliminated);
                    },
                }
            }
            if true {
                // may contain duplicates though :/
                todo!("sort new_constraints_1");
            }
            constraints_0 = new_constraints_0;
            constraints_1 = new_constraints_1;
        }
    }

    pub fn merge_ng(
        ctx: &mut Vec<Ty>,
        constraints_0: Vec<(usize, Constraint)>,
        constraints_1: Vec<(usize, Constraint)>,
        eliminated: &mut Usages,
    ) -> Result<Vec<(usize, Constraint)>, Uninhabited> {
        use std::collections::{BTreeMap, btree_map};

        let mut constraints: BTreeMap<usize, Constraint> = constraints_0.into_iter().collect(); 
        let mut unprocessed = constraints_1;
        while let Some((index, constraint_1)) = unprocessed.pop() {
            let entry = match constraints.entry(index) {
                btree_map::Entry::Vacant(entry) => {
                    entry.insert(constraint_1);
                    continue;
                },
                btree_map::Entry::Occupied(entry) => entry,
            };

            let Constraint { unique_tm: unique_tm_0, proof: proof_0 } = entry.get().clone();
            let Constraint { unique_tm: unique_tm_1, proof: proof_1 } = constraint_1;
            
            let var_ty = ctx[index].clone();
            if let Some(unique_tm) = Unify::unify(
                ctx, var_ty.clone(), unique_tm_0.clone(), unique_tm_1.clone(),
            ) {
                *entry.into_mut() = Constraint { unique_tm, proof: proof_0 };
                continue;
            }

            let equal_ty = Ty::equal(
                var_ty.clone(),
                unique_tm_0.clone(),
                unique_tm_1.clone(),
            );
            let transitively_eq = Scope::make(ctx.len(), |tm| {
                proof_0
                .bind(tm.clone())
                .symmetry(
                    var_ty.clone(),
                    Tm::var(index),
                )
                .transitivity(
                    proof_1.bind(tm),
                    var_ty.clone(),
                    unique_tm_0.clone(),
                    unique_tm_1.clone(),
                )
            });

            match solve::simplify::simplify_equal(
                ctx,
                index,
                &equal_ty,
                &var_ty,
                &unique_tm_0,
                &unique_tm_1,
            ) {
                Err(Uninhabited { tags, proof }) => {
                    let proof = Scope::make(ctx.len(), |tm| {
                        proof.bind(transitively_eq.bind(tm))
                    });
                    return Err(Uninhabited { tags, proof });
                },
                Ok(Simplification {
                    new_ty: _,
                    iso: equals_iso,
                    constraints: equals_constraints,
                    eliminated: equals_eliminated,
                }) => {
                    let equals_fwd = equals_iso.fwd;
                    unprocessed.extend(
                        equals_constraints
                        .into_iter()
                        .map(|(index, Constraint { unique_tm, proof })| {
                            let proof = Scope::make(ctx.len(), |tm| {
                                let eq = transitively_eq.clone().bind(tm);
                                proof.bind(equals_fwd.clone().bind(eq))
                            });
                            (index, Constraint { unique_tm, proof })
                        })
                    );
                    eliminated.or_assign(&equals_eliminated);
                },
            }
        }

        Ok(constraints.into_iter().collect())
    }
}

