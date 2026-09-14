use crate::priv_prelude::*;

impl Ty {
    pub fn simplify(
        &self,
        ctx: &mut Vec<Ty>,

        // when we find a constraint, if the index is greater-or-equal to this then return asap.
        // otherwise we are solving under a sum and the constraint might get dropped, so keep going.
        preserved_constraint_depth: usize,
    ) -> Result<Simplification, Uninhabited> {
        match self.clone().reduced().into_inner() {
            TyKind::Form { form } => {
                match &*form {
                    | FormKind::Name
                    | FormKind::Universe
                    | FormKind::Nat
                    | FormKind::Unit
                    => Ok(Simplification::id(self.clone())),

                    FormKind::Never => {
                        Err(Uninhabited {
                            tags: Vec::new(),
                            proof: Scope::id(),
                        })
                    },

                    /*
                    FormKind::Equal { eq_ty, eq_tm_0, eq_tm_1 } => {
                        simplify_equal(
                            ctx, preserved_constraint_depth, self, eq_ty, eq_tm_0, eq_tm_1,
                        )
                    },
                    */

                    FormKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                        simplify_sum(ctx, self, lhs_name, lhs_ty, rhs_ty)
                    },

                    FormKind::Sigma { head_name, head_ty, tail_ty } => {
                        simplify_sigma(
                            ctx, preserved_constraint_depth, self, head_name, head_ty, tail_ty,
                        )
                    },

                    FormKind::Pi { arg_name, arg_ty, res_ty } => {
                        simplify_pi(
                            ctx, preserved_constraint_depth, self, arg_name, arg_ty, res_ty,
                        )
                    },
                }
            },
            TyKind::Neutral { neutral } => {
                let neutral = Arc::unwrap_or_clone(neutral);
                match neutral.kind {
                    NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 } => {
                        simplify_equal(
                            ctx, preserved_constraint_depth, self, &eq_ty, &eq_tm_0, &eq_tm_1,
                        )
                    },
                    _ => {
                        let mut eliminated = Usages::empty();
                        neutral.collect_stuck_vars(&mut eliminated);
                        Ok(Simplification::from_eliminated(self, eliminated))
                    },
                }
            },
        }
    }
}

pub fn simplify_equal(
    ctx: &mut Vec<Ty>,
    _preserved_constraint_depth: usize,
    orig_ty: &Ty,
    eq_ty: &Ty,
    eq_tm_0: &Tm,
    eq_tm_1: &Tm,
) -> Result<Simplification, Uninhabited> {
    if let Some(eq_tm) = Unify::unify(ctx, eq_ty.clone(), eq_tm_0.clone(), eq_tm_1.clone()) {
        let new_ty = Ty::unit();
        let iso = Iso::reflexive_equality_to_unit(eq_tm);
        return Ok(Simplification::from_iso(new_ty, iso));
    }

    if let Some(var_index) = eq_tm_0.as_var() && eq_tm_1.ctx_len() <= var_index {
        let constraint = Constraint {
            unique_tm: eq_tm_1.clone(),
            proof: Scope::id(),
        };
        return Ok(Simplification::from_constraint(orig_ty, var_index, constraint));
    }

    if let Some(var_index) = eq_tm_1.as_var() && eq_tm_0.ctx_len() <= var_index {
        let constraint = Constraint {
            unique_tm: eq_tm_0.clone(),
            proof: Scope::id(),
        };
        return Ok(Simplification::from_constraint(orig_ty, var_index, constraint));
    }

    Ok(Simplification::id(orig_ty.clone()))
}

fn simplify_sum(
    ctx: &mut Vec<Ty>,
    orig_ty: &Ty,
    lhs_name: &Name,
    lhs_ty: &Ty,
    rhs_ty: &Ty,
) -> Result<Simplification, Uninhabited> {
    match (lhs_ty.simplify(ctx, ctx.len()), rhs_ty.simplify(ctx, ctx.len())) {
        (
            Err(Uninhabited { tags: lhs_tags, proof: lhs_proof }),
            Err(Uninhabited { tags: _, proof: rhs_proof }),
        ) => {
            let tags = match rhs_ty.clone().as_never().and_then(|()| lhs_name.as_tag()) {
                Some(tag) => {
                    let mut tags = lhs_tags;
                    tags.push(tag.clone());
                    tags
                },
                None => Vec::new(),
            };
            
            let proof = Scope::make(ctx.len(), |sum| {
                sum.case(
                    Scope::constant(Ty::never()),
                    lhs_proof,
                    rhs_proof,
                )
            });

            Err(Uninhabited { tags, proof })
        },

        (
            Err(Uninhabited { tags: _, proof: lhs_proof }),
            Ok(Simplification { new_ty, iso: rhs_iso, mut constraints, eliminated }),
        ) => {
            let lhs_iso = Iso::scope_never_to_iso_never(lhs_ty.clone(), lhs_proof.clone());
            let iso = Iso::transitivity(
                Iso::sum_congruence(
                    lhs_name.clone(),
                    lhs_name.clone(),
                    lhs_ty.clone(),
                    Ty::never(),
                    rhs_ty.clone(),
                    new_ty.clone(),
                    lhs_iso,
                    rhs_iso,
                ),
                Iso::sum_never_lhs(
                    lhs_name.clone(),
                    new_ty.clone(),
                ),
                orig_ty.clone(),
                new_ty.clone(),
            );

            constraints.map_in_place(ctx.len(), |index, unique_tm, proof, sum| {
                let motive = Ty::obs_equal(
                    ctx[index].clone(),
                    Tm::var(index),
                    unique_tm.clone(),
                );
                sum.case(
                    Scope::constant(motive.clone()),
                    Scope::make(ctx.len() + 1, |lhs| {
                        lhs_proof.clone().bind(lhs).explode(Scope::constant(motive))
                    }),
                    proof,
                )
            });

            Ok(Simplification { new_ty, iso, constraints, eliminated })
        },

        (
            Ok(Simplification { new_ty, iso: lhs_iso, mut constraints, eliminated }),
            Err(Uninhabited { tags: _, proof: rhs_proof }),
        ) => {
            let rhs_iso = Iso::scope_never_to_iso_never(rhs_ty.clone(), rhs_proof.clone());
            let iso = Iso::transitivity(
                Iso::sum_congruence(
                    lhs_name.clone(),
                    lhs_name.clone(),
                    lhs_ty.clone(),
                    new_ty.clone(),
                    rhs_ty.clone(),
                    Ty::never(),
                    lhs_iso,
                    rhs_iso,
                ),
                Iso::sum_never_rhs(
                    lhs_name.clone(),
                    new_ty.clone(),
                ),
                orig_ty.clone(),
                new_ty.clone(),
            );

            constraints.map_in_place(ctx.len(), |index, unique_tm, proof, sum| {
                let motive = Ty::obs_equal(
                    ctx[index].clone(),
                    Tm::var(index),
                    unique_tm.clone(),
                );
                sum.case(
                    Scope::constant(motive.clone()),
                    proof,
                    Scope::make(ctx.len() + 1, |lhs| {
                        rhs_proof.clone().bind(lhs).explode(Scope::constant(motive))
                    }),
                )
            });

            Ok(Simplification { new_ty, iso, constraints, eliminated })
        },

        (
            Ok(Simplification {
                new_ty: lhs_new_ty,
                iso: lhs_iso,
                constraints: lhs_constraints,
                eliminated: lhs_eliminated,
            }),
            Ok(Simplification {
                new_ty: rhs_new_ty,
                iso: rhs_iso,
                constraints: rhs_constraints,
                eliminated: rhs_eliminated,
            }),
        ) => {
            let new_ty = Ty::sum(lhs_name.clone(), lhs_new_ty.clone(), rhs_new_ty.clone());
            let iso = Iso::sum_congruence(
                lhs_name.clone(),
                lhs_name.clone(),
                lhs_ty.clone(),
                lhs_new_ty,
                rhs_ty.clone(),
                rhs_new_ty,
                lhs_iso,
                rhs_iso,
            );

            let constraints = Constraints::intersection(
                ctx,
                lhs_constraints,
                rhs_constraints,
                |ctx, index, unique_tm, lhs_proof, rhs_proof, sum| {
                    sum.case(
                        Scope::constant(
                            Ty::obs_equal(ctx[index].clone(), Tm::var(index), unique_tm.clone()),
                        ),
                        lhs_proof,
                        rhs_proof,
                    )
                },
            );

            let eliminated = Usages::intersection(lhs_eliminated, rhs_eliminated);
            Ok(Simplification { new_ty, iso, constraints, eliminated })
        },
    }
}

fn simplify_sigma(
    ctx: &mut Vec<Ty>,
    preserved_constraint_depth: usize,
    orig_ty: &Ty,
    head_name: &Name,
    head_ty: &Ty,
    tail_ty: &Scope<Ty>,
) -> Result<Simplification, Uninhabited> {
    let Simplification {
        new_ty: head_new_ty,
        iso: head_iso,
        constraints: mut head_constraints,
        eliminated: head_eliminated,
    } = match head_ty.simplify(ctx, preserved_constraint_depth) {
        Err(Uninhabited { mut tags, proof }) => {
            if let Some(tag) = head_name.as_tag() {
                tags.push(tag.clone());
            };
            let proof = Scope::make(ctx.len(), |pair| {
                proof.bind(pair.proj_head())
            });
            return Err(Uninhabited { tags, proof });
        },
        Ok(simplification) => simplification,
    };

    // TODO: consider handling non-dependent seperately (since it's simpler)
    // though it will require deep-normalizing the tail to check if the head's var is used.
    let iso = Iso::dependent_sigma_head_congruence(
        head_name.clone(),
        head_ty.clone(),
        head_new_ty.clone(),
        tail_ty.clone(),
        head_iso.clone(),
    );

    let tail_ty_rescoped = Scope::make(ctx.len(), |head| {
        tail_ty.clone().bind(head_iso.rev.bind(head))
    });
    let new_ty = Ty::sigma(
        head_name.clone(),
        head_new_ty.clone(),
        tail_ty_rescoped.clone(),
    );
    head_constraints.map_in_place(ctx.len(), |_, _, proof, pair| {
        proof.bind(pair.proj_head())
    });

    if head_constraints.has_preserved_constraints(preserved_constraint_depth) {
        return Ok(Simplification {
            new_ty, iso, constraints: head_constraints, eliminated: head_eliminated,
        });
    }

    let (tail_new_ty, tail_iso, mut tail_constraints, mut tail_eliminated) = {
        let tail_ty_rescoped_inner = tail_ty_rescoped.clone().into_inner(ctx.len());
        let simplification_res = {
            ctx.push(head_new_ty.clone());
            let simplification_res = tail_ty_rescoped_inner.simplify(
                ctx, preserved_constraint_depth,
            );
            ctx.pop();
            simplification_res
        };
        match simplification_res {
            Err(Uninhabited { tags, proof }) => {
                let proof = Scope::new(ctx.len(), proof);
                let proof = Scope::make(ctx.len(), |pair| {
                    let pair = iso.fwd.bind(pair);
                    proof
                    .bind(pair.clone().proj_head())
                    .bind(pair.proj_tail())
                });
                return Err(Uninhabited { tags, proof });
            },
            Ok(Simplification {
                new_ty: tail_new_ty,
                iso: tail_iso,
                constraints: tail_constraints,
                eliminated: tail_eliminated,
            }) => {
                let tail_new_ty = Scope::new(ctx.len(), tail_new_ty);
                let tail_iso = Scope::new(ctx.len(), tail_iso);

                (tail_new_ty, tail_iso, tail_constraints, tail_eliminated)
            },
        }
    };

    let new_ty = Ty::sigma(
        head_name.clone(),
        head_new_ty.clone(),
        tail_new_ty.clone(),
    );
    let iso = Iso::transitivity(
        iso,
        Iso::dependent_sigma_tail_congruence(
            head_name.clone(),
            head_new_ty.clone(),
            tail_ty_rescoped,
            tail_new_ty.clone(),
            tail_iso,
        ),
        orig_ty.clone(),
        new_ty.clone(),
    );

    let head_is_eliminated = tail_eliminated.get(ctx.len());
    tail_eliminated.set_to_zero(ctx.len());

    let mut eliminated = head_eliminated.or(tail_eliminated);

    let head_constrained_opt = tail_constraints.pop_at_index(ctx.len());
    tail_constraints.map_in_place(ctx.len(), |_, _, proof, pair| {
        let proof = Scope::new(ctx.len(), proof);
        proof.bind(pair.clone().proj_head()).bind(pair.proj_tail())
    });

    let mut constraints = Constraints::union(
        ctx,
        &iso.fwd,
        head_constraints,
        tail_constraints,
        &mut eliminated,
    )?;

    if let Some(Constraint { unique_tm: unique_head, proof }) = head_constrained_opt {
        let new_ty = tail_new_ty.clone().bind(unique_head.clone());

        let proof = Scope::new(ctx.len(), proof);
        let iso = Iso::transitivity(
            iso,
            Iso::sigma_tail_constrains_head(
                head_name.clone(),
                head_new_ty.clone(),
                tail_new_ty.clone(),
                unique_head.clone(),
                proof,
            ),
            orig_ty.clone(),
            new_ty.clone(),
        );

        constraints.map_in_place(ctx.len(), |_, _, proof, tail| {
            proof.bind(unique_head.clone().pair(tail))
        });

        return Ok(Simplification { new_ty, iso, constraints, eliminated });
    }

    // TODO: split over Nat head

    /*
    if head_is_eliminated
    && let Some(()) = head_new_ty.clone().as_nat()
    {
        let next_new_ty = Ty::sum(
            Name::from("zero"),
            tail_new_ty.clone().bind(Tm::zero()),
            Ty::sum(
                Name::from("succ"),
                Ty::sigma(
                    head_name.clone(),
                    Ty::nat(),
                    Scope::make(ctx.len(), |n| {
                        tail_new_ty.clone().bind(n.succs(Ubig::ONE))
                    }),
                ),
                Ty::never(),
            ),
        );

        let next_iso = Iso::transitivity(
            Iso::dependent_sigma_head_congruence(
                head_name.clone(),
                head_new_ty.clone(),
                Ty::sum(
                    Name::from("zero"),
                    Ty::unit(),
                    Ty::sum(
                        Name::from("succ"),
                        Ty::nat(),
                        Ty::never(),
                    ),
                ),
                tail_new_ty.clone(),
                Iso::never_into_sum_zero_succ(),
            ),
            Iso::
        );

        let iso = 
    }
    */

    if head_is_eliminated
    && let Some((lhs_name, lhs_ty, rhs_ty)) = head_new_ty.clone().as_sum()
    {
        let new_ty = Ty::sum(
            lhs_name.clone(),
            Ty::sigma(
                head_name.clone(),
                lhs_ty.clone(),
                Scope::make(ctx.len(), |lhs| {
                    tail_new_ty.clone().bind(lhs.inj_lhs())
                }),
            ),
            Ty::sigma(
                head_name.clone(),
                rhs_ty.clone(),
                Scope::make(ctx.len(), |rhs| {
                    tail_new_ty.clone().bind(rhs.inj_rhs())
                }),
            ),
        );
        let next_iso = Iso::sigma_sum_head(
            head_name.clone(),
            lhs_name,
            lhs_ty,
            rhs_ty,
            tail_new_ty,
        );
        let iso = Iso::transitivity(
            iso,
            next_iso.clone(),
            orig_ty.clone(),
            new_ty.clone(),
        );
        constraints.map_in_place(ctx.len(), |_, _, proof, sum| {
            proof.bind(next_iso.rev.clone().bind(sum))
        });
        
        let simplification = Simplification { new_ty, iso, constraints, eliminated };
        return simplification.simplify_more(ctx, preserved_constraint_depth, orig_ty);
    }

    if head_is_eliminated
    && let Some((head_head_name, head_head_ty, head_tail_ty)) = head_new_ty.clone().as_sigma()
    {
        let new_ty = Ty::sigma(
            head_head_name.clone(),
            head_head_ty.clone(),
            Scope::make(ctx.len(), |head_head| {
                Ty::sigma(
                    head_name.clone(),
                    head_tail_ty.clone().bind(head_head.clone()),
                    Scope::make(ctx.len() + 1, |head_tail| {
                        tail_ty.clone().bind(head_head.pair(head_tail))
                    }),
                )
            }),
        );
        let next_iso = Iso::sigma_sigma_head();
        let iso = Iso::transitivity(iso, next_iso.clone(), orig_ty.clone(), new_ty.clone());
        constraints.map_in_place(ctx.len(), |_, _, proof, sigma_1| {
            proof.bind(next_iso.rev.clone().bind(sigma_1))
        });
        let simplification = Simplification { new_ty, iso, constraints, eliminated };
        return simplification.simplify_more(ctx, preserved_constraint_depth, orig_ty);
    }

    if let Some(()) = head_new_ty.clone().as_unit() {
        let new_ty = tail_new_ty.bind(Tm::unit());
        let iso = Iso::transitivity(
            iso,
            Iso::sigma_unit_head(),
            orig_ty.clone(),
            new_ty.clone(),
        );
        constraints.map_in_place(ctx.len(), |_, _, proof, tail| {
            proof.bind(Tm::unit().pair(tail))
        });

        return Ok(Simplification { new_ty, iso, constraints, eliminated });
    }

    Ok(Simplification { new_ty, iso, constraints, eliminated })
}

fn simplify_pi(
    ctx: &mut Vec<Ty>,
    preserved_constraint_depth: usize,
    orig_ty: &Ty,
    arg_name: &Name,
    arg_ty: &Ty,
    res_ty: &Scope<Ty>,
) -> Result<Simplification, Uninhabited> {
    let arg_simplification = match arg_ty.simplify(ctx, ctx.len()) {
        Err(Uninhabited { tags: _, proof }) => {
            let new_ty = Ty::unit();
            let arg_iso = Iso::scope_never_to_iso_never(arg_ty.clone(), proof);
            let iso = Iso::transitivity(
                Iso::dependent_pi_arg_congruence(
                    arg_name.clone(),
                    arg_ty.clone(),
                    Ty::never(),
                    res_ty.clone(),
                    arg_iso.clone(),
                ),
                Iso::pi_never_arg(
                    Scope::make(ctx.len(), |never| {
                        res_ty.clone().bind(arg_iso.rev.bind(never))
                    }),
                ),
                orig_ty.clone(),
                new_ty.clone(),
            );
            return Ok(Simplification::from_iso(Ty::unit(), iso));
        },
        Ok(arg_simplification) => arg_simplification,
    };

    let Simplification {
        new_ty: arg_new_ty,
        iso: arg_iso,
        // TODO: can use these for negative reasoning.
        constraints: _arg_constraints,
        eliminated: arg_eliminated,
    } = arg_simplification;

    let iso = Iso::dependent_pi_arg_congruence(
        arg_name.clone(),
        arg_ty.clone(),
        arg_new_ty.clone(),
        res_ty.clone(),
        arg_iso.clone(),
    );

    let res_ty_rescoped = Scope::make(ctx.len(), |arg| {
        res_ty.clone().bind(arg_iso.rev.clone().bind(arg))
    });

    if let Some(()) = arg_new_ty.clone().as_unit() {
        let new_ty = res_ty_rescoped.clone().bind(Tm::unit());
        let iso = Iso::transitivity(
            iso,
            Iso::pi_unit_arg(res_ty_rescoped),
            orig_ty.clone(),
            new_ty.clone(),
        );
        let simplification = Simplification::from_iso(new_ty, iso);
        return simplification.simplify_more(ctx, preserved_constraint_depth, orig_ty);
    }

    let arg_tm_opt = arg_new_ty.clone().try_find_arbitrary_tm(ctx);

    let (res_new_ty, res_iso, mut res_constraints, mut res_eliminated) = {
        let res_ty_rescoped_inner = res_ty_rescoped.clone().into_inner(ctx.len());
        let simplification_res = {
            let preserved_constraint_depth = if arg_tm_opt.is_some() {
                preserved_constraint_depth
            } else {
                ctx.len()
            };
            ctx.push(arg_new_ty.clone());
            let simplification_res = res_ty_rescoped_inner.simplify(
                ctx, preserved_constraint_depth,
            );
            ctx.pop();
            simplification_res
        };

        match simplification_res {
            Err(Uninhabited { tags, proof }) => {
                let proof = Scope::new(ctx.len(), proof);
                match arg_tm_opt {
                    Some(arg_tm) => {
                        let proof = Scope::make(ctx.len(), |func| {
                            proof.bind(arg_tm.clone()).bind(func.app(arg_tm))
                        });
                        return Err(Uninhabited { tags, proof });
                    },
                    None => {
                        let res_iso = Scope::make(ctx.len(), |arg_tm| {
                            Iso::scope_never_to_iso_never(
                                res_ty_rescoped.clone().bind(arg_tm.clone()),
                                proof.bind(arg_tm),
                            )
                        });
                        let new_ty = Ty::pi(
                            arg_name.clone(),
                            arg_new_ty.clone(),
                            Scope::constant(Ty::never()),
                        );
                        let iso = Iso::transitivity(
                            iso,
                            Iso::dependent_pi_res_congruence(
                                arg_name.clone(),
                                arg_new_ty.clone(),
                                res_ty_rescoped,
                                Scope::constant(Ty::never()),
                                res_iso,
                            ),
                            orig_ty.clone(),
                            new_ty.clone(),
                        );
                        return Ok(Simplification::from_iso(new_ty, iso));
                    },
                }
            },
            Ok(Simplification {
                new_ty: res_new_ty,
                iso: res_iso,
                constraints: res_constraints,
                eliminated: res_eliminated,
            }) => {
                let res_new_ty = Scope::new(ctx.len(), res_new_ty);
                let res_iso = Scope::new(ctx.len(), res_iso);
                (res_new_ty, res_iso, res_constraints, res_eliminated)
            },
        }
    };

    let new_ty = Ty::pi(
        arg_name.clone(),
        arg_new_ty.clone(),
        res_new_ty.clone(),
    );
    let iso = Iso::transitivity(
        iso,
        Iso::dependent_pi_res_congruence(
            arg_name.clone(),
            arg_new_ty.clone(),
            res_ty_rescoped.clone(),
            res_new_ty.clone(),
            res_iso,
        ),
        orig_ty.clone(),
        new_ty.clone(),
    );

    let arg_is_eliminated = res_eliminated.get(ctx.len());
    res_eliminated.set_to_zero(ctx.len());

    let eliminated = arg_eliminated.or(res_eliminated);

    let arg_constrained_opt = res_constraints.pop_at_index(ctx.len());
    let mut constraints = match arg_tm_opt {
        None => Constraints::new(),
        Some(arg_tm) => {
            res_constraints.map_in_place(ctx.len(), |_, _, proof, func| {
                let proof = Scope::new(ctx.len(), proof);
                proof.bind(arg_tm.clone()).bind(func.app(arg_tm.clone()))
            });
            res_constraints
        },
    };

    if let Some(Constraint { unique_tm: unique_arg, proof: unique_proof }) = arg_constrained_opt
    && let Some((alt_arg, alt_proof)) = arg_new_ty.try_find_alternate_tm(ctx, unique_arg)
    {
        let unique_proof = Scope::new(ctx.len(), unique_proof);
        let tags = arg_name.as_tag().cloned().into_iter().collect();
        let proof = Scope::make(ctx.len(), |func| {
            alt_proof
            .bind(
                unique_proof
                .bind(alt_arg.clone())
                .bind(iso.fwd.bind(func).app(alt_arg))
            )
        });
        return Err(Uninhabited { tags, proof });
    }

    if arg_is_eliminated {
        // TODO: split arg
    }

    if let Some(res_new_ty) = res_new_ty.clone().try_strengthen().ok()
    && let Some(()) = res_new_ty.clone().as_unit()
    {
        let new_ty = Ty::unit();
        let iso = Iso::transitivity(
            iso,
            Iso::pi_unit_res(),
            orig_ty.clone(),
            new_ty.clone(),
        );
        return Ok(Simplification::from_iso(new_ty, iso));
    }

    let res_new_ty_inner = res_new_ty.clone().into_inner(ctx.len());
    if let Some((head_name, head_ty, tail_ty)) = res_new_ty_inner.clone().as_sigma()
    && let Some(tail_ty) = tail_ty.try_strengthen().ok()
    && let Some(()) = tail_ty.as_unit()
    && let Some(head_tag) = head_name.as_tag()
    && matches!(head_tag.kind, TagKind::Meta { .. })
    && let Some((_, _, _)) = head_ty.clone().as_pi()
    {
        let head_name = Scope::new(ctx.len(), head_name);
        let sub_pi_ty = Scope::new(ctx.len(), head_ty);

        let new_ty = Ty::pi(
            arg_name.clone(),
            arg_new_ty.clone(),
            sub_pi_ty.clone(),
        );
        let iso = Iso::transitivity(
            iso,
            Iso::dependent_pi_res_congruence(
                arg_name.clone(),
                arg_new_ty.clone(),
                Scope::make(ctx.len(), |arg| {
                    Ty::sigma(
                        head_name.bind(arg.clone()),
                        sub_pi_ty.clone().bind(arg),
                        Scope::constant(Ty::unit()),
                    )
                }),
                sub_pi_ty.clone(),
                Scope::constant(Iso::sigma_unit_tail()),
            ),
            orig_ty.clone(),
            Ty::pi(
                arg_name.clone(),
                arg_new_ty.clone(),
                sub_pi_ty,
            ),
        );

        constraints.map_in_place(ctx.len(), |_, _, proof, func| {
            proof.bind(Tm::func(Scope::make(ctx.len() + 1, |arg| {
                Tm::func(Scope::make(ctx.len() + 2, |sub_arg| {
                    func.app(arg).app(sub_arg)
                }))
                .pair(Tm::unit())
            })))
        });

        return Ok(Simplification { new_ty, iso, constraints, eliminated });
    }

    Ok(Simplification { new_ty, iso, constraints, eliminated })
}

