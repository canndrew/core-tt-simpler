use crate::priv_prelude::*;

impl Ty {
    pub fn simplify(
        &self,
        ctx: &mut Vec<Ty>,

        // when we find a constraint, if the index is greater-or-equal to this then return asap.
        // otherwise we are solving under a sum and the constraint might get dropped, so keep going.
        preserved_constraint_depth: usize,
        funext: &Tm,
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

                    FormKind::Equal { eq_ty, eq_tm_0, eq_tm_1 } => {
                        simplify_equal(
                            ctx, preserved_constraint_depth, funext, self, eq_ty, eq_tm_0, eq_tm_1,
                        )
                    },

                    FormKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                        simplify_sum(ctx, funext, self, lhs_name, lhs_ty, rhs_ty)
                    },

                    FormKind::Sigma { head_name, head_ty, tail_ty } => {
                        simplify_sigma(
                            ctx, preserved_constraint_depth, funext, self, head_name, head_ty, tail_ty,
                        )
                    },

                    FormKind::Pi { arg_name, arg_ty, res_ty } => {
                        simplify_pi(
                            ctx, preserved_constraint_depth, funext, self, arg_name, arg_ty, res_ty,
                        )
                    },
                }
            },
            TyKind::Neutral { neutral } => {
                let mut eliminated = Usages::empty();
                neutral.collect_stuck_vars(&mut eliminated);
                Ok(Simplification::from_eliminated(self, eliminated))
            },
        }
    }
}

pub fn simplify_equal(
    ctx: &mut Vec<Ty>,
    preserved_constraint_depth: usize,
    funext: &Tm,
    orig_ty: &Ty,
    eq_ty: &Ty,
    eq_tm_0: &Tm,
    eq_tm_1: &Tm,
) -> Result<Simplification, Uninhabited> {
    if let Some(eq_tm) = Unify::unify(ctx, eq_ty.clone(), eq_tm_0.clone(), eq_tm_1.clone()) {
        let new_ty = Ty::unit();
        let iso = Iso::reflexive_equality_to_unit(eq_ty.clone(), eq_tm);
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
            proof: Scope::make(ctx.len(), |eq| {
                eq.symmetry(eq_ty.clone(), eq_tm_0.clone())
            }),
        };
        return Ok(Simplification::from_constraint(orig_ty, var_index, constraint));
    }

    if let Some((eq_ty_eq_ty, eq_ty_eq_tm_0, eq_ty_eq_tm_1)) = eq_ty.clone().as_equal() {
        return Ok(Simplification::from_iso(
            Ty::unit(),
            Iso::equality_of_equalities_to_unit(
                eq_ty_eq_ty,
                eq_ty_eq_tm_0,
                eq_ty_eq_tm_1,
                eq_tm_0.clone(),
                eq_tm_1.clone(),
            ),
        ));
    }

    let (intro_0, intro_1) = match (
        eq_tm_0.clone().try_reduce_to_intro(), 
        eq_tm_1.clone().try_reduce_to_intro(), 
    ) {
        (Some(intro_0), Some(intro_1)) => (intro_0, intro_1),
        _ => return Ok(Simplification::id(orig_ty.clone())),
    };

    let intro_0 = Arc::unwrap_or_clone(intro_0.into_inner());
    let intro_1 = Arc::unwrap_or_clone(intro_1.into_inner());

    let simplification = match (intro_0, intro_1) {
        (IntroKind::Tag { .. }, IntroKind::Tag { .. }) => {
            return Err(Uninhabited::from_proof(
                Scope::make(0, |tm| tm.tags_apart()),
            ));
        },

        (IntroKind::Constant { ubig: ubig_0 }, IntroKind::Constant { ubig: ubig_1 }) => {
            return Err(Uninhabited::from_proof(
                Scope::make(0, |tm| tm.constants_apart(ubig_0, ubig_1)),
            ));
        },

        (IntroKind::Constant { ubig }, IntroKind::Succs { succ_count_m1, pred_tm }) => {
            if ubig <= succ_count_m1 {
                return Err(Uninhabited::from_proof(
                    Scope::make(0, |tm| {
                        tm.succs_injective(Tm::zero(), ubig).zero_isnt_succ()
                    }),
                ));
            } else {
                let succ_count = succ_count_m1 + 1usize;
                let ubig = ubig.strict_sub(&succ_count);
                let new_eq_tm_0 = Tm::constant(ubig);
                let new_eq_tm_1 = Weaken::new(pred_tm).into_tm();

                Simplification::from_iso(
                    Ty::equal(eq_ty.clone(), new_eq_tm_0.clone(), new_eq_tm_1),
                    Iso::succs_of_tms_equal_to_tms_equal(
                        new_eq_tm_0,
                        succ_count,
                    )
                )
            }
        },

        (IntroKind::Succs { succ_count_m1, pred_tm }, IntroKind::Constant { ubig }) => {
            if ubig <= succ_count_m1 {
                let pred_tm = Weaken::new(pred_tm).into_tm();
                return Err(Uninhabited::from_proof(
                    Scope::make(0, |tm| {
                        tm
                        .succs_injective(
                            pred_tm.succs(succ_count_m1.strict_sub(&ubig) + 1usize),
                            ubig,
                        )
                        .succ_isnt_zero()
                    }),
                ));
            } else {
                let succ_count = succ_count_m1 + 1usize;
                let ubig = ubig.strict_sub(&succ_count);
                let new_eq_tm_0 = Weaken::new(pred_tm).into_tm();
                let new_eq_tm_1 = Tm::constant(ubig);
                Simplification::from_iso(
                    Ty::equal(eq_ty.clone(), new_eq_tm_0.clone(), new_eq_tm_1),
                    Iso::succs_of_tms_equal_to_tms_equal(
                        new_eq_tm_0,
                        succ_count,
                    )
                )
            }
        },

        (
            IntroKind::Succs { succ_count_m1: succ_count_m1_0, pred_tm: pred_tm_0 },
            IntroKind::Succs { succ_count_m1: succ_count_m1_1, pred_tm: pred_tm_1 },
        ) => {
            if succ_count_m1_0 <= succ_count_m1_1 {
                let new_eq_tm_0 = Weaken::new(pred_tm_0).into_tm();
                let new_eq_tm_1 = {
                    Weaken::new(pred_tm_1)
                    .into_tm()
                    .succs(succ_count_m1_1.strict_sub(&succ_count_m1_0))
                };
                Simplification::from_iso(
                    Ty::equal(eq_ty.clone(), new_eq_tm_0.clone(), new_eq_tm_1),
                    Iso::succs_of_tms_equal_to_tms_equal(
                        new_eq_tm_0,
                        succ_count_m1_0 + 1usize,
                    )
                )
            } else {
                let new_eq_tm_0 = {
                    Weaken::new(pred_tm_0)
                    .into_tm()
                    .succs(succ_count_m1_0.strict_sub(&succ_count_m1_1))
                };
                let new_eq_tm_1 = Weaken::new(pred_tm_1).into_tm();
                Simplification::from_iso(
                    Ty::equal(eq_ty.clone(), new_eq_tm_0.clone(), new_eq_tm_1),
                    Iso::succs_of_tms_equal_to_tms_equal(
                        new_eq_tm_0,
                        succ_count_m1_1 + 1usize,
                    )
                )
            }
        },

        (IntroKind::InjLhs { lhs_tm: lhs_tm_0 }, IntroKind::InjLhs { lhs_tm: lhs_tm_1 }) => {
            let lhs_tm_0 = Weaken::new(lhs_tm_0);
            let lhs_tm_1 = Weaken::new(lhs_tm_1);
            let (lhs_name, lhs_ty, rhs_ty) = eq_ty.clone().as_sum().unwrap();
            Simplification::from_iso(
                Ty::equal(lhs_ty.clone(), lhs_tm_0.clone(), lhs_tm_1),
                Iso::inj_lhs_of_tms_equal_to_tms_equal(
                    lhs_name, lhs_ty, rhs_ty, lhs_tm_0,
                ),
            )
        },

        (IntroKind::InjRhs { rhs_tm: rhs_tm_0 }, IntroKind::InjRhs { rhs_tm: rhs_tm_1 }) => {
            let rhs_tm_0 = Weaken::new(rhs_tm_0);
            let rhs_tm_1 = Weaken::new(rhs_tm_1);
            let (lhs_name, lhs_ty, rhs_ty) = eq_ty.clone().as_sum().unwrap();
            Simplification::from_iso(
                Ty::equal(rhs_ty.clone(), rhs_tm_0.clone(), rhs_tm_1),
                Iso::inj_rhs_of_tms_equal_to_tms_equal(
                    lhs_name, lhs_ty, rhs_ty, rhs_tm_0,
                ),
            )
        },

        (IntroKind::InjLhs { lhs_tm: lhs_tm_0 }, IntroKind::InjRhs { rhs_tm: _ }) => {
            let lhs_tm_0 = Weaken::new(lhs_tm_0);
            let (_lhs_name, lhs_ty, _rhs_ty) = eq_ty.clone().as_sum().unwrap();
            return Err(Uninhabited::from_proof(
                Scope::make(ctx.len(), |sum_eq| sum_eq.inj_lhs_injective(lhs_ty, lhs_tm_0)),
            ));
        },

        (IntroKind::InjRhs { rhs_tm: rhs_tm_0 }, IntroKind::InjLhs { lhs_tm: _ }) => {
            let rhs_tm_0 = Weaken::new(rhs_tm_0);
            let (_lhs_name, _lhs_ty, rhs_ty) = eq_ty.clone().as_sum().unwrap();
            return Err(Uninhabited::from_proof(
                Scope::make(ctx.len(), |sum_eq| sum_eq.inj_rhs_injective(rhs_ty, rhs_tm_0)),
            ));
        },

        (
            IntroKind::Pair { head_tm: head_tm_0, tail_tm: tail_tm_0 },
            IntroKind::Pair { head_tm: head_tm_1, tail_tm: tail_tm_1 },
        ) => {
            let (head_name, head_ty, tail_ty) = eq_ty.clone().as_sigma().unwrap();
            match tail_ty.try_strengthen() {
                Ok(tail_ty) => {
                    Simplification::from_iso(
                        Ty::sigma(
                            head_name.clone(),
                            Ty::equal(head_ty.clone(), head_tm_0.clone(), head_tm_1.clone()),
                            Scope::constant(
                                Ty::equal(tail_ty.clone(), tail_tm_0.clone(), tail_tm_1.clone()),
                            ),
                        ),
                        Iso::equality_of_non_dependent_pairs_to_non_dependent_pair_of_equalities(
                            head_name,
                            head_ty,
                            tail_ty,
                            head_tm_0,
                            head_tm_1,
                            tail_tm_0,
                            tail_tm_1,
                        ),
                    )
                },
                Err(tail_ty) => {
                    Simplification::from_iso(
                        Ty::sigma(
                            head_name.clone(),
                            Ty::equal(head_ty.clone(), head_tm_0.clone(), head_tm_1.clone()),
                            Scope::make(ctx.len(), |head_eq| {
                                Ty::heterogeneous_equal(
                                    tail_ty.clone().bind(head_tm_0.clone()),
                                    tail_ty.clone().bind_eq(head_tm_0.clone(), head_eq),
                                    tail_tm_0.clone(),
                                    tail_tm_1.clone(),
                                )
                            }),
                        ),
                        Iso::equality_of_dependent_pairs_to_dependent_pair_of_equalities(
                            head_name,
                            head_ty,
                            tail_ty,
                            head_tm_0,
                            head_tm_1,
                            tail_tm_0,
                            tail_tm_1,
                        ),
                    )
                },
            }
        },

        _ => {
            return Ok(Simplification::id(orig_ty.clone()));
        },
    };

    simplification.simplify_more(ctx, preserved_constraint_depth, funext, orig_ty)
}

fn simplify_sum(
    ctx: &mut Vec<Ty>,
    funext: &Tm,
    orig_ty: &Ty,
    lhs_name: &Name,
    lhs_ty: &Ty,
    rhs_ty: &Ty,
) -> Result<Simplification, Uninhabited> {
    match (lhs_ty.simplify(ctx, ctx.len(), funext), rhs_ty.simplify(ctx, ctx.len(), funext)) {
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
                let motive = Ty::equal(
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
                let motive = Ty::equal(
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
                            Ty::equal(ctx[index].clone(), Tm::var(index), unique_tm.clone()),
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
    funext: &Tm,
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
    } = match head_ty.simplify(ctx, preserved_constraint_depth, funext) {
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
                ctx, preserved_constraint_depth, funext,
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
        funext,
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

    if head_is_eliminated {
        // TODO: split head
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
    funext: &Tm,
    orig_ty: &Ty,
    arg_name: &Name,
    arg_ty: &Ty,
    res_ty: &Scope<Ty>,
) -> Result<Simplification, Uninhabited> {
    let arg_simplification = match arg_ty.simplify(ctx, ctx.len(), funext) {
        Err(Uninhabited { tags: _, proof }) => {
            let new_ty = Ty::unit();
            let arg_iso = Iso::scope_never_to_iso_never(arg_ty.clone(), proof);
            let iso = Iso::transitivity(
                Iso::dependent_pi_arg_congruence(
                    funext,
                    arg_name.clone(),
                    arg_ty.clone(),
                    Ty::never(),
                    res_ty.clone(),
                    arg_iso.clone(),
                ),
                Iso::pi_never_arg(
                    funext,
                    arg_name.clone(),
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
        funext,
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
        return simplification.simplify_more(ctx, preserved_constraint_depth, funext, orig_ty);
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
                ctx, preserved_constraint_depth, funext,
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
                                funext,
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
            funext,
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
    let constraints = match arg_tm_opt {
        None => Constraints::new(),
        Some(arg_tm) => {
            res_constraints.map_in_place(ctx.len(), |_, _, proof, func| {
                let proof = Scope::new(ctx.len(), proof);
                proof.bind(arg_tm.clone()).bind(func.app(arg_tm.clone()))
            });
            res_constraints
        },
    };

    if let Some(_arg_constrained) = arg_constrained_opt {
        // TODO: check for contradictions.
    }

    if arg_is_eliminated {
        // TODO: split arg
    }

    if let Some(res_new_ty) = res_new_ty.try_strengthen().ok()
    && let Some(()) = res_new_ty.as_unit()
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

    /*
    if let Some((head_name, head_ty, tail_ty)) = res_new_ty.clone().as_sigma()
    && let Some(tail_ty) = tail_ty.try_strengthen().ok()
    && let Some(()) = tail_ty.as_unit()
    && let Some(head_tag) = head_name.as_tag()
    && matches!(head_tag, TagKind::Meta { .. })
    && let Some((sub_arg_name, sub_arg_ty, sub_res_ty)) = head_ty.as_pi()
    {
        // TODO: inline singleton sigma res
    }
    */

    Ok(Simplification { new_ty, iso, constraints, eliminated })
}

