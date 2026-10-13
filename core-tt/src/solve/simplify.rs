use crate::priv_prelude::*;

impl Ty {
    pub fn simplify(
        &self,
        ctx: &mut Vec<Ty>,

        // when we find a constraint, if the index is greater-or-equal to this then return asap.
        // otherwise we are solving under a sum and the constraint might get dropped, so keep going.
        preserved_constraint_depth: usize,
    ) -> Result<Simplification, Uninhabited> {
        //debug!("simplify: {}", debug_print(ctx, self));
        let ret = {
            //debug_indent!();
            self.simplify_inner(ctx, preserved_constraint_depth)
        };
        /*
        match &ret {
            Err(_) => {
                debug!("uninhabited.")
            },
            Ok(simplification) => {
                debug!("got: {}", debug_print(ctx, &simplification.new_ty));
                if !simplification.constraints.is_empty() {
                    debug!("with:");
                    debug_indent!();
                    for (var_index, tm) in simplification.constraints.clone() {
                        debug!("#{} = {}", var_index, debug_print(ctx, &tm))
                    }
                }
            },
        }
        */
        ret
    }

    fn simplify_inner(
        &self,
        ctx: &mut Vec<Ty>,
        preserved_constraint_depth: usize,
    ) -> Result<Simplification, Uninhabited> {
        let this = self.clone().reduced();
        if let Some((_eq_ty, eq_tm_0, eq_tm_1)) = this.clone().as_equal() {
            //debug!("as_equal({}) == ObsEqual({}, {}, {})", debug_print(ctx, &this), debug_print(ctx, &eq_ty), debug_print(ctx, &eq_tm_0), debug_print(ctx, &eq_tm_1));
            return simplify_equal(ctx, &this.into_ty(), &eq_tm_0, &eq_tm_1);
        }

        match this.clone().into_inner() {
            TyKind::Form { form } => {
                match &*form {
                    | FormKind::Name
                    | FormKind::Universe
                    | FormKind::Nat
                    | FormKind::Unit
                    => Ok(Simplification::id(this.into_ty())),

                    FormKind::Never => {
                        Err(Uninhabited::new())
                    },

                    FormKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                        simplify_sum(ctx, lhs_name, lhs_ty, rhs_ty)
                    },

                    FormKind::Sigma { head_name, head_ty, tail_ty } => {
                        simplify_sigma(
                            ctx, preserved_constraint_depth, head_name, head_ty, tail_ty,
                        )
                    },

                    FormKind::Pi { arg_name, arg_ty, res_ty } => {
                        simplify_pi(
                            ctx, preserved_constraint_depth, arg_name, arg_ty, res_ty,
                        )
                    },
                }
            },
            TyKind::Stuck { stuck } => {
                let mut eliminated = Usages::empty();
                stuck.collect_stuck_vars(&mut eliminated);
                Ok(Simplification::from_eliminated(&this.into_ty(), eliminated))
            },
        }
    }
}

pub fn simplify_equal(
    _ctx: &mut Vec<Ty>,
    orig_ty: &Ty,
    eq_tm_0: &Tm,
    eq_tm_1: &Tm,
) -> Result<Simplification, Uninhabited> {
    if let Some(_) = Unify::unify(eq_tm_0.clone(), eq_tm_1.clone()) {
        let new_ty = Ty::unit();
        let iso = Iso::between_props();
        return Ok(Simplification::from_iso(new_ty, iso));
    }

    let eq_tm_0 = eq_tm_0.clone().deep_nf();
    let eq_tm_1 = eq_tm_1.clone().deep_nf();

    if let Some(var_index) = eq_tm_0.usages().as_single_var()
    && eq_tm_1.ctx_len() <= var_index
    && let Some(_) = Unify::unify(Tm::var(var_index), eq_tm_0.clone().into_tm())
    {
        return Ok(Simplification::from_constraint(orig_ty, var_index, eq_tm_1.into_tm()));
    }

    if let Some(var_index) = eq_tm_1.usages().as_single_var()
    && eq_tm_0.ctx_len() <= var_index
    && let Some(_) = Unify::unify(Tm::var(var_index), eq_tm_1.into_tm())
    {
        return Ok(Simplification::from_constraint(orig_ty, var_index, eq_tm_0.into_tm()));
    }

    //debug!("failed to do anything with {}", debug_print(ctx, orig_ty));

    Ok(Simplification::id(orig_ty.clone()))
}

fn simplify_sum(
    ctx: &mut Vec<Ty>,
    lhs_name: &Name,
    lhs_ty: &Ty,
    rhs_ty: &Ty,
) -> Result<Simplification, Uninhabited> {
    match (lhs_ty.simplify(ctx, ctx.len()), rhs_ty.simplify(ctx, ctx.len())) {
        (
            Err(Uninhabited { tags: lhs_tags }),
            Err(Uninhabited { tags: _ }),
        ) => {
            let tags = match rhs_ty.clone().as_never().and_then(|()| lhs_name.clone().as_tag()) {
                Some(tag) => {
                    let mut tags = lhs_tags;
                    tags.push(tag.clone());
                    tags
                },
                None => Vec::new(),
            };
            
            Err(Uninhabited { tags })
        },

        (
            Err(Uninhabited { tags: _ }),
            Ok(Simplification { new_ty, iso: rhs_iso, constraints, eliminated }),
        ) => {
            let lhs_iso = Iso::scope_never_to_iso_never(lhs_ty.clone());
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
            );

            Ok(Simplification { new_ty, iso, constraints, eliminated })
        },

        (
            Ok(Simplification { new_ty, iso: lhs_iso, constraints, eliminated }),
            Err(Uninhabited { tags: _ }),
        ) => {
            let rhs_iso = Iso::scope_never_to_iso_never(rhs_ty.clone());
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
            );

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
                lhs_constraints,
                rhs_constraints,
            );

            let eliminated = Usages::intersection(lhs_eliminated, rhs_eliminated);
            Ok(Simplification { new_ty, iso, constraints, eliminated })
        },
    }
}

fn simplify_sigma(
    ctx: &mut Vec<Ty>,
    preserved_constraint_depth: usize,
    head_name: &Name,
    head_ty: &Ty,
    tail_ty: &Scope<Ty>,
) -> Result<Simplification, Uninhabited> {
    let Simplification {
        new_ty: head_new_ty,
        iso: head_iso,
        constraints: head_constraints,
        eliminated: head_eliminated,
    } = match head_ty.simplify(ctx, preserved_constraint_depth) {
        Err(Uninhabited { mut tags }) => {
            if let Some(tag) = head_name.clone().as_tag() {
                tags.push(tag.clone());
            };
            return Err(Uninhabited { tags });
        },
        Ok(simplification) => simplification,
    };

    // TODO: consider handling non-dependent seperately (since it's simpler)
    // though it will require deep-normalizing the tail to check if the head's var is used.
    let iso = Iso::dependent_sigma_head_congruence(
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

    if head_constraints.has_preserved_constraints(preserved_constraint_depth) {
        return Ok(Simplification {
            new_ty, iso, constraints: head_constraints, eliminated: head_eliminated,
        });
    }

    let (tail_new_ty, tail_iso, mut tail_constraints, mut tail_eliminated) = {
        let tail_ty_rescoped_inner = tail_ty_rescoped.clone().into_inner(ctx.len());
        let Simplification {
            new_ty: tail_new_ty,
            iso: tail_iso,
            constraints: tail_constraints,
            eliminated: tail_eliminated,
        } = {
            ctx.push(head_new_ty.clone());
            let simplification_res = tail_ty_rescoped_inner.simplify(
                ctx, preserved_constraint_depth,
            );
            ctx.pop();
            simplification_res?
        };

        let tail_new_ty = Scope::new(ctx.len(), tail_new_ty);
        let tail_iso = Scope::new(ctx.len(), tail_iso);

        (tail_new_ty, tail_iso, tail_constraints, tail_eliminated)
    };

    let new_ty = Ty::sigma(
        head_name.clone(),
        head_new_ty.clone(),
        tail_new_ty.clone(),
    );
    let iso = Iso::transitivity(iso, Iso::dependent_sigma_tail_congruence(tail_iso));

    let head_is_eliminated = tail_eliminated.get(ctx.len());
    tail_eliminated.set_to_zero(ctx.len());

    let mut eliminated = head_eliminated.or(tail_eliminated);

    let head_constrained_opt = tail_constraints.pop_at_index(ctx.len());

    let constraints = Constraints::union(
        ctx,
        head_constraints,
        tail_constraints,
        &mut eliminated,
    )?;

    if let Some(unique_head) = head_constrained_opt {
        let new_ty = tail_new_ty.clone().bind(unique_head.clone());

        let iso = Iso::transitivity(
            iso,
            Iso::sigma_tail_constrains_head(
                tail_new_ty.clone(),
                unique_head.clone(),
            ),
        );

        let simplification = Simplification { new_ty, iso, constraints, eliminated };
        return simplification.simplify_more(ctx, preserved_constraint_depth);
    }

    if constraints.has_preserved_constraints(preserved_constraint_depth) {
        return Ok(Simplification { new_ty, iso, constraints, eliminated });
    }

    if head_is_eliminated
    && let Some(()) = head_new_ty.clone().as_nat()
    {
        //debug!("spliting sigma nat head");
        let tail_ty_zero = tail_new_ty.clone().bind(Tm::zero());
        let tail_ty_succ = Scope::make(ctx.len(), |n| {
            tail_new_ty.clone().bind(n.succs(Ubig::ONE))
        });

        let new_ty = Ty::sum(
            Name::from("zero"),
            tail_ty_zero,
            Ty::sum(
                Name::from("succ"),
                Ty::sigma(
                    head_name.clone(),
                    Ty::nat(),
                    tail_ty_succ.clone(),
                ),
                Ty::never(),
            ),
        );

        let iso = Iso::transitivity(
            iso,
            Iso::sigma_head_nat_split(head_name.clone(), tail_new_ty.clone()),
        );

        let simplification = Simplification { new_ty, iso, constraints, eliminated };
        return simplification.simplify_more(ctx, preserved_constraint_depth);
    }

    if head_is_eliminated
    && let Some((lhs_name, lhs_ty, rhs_ty)) = head_new_ty.clone().as_sum()
    {
        //debug!("spliting sigma sum head");
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
        );

        let simplification = Simplification { new_ty, iso, constraints, eliminated };
        return simplification.simplify_more(ctx, preserved_constraint_depth);
    }

    if head_is_eliminated
    && let Some((head_head_name, head_head_ty, head_tail_ty)) = head_new_ty.clone().as_sigma()
    {
        //debug!("reassociating sigma");
        let new_ty = Ty::sigma(
            head_head_name.clone(),
            head_head_ty.clone(),
            Scope::make(ctx.len(), |head_head| {
                Ty::sigma(
                    head_name.clone(),
                    head_tail_ty.clone().bind(head_head.clone()),
                    Scope::make(ctx.len() + 1, |head_tail| {
                        tail_new_ty.clone().bind(head_head.pair(head_tail))
                    }),
                )
            }),
        );
        let next_iso = Iso::sigma_sigma_head();
        let iso = Iso::transitivity(iso, next_iso.clone());
        let simplification = Simplification { new_ty, iso, constraints, eliminated };
        return simplification.simplify_more(ctx, preserved_constraint_depth);
    }

    if let Some(()) = head_new_ty.clone().as_unit() {
        let new_ty = tail_new_ty.bind(Tm::proof());
        let iso = Iso::transitivity(
            iso,
            Iso::sigma_unit_head(),
        );

        return Ok(Simplification { new_ty, iso, constraints, eliminated });
    }

    Ok(Simplification { new_ty, iso, constraints, eliminated })
}

fn simplify_pi(
    ctx: &mut Vec<Ty>,
    preserved_constraint_depth: usize,
    arg_name: &Name,
    arg_ty: &Ty,
    res_ty: &Scope<Ty>,
) -> Result<Simplification, Uninhabited> {
    if let Some((new_ty, iso)) = try_distribute_pi_over_sigmas(
        ctx.len(), arg_name.clone(), arg_ty.clone(), res_ty.clone(),
    ) {
        let simplification = Simplification::from_iso(new_ty, iso);
        return simplification.simplify_more(ctx, preserved_constraint_depth);
    }

    let arg_simplification = match arg_ty.simplify(ctx, ctx.len()) {
        Err(Uninhabited { tags: _ }) => {
            let arg_iso = Iso::scope_never_to_iso_never(arg_ty.clone());
            let iso = Iso::transitivity(
                Iso::dependent_pi_arg_congruence(
                    res_ty.clone(),
                    arg_iso.clone(),
                ),
                Iso::pi_never_arg(
                    Scope::make(ctx.len(), |never| {
                        res_ty.clone().bind(arg_iso.rev.bind(never))
                    }),
                ),
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
        res_ty.clone(),
        arg_iso.clone(),
    );

    let res_ty_rescoped = Scope::make(ctx.len(), |arg| {
        res_ty.clone().bind(arg_iso.rev.clone().bind(arg))
    });

    if let Some(()) = arg_new_ty.clone().as_unit() {
        let new_ty = res_ty_rescoped.clone().bind(Tm::proof());
        let iso = Iso::transitivity(iso, Iso::pi_unit_arg());
        let simplification = Simplification::from_iso(new_ty, iso);
        return simplification.simplify_more(ctx, preserved_constraint_depth);
    }

    let arg_ty_inhabited = arg_new_ty.clone().try_find_arbitrary_tm(ctx).is_some();

    let (res_new_ty, res_iso, mut res_constraints, mut res_eliminated) = {
        let res_ty_rescoped_inner = res_ty_rescoped.clone().into_inner(ctx.len());
        let simplification_res = {
            let preserved_constraint_depth = if arg_ty_inhabited {
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
            Err(Uninhabited { tags }) => {
                if arg_ty_inhabited {
                    return Err(Uninhabited { tags });
                }
                let res_iso = Scope::make(ctx.len(), |arg_tm| {
                    Iso::scope_never_to_iso_never(
                        res_ty_rescoped.clone().bind(arg_tm.clone()),
                    )
                });
                let new_ty = Ty::pi(
                    arg_name.clone(),
                    arg_new_ty.clone(),
                    Scope::constant(Ty::never()),
                );
                let iso = Iso::transitivity(
                    iso,
                    Iso::dependent_pi_res_congruence(res_iso),
                );
                return Ok(Simplification::from_iso(new_ty, iso));
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
    let iso = Iso::transitivity(iso, Iso::dependent_pi_res_congruence(res_iso));

    let arg_is_eliminated = res_eliminated.get(ctx.len());
    res_eliminated.set_to_zero(ctx.len());

    let eliminated = arg_eliminated.or(res_eliminated);

    let arg_constrained_opt = res_constraints.pop_at_index(ctx.len());
    let constraints = if arg_ty_inhabited {
        res_constraints
    } else {
        Constraints::new()
    };

    if let Some(unique_arg) = arg_constrained_opt
    && let Some(_) = arg_new_ty.try_find_alternate_tm(ctx, unique_arg)
    {
        let tags = arg_name.clone().as_tag().into_iter().collect();
        return Err(Uninhabited { tags });
    }

    if arg_is_eliminated {
        // TODO: split arg
    }

    if !constraints.is_empty() {
        return Ok(Simplification { new_ty, iso, constraints, eliminated });
    }

    if let Some((new_ty, next_iso)) = try_distribute_pi_over_sigmas(
        ctx.len(), arg_name.clone(), arg_new_ty.clone(), res_new_ty.clone(),
    ) {
        let iso = Iso::transitivity(
            iso,
            next_iso,
        );
        let simplification = Simplification { new_ty, iso, constraints, eliminated };
        return simplification.simplify_more(ctx, preserved_constraint_depth);
    }

    Ok(Simplification { new_ty, iso, constraints, eliminated })
}

fn try_distribute_pi_over_sigmas(
    ctx_len: usize,
    arg_name: Name,
    arg_ty: Ty,
    res_ty: Scope<Ty>,
) -> Option<(Ty, Iso)> {
    let res_ty_inner = res_ty.clone().into_inner(ctx_len);
    if let Some(()) = res_ty_inner.clone().as_unit() {
        let new_ty = Ty::unit();
        let iso = Iso::between_props();
        return Some((new_ty, iso));
    }

    if let Some((head_name, head_ty, tail_ty)) = res_ty_inner.as_sigma()
    && let Some(head_name) = Scope::new(ctx_len, head_name).try_strengthen().ok()
    {
        let head_ty = Scope::new(ctx_len, head_ty);
        let tail_ty = Scope::new(ctx_len, tail_ty);

        let next_tail_ty = Scope::make(ctx_len, |head| {
            Ty::pi(
                arg_name.clone(),
                arg_ty.clone(),
                Scope::make(ctx_len + 1, |arg| {
                    tail_ty.clone().bind(arg.clone()).bind(head.app(arg))
                }),
            )
        });

        let (distributed_head_ty, head_iso) = distribute_pi_over_sigmas(
            ctx_len,
            arg_name.clone(),
            arg_ty.clone(),
            head_ty,
        );
        let (distributed_tail_ty, tail_iso) = distribute_pi_over_sigmas(
            ctx_len + 1,
            arg_name,
            arg_ty,
            Scope::make(ctx_len + 1, |arg| {
                tail_ty.clone().bind(arg.clone()).bind(Tm::var(ctx_len).app(arg))
            }),
        );
        let distributed_tail_ty = Scope::new(ctx_len, distributed_tail_ty);
        let tail_iso = Scope::new(ctx_len, tail_iso);

        let new_ty = Ty::sigma(
            head_name,
            distributed_head_ty,
            Scope::make(ctx_len, |distributed_head| {
                distributed_tail_ty.bind(head_iso.rev.clone().bind(distributed_head))
            }),
        );

        let iso = Iso::transitivity(
            Iso::pi_sigma_res(),
            Iso::transitivity(
                Iso::dependent_sigma_head_congruence(
                    next_tail_ty,
                    head_iso.clone(),
                ),
                Iso::dependent_sigma_tail_congruence(
                    Scope::make(ctx_len, |distributed_head| {
                        tail_iso.bind(head_iso.rev.bind(distributed_head))
                    }),
                ),
            ),
        );

        return Some((new_ty, iso));
    }

    None
}

fn distribute_pi_over_sigmas(
    ctx_len: usize,
    arg_name: Name,
    arg_ty: Ty,
    res_ty: Scope<Ty>,
) -> (Ty, Iso) {
    match try_distribute_pi_over_sigmas(
        ctx_len, arg_name.clone(), arg_ty.clone(), res_ty.clone(),
    ) {
        Some((new_ty, iso)) => (new_ty, iso),
        None => {
            let new_ty = Ty::pi(arg_name, arg_ty, res_ty);
            let iso = Iso::refl();
            (new_ty, iso)
        },
    }
}



#[allow(unused)]
fn debug_print<T: crate::pprint::Pretty<()> + Clone>(
    ctx: &[Ty],
    val: &T,
) -> impl fmt::Display {
    fmt::from_fn(|f| {
        let mut ctx = ctx.iter().map(|ty| (None, Some(ty.clone()))).collect();
        let mut s = String::new();
        crate::pprint::Pretty::pretty(val.clone(), &mut ctx, 0, &mut s, ());
        f.write_str(&s)
    })
}

#[allow(unused)]
fn debug_print_short(ty: Ty, output: &mut String) {
    if let Some(_) = ty.clone().as_equal() {
        output.push('=');
        return;
    }
    match ty.reduced().into_inner() {
        TyKind::Form { form } => {
            match &*form {
                FormKind::Name => {
                    output.push('S');
                },
                FormKind::Universe => {
                    output.push('U');
                },
                FormKind::Nat => {
                    output.push('N');
                },
                FormKind::Never => {
                    output.push('0');
                },
                FormKind::Unit => {
                    output.push('1');
                },
                FormKind::Sum { lhs_name: _, lhs_ty, rhs_ty } => {
                    let mut lhs_ty = lhs_ty.clone();
                    let mut rhs_ty = rhs_ty.clone();
                    output.push('(');
                    loop {
                        debug_print_short(lhs_ty, output);
                        output.push('+');
                        if let Some((_, next_lhs_ty, next_rhs_ty)) = rhs_ty.clone().as_sum() {
                            lhs_ty = next_lhs_ty;
                            rhs_ty = next_rhs_ty;
                            continue;
                        }
                        break;
                    }
                    debug_print_short(rhs_ty, output);
                    output.push(')');
                },
                FormKind::Sigma { head_name: _, head_ty, tail_ty } => {
                    let mut head_ty = head_ty.clone();
                    let mut tail_ty = tail_ty.clone().into_inner(tail_ty.ctx_len());
                    output.push('(');
                    loop {
                        debug_print_short(head_ty, output);
                        output.push('*');
                        if let Some((_, next_head_ty, next_tail_ty)) = tail_ty.clone().as_sigma() {
                            head_ty = next_head_ty;
                            let ctx_len = next_tail_ty.ctx_len();
                            tail_ty = next_tail_ty.into_inner(ctx_len);
                            continue;
                        }
                        break;
                    }
                    debug_print_short(tail_ty, output);
                    output.push(')');
                },
                FormKind::Pi { arg_name: _, arg_ty, res_ty } => {
                    let mut arg_ty = arg_ty.clone();
                    let mut res_ty = res_ty.clone().into_inner(res_ty.ctx_len());
                    output.push('(');
                    loop {
                        debug_print_short(arg_ty, output);
                        output.push_str("->");
                        if let Some((_, next_arg_ty, next_res_ty)) = res_ty.clone().as_pi() {
                            arg_ty = next_arg_ty;
                            let ctx_len = next_res_ty.ctx_len();
                            res_ty = next_res_ty.into_inner(ctx_len);
                            continue;
                        }
                        break;
                    }
                    debug_print_short(res_ty, output);
                    output.push(')');
                },
            }
        },
        TyKind::Stuck { stuck } => {
            if let Some(index) = stuck.as_var() {
                let c = (('a' as u8) + ((index % 26) as u8)) as char;
                for _ in 0..(1 + (index / 26)) {
                    output.push(c);
                }
            } else {
                output.push('?');
            }
        },
    }
}


