use crate::priv_prelude::*;

thread_local! {
    //static DEBUG_IDEMPOTENCY: Cell<bool> = const { Cell::new(true) };
    static DEBUG_IDEMPOTENCY: Cell<bool> = const { Cell::new(false) };
}

impl Ty {
    pub fn simplify(
        &self,
        ctx_names_opt: Option<&mut Vec<Name>>,
        ctx: &mut Vec<Ty>,

        // when we find a constraint, if the index is greater-or-equal to this then return asap.
        // otherwise we are solving under a sum and the constraint might get dropped,
        // so keep going.
        preserved_constraint_depth: usize,
        cache: &mut SimplifyCache,

        // The depth of case-splits on sum types we will consider before giving up and
        // back-tracking.
        remaining_case_splits: u32,
    ) -> Result<Simplification, Uninhabited> {
        // FIXME: this should be simplify_with_cache once that's fixed.
        self.clone().reduced().simplify_debug(
            ctx_names_opt, ctx, preserved_constraint_depth, cache, remaining_case_splits, self,
        )
    }
}

impl ValTy {
    // FIXME: cache is broken. Can return spurious hits because it doesn't store contexts and
    // simplify can return different results based on the context.
    //
    // A possible fix: track whether we attempt to use the context and only cache results that
    // don't.
    #[expect(unused)]
    fn simplify_with_cache(
        &self,
        mut ctx_names_opt: Option<&mut Vec<Name>>,
        ctx: &mut Vec<Ty>,
        preserved_constraint_depth: usize,
        cache: &mut SimplifyCache,
        remaining_case_splits: u32,
        orig_ty: &Ty,
    ) -> Result<Simplification, Uninhabited> {
        if let Some(eliminated) = cache.get(self) {
            //return Ok(Simplification::from_eliminated(&self.into_ty(), eliminated));
        }

        let simplification = self.simplify_debug(
            ctx_names_opt, ctx, preserved_constraint_depth, cache, remaining_case_splits, orig_ty,
        )?;

        let undecided = simplification.clone().into_undecided(self.clone().into_ty());
        if undecided.constraints.is_empty() {
            cache.insert(
                &undecided.new_ty(&self.clone().into_ty()).clone().reduced(),
                undecided.eliminated.clone(),
            );
        }
        Ok(simplification)
    }

    fn simplify_debug(
        &self,
        mut ctx_names_opt: Option<&mut Vec<Name>>,
        ctx: &mut Vec<Ty>,
        preserved_constraint_depth: usize,
        cache: &mut SimplifyCache,
        remaining_case_splits: u32,
        orig_ty: &Ty,
    ) -> Result<Simplification, Uninhabited> {
        debug!("simplify: {}", self.clone().pprint(ctx_names_opt.as_mut().unwrap(), ctx, ()));
        let ret = {
            debug_indent!();
            self.simplify(
                ctx_names_opt.as_deref_mut(),
                ctx,
                preserved_constraint_depth,
                cache,
                remaining_case_splits,
                orig_ty,
            )
        };
        match &ret {
            Err(_) => {
                debug!("uninhabited.")
            },
            Ok(Simplification::Unique { .. }) => {
                debug!("solved.")
            },
            Ok(Simplification::Undecided(undecided)) => {
                if let Some(progress) = &undecided.progress_opt {
                    debug!(
                        "got: {}",
                        progress.new_ty.clone().pprint(
                            ctx_names_opt.as_mut().unwrap(), ctx, (),
                        ),
                    );

                    if DEBUG_IDEMPOTENCY.get()
                    && !undecided.constraints.has_preserved_constraints(preserved_constraint_depth)
                    {
                        DEBUG_IDEMPOTENCY.set(false);
                        debug!("testing idempotency");
                        debug_indent!();
                        let new_simplification = progress.new_ty.simplify(
                            ctx_names_opt.as_deref_mut(),
                            ctx,
                            preserved_constraint_depth,
                            cache,
                            remaining_case_splits,
                        ).ok().unwrap();
                        let new_undecided = new_simplification.into_undecided(
                            progress.new_ty.clone(),
                        );
                        if let Some(new_progress) = new_undecided.progress_opt {
                            match Unify::unify(
                                progress.new_ty.clone(),
                                new_progress.new_ty.clone(),
                            ) {
                                Some(_) => {
                                    debug!("spurious progress for type:");
                                    debug!("{}", progress.new_ty.clone().pprint(
                                        ctx_names_opt.as_mut().unwrap(), ctx, (),
                                    ));
                                },
                                None => {
                                    debug!("non-idempotent simplification for type:");
                                    debug!("{}", self.clone().pprint(
                                        ctx_names_opt.as_mut().unwrap(), ctx, (),
                                    ));
                                    debug!("which reduces to:");
                                    debug!("{}", progress.new_ty.clone().pprint(
                                        ctx_names_opt.as_mut().unwrap(), ctx, (),
                                    ));
                                    debug!("and then to:");
                                    debug!("{}", new_progress.new_ty.clone().pprint(
                                        ctx_names_opt.as_mut().unwrap(), ctx, (),
                                    ));
                                },
                            }
                            panic!("oh no");
                        }
                        DEBUG_IDEMPOTENCY.set(true);
                    }
                } else {
                    debug!("unchanged");
                }
                if !undecided.constraints.is_empty() {
                    debug!("with constraints:");
                    debug_indent!();
                    for (var_index, tm) in undecided.constraints.clone() {
                        let var_name = match &mut ctx_names_opt {
                            Some(ctx_names) => {
                                let name = ctx_names[var_index].clone();
                                format!("{}", name.pprint(ctx_names, ctx, ()))
                            },
                            None => format!("#{}", var_index),
                        };
                        let var_ty = ctx[var_index].clone();
                        debug!(
                            "{} = {}",
                            var_name,
                            tm.clone().pprint(ctx_names_opt.as_mut().unwrap(), ctx, var_ty),
                        );
                    }
                }
                if undecided.eliminated.ctx_len() != 0 {
                    if let Some(ctx_names) = ctx_names_opt.as_mut() {
                        let mut names = Vec::with_capacity(undecided.eliminated.count_ones());
                        for index in 0..undecided.eliminated.ctx_len() {
                            if undecided.eliminated.get(index) {
                                let name = ctx_names[index].clone().pprint(
                                    ctx_names, ctx, (),
                                );
                                names.push(name);
                            }
                        }
                        //debug!("with eliminated: {:?}", simplification.eliminated);
                        debug!("with eliminated: {:?}", names)
                    }
                }
            },
        }
        ret
    }

    fn simplify(
        &self,
        mut ctx_names_opt: Option<&mut Vec<Name>>,
        ctx: &mut Vec<Ty>,
        preserved_constraint_depth: usize,
        cache: &mut SimplifyCache,
        remaining_case_splits: u32,
        orig_ty: &Ty,
    ) -> Result<Simplification, Uninhabited> {
        match self.clone().into_inner() {
            TyKind::Form { form } => {
                form.simplify(
                    ctx_names_opt.as_deref_mut(),
                    ctx,
                    preserved_constraint_depth,
                    cache,
                    remaining_case_splits,
                    orig_ty,
                )
            },
            TyKind::Stuck { stuck } => {
                stuck.simplify(preserved_constraint_depth, orig_ty)
            },
        }
    }
}

impl FormKind {
    fn simplify(
        self: &Arc<FormKind>,
        mut ctx_names_opt: Option<&mut Vec<Name>>,
        ctx: &mut Vec<Ty>,
        preserved_constraint_depth: usize,
        cache: &mut SimplifyCache,
        remaining_case_splits: u32,
        orig_ty: &Ty,
    ) -> Result<Simplification, Uninhabited> {
        let simplification = match &**self {
            | FormKind::Name
            | FormKind::Universe
            | FormKind::Nat
            => Simplification::id(),

            FormKind::Unit => {
                Simplification::solved(Tm::proof())
            },

            FormKind::Never => {
                return Err(Uninhabited::new());
            },

            FormKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                simplify_sum(
                    ctx_names_opt,
                    ctx,
                    preserved_constraint_depth,
                    cache,
                    remaining_case_splits,
                    lhs_name,
                    lhs_ty,
                    rhs_ty,
                )?
            },

            FormKind::Sigma { head_name, head_ty, tail_ty } => {
                simplify_sigma(
                    ctx_names_opt,
                    ctx,
                    preserved_constraint_depth,
                    cache,
                    remaining_case_splits,
                    head_name,
                    head_ty,
                    tail_ty,
                )?
            },

            FormKind::Pi { arg_name, arg_ty, res_ty } => {
                let simplification = simplify_pi(
                    ctx_names_opt.as_deref_mut(),
                    ctx,
                    preserved_constraint_depth,
                    cache,
                    remaining_case_splits,
                    arg_name,
                    arg_ty,
                    res_ty,
                )?;
                // debugging
                if let Some(ctx_names) = ctx_names_opt
                && let Some((eq_ty, eq_tm_0, eq_tm_1)) = orig_ty.clone().as_equal()
                {
                    debug!("got equality");
                    debug!("eq_tm_0: {}", eq_tm_0.pprint(ctx_names, ctx, eq_ty.clone()));
                    debug!("eq_tm_1: {}", eq_tm_1.pprint(ctx_names, ctx, eq_ty.clone()));
                }


                simplification.consider_equality(orig_ty)?
            },
        };
        Ok(simplification)
    }
}

impl StuckKind {
    fn simplify(
        self: &StuckKind,
        preserved_constraint_depth: usize,
        orig_ty: &Ty,
    ) -> Result<Simplification, Uninhabited> {
        if let Some((_, eq_tm_0, eq_tm_1)) = orig_ty.clone().as_equal() {
            if let Some(_) = Unify::unify(eq_tm_0.clone(), eq_tm_1.clone()) {
                return Ok(Simplification::solved(Tm::proof()));
            }
            if let Some((var_index, unique_tm)) = Constraints::single_from_equality(
                eq_tm_0, eq_tm_1,
            ) {
                if var_index < preserved_constraint_depth {
                    let constraints = Constraints::single(var_index, unique_tm);
                    let undecided = {
                        Undecided::stuck(self.clone())
                        .with_additional_constraints(constraints)?
                    };
                    return Ok(Simplification::Undecided(undecided));
                }
                return Ok(Simplification::from_constraint(var_index, unique_tm));
            }
        }

        Ok(Simplification::stuck(self.clone()))
    }
}

pub fn try_get_equals_constraint(
    eq_tm_0: &Tm,
    eq_tm_1: &Tm,
) -> Option<(usize, Tm)> {
    let eq_tm_0 = eq_tm_0.clone().deep_nf();
    let eq_tm_1 = eq_tm_1.clone().deep_nf();

    if let Some(var_index) = eq_tm_0.usages().as_single_var()
    && eq_tm_1.ctx_len() <= var_index
    && let Some(_) = Unify::unify(Tm::var(var_index), eq_tm_0.clone().into_tm())
    {
        return Some((var_index, eq_tm_1.into_tm()));
    }

    if let Some(var_index) = eq_tm_1.usages().as_single_var()
    && eq_tm_0.ctx_len() <= var_index
    && let Some(_) = Unify::unify(Tm::var(var_index), eq_tm_1.clone().into_tm())
    {
        return Some((var_index, eq_tm_0.into_tm()));
    }

    None
}

fn simplify_sum(
    mut ctx_names_opt: Option<&mut Vec<Name>>,
    ctx: &mut Vec<Ty>,
    preserved_constraint_depth: usize,
    cache: &mut SimplifyCache,
    remaining_case_splits: u32,
    lhs_name: &Name,
    lhs_ty: &Ty,
    rhs_ty: &Ty,
) -> Result<Simplification, Uninhabited> {
    let Some(next_remaining_case_splits) = remaining_case_splits.checked_sub(1) else {
        debug!("hit case-split limit");
        return Ok(Simplification::hit_case_split_limit());
    };

    match (
        lhs_ty.simplify(
            ctx_names_opt.as_deref_mut(),
            ctx,
            ctx.len(),
            cache,
            next_remaining_case_splits,
        ),
        rhs_ty.simplify(
            ctx_names_opt.as_deref_mut(),
            ctx,
            ctx.len(),
            cache,
            next_remaining_case_splits,
        ),
    ) {
        (
            Err(Uninhabited { mut tag }),
            Err(Uninhabited { tag: _ }),
        ) => {
            if let Some(()) = rhs_ty.clone().as_never()
            && let Some(lhs_tag) = lhs_name.clone().as_tag()
            {
                tag = Tag::concat([tag, lhs_tag]);
            }
            
            Err(Uninhabited { tag })
        },

        (
            Err(Uninhabited { tag: _ }),
            Ok(Simplification::Unique { unique_tm }),
        ) => {
            let unique_tm = unique_tm.inj_rhs();
            Ok(Simplification::Unique { unique_tm })
        },

        (
            Ok(Simplification::Unique { unique_tm }),
            Err(Uninhabited { tag: _ }),
        ) => {
            let unique_tm = unique_tm.inj_lhs();
            Ok(Simplification::Unique { unique_tm })
        },

        (
            Err(Uninhabited { tag: _ }),
            Ok(Simplification::Undecided(Undecided {
                progress_opt, constraints, eliminated, hit_case_split_limit,
            })),
        ) => {
            let Progress { new_ty, iso } = {
                progress_opt.unwrap_or_else(|| Progress::id(rhs_ty.clone()))
            };
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
                    iso,
                ),
                Iso::sum_never_lhs(
                    lhs_name.clone(),
                    new_ty.clone(),
                ),
            );
            let progress = Progress { new_ty, iso };

            if hit_case_split_limit {
                progress.simplify_more(
                    ctx_names_opt,
                    ctx,
                    preserved_constraint_depth,
                    cache,
                    remaining_case_splits,
                )
            } else {
                Ok(Simplification::Undecided(Undecided {
                    progress_opt: Some(progress), constraints, eliminated, hit_case_split_limit,
                }))
            }
        },

        (
            Ok(Simplification::Undecided(Undecided {
                progress_opt, constraints, eliminated, hit_case_split_limit,
            })),
            Err(Uninhabited { tag: _ }),
        ) => {
            let Progress { new_ty, iso } = {
                progress_opt.unwrap_or_else(|| Progress::id(lhs_ty.clone()))
            };
            let rhs_iso = Iso::scope_never_to_iso_never(rhs_ty.clone());
            let iso = Iso::transitivity(
                Iso::sum_congruence(
                    lhs_name.clone(),
                    lhs_name.clone(),
                    lhs_ty.clone(),
                    new_ty.clone(),
                    rhs_ty.clone(),
                    Ty::never(),
                    iso,
                    rhs_iso,
                ),
                Iso::sum_never_rhs(
                    lhs_name.clone(),
                    new_ty.clone(),
                ),
            );
            let progress = Progress { new_ty, iso };

            if hit_case_split_limit {
                progress.simplify_more(
                    ctx_names_opt,
                    ctx,
                    preserved_constraint_depth,
                    cache,
                    remaining_case_splits,
                )
            } else {
                Ok(Simplification::Undecided(Undecided {
                    progress_opt: Some(progress), constraints, eliminated, hit_case_split_limit,
                }))
            }
        },

        (
            Ok(lhs_simplification),
            Ok(rhs_simplification),
        ) => {
            let Undecided {
                progress_opt: lhs_progress_opt,
                constraints: lhs_constraints,
                eliminated: lhs_eliminated,
                hit_case_split_limit: lhs_hit_case_split_limit,
            } = lhs_simplification.into_undecided(lhs_ty.clone());
            let Undecided {
                progress_opt: rhs_progress_opt,
                constraints: rhs_constraints,
                eliminated: rhs_eliminated,
                hit_case_split_limit: rhs_hit_case_split_limit,
            } = rhs_simplification.into_undecided(rhs_ty.clone());

            let progress_opt = match (lhs_progress_opt, rhs_progress_opt) {
                (None, None) => None,
                (lhs_progress_opt, rhs_progress_opt) => {
                    let Progress { new_ty: lhs_new_ty, iso: lhs_iso } = {
                        lhs_progress_opt.unwrap_or_else(|| Progress::id(lhs_ty.clone()))
                    };
                    let Progress { new_ty: rhs_new_ty, iso: rhs_iso } = {
                        rhs_progress_opt.unwrap_or_else(|| Progress::id(rhs_ty.clone()))
                    };
                    let new_ty = Ty::sum(
                        lhs_name.clone(), lhs_new_ty.clone(), rhs_new_ty.clone(),
                    );
                    let iso = Iso::sum_congruence(
                        lhs_name.clone(),
                        lhs_name.clone(),
                        lhs_ty.clone(),
                        lhs_new_ty.clone(),
                        rhs_ty.clone(),
                        rhs_new_ty,
                        lhs_iso,
                        rhs_iso,
                    );
                    Some(Progress { new_ty, iso })
                },
            };
            let constraints = Constraints::intersection(
                lhs_constraints,
                rhs_constraints,
            );
            let eliminated = Usages::intersection(lhs_eliminated, rhs_eliminated);
            let hit_case_split_limit = lhs_hit_case_split_limit || rhs_hit_case_split_limit;
            Ok(Simplification::Undecided(Undecided {
                progress_opt, constraints, eliminated, hit_case_split_limit,
            }))
        },
    }
}

fn simplify_sigma(
    mut ctx_names_opt: Option<&mut Vec<Name>>,
    ctx: &mut Vec<Ty>,
    preserved_constraint_depth: usize,
    cache: &mut SimplifyCache,
    remaining_case_splits: u32,
    head_name: &Name,
    head_ty: &Ty,
    tail_ty: &Scope<Ty>,
) -> Result<Simplification, Uninhabited> {
    let head_undecided = match head_ty.simplify(
        ctx_names_opt.as_deref_mut(),
        ctx,
        preserved_constraint_depth,
        cache,
        remaining_case_splits,
    ) {
        Err(Uninhabited { mut tag }) => {
            if let Some(head_tag) = head_name.clone().as_tag() {
                tag = Tag::concat([head_tag, tag]);
            };
            return Err(Uninhabited { tag });
        },
        Ok(Simplification::Unique { unique_tm: head_unique_tm }) => {
            let iso = Iso::transitivity(
                Iso::dependent_sigma_head_congruence(
                    tail_ty.clone(),
                    Iso::uniquely_inhabited_to_unit(head_unique_tm.clone()),
                ),
                Iso::sigma_unit_head(),
            );

            let rescoped_tail_ty = tail_ty.clone().bind(head_unique_tm.clone());
            let tail_undecided = match rescoped_tail_ty.clone().simplify(
                ctx_names_opt.as_deref_mut(),
                ctx,
                preserved_constraint_depth,
                cache,
                remaining_case_splits,
            )? {
                Simplification::Unique { unique_tm: tail_unique_tm } => {
                    let unique_tm = head_unique_tm.pair(tail_unique_tm);
                    return Ok(Simplification::Unique { unique_tm });
                },
                Simplification::Undecided(undecided) => undecided,
            };
            let Undecided {
                progress_opt, constraints, eliminated, hit_case_split_limit,
            } = tail_undecided;

            let progress = match progress_opt {
                None => Progress { new_ty: rescoped_tail_ty, iso },
                Some(Progress { new_ty, iso: tail_iso }) => {
                    let iso = Iso::transitivity(iso, tail_iso);
                    Progress { new_ty, iso }
                },
            };
            return Ok(Simplification::Undecided(Undecided {
                progress_opt: Some(progress), constraints, eliminated, hit_case_split_limit,
            }));
        },
        Ok(Simplification::Undecided(undecided)) => undecided,
    };

    let Undecided {
        progress_opt: head_progress_opt,
        constraints: head_constraints,
        eliminated: head_eliminated,
        hit_case_split_limit: head_hit_case_split_limit,
    } = head_undecided;

    let Progress { new_ty: head_new_ty, iso: head_iso } = {
        head_progress_opt.clone().unwrap_or_else(|| Progress::id(head_ty.clone()))
    };
    let iso = Iso::dependent_sigma_head_congruence(tail_ty.clone(), head_iso.clone());
    let tail_ty_rescoped = Scope::make(ctx.len(), |head| {
        tail_ty.clone().bind(head_iso.rev.clone().bind(head))
    });

    if head_constraints.has_preserved_constraints(preserved_constraint_depth) {
        let progress_opt = head_progress_opt.map(|_| {
            let new_ty = Ty::sigma(head_name.clone(), head_new_ty, tail_ty_rescoped);
            Progress { new_ty, iso }
        });
        return Ok(Simplification::Undecided(Undecided {
            progress_opt,
            constraints: head_constraints,
            eliminated: head_eliminated,
            hit_case_split_limit: head_hit_case_split_limit,
        }));
    }

    let tail_undecided = match tail_ty_rescoped.simplify(
        ctx_names_opt.as_deref_mut().map(|names| (names, head_name)),
        ctx,
        preserved_constraint_depth,
        cache,
        remaining_case_splits,
        &head_new_ty,
    )? {
        Ok(tail_unique_tm) => {
            let iso = Iso::transitivity(
                iso,
                Iso::dependent_sigma_tail_congruence(
                    Scope::make(ctx.len(), |head| {
                        Iso::uniquely_inhabited_to_unit(tail_unique_tm.bind(head))
                    }),
                ),
            );
            let progress_opt = {
                if let Some(head_form) = head_new_ty.clone().reduced().into_inner().as_form()
                && matches!(&*head_form, FormKind::Unit | FormKind::Sigma { .. })
                {
                    let new_ty = head_new_ty;
                    let iso = Iso::transitivity(iso, Iso::sigma_unit_tail());
                    Some(Progress { new_ty, iso })
                } else if {
                    head_progress_opt.is_some() ||
                    tail_ty.clone().into_inner(ctx.len()).as_unit().is_none()
                } {
                    let new_ty = Ty::sigma(
                        head_name.clone(),
                        head_new_ty,
                        Scope::constant(Ty::unit()),
                    );
                    Some(Progress { new_ty, iso })
                } else {
                    None
                }
            };
            return Ok(Simplification::Undecided(Undecided {
                progress_opt,
                constraints: head_constraints,
                eliminated: head_eliminated,
                hit_case_split_limit: head_hit_case_split_limit,
            }));
        },
        Err(undecided) => undecided,
    };

    let UnscopedUndecided {
        progress_opt: tail_progress_opt,
        constraints: tail_constraints,
        eliminated: tail_eliminated,
        hit_case_split_limit: tail_hit_case_split_limit,
        var_constraint_opt,
        var_eliminated,
    } = tail_undecided;

    if let Some(head_unique_tm) = var_constraint_opt {
        let Progress { new_ty, iso: tail_iso } = match tail_progress_opt.clone() {
            Some(tail_progress) => tail_progress.bind(head_unique_tm.clone()),
            None => Progress::id(tail_ty_rescoped.clone().bind(head_unique_tm.clone())),
        };
        let progress = Progress {
            new_ty,
            iso: Iso::transitivity(
                Iso::transitivity(
                    iso,
                    Iso::sigma_tail_constrains_head(
                        tail_ty_rescoped.clone(), head_unique_tm,
                    ),
                ),
                tail_iso,
            ),
        };
        return progress.simplify_more(
            ctx_names_opt,
            ctx,
            preserved_constraint_depth,
            cache,
            remaining_case_splits,
        );
    }

    let (tail_new_ty, tail_iso) = {
        tail_progress_opt
        .clone()
        .unwrap_or_else(|| {
            Scope::make(ctx.len(), |head| {
                Progress::id(tail_ty_rescoped.clone().bind(head))
            })
        })
        .lift_progress()
    };
    let iso = Iso::transitivity(
        iso,
        Iso::dependent_sigma_tail_congruence(tail_iso),
    );
    let progress_opt = match (head_progress_opt, tail_progress_opt) {
        (None, None) => None,
        (_, _) => {
            Some(Progress {
                new_ty: Ty::sigma(head_name.clone(), head_new_ty.clone(), tail_new_ty.clone()),
                iso: iso.clone(),
            })
        },
    };

    let constraints = Constraints::union(head_constraints, tail_constraints)?;
    let eliminated = head_eliminated.or(tail_eliminated);
    let hit_case_split_limit = head_hit_case_split_limit || tail_hit_case_split_limit;

    if constraints.has_preserved_constraints(preserved_constraint_depth) {
        return Ok(Simplification::Undecided(Undecided {
            progress_opt, constraints, eliminated, hit_case_split_limit,
        }))
    }

    if var_eliminated && let Some(head_form) = head_new_ty.clone().try_reduce_to_form() {
        match Arc::unwrap_or_clone(head_form.into_inner()) {
            FormKind::Nat => {
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
                let progress = Progress { new_ty, iso };
                return progress.simplify_more(
                    ctx_names_opt,
                    ctx,
                    preserved_constraint_depth,
                    cache,
                    remaining_case_splits,
                );
            },

            FormKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
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
                let iso = Iso::transitivity(
                    iso,
                    Iso::sigma_sum_head(
                        head_name.clone(),
                        lhs_name,
                        lhs_ty,
                        rhs_ty,
                        tail_new_ty,
                    ),
                );
                let progress = Progress { new_ty, iso };
                return progress.simplify_more(
                    ctx_names_opt,
                    ctx,
                    preserved_constraint_depth,
                    cache,
                    remaining_case_splits,
                );
            },

            FormKind::Sigma {
                head_name: head_head_name,
                head_ty: head_head_ty,
                tail_ty: head_tail_ty,
            } => {
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
                let iso = Iso::transitivity(
                    iso,
                    Iso::sigma_sigma_head(),
                );
                let progress = Progress { new_ty, iso };
                return progress.simplify_more(
                    ctx_names_opt,
                    ctx,
                    preserved_constraint_depth,
                    cache,
                    remaining_case_splits,
                );
            },

            FormKind::Pi { arg_name, arg_ty, res_ty: head_res_ty } => {
                if let Some((tail_res_ty, tail_iso)) = try_factor_pi_from_sigma_tail(
                    ctx.len(), arg_name.clone(), arg_ty.clone(), tail_new_ty.clone(),
                ) {
                    let new_ty = Ty::pi(
                        arg_name,
                        arg_ty,
                        Scope::make(ctx.len(), |arg| {
                            Ty::sigma(
                                head_name.clone(),
                                head_res_ty.bind(arg.clone()),
                                tail_res_ty.bind(arg),
                            )
                        }),
                    );
                    let iso = Iso::transitivity(
                        iso,
                        Iso::transitivity(
                            Iso::dependent_sigma_tail_congruence(tail_iso),
                            Iso::pi_sigma_res().symmetry(),
                        ),
                    );

                    let progress = Progress { new_ty, iso };
                    return progress.simplify_more(
                        ctx_names_opt,
                        ctx,
                        preserved_constraint_depth,
                        cache,
                        remaining_case_splits,
                    );
                }
            },

            _ => (),
        }
    }

    if let Some(()) = tail_new_ty.clone().into_inner(ctx.len()).as_unit()
    && let Some((_, _, head_tail_ty)) = head_new_ty.clone().as_sigma()
    && let Some(head_tail_ty) = head_tail_ty.try_strengthen().ok()
    && let Some(()) = head_tail_ty.as_unit()
    {
        let new_ty = head_new_ty;
        let iso = Iso::transitivity(iso, Iso::sigma_unit_tail());
        let progress_opt = Some(Progress { new_ty, iso });
        return Ok(Simplification::Undecided(Undecided {
            progress_opt, constraints, eliminated, hit_case_split_limit,
        }));
    }

    Ok(Simplification::Undecided(Undecided {
        progress_opt, constraints, eliminated, hit_case_split_limit,
    }))
}

fn simplify_pi(
    mut ctx_names_opt: Option<&mut Vec<Name>>,
    ctx: &mut Vec<Ty>,
    preserved_constraint_depth: usize,
    cache: &mut SimplifyCache,
    remaining_case_splits: u32,
    arg_name: &Name,
    arg_ty: &Ty,
    res_ty: &Scope<Ty>,
) -> Result<Simplification, Uninhabited> {
    let arg_undecided = match arg_ty.simplify(
        ctx_names_opt.as_deref_mut(),
        ctx,
        ctx.len(),
        cache,
        remaining_case_splits,
    ) {
        Err(Uninhabited { tag: _ }) => {
            let unique_tm = Tm::func(Scope::make(ctx.len(), |arg| {
                Tm::explode(Scope::constant(res_ty.clone().bind(arg)))
            }));
            return Ok(Simplification::solved(unique_tm));
        },
        Ok(Simplification::Unique { unique_tm: arg_unique_tm }) => {
            let progress = Progress {
                new_ty: res_ty.clone().bind(arg_unique_tm.clone()),
                iso: Iso::transitivity(
                    Iso::dependent_pi_arg_congruence(
                        res_ty.clone(),
                        Iso::uniquely_inhabited_to_unit(arg_unique_tm.clone()),
                    ),
                    Iso::pi_unit_arg(),
                ),
            };
            return progress.simplify_more(
                ctx_names_opt,
                ctx,
                preserved_constraint_depth,
                cache,
                remaining_case_splits,
            );
        },
        Ok(Simplification::Undecided(undecided)) => undecided,
    };

    let Undecided {
         progress_opt: arg_progress_opt,
        // TODO: can use these for negative reasoning.
        constraints: _arg_constraints,
        eliminated: arg_eliminated,
        hit_case_split_limit: arg_hit_case_split_limit,
    } = arg_undecided;

    let Progress { new_ty: arg_new_ty, iso: arg_iso } = {
        arg_progress_opt
        .clone()
        .unwrap_or_else(|| Progress::id(arg_ty.clone()))
    };
    let res_ty_rescoped = Scope::make(ctx.len(), |head| {
        res_ty.clone().bind(arg_iso.rev.clone().bind(head))
    });
    let iso = Iso::dependent_pi_arg_congruence(res_ty.clone(), arg_iso.clone());

    let arg_ty_inhabited = arg_new_ty.clone().try_find_arbitrary_tm(ctx).is_some();

    let res_undecided = match res_ty_rescoped.simplify(
        ctx_names_opt.as_deref_mut().map(|names| (names, arg_name)),
        ctx,
        if arg_ty_inhabited { preserved_constraint_depth } else { ctx.len() },
        cache,
        remaining_case_splits,
        &arg_new_ty,
    ) {
        Err(Uninhabited { tag }) => {
            if arg_ty_inhabited {
                return Err(Uninhabited { tag });
            }

            let new_ty = Ty::pi(
                arg_name.clone(),
                arg_new_ty.clone(),
                Scope::constant(Ty::never()),
            );
            let iso = Iso::transitivity(
                iso,
                Iso::dependent_pi_res_congruence(
                    Scope::make(ctx.len(), |arg_tm| {
                        Iso::scope_never_to_iso_never(
                            res_ty_rescoped.clone().bind(arg_tm.clone()),
                        )
                    }),
                ),
            );
            let progress = Progress { new_ty, iso };
            return Ok(Simplification::from_progress(progress));
        },
        Ok(Ok(res_unique_tm)) => {
            let unique_tm = Tm::func(res_unique_tm);
            return Ok(Simplification::Unique { unique_tm });
        },
        Ok(Err(undecided)) => undecided,
    };

    let UnscopedUndecided {
        progress_opt: res_progress_opt,
        constraints: res_constraints,
        eliminated: res_eliminated,
        hit_case_split_limit: res_hit_case_split_limit,
        var_constraint_opt,
        var_eliminated,
    } = res_undecided;

    if let Some(unique_arg) = var_constraint_opt
    && let Some(_) = arg_new_ty.try_find_alternate_tm(ctx, unique_arg)
    {
        let tag = Tag::concat(arg_name.clone().as_tag().into_iter());
        return Err(Uninhabited { tag });
    }

    let (res_new_ty, res_iso) = {
        res_progress_opt
        .clone()
        .unwrap_or_else(|| {
            Scope::make(ctx.len(), |arg| {
                Progress::id(res_ty_rescoped.clone().bind(arg))
            })
        })
        .lift_progress()
    };
    let iso = Iso::transitivity(
        iso,
        Iso::dependent_pi_res_congruence(res_iso),
    );

    let progress_opt = match (arg_progress_opt, res_progress_opt) {
        (None, None) => None,
        (_, _) => {
            Some(Progress {
                new_ty: Ty::pi(arg_name.clone(), arg_new_ty.clone(), res_new_ty.clone()),
                iso: iso.clone(),
            })
        },
    };

    let mut constraints = if arg_ty_inhabited { res_constraints } else { Constraints::new() };
    let mut eliminated = arg_eliminated.or(res_eliminated);
    let hit_case_split_limit = arg_hit_case_split_limit || res_hit_case_split_limit;

    if constraints.has_preserved_constraints(preserved_constraint_depth) {
        return Ok(Simplification::Undecided(Undecided {
            progress_opt, constraints, eliminated, hit_case_split_limit,
        }));
    }

    if var_eliminated && let Some(arg_form) = arg_new_ty.clone().try_reduce_to_form() {
        match Arc::unwrap_or_clone(arg_form.into_inner()) {
            FormKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                let new_ty = Ty::sigma(
                    lhs_name.clone(),
                    Ty::pi(
                        arg_name.clone(),
                        lhs_ty.clone(),
                        Scope::make(ctx.len(), |lhs| {
                            res_new_ty.clone().bind(lhs.inj_lhs())
                        }),
                    ),
                    Scope::constant(
                        Ty::pi(
                            arg_name.clone(),
                            rhs_ty.clone(),
                            Scope::make(ctx.len() + 1, |rhs| {
                                res_new_ty.clone().bind(rhs.inj_rhs())
                            }),
                        ),
                    ),
                );
                let iso = Iso::transitivity(iso, Iso::pi_sum_arg(lhs_name, res_new_ty));
                let progress = Progress { new_ty, iso };
                return progress.simplify_more(
                    ctx_names_opt,
                    ctx,
                    preserved_constraint_depth,
                    cache,
                    remaining_case_splits,
                );
            },
            FormKind::Sigma { head_name, head_ty, tail_ty } => {
                let new_ty = Ty::pi(
                    head_name.clone(),
                    head_ty.clone(),
                    Scope::make(ctx.len(), |head| {
                        Ty::pi(
                            arg_name.clone(),
                            tail_ty.bind(head.clone()),
                            Scope::make(ctx.len() + 1, |tail| {
                                res_new_ty.bind(head.pair(tail))
                            }),
                        )
                    }),
                );
                let iso = Iso::transitivity(iso, Iso::pi_sigma_arg());
                let progress = Progress { new_ty, iso };
                return progress.simplify_more(
                    ctx_names_opt,
                    ctx,
                    preserved_constraint_depth,
                    cache,
                    remaining_case_splits,
                );
            },
            FormKind::Universe => {
                debug!("collect pi universe arg constraints");
                debug_indent!();
                let (
                    pi_universe_arg_constraints,
                    pi_universe_arg_eliminated,
                ) = collect_pi_universe_arg_constraints(
                    ctx_names_opt.as_deref_mut(),
                    ctx,
                    preserved_constraint_depth,
                    cache,
                    remaining_case_splits,
                    res_new_ty.clone(),
                )?;
                eliminated.or_assign(&pi_universe_arg_eliminated);
                constraints = Constraints::union(constraints, pi_universe_arg_constraints)?;
                if constraints.has_preserved_constraints(preserved_constraint_depth) {
                    return Ok(Simplification::Undecided(Undecided {
                        progress_opt, constraints, eliminated, hit_case_split_limit,
                    }));
                }
            },
            _ => (),
        }
    }

    if let Some((
        res_head_name, res_head_ty, res_tail_ty,
    )) = res_new_ty.clone().into_inner(ctx.len()).as_sigma()
    && let Some(()) = res_tail_ty.into_inner(ctx.len() + 1).as_unit()
    && let Some(head_name) = Scope::new(ctx.len(), res_head_name).try_strengthen().ok()
    {
        let new_ty = Ty::sigma(
            head_name,
            Ty::pi(
                arg_name.clone(),
                arg_new_ty,
                Scope::new(ctx.len(), res_head_ty),
            ),
            Scope::constant(Ty::unit()),
        );

        let iso = Iso::transitivity(
            iso,
            Iso::transitivity(
                Iso::dependent_pi_res_congruence(
                    Scope::constant(Iso::sigma_unit_tail()),
                ),
                Iso::sigma_unit_tail().symmetry(),
            ),
        );
        let progress_opt = Some(Progress { new_ty, iso });
        return Ok(Simplification::Undecided(Undecided {
            progress_opt, constraints, eliminated, hit_case_split_limit,
        }));
    }

    Ok(Simplification::Undecided(Undecided {
        progress_opt, constraints, eliminated, hit_case_split_limit,
    }))
}

impl Scope<Ty> {
    fn simplify(
        &self,
        ctx_names_and_var_name_opt: Option<(&mut Vec<Name>, &Name)>,
        ctx: &mut Vec<Ty>,
        preserved_constraint_depth: usize,
        cache: &mut SimplifyCache,
        remaining_case_splits: u32,
        var_ty: &Ty,
    ) -> Result<Result<Scope<Tm>, UnscopedUndecided>, Uninhabited> {
        let inner = self.clone().into_inner(ctx.len());
        let mut ctx_names_opt = ctx_names_and_var_name_opt.map(|(names, name)| {
            names.push(name.clone());
            names
        });
        ctx.push(var_ty.clone());
        let simplify_res = inner.simplify(
            ctx_names_opt.as_deref_mut(),
            ctx,
            preserved_constraint_depth,
            cache,
            remaining_case_splits,
        );
        if let Some(names) = ctx_names_opt {
            names.pop().unwrap();
        }
        ctx.pop().unwrap();

        match simplify_res? {
            Simplification::Unique { unique_tm } => {
                Ok(Ok(Scope::new(ctx.len(), unique_tm)))
            },
            Simplification::Undecided(Undecided {
                progress_opt, mut constraints, mut eliminated, hit_case_split_limit,
            }) => {
                let progress_opt = progress_opt.map(|progress| Scope::new(ctx.len(), progress));
                let var_constraint_opt = constraints.pop_at_index(ctx.len());
                let var_eliminated = eliminated.pop_scoped(ctx.len());
                Ok(Err(UnscopedUndecided {
                    progress_opt,
                    constraints,
                    var_constraint_opt,
                    eliminated,
                    var_eliminated,
                    hit_case_split_limit,
                }))
            },
        }
    }
}

fn collect_pi_universe_arg_constraints(
    mut ctx_names_opt: Option<&mut Vec<Name>>,
    ctx: &mut Vec<Ty>,
    preserved_constraint_depth: usize,
    cache: &mut SimplifyCache,
    remaining_case_splits: u32,
    res_ty: Scope<Ty>,
) -> Result<(Constraints, Usages), Uninhabited> {
    let never_res_ty = res_ty.clone().bind(Ty::never().into_tm());
    let never_simplification = never_res_ty.simplify(
        ctx_names_opt.as_deref_mut(),
        ctx,
        preserved_constraint_depth,
        cache,
        remaining_case_splits,
    )?;

    let unit_res_ty = res_ty.clone().bind(Ty::unit().into_tm());
    let unit_simplification = unit_res_ty.simplify(
        ctx_names_opt.as_deref_mut(),
        ctx,
        preserved_constraint_depth,
        cache,
        remaining_case_splits,
    )?;

    let mut constraints = Constraints::new();
    let mut eliminated = Usages::empty();

    if let Simplification::Undecided(Undecided {
        constraints: never_constraints, eliminated: never_eliminated, ..
    }) = never_simplification {
        constraints = Constraints::union(constraints, never_constraints)?;
        eliminated = eliminated.or(never_eliminated);
    }
    if let Simplification::Undecided(Undecided {
        constraints: unit_constraints, eliminated: unit_eliminated, ..
    }) = unit_simplification {
        constraints = Constraints::union(constraints, unit_constraints)?;
        eliminated = eliminated.or(unit_eliminated);
    }

    Ok((constraints, eliminated))
}

fn try_factor_pi_from_sigmas(
    ctx_len: usize,
    arg_name: Name,
    arg_ty: Ty,
    sigmas: Ty,
) -> Option<(Scope<Ty>, Iso)> {
    let form = sigmas.reduced().into_inner().as_form()?;
    match Arc::unwrap_or_clone(form) {
        FormKind::Unit => {
            let res_ty = Scope::constant(Ty::unit());
            let iso = Iso::between_props();
            Some((res_ty, iso))
        },
        FormKind::Sigma { head_name, head_ty, tail_ty } => {
            let (head_res_ty, head_iso) = try_factor_pi_from_sigmas(
                ctx_len,
                arg_name.clone(),
                arg_ty.clone(),
                head_ty,
            )?;

            let rebound_tail_ty = Scope::make(ctx_len, |pi_head| {
                tail_ty.clone().bind(head_iso.rev.clone().bind(pi_head))
            });

            let (tail_res_ty, tail_iso) = try_factor_pi_from_sigma_tail(
                ctx_len,
                arg_name.clone(),
                arg_ty.clone(),
                rebound_tail_ty,
            )?;

            let res_ty = Scope::make(ctx_len, |arg| {
                Ty::sigma(
                    head_name,
                    head_res_ty.bind(arg.clone()),
                    tail_res_ty.bind(arg),
                )
            });

            let iso = Iso::dependent_sigma_head_congruence(tail_ty.clone(), head_iso);
            let iso = Iso::transitivity(
                iso, 
                Iso::dependent_sigma_tail_congruence(tail_iso),
            );
            let iso = Iso::transitivity(iso, Iso::pi_sigma_res().symmetry());

            Some((res_ty, iso))
        },
        FormKind::Pi { arg_name: this_arg_name, arg_ty: this_arg_ty, res_ty } => {
            let _arg_name = Unify::unify(arg_name, this_arg_name)?;
            let _arg_ty = Unify::unify(arg_ty, this_arg_ty)?;
            Some((res_ty, Iso::refl()))
        },
        _ => None,
    }
}

fn try_factor_pi_from_sigma_tail(
    ctx_len: usize,
    arg_name: Name,
    arg_ty: Ty,
    tail_ty: Scope<Ty>,
) -> Option<(Scope<Scope<Ty>>, Scope<Iso>)> {
    let tail_ty_inner = tail_ty.clone().into_inner(ctx_len);
    let (tail_res_ty, tail_iso) = try_factor_pi_from_sigmas(
        ctx_len + 1,
        arg_name.clone(),
        arg_ty.clone(),
        tail_ty_inner,
    )?;

    let tail_res_ty_inner = tail_res_ty.into_inner(ctx_len + 1);
    let tail_res_ty_inner = tail_res_ty_inner.try_unswap_vars(ctx_len)?;
    let tail_res_ty = Scope::new(ctx_len, Scope::new(ctx_len + 1, tail_res_ty_inner));
    let tail_iso = Scope::new(ctx_len, tail_iso);
    Some((tail_res_ty, tail_iso))
}


/*
impl Name {
    fn try_concat_tag_front(
        self,
        tag: Tag,
    ) -> Option<Name> {
        let tag_0 = self.as_tag()?;
        let tag = Tag::concat([tag_0, tag]);
        Some(Weaken::new(OrLazy::Reduced(NameKind::Tag { tag })))
    }
}

impl Ty {
    fn try_concat_tag_front(self, tag: Tag) -> Option<Ty> {
        match self.reduced().into_inner() {
            TyKind::Form { form } => {
                let form = Arc::unwrap_or_clone(form).try_concat_tag_front(tag)?;
                Some(Weaken::new(OrLazy::Reduced(TyKind::Form { form: Arc::new(form) })))
            },
            TyKind::Stuck { .. } => None,
        }
    }

    fn try_concat_name_front(self, name: Name) -> Option<Ty> {
        let tag = name.as_tag()?;
        self.try_concat_tag_front(tag)
    }
}

impl FormKind {
    fn try_concat_tag_front(self, tag: Tag) -> Option<FormKind> {
        match self {
            | FormKind::Name
            | FormKind::Universe
            | FormKind::Nat
            | FormKind::Never
            | FormKind::Sum { .. }
            => None,

            FormKind::Unit => Some(FormKind::Unit),

            FormKind::Sigma { head_name, head_ty, tail_ty } => {
                let head_name = head_name.try_concat_tag_front(tag.clone())?;
                let tail_ty = tail_ty.try_map_without_capture(|tail_ty| {
                    tail_ty.try_concat_tag_front(tag.clone())
                })?;
                Some(FormKind::Sigma { head_name, head_ty, tail_ty })
            },

            /*
            FormKind::Pi { arg_name, arg_ty, res_ty } => {
                let res_ty = res_ty.try_map_without_capture(|res_ty| {
                    res_ty.try_concat_tag_front(tag.clone())
                })?;
                Some(FormKind::Pi { arg_name, arg_ty, res_ty })
            },
            */

            FormKind::Pi { .. } => None,
        }
    }
}
*/


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


