use crate::priv_prelude::*;

#[derive(Clone, Debug, Contextual)]
pub struct Iso {
    pub(crate) fwd: Scope<Tm>,
    pub(crate) rev: Scope<Tm>,
    pub(crate) fwd_rev: Scope<Tm>,
    pub(crate) rev_fwd: Scope<Tm>,
}

impl Substitutable for Iso {
    type Output = Iso;

    fn subst(self, subst: &mut Subst) -> Iso {
        let Iso { fwd, rev, fwd_rev, rev_fwd } = self;
        let fwd = fwd.subst(subst);
        let rev = rev.subst(subst);
        let fwd_rev = fwd_rev.subst(subst);
        let rev_fwd = rev_fwd.subst(subst);
        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    fn into_output(self) -> Iso {
        self
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<Iso> {
        let Iso { fwd, rev, fwd_rev, rev_fwd } = self;
        let fwd = fwd.try_strengthen_index(var_index)?;
        let rev = rev.try_strengthen_index(var_index)?;
        let fwd_rev = fwd_rev.try_strengthen_index(var_index)?;
        let rev_fwd = rev_fwd.try_strengthen_index(var_index)?;
        Some(Iso { fwd, rev, fwd_rev, rev_fwd })
    }
}

impl Bindable for Iso {
    fn capture_subst(self, subst: Subst) -> Iso {
        let Iso { fwd, rev, fwd_rev, rev_fwd } = self;
        let fwd = fwd.capture_subst(subst.clone());
        let rev = rev.capture_subst(subst.clone());
        let fwd_rev = fwd_rev.capture_subst(subst.clone());
        let rev_fwd = rev_fwd.capture_subst(subst.clone());
        Iso { fwd, rev, fwd_rev, rev_fwd }
    }
}

impl Iso {
    /// ```ignore
    /// Γ ⊢ ty : Type
    /// ----
    /// Γ ⊢ Iso::refl() : ty ≅ ty
    /// ```

    pub fn refl() -> Iso {
        Iso {
            fwd: Scope::id(),
            rev: Scope::id(),
            fwd_rev: Scope::make(0, |tm| tm.obs_refl()),
            rev_fwd: Scope::make(0, |tm| tm.obs_refl()),
        }
    }

    /// ```ignore
    /// Γ ⊢ ty_0 : Type
    /// Γ ⊢ ty_1 : Type
    /// Γ ⊢ self : ty_0 ≅ ty_1
    /// ----
    /// Γ ⊢ self.symmetry() : ty_1 ≅ ty_0
    /// ```

    pub fn symmetry(self) -> Iso {
        let Iso { fwd, rev, fwd_rev, rev_fwd } = self;
        Iso {
            fwd: rev,
            rev: fwd,
            fwd_rev: rev_fwd,
            rev_fwd: fwd_rev,
        }
    }

    /// ```ignore
    /// Γ ⊢ from_ty_0 : Type
    /// Γ ⊢ middle_ty : Type
    /// Γ ⊢ into_ty_1 : Type
    /// Γ ⊢ iso_0 : from_ty_0 ≅ middle_ty
    /// Γ ⊢ iso_1 : middle_ty ≅ into_ty_1
    /// ----
    /// Γ ⊢ Iso::transitivity(iso_0, iso_1, from_ty_0, from_ty_1) : from_ty_0 ≅ into_ty_1
    /// ```

    pub fn transitivity(
        iso_0: Iso,
        iso_1: Iso,
        from_ty_0: Ty,
        into_ty_1: Ty,
    ) -> Iso {
        let ctx_len = max_all([
            iso_0.ctx_len(),
            iso_1.ctx_len(),
            from_ty_0.ctx_len(),
            into_ty_1.ctx_len(),
        ]);

        let Iso { fwd: fwd_0, rev: rev_0, fwd_rev: fwd_rev_0, rev_fwd: rev_fwd_0 } = iso_0;
        let Iso { fwd: fwd_1, rev: rev_1, fwd_rev: fwd_rev_1, rev_fwd: rev_fwd_1 } = iso_1;

        let fwd = Scope::make(ctx_len, |tm| {
            fwd_1.clone().bind(fwd_0.clone().bind(tm))
        });

        let rev = Scope::make(ctx_len, |tm| {
            rev_0.clone().bind(rev_1.clone().bind(tm))
        });

        let fwd_rev = Scope::make(ctx_len, |from_tm| {
            let midd_tm_0 = fwd_0.clone().bind(from_tm.clone());
            let midd_tm_1 = rev_1.clone().bind(fwd_1.clone().bind(midd_tm_0.clone()));

            rev_0
            .clone()
            .bind_eq(
                from_ty_0.clone(),
                midd_tm_1.clone(),
                fwd_rev_1.bind(midd_tm_0.clone())
            )
            .transitivity(
                fwd_rev_0.bind(from_tm.clone()),
                from_ty_0,
                rev_0.clone().bind(midd_tm_1),
                from_tm,
            )
        });

        let rev_fwd = Scope::make(ctx_len, |into_tm| {
            let midd_tm_0 = rev_1.bind(into_tm.clone());
            let midd_tm_1 = fwd_0.clone().bind(rev_0.bind(midd_tm_0.clone()));

            fwd_1
            .clone()
            .bind_eq(
                into_ty_1.clone(),
                midd_tm_1.clone(),
                rev_fwd_0.bind(midd_tm_0.clone()),
            )
            .transitivity(
                rev_fwd_1.bind(into_tm.clone()),
                into_ty_1,
                fwd_1.bind(midd_tm_1),
                into_tm,
            )
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ from_ty : Type
    /// Γ ⊢ fwd : from_ty ⊢ Never
    /// ----
    /// Γ ⊢ Iso::scope_never_to_iso_never(from_ty, fwd) : from_ty ≅ Never
    /// ```

    pub fn scope_never_to_iso_never(
        from_ty: Ty,
        fwd: Scope<Tm>,
    ) -> Iso {
        let ctx_len = max_all([from_ty.ctx_len(), fwd.ctx_len()]);

        let rev = Scope::make(ctx_len, |never| {
            never.explode(Scope::constant(from_ty.clone()))
        });

        let fwd_rev = Scope::make(ctx_len, |tm| {
            let never = fwd.clone().bind(tm.clone());

            never
            .clone()
            .explode(Scope::constant(
                Ty::obs_equal(
                    from_ty.clone(),
                    rev.clone().bind(never),
                    tm,
                )
            ))
        });

        let rev_fwd = Scope::make(ctx_len, |never| {
            never.obs_refl()
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ eq_ty : Type
    /// Γ ⊢ eq_tm : eq_ty == eq_ty
    /// ----
    /// Γ ⊢ Iso::reflexive_equality_to_unit(
    ///     eq_ty,
    ///     eq_tm,
    /// ) : (eq_tm == eq_tm) ≅ Unit
    /// ```

    pub fn reflexive_equality_to_unit(
        eq_tm: Tm,
    ) -> Iso {
        let fwd = Scope::constant(Tm::unit());
        let rev = Scope::constant(eq_tm.clone().obs_refl());
        let fwd_rev = Scope::make(0, |elim| elim.obs_refl());
        let rev_fwd = Scope::constant(Tm::unit().obs_refl());

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ lhs_name_0 : Name
    /// Γ ⊢ lhs_name_1 : Name
    /// Γ ⊢ lhs_ty_0 : Type
    /// Γ ⊢ lhs_ty_1 : Type
    /// Γ ⊢ rhs_ty_0 : Type
    /// Γ ⊢ rhs_ty_1 : Type
    /// Γ ⊢ lhs_iso : lhs_ty_0 ≅ lhs_ty_1
    /// Γ ⊢ rhs_iso : rhs_ty_0 ≅ rhs_ty_1
    /// ----
    /// Γ ⊢ Iso::sum_congruence(
    ///     lhs_name_0,
    ///     lhs_name_1,
    ///     lhs_ty_0,
    ///     lhs_ty_1,
    ///     rhs_ty_0,
    ///     rhs_ty_1,
    ///     lhs_iso,
    ///     rhs_iso,
    /// ) : Ty::sum(lhs_name_0, lhs_ty_0, rhs_ty_0) ≅ Ty::sum(lhs_name_1, lhs_ty_1, rhs_ty_1)
    /// ```

    pub fn sum_congruence(
        lhs_name_0: Name,
        lhs_name_1: Name,
        lhs_ty_0: Ty,
        lhs_ty_1: Ty,
        rhs_ty_0: Ty,
        rhs_ty_1: Ty,
        lhs_iso: Iso,
        rhs_iso: Iso,
    ) -> Iso {
        let ctx_len = max_all([
            lhs_name_0.ctx_len(),
            lhs_name_1.ctx_len(),
            lhs_ty_0.ctx_len(),
            lhs_ty_1.ctx_len(),
            rhs_ty_0.ctx_len(),
            lhs_iso.ctx_len(),
            rhs_iso.ctx_len(),
        ]);

        let sum_ty_0 = Ty::sum(lhs_name_0, lhs_ty_0, rhs_ty_0);
        let sum_ty_1 = Ty::sum(lhs_name_1, lhs_ty_1, rhs_ty_1);

        let Iso { fwd: lhs_fwd, rev: lhs_rev, fwd_rev: lhs_fwd_rev, rev_fwd: lhs_rev_fwd } = lhs_iso;
        let Iso { fwd: rhs_fwd, rev: rhs_rev, fwd_rev: rhs_fwd_rev, rev_fwd: rhs_rev_fwd } = rhs_iso;

        let fwd = Scope::make(ctx_len, |sum_0| {
            sum_0
            .case(
                Scope::constant(sum_ty_1.clone()),
                Scope::make(ctx_len + 1, |lhs_0| lhs_fwd.clone().bind(lhs_0).inj_lhs()),
                Scope::make(ctx_len + 1, |rhs_0| rhs_fwd.clone().bind(rhs_0).inj_rhs()),
            )
        });

        let rev = Scope::make(ctx_len, |sum_1| {
            sum_1
            .case(
                Scope::constant(sum_ty_0.clone()),
                Scope::make(ctx_len + 1, |lhs_1| lhs_rev.clone().bind(lhs_1).inj_lhs()),
                Scope::make(ctx_len + 1, |rhs_1| rhs_rev.clone().bind(rhs_1).inj_rhs()),
            )
        });

        let fwd_rev = Scope::make(ctx_len, |sum_0| {
            sum_0
            .case(
                Scope::make(ctx_len + 1, |sum_0| {
                    Ty::obs_equal(
                        sum_ty_0.clone(),
                        rev.clone().bind(fwd.clone().bind(sum_0.clone())),
                        sum_0,
                    )
                }),
                Scope::make(ctx_len + 1, |lhs_0| {
                    Scope::make(ctx_len + 2, |lhs| lhs.inj_lhs())
                    .bind_eq(
                        sum_ty_0.clone(),
                        lhs_rev.clone().bind(lhs_fwd.clone().bind(lhs_0.clone())),
                        lhs_fwd_rev.bind(lhs_0),
                    )
                }),
                Scope::make(ctx_len + 1, |rhs_0| {
                    Scope::make(ctx_len + 2, |rhs| rhs.inj_rhs())
                    .bind_eq(
                        sum_ty_0.clone(),
                        rhs_rev.clone().bind(rhs_fwd.clone().bind(rhs_0.clone())),
                        rhs_fwd_rev.bind(rhs_0),
                    )
                }),
            )
        });

        let rev_fwd = Scope::make(ctx_len, |sum_1| {
            sum_1
            .case(
                Scope::make(ctx_len + 1, |sum_1| {
                    Ty::obs_equal(
                        sum_ty_1.clone(),
                        fwd.clone().bind(rev.clone().bind(sum_1.clone())),
                        sum_1,
                    )
                }),
                Scope::make(ctx_len + 1, |lhs_1| {
                    Scope::make(ctx_len + 2, |lhs| lhs.inj_lhs())
                    .bind_eq(
                        sum_ty_1.clone(),
                        lhs_fwd.bind(lhs_rev.bind(lhs_1.clone())),
                        lhs_rev_fwd.bind(lhs_1),
                    )
                }),
                Scope::make(ctx_len + 1, |rhs_1| {
                    Scope::make(ctx_len + 2, |rhs| rhs.inj_rhs())
                    .bind_eq(
                        sum_ty_1.clone(),
                        rhs_fwd.bind(rhs_rev.bind(rhs_1.clone())),
                        rhs_rev_fwd.bind(rhs_1),
                    )
                }),
            )
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ lhs_name : Name
    /// Γ ⊢ rhs_ty : Type
    /// ----
    /// Γ ⊢ Iso::sum_never_lhs(lhs_name, rhs_ty) : Ty::sum(lhs_name, Never, rhs_ty) ≅ rhs_ty
    /// ```

    pub fn sum_never_lhs(
        lhs_name: Name,
        rhs_ty: Ty,
    ) -> Iso {
        let ctx_len = max_all([
            lhs_name.ctx_len(),
            rhs_ty.ctx_len(),
        ]);

        let fwd = Scope::make(ctx_len, |sum| {
            sum
            .case(
                Scope::constant(rhs_ty.clone()),
                Scope::make(ctx_len + 1, |never| {
                    never.explode(Scope::constant(rhs_ty.clone()))
                }),
                Scope::make(ctx_len + 1, |rhs| rhs),
            )
        });
        
        let rev = Scope::make(ctx_len, |rhs| rhs.inj_rhs());

        let fwd_rev = Scope::make(ctx_len, |sum| {
            let sum_ty = Ty::sum(lhs_name, Ty::never(), rhs_ty);

            sum
            .case(
                Scope::make(ctx_len + 1, |sum| {
                    Ty::obs_equal(
                        sum_ty.clone(),
                        rev.clone().bind(fwd.clone().bind(sum.clone())),
                        sum,
                    )
                }),
                Scope::make(ctx_len + 1, |never| {
                    let sum = never.clone().inj_lhs();
                    never
                    .explode(Scope::constant(
                        Ty::obs_equal(
                            sum_ty,
                            rev.clone().bind(fwd.clone().bind(sum.clone())),
                            sum,
                        )
                    ))
                }),
                Scope::make(ctx_len + 1, |rhs| {
                    rhs.inj_rhs().obs_refl()
                }),
            )
        });

        let rev_fwd = Scope::make(ctx_len, |rhs| {
            rhs.obs_refl()
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ lhs_name : Name
    /// Γ ⊢ lhs_ty : Type
    /// ----
    /// Γ ⊢ Iso::sum_never_rhs(lhs_name, lhs_ty) : Ty::sum(lhs_name, lhs_ty, Never) ≅ lhs_ty
    /// ```

    pub fn sum_never_rhs(
        lhs_name: Name,
        lhs_ty: Ty,
    ) -> Iso {
        let ctx_len = max_all([
            lhs_name.ctx_len(),
            lhs_ty.ctx_len(),
        ]);

        let fwd = Scope::make(ctx_len, |sum| {
            sum
            .case(
                Scope::constant(lhs_ty.clone()),
                Scope::make(ctx_len + 1, |lhs| lhs),
                Scope::make(ctx_len + 1, |never| {
                    never.explode(Scope::constant(lhs_ty.clone()))
                }),
            )
        });
        
        let rev = Scope::make(ctx_len, |lhs| lhs.inj_lhs());

        let fwd_rev = Scope::make(ctx_len, |sum| {
            let sum_ty = Ty::sum(lhs_name, lhs_ty, Ty::never());

            sum
            .case(
                Scope::make(ctx_len + 1, |sum| {
                    Ty::obs_equal(
                        sum_ty.clone(),
                        rev.clone().bind(fwd.clone().bind(sum.clone())),
                        sum,
                    )
                }),
                Scope::make(ctx_len + 1, |lhs| {
                    lhs.inj_lhs().obs_refl()
                }),
                Scope::make(ctx_len + 1, |never| {
                    let sum = never.clone().inj_rhs();
                    never
                    .explode(Scope::constant(
                        Ty::obs_equal(
                            sum_ty,
                            rev.clone().bind(fwd.clone().bind(sum.clone())),
                            sum,
                        )
                    ))
                }),
            )
        });

        let rev_fwd = Scope::make(ctx_len, |lhs| {
            lhs.obs_refl()
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ head_name : Name
    /// Γ ⊢ head_ty_0 : Type
    /// Γ ⊢ head_ty_1 : Type
    /// Γ ⊢ tail_ty : head_ty_0 ⊢ Type
    /// Γ ⊢ head_iso : head_ty_0 ≅ head_ty_1
    /// ----
    /// Γ ⊢ Iso::dependent_sigma_head_congruence(
    ///     head_name,
    ///     head_ty_0,
    ///     head_ty_1,
    ///     tail_ty,
    ///     head_iso,
    /// ) : Ty::sigma(head_name, head_ty_0, tail_ty)
    ///   ≅ Ty::sigma(head_name, head_ty_1, Scope::make(Γ.len(), |head|
    ///     tail_ty.bind(head_eq.rev.bind(head))
    ///   })
    /// ```

    pub fn dependent_sigma_head_congruence(
        head_name: Name,
        head_ty_0: Ty,
        head_ty_1: Ty,
        tail_ty: Scope<Ty>,
        head_iso: Iso,
    ) -> Iso {
        let ctx_len = max_all([
            head_name.ctx_len(),
            head_ty_0.ctx_len(),
            head_ty_1.ctx_len(),
            tail_ty.ctx_len(),
            head_iso.ctx_len(),
        ]);

        let Iso {
            fwd: head_fwd, rev: head_rev, fwd_rev: head_fwd_rev, rev_fwd: head_rev_fwd,
        } = head_iso;

        lazy_static! {
            static ref TAIL_NAME: Name = Name::from("tail");
        }

        let tail_ty_0 = tail_ty.clone();
        let tail_ty_1 = Scope::make(ctx_len, |head| tail_ty.bind(head_rev.clone().bind(head)));

        let fwd = Scope::make(ctx_len, |pair_0| {
            let head_0 = pair_0.clone().proj_head();
            let head_1 = head_fwd.clone().bind(head_0.clone());

            let bound_tail_ty_0 = tail_ty_0.clone().bind(head_0.clone());
            let bound_tail_ty_1 = tail_ty_1.clone().bind(head_1.clone());

            let tail_0 = pair_0.proj_tail();
            let tail_1 = {
                head_fwd_rev
                .clone()
                .bind(head_0)
                .obs_cong(
                    Scope::make(ctx_len + 1, |head_0| {
                        Scope::constant(
                            Ty::obs_equal(
                                Ty::universe(),
                                tail_ty_0.clone().bind(head_0).into_tm(),
                                bound_tail_ty_1.clone().into_tm(),
                            ),
                        )
                    }),
                    bound_tail_ty_1.clone().into_tm().obs_refl(),
                )
                .cast(
                    bound_tail_ty_0,
                    bound_tail_ty_1,
                    tail_0,
                )
            };

            head_1.pair(tail_1)
        });

        let rev = Scope::make(ctx_len, |pair_1| {
            let head_1 = pair_1.clone().proj_head();
            let tail_1 = pair_1.proj_tail();

            let head_0 = head_rev.clone().bind(head_1);
            let tail_0 = tail_1;

            head_0.pair(tail_0)
        });

        let fwd_rev = Scope::make(ctx_len, |pair_0| {
            let head_0 = pair_0.clone().proj_head();
            let head_1 = head_fwd.clone().bind(head_0.clone());
            let head_eq = head_fwd_rev.clone().bind(head_0.clone());

            let bound_tail_ty_0 = tail_ty_0.clone().bind(head_0);
            let bound_tail_ty_1 = tail_ty_1.clone().bind(head_1);

            let bound_tail_ty_eq = {
                head_eq
                .clone()
                .obs_cong(
                    Scope::make(ctx_len + 1, |head_0| {
                        Scope::constant(
                            Ty::obs_equal(
                                Ty::universe(),
                                tail_ty_0.clone().bind(head_0).into_tm(),
                                bound_tail_ty_1.clone().into_tm(),
                            ),
                        )
                    }),
                    bound_tail_ty_1.clone().into_tm().obs_refl(),
                )
            };

            let tail_0 = pair_0.clone().proj_tail();
            let tail_eq = {
                bound_tail_ty_eq
                .cast_round_trip(
                    bound_tail_ty_0,
                    bound_tail_ty_1,
                    tail_0,
                )
            };

            head_eq.pair(tail_eq)
        });

        let rev_fwd = Scope::make(ctx_len, |pair_1| {
            let head_1 = pair_1.clone().proj_head();
            let tail_1 = pair_1.proj_tail();

            let head_0 = head_rev.clone().bind(head_1.clone());
            let head_eq = head_rev_fwd.clone().bind(head_1);

            let bound_tail_ty_0 = tail_ty_0.clone().bind(head_0.clone());
            let bound_tail_ty_1 = tail_ty_1.clone().bind(head_fwd.bind(head_0.clone()));

            let bound_tail_ty_eq = {
                head_fwd_rev
                .bind(head_0)
                .obs_cong(
                    Scope::make(ctx_len + 1, |head_0| {
                        Scope::constant(
                            Ty::obs_equal(
                                Ty::universe(),
                                tail_ty_0.bind(head_0).into_tm(),
                                bound_tail_ty_1.clone().into_tm(),
                            )
                        )
                    }),
                    bound_tail_ty_1.clone().into_tm().obs_refl(),
                )
            };

            let tail_eq = {
                bound_tail_ty_eq
                .cast_round_trip(
                    bound_tail_ty_0,
                    bound_tail_ty_1,
                    tail_1,
                )
            };

            head_eq.pair(tail_eq)
        });
        
        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ head_name : Name
    /// Γ ⊢ head_ty : Type
    /// Γ ⊢ tail_ty_0 : head_ty ⊢ Type
    /// Γ ⊢ tail_ty_1 : head_ty ⊢ Type
    /// Γ ⊢ tail_iso : head_ty ⊢ tail_ty_0 ≅ tail_ty_1
    /// ----
    /// Γ ⊢ Iso::dependent_sigma_tail_congruence(
    ///     head_name,
    ///     head_ty,
    ///     tail_ty_0,
    ///     tail_ty_1,
    ///     tail_iso,
    /// ) : Ty::sigma(head_name, head_ty, tail_ty_0)
    ///   ≅ Ty::sigma(head_name, head_ty, tail_ty_1)
    /// ```

    pub fn dependent_sigma_tail_congruence(
        head_name: Name,
        head_ty: Ty,
        tail_ty_0: Scope<Ty>,
        tail_ty_1: Scope<Ty>,
        tail_iso: Scope<Iso>,
    ) -> Iso {
        let ctx_len = max_all([
            head_name.ctx_len(),
            head_ty.ctx_len(),
            tail_ty_0.ctx_len(),
            tail_ty_1.ctx_len(),
            tail_iso.ctx_len(),
        ]);

        let (tail_fwd, tail_rev, tail_fwd_rev, tail_rev_fwd) = tail_iso.map_multi(
            ctx_len,
            |_, tail_iso| {
                let Iso { fwd, rev, fwd_rev, rev_fwd } = tail_iso;
                (fwd, rev, fwd_rev, rev_fwd)
            },
        );

        let fwd = Scope::make(ctx_len, |pair_0| {
            let head = pair_0.clone().proj_head();
            let tail_0 = pair_0.proj_tail();
            let tail_1 = tail_fwd.clone().bind(head.clone()).bind(tail_0);
            head.pair(tail_1)
        });

        let rev = Scope::make(ctx_len, |pair_1| {
            let head = pair_1.clone().proj_head();
            let tail_1 = pair_1.proj_tail();
            let tail_0 = tail_rev.clone().bind(head.clone()).bind(tail_1);
            head.pair(tail_0)
        });

        let fwd_rev = Scope::make(ctx_len, |pair_0| {
            let head = pair_0.clone().proj_head();
            let tail_0 = pair_0.proj_tail();

            let bound_tail_ty_0 = tail_ty_0.bind(head.clone());

            Tm::cast_refl()
            .transitivity(
                tail_fwd_rev.bind(head.clone()).bind(tail_0.clone()),
                bound_tail_ty_0.clone(),
                bound_tail_ty_0
                .clone()
                .into_tm()
                .obs_refl()
                .cast(
                    bound_tail_ty_0.clone(),
                    bound_tail_ty_0.clone(),
                    tail_rev
                    .clone()
                    .bind(head.clone())
                    .bind(tail_fwd.clone().bind(head).bind(tail_0.clone())),
                ),
                tail_0,
            )
        });

        let rev_fwd = Scope::make(ctx_len, |pair_1| {
            let head = pair_1.clone().proj_head();
            let tail_1 = pair_1.proj_tail();

            let bound_tail_ty_1 = tail_ty_1.bind(head.clone());

            Tm::cast_refl()
            .transitivity(
                tail_rev_fwd.bind(head.clone()).bind(tail_1.clone()),
                bound_tail_ty_1.clone(),
                bound_tail_ty_1
                .clone()
                .into_tm()
                .obs_refl()
                .cast(
                    bound_tail_ty_1.clone(),
                    bound_tail_ty_1.clone(),
                    tail_fwd
                    .clone()
                    .bind(head.clone())
                    .bind(tail_rev.clone().bind(head).bind(tail_1.clone())),
                ),
                tail_1,
            )
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /*
    /// ```ignore
    /// Γ ⊢ head_name : Name
    /// Γ ⊢ head_ty_0 : Type
    /// Γ ⊢ head_ty_1 : Type
    /// Γ ⊢ tail_ty : Type
    /// Γ ⊢ head_iso : head_ty_0 ≅ head_ty_1
    /// ----
    /// Γ ⊢ Iso::non_dependent_sigma_head_congruence(
    ///     head_name,
    ///     head_ty_0,
    ///     head_ty_1,
    ///     tail_ty,
    ///     head_iso,
    /// ) : Ty::sigma(head_name, head_ty_0, Scope::constant(tail_ty))
    ///   ≅ Ty::sigma(head_name, head_ty_1, Scope::constant(tail_ty))
    /// ```

    pub fn non_dependent_sigma_head_congruence(
        head_name: Name,
        head_ty_0: Ty,
        head_ty_1: Ty,
        tail_ty: Ty,
        head_iso: Iso,
    ) -> Iso {
        let ctx_len = max_all([
            head_name.ctx_len(),
            head_ty_0.ctx_len(),
            head_ty_1.ctx_len(),
            tail_ty.ctx_len(),
            head_iso.ctx_len(),
        ]);

        let Iso {
            fwd: head_fwd, rev: head_rev, fwd_rev: head_fwd_rev, rev_fwd: head_rev_fwd,
        } = head_iso;

        let fwd = Scope::make(ctx_len, |pair_0| {
            let head_0 = pair_0.clone().proj_head();
            let tail = pair_0.proj_tail();

            let head_1 = head_fwd.clone().bind(head_0);
            head_1.pair(tail)
        });

        let rev = Scope::make(ctx_len, |pair_1| {
            let head_1 = pair_1.clone().proj_head();
            let tail = pair_1.proj_tail();

            let head_0 = head_rev.clone().bind(head_1);
            head_0.pair(tail)
        });

        let fwd_rev = Scope::make(ctx_len, |pair_0| {
            let head_0 = pair_0.clone().proj_head();
            let tail = pair_0.proj_tail();

            head_fwd_rev.bind(head_0.clone()).map_eq(
                ctx_len + 1,
                Ty::sigma(head_name.clone(), head_ty_0, Scope::constant(tail_ty.clone())),
                head_rev.clone().bind(head_fwd.clone().bind(head_0)),
                |head| head.pair(tail),
            )
        });

        let rev_fwd = Scope::make(ctx_len, |pair_1| {
            let head_1 = pair_1.clone().proj_head();
            let tail = pair_1.proj_tail();

            head_rev_fwd.bind(head_1.clone()).map_eq(
                ctx_len + 1,
                Ty::sigma(head_name, head_ty_1, Scope::constant(tail_ty)),
                head_fwd.clone().bind(head_rev.clone().bind(head_1)),
                |head| head.pair(tail),
            )
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ head_name : Name
    /// Γ ⊢ head_ty : Type
    /// Γ ⊢ tail_ty_0 : Type
    /// Γ ⊢ tail_ty_1 : Type
    /// Γ ⊢ tail_iso : tail_ty_0 ≅ tail_ty_1
    /// ----
    /// Γ ⊢ Iso::non_dependent_sigma_tail_congruence(
    ///     head_name,
    ///     head_ty,
    ///     tail_ty_0,
    ///     tail_ty_1,
    ///     tail_iso,
    /// ) : Ty::sigma(head_name, head_ty, Scope::constant(tail_ty_0))
    ///   ≅ Ty::sigma(head_name, head_ty, Scope::constant(tail_ty_1))
    /// ```

    pub fn non_dependent_sigma_tail_congruence(
        head_name: Name,
        head_ty: Ty,
        tail_ty_0: Ty,
        tail_ty_1: Ty,
        tail_iso: Iso,
    ) -> Iso {
        let ctx_len = max_all([
            head_name.ctx_len(),
            head_ty.ctx_len(),
            tail_ty_0.ctx_len(),
            tail_ty_1.ctx_len(),
            tail_iso.ctx_len(),
        ]);

        let Iso {
            fwd: tail_fwd, rev: tail_rev, fwd_rev: tail_fwd_rev, rev_fwd: tail_rev_fwd,
        } = tail_iso;

        let fwd = Scope::make(ctx_len, |pair_0| {
            let head = pair_0.clone().proj_head();
            let tail_0 = pair_0.proj_tail();

            let tail_1 = tail_fwd.clone().bind(tail_0);
            head.pair(tail_1)
        });

        let rev = Scope::make(ctx_len, |pair_1| {
            let head = pair_1.clone().proj_head();
            let tail_1 = pair_1.proj_tail();

            let tail_0 = tail_rev.clone().bind(tail_1);
            head.pair(tail_0)
        });

        let fwd_rev = Scope::make(ctx_len, |pair_0| {
            let head = pair_0.clone().proj_head();
            let tail_0 = pair_0.proj_tail();

            tail_fwd_rev.bind(tail_0.clone()).map_eq(
                ctx_len + 1,
                Ty::sigma(head_name.clone(), head_ty.clone(), Scope::constant(tail_ty_0)),
                tail_rev.clone().bind(tail_fwd.clone().bind(tail_0)),
                |tail| head.pair(tail),
            )
        });

        let rev_fwd = Scope::make(ctx_len, |pair_1| {
            let head = pair_1.clone().proj_head();
            let tail_1 = pair_1.proj_tail();

            tail_rev_fwd.bind(tail_1.clone()).map_eq(
                ctx_len + 1,
                Ty::sigma(head_name, head_ty, Scope::constant(tail_ty_1)),
                tail_fwd.clone().bind(tail_rev.clone().bind(tail_1)),
                |tail| head.pair(tail),
            )
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }
    */

    /// ```ignore
    /// Γ ⊢ head_name : Name
    /// Γ ⊢ tail_ty : Unit ⊢ Type
    /// ----
    /// Γ ⊢ Iso::sigma_unit_head()
    ///   : Ty::sigma(head_name, Unit, tail_ty) ≅ tail_ty.bind(Tm::unit())
    /// ```

    pub fn sigma_unit_head() -> Iso {
        let fwd = Scope::make(0, |pair| {
            pair.proj_tail()
        });

        let rev = Scope::make(0, |tail| {
            Tm::unit().pair(tail)
        });

        let fwd_rev = Scope::make(0, |pair| {
            pair.obs_refl()
        });

        let rev_fwd = Scope::make(0, |tail| {
            tail.obs_refl()
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ head_name : Name
    /// Γ ⊢ lhs_name : Name
    /// Γ ⊢ lhs_ty : Type
    /// Γ ⊢ rhs_ty : Type
    /// Γ ⊢ tail_ty : Ty::sum(lhs_name, lhs_ty, rhs_ty) ⊢ Type
    /// ----
    /// Γ ⊢ Iso::sigma_sum_head(head_name, lhs_name, lhs_ty, rhs_ty, tail_ty)
    ///   : Ty::sigma(head_name, Ty::sum(lhs_name, lhs_ty, rhs_ty), tail_ty)
    ///   ≅ Ty::sum(
    ///       lhs_name,
    ///       Ty::sigma(
    ///           head_name,
    ///           lhs_ty,
    ///           Scope::make(Γ.len(), |lhs| tail_ty.bind(lhs.inj_lhs())),
    ///       ),
    ///       Ty::sigma(
    ///           head_name,
    ///           rhs_ty,
    ///           Scope::make(Γ.len(), |rhs| tail_ty.bind(rhs.inj_rhs())),
    ///       ),
    ///   )
    /// ```

    pub fn sigma_sum_head(
        head_name: Name,
        lhs_name: Name,
        lhs_ty: Ty,
        rhs_ty: Ty,
        tail_ty: Scope<Ty>,
    ) -> Iso {
        let ctx_len = max_all([
            head_name.ctx_len(),
            lhs_name.ctx_len(),
            lhs_ty.ctx_len(),
            rhs_ty.ctx_len(),
            tail_ty.ctx_len(),
        ]);

        let sum_ty = Ty::sum(lhs_name.clone(), lhs_ty.clone(), rhs_ty.clone());
        let sigma_ty = Ty::sigma(head_name.clone(), sum_ty.clone(), tail_ty.clone());
        let distributed_sum_ty = Ty::sum(
            lhs_name.clone(),
            Ty::sigma(
                head_name.clone(),
                lhs_ty.clone(),
                Scope::make(ctx_len + 3, |lhs| {
                    tail_ty.clone().bind(lhs.inj_lhs())
                }),
            ),
            Ty::sigma(
                head_name.clone(),
                rhs_ty.clone(),
                Scope::make(ctx_len + 3, |rhs| {
                    tail_ty.clone().bind(rhs.inj_rhs())
                }),
            ),
        );

        let fwd = Scope::make(ctx_len, |sigma| {
            let sum = sigma.clone().proj_head();
            let tail = sigma.proj_tail();

            sum
            .case(
                Scope::make(ctx_len + 1, |sum| {
                    Ty::pi(
                        Name::from("tail"),
                        tail_ty.clone().bind(sum),
                        Scope::constant(distributed_sum_ty.clone()),
                    )
                }),
                Scope::make(ctx_len + 1, |lhs| {
                    Tm::func(Scope::make(ctx_len + 2, |tail| {
                        lhs.pair(tail.clone()).inj_lhs()
                    }))
                }),
                Scope::make(ctx_len + 1, |rhs| {
                    Tm::func(Scope::make(ctx_len + 2, |tail| {
                        rhs.pair(tail.clone()).inj_rhs()
                    }))
                }),
            )
            .app(tail)
        });

        let rev = Scope::make(ctx_len, |sum| {
            sum
            .case(
                Scope::constant(sigma_ty.clone()),
                Scope::make(ctx_len + 1, |sigma| {
                    let lhs = sigma.clone().proj_head();
                    let tail = sigma.proj_tail();
                    lhs.inj_lhs().pair(tail)
                }),
                Scope::make(ctx_len + 1, |sigma| {
                    let rhs = sigma.clone().proj_head();
                    let tail = sigma.proj_tail();
                    rhs.inj_rhs().pair(tail)
                }),
            )
        });

        let fwd_rev = Scope::make(ctx_len, |sigma| {
            let sum = sigma.clone().proj_head();
            let tail = sigma.proj_tail();

            sum
            .case(
                Scope::make(ctx_len + 1, |sum| {
                    Ty::pi(
                        Name::from("tail"),
                        tail_ty.clone().bind(sum.clone()),
                        Scope::make(ctx_len + 2, |tail| {
                            let sigma = sum.pair(tail);
                            Ty::obs_equal(
                                sigma_ty.clone(),
                                rev.clone().bind(fwd.clone().bind(sigma.clone())),
                                sigma,
                            )
                        }),
                    )
                }),
                Scope::make(ctx_len + 1, |lhs| {
                    Tm::func(Scope::make(ctx_len + 2, |tail| {
                        lhs.inj_lhs().pair(tail).obs_refl()
                    }))
                }),
                Scope::make(ctx_len + 1, |rhs| {
                    Tm::func(Scope::make(ctx_len + 2, |tail| {
                        rhs.inj_rhs().pair(tail).obs_refl()
                    }))
                }),
            )
            .app(tail)
        });

        let rev_fwd = Scope::make(ctx_len, |sum| {
            sum
            .case(
                Scope::make(ctx_len + 1, |sum| {
                    Ty::obs_equal(
                        distributed_sum_ty.clone(),
                        fwd.clone().bind(rev.clone().bind(sum.clone())),
                        sum,
                    )
                }),
                Scope::make(ctx_len + 1, |sigma| {
                    let lhs = sigma.clone().proj_head();
                    let tail = sigma.proj_tail();
                    lhs.pair(tail).inj_lhs().obs_refl()
                }),
                Scope::make(ctx_len + 1, |sigma| {
                    let rhs = sigma.clone().proj_head();
                    let tail = sigma.proj_tail();
                    rhs.pair(tail).inj_rhs().obs_refl()
                }),
            )
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ head_name : Name
    /// Γ ⊢ head_head_name : Name
    /// Γ ⊢ head_head_ty : Type
    /// Γ ⊢ head_tail_ty : head_head_ty ⊢ Type
    /// Γ ⊢ tail_ty : Ty::sigma(head_head_name, head_head_ty, head_tail_ty) ⊢ Type
    /// ----
    /// Γ ⊢ Iso::sigma_sigma_head(
    ///     head_name,
    ///     head_head_name,
    ///     head_head_ty,
    ///     head_tail_ty,
    ///     tail_ty,
    /// ) : Ty::sigma(
    ///     head_name,
    ///     Ty::sigma(
    ///         head_head_name,
    ///         head_head_ty,
    ///         head_tail_ty,
    ///     ),
    ///     tail_ty,
    /// ) ≅ Ty::sigma(
    ///     head_head_name,
    ///     head_head_ty,
    ///     Scope::make(Γ.len(), |head_head| {
    ///         Ty::sigma(
    ///             head_name,
    ///             head_tail_ty.bind(head_head),
    ///             Scope::make(Γ.len() + 1, |head_tail| {
    ///                 tail_ty.bind(head_head.pair(head_tail))
    ///             }),
    ///         )
    ///     }),
    /// )
    /// ```

    pub fn sigma_sigma_head() -> Iso {
        let fwd = Scope::make(0, |sigma_0| {
            let head = sigma_0.clone().proj_head();
            let head_head = head.clone().proj_head();
            let head_tail = head.proj_tail();
            let tail = sigma_0.proj_tail();

            head_head.pair(head_tail.pair(tail))
        });

        let rev = Scope::make(0, |sigma_1| {
            let head_head = sigma_1.clone().proj_head();
            let sigma_1 = sigma_1.proj_tail();
            let head_tail = sigma_1.clone().proj_head();
            let tail = sigma_1.proj_tail();

            head_head.pair(head_tail).pair(tail)
        });

        let fwd_rev = Scope::make(0, |sigma_0| {
            sigma_0.obs_refl()
        });

        let rev_fwd = Scope::make(0, |sigma_1| {
            sigma_1.obs_refl()
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ head_name : Name
    /// Γ ⊢ head_ty : Type
    /// ----
    /// Γ ⊢ Iso::sigma_unit_tail()
    ///   : Ty::sigma(head_name, head_ty, Unit) ≅ head_ty
    /// ```

    pub fn sigma_unit_tail() -> Iso {
        let fwd = Scope::make(0, |pair| {
            pair.proj_head()
        });

        let rev = Scope::make(0, |head| {
            head.pair(Tm::unit())
        });

        let fwd_rev = Scope::make(0, |pair| {
            pair.obs_refl()
        });

        let rev_fwd = Scope::make(0, |head| {
            head.obs_refl()
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ head_name : Name
    /// Γ ⊢ head_ty : Type
    /// Γ ⊢ tail_ty : head_ty ⊢ Type
    /// Γ ⊢ unique_head : head_ty
    /// Γ ⊢ constrains : (head : head_ty), tail_ty ⊢ head == unique_head
    /// ----
    /// Γ ⊢ Iso::sigma_tail_constrains_head(
    ///     head_name,
    ///     head_ty,
    ///     tail_ty,
    ///     unique_head,
    ///     constrains,
    /// ) : Ty::sigma(head_name, head_ty, tail_ty) ≅ tail_ty.bind(unique_head)
    /// ```

    pub fn sigma_tail_constrains_head(
        head_name: Name,
        head_ty: Ty,
        tail_ty: Scope<Ty>,
        unique_head: Tm,
        constrains: Scope<Scope<Tm>>,
    ) -> Iso {
        let ctx_len = max_all([
            head_name.ctx_len(),
            head_ty.ctx_len(),
            tail_ty.ctx_len(),
            unique_head.ctx_len(),
            constrains.ctx_len(),
        ]);

        lazy_static! {
            static ref TAIL_NAME: Name = Name::from("tail");
        }

        let unique_bound_tail_ty = tail_ty.clone().bind(unique_head.clone());

        let fwd = Scope::make(ctx_len, |pair| {
            let head = pair.clone().proj_head();
            let tail = pair.proj_tail();

            tail_ty
            .clone()
            .bind_eq(
                head.clone(),
                constrains.clone().bind(head.clone()).bind(tail.clone()),
            )
            .cast(
                tail_ty.clone().bind(head),
                unique_bound_tail_ty.clone(),
                tail,
            )
        });

        let rev = Scope::make(ctx_len, |tail| {
            unique_head.clone().pair(tail)
        });

        let fwd_rev = Scope::make(ctx_len, |pair| {
            let head = pair.clone().proj_head();
            let tail = pair.clone().proj_tail();

            tail_ty
            .clone()
            .bind_eq(
                head.clone(),
                constrains.clone().bind(head.clone()).bind(tail.clone()),
            )
            .cast_round_trip(
                tail_ty.bind(head),
                unique_bound_tail_ty,
                tail,
            )
        });

        let rev_fwd = Scope::make(ctx_len, |_tail| {
            Tm::cast_refl()
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ arg_name : Name
    /// Γ ⊢ arg_ty_0 : Type
    /// Γ ⊢ arg_ty_1 : Type
    /// Γ ⊢ res_ty : arg_ty_0 ⊢ Type
    /// Γ ⊢ arg_iso : arg_ty_0 ≅ arg_ty_1
    /// ----
    /// Γ ⊢ Iso::dependent_pi_arg_congruence(
    ///     arg_name,
    ///     arg_ty_0,
    ///     arg_ty_1,
    ///     res_ty,
    ///     arg_iso,
    /// ) : Ty::pi(arg_name, arg_ty_0, res_ty) ≅ Ty::pi(arg_name, arg_ty_1, res_ty)
    /// ```

    pub fn dependent_pi_arg_congruence(
        arg_name: Name,
        arg_ty_0: Ty,
        arg_ty_1: Ty,
        res_ty: Scope<Ty>,
        arg_iso: Iso,
    ) -> Iso {
        let ctx_len = max_all([
            arg_name.ctx_len(),
            arg_ty_0.ctx_len(),
            arg_ty_1.ctx_len(),
            res_ty.ctx_len(),
            arg_iso.ctx_len(),
        ]);

        let Iso {
            fwd: arg_fwd, rev: arg_rev, fwd_rev: arg_fwd_rev, rev_fwd: arg_rev_fwd,
        } = arg_iso;

        lazy_static! {
            static ref RES_NAME: Name = Name::from("res");
        }

        let fwd = Scope::make(ctx_len, |func| {
            Tm::func(Scope::make(ctx_len + 1, |arg_1| {
                func.app(arg_rev.clone().bind(arg_1))
            }))
        });

        let rev = Scope::make(ctx_len, |func| {
            Tm::func(Scope::make(ctx_len + 1, |arg_0| {
                let arg_1 = arg_fwd.clone().bind(arg_0.clone());
                let arg_0_round_trip = arg_rev.clone().bind(arg_1.clone());

                res_ty
                .clone()
                .bind_eq(
                    arg_0_round_trip.clone(),
                    arg_fwd_rev.clone().bind(arg_0.clone()),
                )
                .cast(
                    res_ty.clone().bind(arg_0_round_trip),
                    res_ty.clone().bind(arg_0),
                    func.app(arg_1),
                )
            }))
        });

        let fwd_rev = Scope::make(ctx_len, |func| {
            Tm::func(Scope::make(ctx_len + 1, |arg_0| {
                let arg_0_round_trip = arg_rev.clone().bind(arg_fwd.clone().bind(arg_0.clone()));

                arg_fwd_rev
                .bind(arg_0)
                .obs_cong(
                    Scope::make(ctx_len + 2, |arg_0| {
                        Scope::make(ctx_len + 3, |arg_eq| {
                            Ty::obs_equal(
                                res_ty.clone().bind(arg_0.clone()),
                                res_ty
                                .clone()
                                .bind_eq(
                                    arg_0_round_trip.clone(),
                                    arg_eq,
                                )
                                .cast(
                                    res_ty.clone().bind(arg_0_round_trip.clone()),
                                    res_ty.clone().bind(arg_0.clone()),
                                    func.clone().app(arg_0_round_trip),
                                ),
                                func.app(arg_0),
                            )
                        })
                    }),
                    Tm::cast_refl(),
                )
            }))
        });

        let rev_fwd = Scope::make(ctx_len, |func| {
            let res_ty_1 = Scope::make(ctx_len + 1, |arg_1| {
                res_ty.clone().bind(arg_rev.clone().bind(arg_1))
            });

            Tm::func(Scope::make(ctx_len + 1, |arg_1| {
                let arg_1_round_trip = arg_fwd.bind(arg_rev.bind(arg_1.clone()));

                arg_rev_fwd
                .bind(arg_1)
                .obs_cong(
                    Scope::make(ctx_len + 2, |arg_1| {
                        let bound_res_ty_1 = res_ty_1.clone().bind(arg_1.clone());
                        Scope::make(ctx_len + 3, |arg_eq| {
                            Ty::obs_equal(
                                bound_res_ty_1.clone(),
                                res_ty_1
                                .clone()
                                .bind_eq(
                                    arg_1_round_trip.clone(),
                                    arg_eq,
                                )
                                .cast(
                                    res_ty_1.bind(arg_1_round_trip.clone()),
                                    bound_res_ty_1,
                                    func.clone().app(arg_1_round_trip),
                                ),
                                func.app(arg_1),
                            )
                        })
                    }),
                    Tm::cast_refl(),
                )
            }))
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ arg_name : Name
    /// Γ ⊢ arg_ty : Type
    /// Γ ⊢ res_ty_0 : arg_ty ⊢ Type
    /// Γ ⊢ res_ty_1 : arg_ty ⊢ Type
    /// Γ ⊢ res_iso : arg_ty |- res_ty_0 ≅ res_ty_1
    /// ----
    /// Γ ⊢ Iso::dependent_pi_res_congruence(
    ///     arg_name,
    ///     arg_ty,
    ///     res_ty_0,
    ///     res_ty_1,
    ///     res_iso,
    /// ) : Ty::pi(arg_name, arg_ty, res_ty_0) ≅ Ty::pi(arg_name, arg_ty, res_ty_1)
    /// ```

    pub fn dependent_pi_res_congruence(
        arg_name: Name,
        arg_ty: Ty,
        res_ty_0: Scope<Ty>,
        res_ty_1: Scope<Ty>,
        res_iso: Scope<Iso>,
    ) -> Iso {
        let ctx_len = max_all([
            arg_name.ctx_len(),
            arg_ty.ctx_len(),
            res_ty_0.ctx_len(),
            res_ty_1.ctx_len(),
            res_iso.ctx_len(),
        ]);

        let (res_fwd, res_rev, res_fwd_rev, res_rev_fwd) = res_iso.map_multi(
            ctx_len,
            |_, res_iso| {
                let Iso { fwd, rev, fwd_rev, rev_fwd } = res_iso;
                (fwd, rev, fwd_rev, rev_fwd)
            },
        );

        let fwd = Scope::make(ctx_len, |func| {
            Tm::func(Scope::make(ctx_len + 1, |arg| {
                res_fwd
                .bind(arg.clone())
                .bind(func.app(arg))
            }))
        });

        let rev = Scope::make(ctx_len, |func| {
            Tm::func(Scope::make(ctx_len + 1, |arg| {
                res_rev
                .bind(arg.clone())
                .bind(func.app(arg))
            }))
        });

        let fwd_rev = Scope::make(ctx_len, |func| {
            Tm::func(Scope::make(ctx_len + 1, |arg| {
                res_fwd_rev
                .bind(arg.clone())
                .bind(func.app(arg))
            }))
        });

        let rev_fwd = Scope::make(ctx_len, |func| {
            Tm::func(Scope::make(ctx_len + 1, |arg| {
                res_rev_fwd
                .bind(arg.clone())
                .bind(func.app(arg))
            }))
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ arg_name : Name
    /// Γ ⊢ res_ty : Ty::never() ⊢ Type
    /// ----
    /// Γ ⊢ Iso::pi_never_arg(res_ty)
    ///   : Ty::pi(arg_name, Ty::never(), res_ty)
    ///   ≅ Ty::unit()
    /// ```

    pub fn pi_never_arg(
        res_ty: Scope<Ty>,
    ) -> Iso {
        let ctx_len = res_ty.ctx_len();

        let fwd = Scope::constant(Tm::unit());
        let rev = Scope::constant(Tm::func(Scope::make(ctx_len + 1, |never| {
            never.explode(res_ty.clone())
        })));

        let fwd_rev = Scope::make(ctx_len, |func| {
            Tm::func(Scope::make(ctx_len + 1, |never| {
                never
                .clone()
                .explode(Scope::constant(
                    Ty::obs_equal(
                        res_ty.clone().bind(never.clone()),
                        func.app(never.clone()),
                        never.explode(res_ty),
                    )
                ))
            }))
        });

        let rev_fwd = Scope::constant(Tm::unit().obs_refl());

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ arg_name : Name
    /// Γ ⊢ res_ty : Ty::unit() ⊢ Type
    /// ----
    /// Γ ⊢ Iso::pi_unit_arg(res_ty)
    ///   : Ty::pi(arg_name, Ty::unit(), res_ty)
    ///   ≅ res_ty.bind(Tm::unit())
    /// ```

    pub fn pi_unit_arg(
        res_ty: Scope<Ty>,
    ) -> Iso {
        let ctx_len = res_ty.ctx_len();

        let fwd = Scope::make(ctx_len, |func| {
            func.app(Tm::unit())
        });

        let rev = Scope::make(ctx_len, |res| {
            Tm::func(Scope::constant(res))
        });

        let fwd_rev = Scope::make(ctx_len, |func| func.obs_refl());

        let rev_fwd = Scope::make(ctx_len, |res| res.obs_refl());

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ arg_name : Name
    /// Γ ⊢ arg_ty : Type
    /// ----
    /// Γ ⊢ Iso::pi_unit_res() : Ty::pi(arg_name, arg_ty, Unit) ≅ Unit
    /// ```

    pub fn pi_unit_res() -> Iso {
        let fwd = Scope::constant(Tm::unit());
        let rev = Scope::constant(Tm::func(Scope::constant(Tm::unit())));
        let fwd_rev = Scope::make(0, |func| func.obs_refl());
        let rev_fwd = Scope::constant(Tm::unit());
        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// ----
    /// Γ ⊢ Iso::nat_into_sum_of_zero_and_succ()
    ///   : Ty::nat()
    ///   ≅ Ty::sum(
    ///     Name::from("zero"),
    ///     Ty::unit(),
    ///     Ty::sum(
    ///         Name::from("succ"),
    ///         Ty::nat(),
    ///         Ty::never(),
    ///     )
    /// )
    /// ```

    pub fn nat_into_sum_of_zero_and_succ() -> Iso {
        let output_ty = Ty::sum(
            Name::from("zero"),
            Ty::unit(),
            Ty::sum(
                Name::from("succ"),
                Ty::nat(),
                Ty::never(),
            ),
        );

        let fwd = Scope::make(0, |n| {
            n
            .fold(
                Scope::constant(output_ty.clone()),
                Tm::unit().inj_lhs(),
                Scope::make(1, |n| {
                    Scope::constant(
                        n.inj_lhs().inj_rhs()
                    )
                }),
            )
        });

        let rev = Scope::make(0, |sum| {
            sum
            .case(
                Scope::constant(Ty::nat()),
                Scope::constant(Tm::zero()),
                Scope::make(1, |sum| {
                    sum
                    .case(
                        Scope::constant(Ty::nat()),
                        Scope::make(2, |n| n.succs(Ubig::ONE)),
                        Scope::make(2, |never| {
                            never.explode(Scope::constant(Ty::nat()))
                        }),
                    )
                }),
            )
        });

        let fwd_rev = Scope::make(0, |n| {
            n
            .fold(
                Scope::make(1, |n| {
                    Ty::obs_equal(
                        Ty::nat(),
                        rev.clone().bind(fwd.clone().bind(n.clone())),
                        n,
                    )
                }),
                Tm::zero().obs_refl(),
                Scope::make(1, |n| {
                    Scope::constant(
                        n.succs(Ubig::ONE).obs_refl()
                    )
                })
            )
        });

        let rev_fwd = Scope::make(0, |sum| {
            sum
            .case(
                Scope::make(1, |sum| {
                    Ty::obs_equal(
                        output_ty.clone(),
                        fwd.clone().bind(rev.clone().bind(sum.clone())),
                        sum,
                    )
                }),
                Scope::constant(
                    Tm::unit().inj_lhs().obs_refl()
                ),
                Scope::make(1, |sum| {
                    sum
                    .case(
                        Scope::make(2, |sum| {
                            let sum = sum.inj_rhs();
                            Ty::obs_equal(
                                output_ty.clone(),
                                fwd.clone().bind(rev.clone().bind(sum.clone())),
                                sum,
                            )
                        }),
                        Scope::make(2, |n| {
                            n.inj_lhs().inj_rhs().obs_refl()
                        }),
                        Scope::make(2, |never| {
                            let sum = never.clone().inj_rhs().inj_rhs();
                            never
                            .explode(
                                Scope::constant(
                                    Ty::obs_equal(
                                        output_ty.clone(),
                                        fwd.clone().bind(rev.clone().bind(sum.clone())),
                                        sum,
                                    )
                                )
                            )
                        }),
                    )
                }),
            )
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }
}

