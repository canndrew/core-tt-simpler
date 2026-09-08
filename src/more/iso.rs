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

    fn try_strengthen_index(self, _var_index: usize) -> Option<Iso> {
        todo!()
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
            fwd_rev: Scope::make(0, |tm| tm.refl()),
            rev_fwd: Scope::make(0, |tm| tm.refl()),
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
                Ty::equal(
                    from_ty.clone(),
                    rev.clone().bind(never),
                    tm,
                )
            ))
        });

        let rev_fwd = Scope::make(ctx_len, |never| {
            never
            .clone()
            .explode(Scope::constant(
                Ty::equal(
                    Ty::never(),
                    fwd.clone().bind(rev.clone().bind(never.clone())),
                    never,
                )
            ))
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
        eq_ty: Ty,
        eq_tm: Tm,
    ) -> Iso {
        let ctx_len = max_all([
            eq_ty.ctx_len(),
            eq_tm.ctx_len(),
        ]);
        let fwd = Scope::constant(Tm::unit());
        let rev = Scope::constant(eq_tm.clone().refl());
        let fwd_rev = Scope::make(ctx_len, |elim| {
            elim
            .unique_identity(
                Scope::make(ctx_len, |elim| {
                    Ty::equal(
                        Ty::equal(eq_ty, eq_tm.clone(), eq_tm.clone()),
                        elim,
                        eq_tm.clone().refl(),
                    )
                }),
                eq_tm.refl().refl(),
            )
        });
        let rev_fwd = Scope::constant(Tm::unit().refl());

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ pred_tm_0 : Nat
    /// Γ ⊢ pred_tm_1 : Nat
    /// ----
    /// Γ ⊢ Iso::succs_of_tms_equal_to_tms_equal(
    ///     pred_tm_0,
    ///     succ_count,
    /// ) : (pred_tm_0.succs(succ_count) == pred_tm_1.succs(succ_count)) ≅ (pred_tm_0 == pred_tm_1)
    /// ```

    pub fn succs_of_tms_equal_to_tms_equal(
        pred_tm_0: Tm,
        succ_count: impl Into<Ubig>,
    ) -> Iso {
        let ctx_len = pred_tm_0.ctx_len();

        let succ_count = succ_count.into();
        let fwd = Scope::make(ctx_len, |tms_eq| {
            tms_eq.succs_injective(pred_tm_0.clone(), succ_count.clone())
        });
        let rev = Scope::make(ctx_len, |pred_tms_eq| {
            Scope::make(0, |tm| tm.succs(succ_count.clone()))
            .bind_eq(
                Ty::nat(),
                pred_tm_0.clone(),
                pred_tms_eq,
            )
        });

        let fwd_rev = Scope::make(ctx_len, |tms_eq| {
            Tm::equality_contractible(
                Ty::nat(),
                pred_tm_0.clone().succs(succ_count),
                rev.clone().bind(fwd.clone().bind(tms_eq.clone())),
                tms_eq,
            )
        });

        let rev_fwd = Scope::make(ctx_len, |pred_tms_eq| {
            Tm::equality_contractible(
                Ty::nat(),
                pred_tm_0,
                fwd.clone().bind(rev.clone().bind(pred_tms_eq.clone())),
                pred_tms_eq,
            )
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ eq_ty : Type
    /// Γ ⊢ eq_tm_0 : eq_ty
    /// Γ ⊢ eq_tm_1 : eq_ty
    /// Γ ⊢ eq_0 : eq_tm_0 == eq_tm_1
    /// Γ ⊢ eq_1 : eq_tm_0 == eq_tm_1
    /// ----
    /// Γ ⊢ Iso::equality_of_equalities_to_unit(
    ///     eq_ty,
    ///     eq_tm_0,
    ///     eq_tm_1,
    ///     eq_0,
    ///     eq_1,
    /// ) : (eq_0 == eq_1) ≅ Unit
    /// ```

    pub fn equality_of_equalities_to_unit(
        eq_ty: Ty,
        eq_tm_0: Tm,
        eq_tm_1: Tm,
        eq_0: Tm,
        eq_1: Tm,
    ) -> Iso {
        let ctx_len = max_all([
            eq_ty.ctx_len(),
            eq_tm_0.ctx_len(),
            eq_tm_1.ctx_len(),
            eq_0.ctx_len(),
            eq_1.ctx_len(),
        ]);
        let eqs_eq = Tm::equality_contractible(eq_ty.clone(), eq_tm_0.clone(), eq_0.clone(), eq_1);
        let fwd = Scope::constant(Tm::unit());
        let rev = Scope::constant(eqs_eq.clone());

        let fwd_rev = Scope::make(ctx_len, |tm| {
            Tm::equality_contractible(
                Ty::equal(eq_ty, eq_tm_0, eq_tm_1),
                eq_0,
                eqs_eq,
                tm,
            )
        });
        let rev_fwd = Scope::constant(Tm::unit().refl());

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ lhs_name : Name
    /// Γ ⊢ lhs_ty : Ty
    /// Γ ⊢ rhs_ty : Ty
    /// Γ ⊢ lhs_tm_0 : lhs_ty
    /// Γ ⊢ lhs_tm_1 : lhs_ty
    /// ----
    /// Γ ⊢ Iso::inj_lhs_of_tms_equal_to_tms_equal(
    ///     lhs_name,
    ///     lhs_ty,
    ///     rhs_ty,
    ///     lhs_tm_0,
    /// ) : (lhs_tm_0.inj_lhs() == lhs_tm_1.inj_lhs()) ≅ (lhs_tm_0 == lhs_tm_1)
    /// ```

    pub fn inj_lhs_of_tms_equal_to_tms_equal(
        lhs_name: Name,
        lhs_ty: Ty,
        rhs_ty: Ty,
        lhs_tm_0: Tm,
    ) -> Iso {
        let ctx_len = max_all([
            lhs_name.ctx_len(),
            lhs_ty.ctx_len(),
            rhs_ty.ctx_len(),
            lhs_tm_0.ctx_len(),
        ]);

        let sum_ty = Ty::sum(lhs_name, lhs_ty.clone(), rhs_ty);

        let fwd = Scope::make(ctx_len, |sum_eq| {
            sum_eq.inj_lhs_injective(lhs_ty.clone(), lhs_tm_0.clone())
        });

        let rev = Scope::make(ctx_len, |lhs_eq| {
            Scope::make(ctx_len + 1, |lhs_tm| lhs_tm.inj_lhs())
            .bind_eq(
                sum_ty.clone(),
                lhs_tm_0.clone(),
                lhs_eq,
            )
        });

        let fwd_rev = Scope::make(ctx_len, |sum_eq| {
            Tm::equality_contractible(
                sum_ty,
                lhs_tm_0.clone().inj_lhs(),
                rev.clone().bind(fwd.clone().bind(sum_eq.clone())),
                sum_eq,
            )
        });

        let rev_fwd = Scope::make(ctx_len, |lhs_eq| {
            Tm::equality_contractible(
                lhs_ty,
                lhs_tm_0,
                fwd.clone().bind(rev.clone().bind(lhs_eq.clone())),
                lhs_eq,
            )
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    /// ```ignore
    /// Γ ⊢ lhs_name : Name
    /// Γ ⊢ lhs_ty : Ty
    /// Γ ⊢ rhs_ty : Ty
    /// Γ ⊢ rhs_tm_0 : rhs_ty
    /// Γ ⊢ rhs_tm_1 : rhs_ty
    /// ----
    /// Γ ⊢ Iso::inj_rhs_of_tms_equal_to_tms_equal(
    ///     lhs_name,
    ///     lhs_ty,
    ///     rhs_ty,
    ///     rhs_tm_0,
    /// ) : (rhs_tm_0.inj_rhs() == rhs_tm_1.inj_rhs()) ≅ (rhs_tm_0 == rhs_tm_1)
    /// ```

    pub fn inj_rhs_of_tms_equal_to_tms_equal(
        lhs_name: Name,
        lhs_ty: Ty,
        rhs_ty: Ty,
        rhs_tm_0: Tm,
    ) -> Iso {
        let ctx_len = max_all([
            lhs_name.ctx_len(),
            lhs_ty.ctx_len(),
            rhs_ty.ctx_len(),
            rhs_tm_0.ctx_len(),
        ]);

        let sum_ty = Ty::sum(lhs_name, lhs_ty, rhs_ty.clone());

        let fwd = Scope::make(ctx_len, |sum_eq| {
            sum_eq.inj_rhs_injective(rhs_ty.clone(), rhs_tm_0.clone())
        });

        let rev = Scope::make(ctx_len, |rhs_eq| {
            Scope::make(ctx_len + 1, |rhs_tm| rhs_tm.inj_rhs())
            .bind_eq(
                sum_ty.clone(),
                rhs_tm_0.clone(),
                rhs_eq,
            )
        });

        let fwd_rev = Scope::make(ctx_len, |sum_eq| {
            Tm::equality_contractible(
                sum_ty,
                rhs_tm_0.clone().inj_rhs(),
                rev.clone().bind(fwd.clone().bind(sum_eq.clone())),
                sum_eq,
            )
        });

        let rev_fwd = Scope::make(ctx_len, |rhs_eq| {
            Tm::equality_contractible(
                rhs_ty,
                rhs_tm_0,
                fwd.clone().bind(rev.clone().bind(rhs_eq.clone())),
                rhs_eq,
            )
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    pub fn equality_of_non_dependent_pairs_to_non_dependent_pair_of_equalities(
        head_name: Name,
        head_ty: Ty,
        tail_ty: Ty,
        head_0: Tm,
        head_1: Tm,
        tail_0: Tm,
        tail_1: Tm,
    ) -> Iso {
        let ctx_len = max_all([
            head_name.ctx_len(),
            head_ty.ctx_len(),
            tail_ty.ctx_len(),
            head_0.ctx_len(),
            head_1.ctx_len(),
            tail_0.ctx_len(),
            tail_1.ctx_len(),
        ]);

        let fwd = Scope::make(ctx_len, |pair_eq| {
            Tm::equality_of_non_dependent_pairs_to_non_dependent_pair_of_equalities(
                head_name.clone(),
                head_ty.clone(),
                tail_ty.clone(),
                head_0.clone(),
                tail_0.clone(),
                pair_eq,
            )
        });

        let rev = Scope::make(ctx_len, |eq_pair| {
            Tm::non_dependent_pair_of_equalities_to_equality_of_non_dependent_pairs(
                head_name.clone(),
                head_ty.clone(),
                tail_ty.clone(),
                head_0.clone(),
                tail_0.clone(),
                tail_1.clone(),
                eq_pair.clone().proj_head(),
                eq_pair.proj_tail(),
            )
        });

        let fwd_rev = Scope::make(ctx_len, |pair_eq| {
            Tm::equality_contractible(
                Ty::sigma(head_name.clone(), head_ty.clone(), Scope::constant(tail_ty.clone())),
                head_0.clone().pair(tail_0.clone()),
                rev.clone().bind(fwd.clone().bind(pair_eq.clone())),
                pair_eq,
            )
        });

        let rev_fwd = Scope::make(ctx_len, |eq_pair_1| {
            let eq_pair_0 = fwd.clone().bind(rev.clone().bind(eq_pair_1.clone()));

            let head_eq_0 = eq_pair_0.clone().proj_head();
            let tail_eq_0 = eq_pair_0.proj_tail();
            let head_eq_1 = eq_pair_1.clone().proj_head();
            let tail_eq_1 = eq_pair_1.proj_tail();

            let head_eq_eq = Tm::equality_contractible(
                head_ty.clone(), head_0.clone(), head_eq_0.clone(), head_eq_1,
            );
            let tail_eq_eq = Tm::equality_contractible(
                tail_ty.clone(), tail_0.clone(), tail_eq_0.clone(), tail_eq_1.clone(),
            );
            Tm::non_dependent_pair_of_equalities_to_equality_of_non_dependent_pairs(
                head_name,
                Ty::equal(head_ty, head_0, head_1),
                Ty::equal(tail_ty, tail_0, tail_1),
                head_eq_0,
                tail_eq_0,
                tail_eq_1,
                head_eq_eq,
                tail_eq_eq,
            )
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    pub fn equality_of_dependent_pairs_to_dependent_pair_of_equalities(
        head_name: Name,
        head_ty: Ty,
        tail_ty: Scope<Ty>,
        head_0: Tm,
        head_1: Tm,
        tail_0: Tm,
        tail_1: Tm,
    ) -> Iso {
        let ctx_len = max_all([
            head_name.ctx_len(),
            head_ty.ctx_len(),
            tail_ty.ctx_len(),
            head_0.ctx_len(),
            head_1.ctx_len(),
            tail_0.ctx_len(),
            tail_1.ctx_len(),
        ]);

        let fwd = Scope::make(ctx_len, |pair_eq| {
            Tm::equality_of_dependent_pairs_to_dependent_pair_of_equalities(
                head_name.clone(),
                head_ty.clone(),
                tail_ty.clone(),
                head_0.clone(),
                tail_0.clone(),
                pair_eq,
            )
        });

        let rev = Scope::make(ctx_len, |eq_pair| {
            Tm::dependent_pair_of_equalities_to_equality_of_dependent_pairs(
                head_name.clone(),
                head_ty.clone(),
                tail_ty.clone(),
                head_0.clone(),
                tail_0.clone(),
                tail_1.clone(),
                eq_pair.clone().proj_head(),
                eq_pair.proj_tail(),
            )
        });

        let fwd_rev = Scope::make(ctx_len, |pair_eq| {
            Tm::equality_contractible(
                Ty::sigma(head_name.clone(), head_ty.clone(), tail_ty.clone()),
                head_0.clone().pair(tail_0.clone()),
                rev.clone().bind(fwd.clone().bind(pair_eq.clone())),
                pair_eq,
            )
        });

        let rev_fwd = Scope::make(ctx_len, |eq_pair_1| {
            lazy_static! {
                static ref TAIL_EQ_NAME: Name = Name::from("tail_eq");
            }

            let eq_pair_0 = fwd.clone().bind(rev.clone().bind(eq_pair_1.clone()));
            
            let head_eq_0 = eq_pair_0.clone().proj_head();
            let tail_eq_0 = eq_pair_0.clone().proj_tail();
            let head_eq_1 = eq_pair_1.clone().proj_head();
            let tail_eq_1 = eq_pair_1.proj_tail();

            let head_eq_eq = Tm::equality_contractible(
                head_ty.clone(), head_0.clone(), head_eq_0.clone(), head_eq_1.clone(),
            );

            let tail_ty_bind_head_0 = tail_ty.clone().bind(head_0.clone());
            let eq_pair_ty = Ty::sigma(
                head_name.clone(),
                Ty::equal(head_ty, head_0.clone(), head_1),
                Scope::make(ctx_len + 3, |head_eq| {
                    Ty::heterogeneous_equal(
                        tail_ty_bind_head_0.clone(),
                        tail_ty.clone().bind_eq(head_0.clone(), head_eq),
                        tail_0.clone(),
                        tail_1.clone(),
                    )
                }),
            );

            head_eq_eq
            .cong(
                Scope::make(ctx_len, |head_eq_1| {
                    Scope::constant(
                        Ty::pi(
                            TAIL_EQ_NAME.clone(),
                            Ty::heterogeneous_equal(
                                tail_ty_bind_head_0.clone(),
                                tail_ty.clone().bind_eq(head_0.clone(), head_eq_1.clone()),
                                tail_0.clone(),
                                tail_1.clone(),
                            ),
                            Scope::make(ctx_len + 2, |tail_eq_1| {
                                Ty::equal(
                                    eq_pair_ty.clone(),
                                    eq_pair_0.clone(),
                                    head_eq_1.pair(tail_eq_1),
                                )
                            }),
                        )
                    )
                }),
                Tm::func(Scope::make(ctx_len, |tail_eq_1| {
                    Tm::heterogeneous_equality_contractible(
                        tail_ty_bind_head_0,
                        tail_ty.bind_eq(head_0, head_eq_0.clone()),
                        tail_0,
                        tail_1,
                        tail_eq_0,
                        tail_eq_1,
                    )
                    .cong(
                        Scope::make(ctx_len + 1, |tail_eq_1| {
                            Scope::constant(
                                Ty::equal(
                                    eq_pair_ty,
                                    eq_pair_0.clone(),
                                    head_eq_0.pair(tail_eq_1),
                                )
                            )
                        }),
                        eq_pair_0.refl(),
                    )
                })),
            )
            .app(tail_eq_1)
        });

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
                    Ty::equal(
                        sum_ty_0.clone(),
                        rev.clone().bind(fwd.clone().bind(sum_0.clone())),
                        sum_0,
                    )
                }),
                Scope::make(ctx_len + 1, |lhs_0| {
                    lhs_fwd_rev
                    .bind(lhs_0.clone())
                    .map_eq(
                        ctx_len + 2,
                        sum_ty_0.clone(),
                        lhs_rev.clone().bind(lhs_fwd.clone().bind(lhs_0)),
                        |lhs| lhs.inj_lhs(),
                    )
                }),
                Scope::make(ctx_len + 1, |rhs_0| {
                    rhs_fwd_rev
                    .bind(rhs_0.clone())
                    .map_eq(
                        ctx_len + 2,
                        sum_ty_0,
                        rhs_rev.clone().bind(rhs_fwd.clone().bind(rhs_0)),
                        |rhs| rhs.inj_rhs(),
                    )
                }),
            )
        });

        let rev_fwd = Scope::make(ctx_len, |sum_1| {
            sum_1
            .case(
                Scope::make(ctx_len + 1, |sum_1| {
                    Ty::equal(
                        sum_ty_1.clone(),
                        fwd.clone().bind(rev.clone().bind(sum_1.clone())),
                        sum_1,
                    )
                }),
                Scope::make(ctx_len + 1, |lhs_1| {
                    lhs_rev_fwd
                    .bind(lhs_1.clone())
                    .map_eq(
                        ctx_len + 2,
                        sum_ty_1.clone(),
                        lhs_fwd.bind(lhs_rev.bind(lhs_1)),
                        |lhs| lhs.inj_lhs(),
                    )
                }),
                Scope::make(ctx_len + 1, |rhs_1| {
                    rhs_rev_fwd
                    .bind(rhs_1.clone())
                    .map_eq(
                        ctx_len + 2,
                        sum_ty_1,
                        rhs_fwd.bind(rhs_rev.bind(rhs_1)),
                        |rhs| rhs.inj_rhs(),
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
                    Ty::equal(
                        sum_ty.clone(),
                        rev.clone().bind(fwd.clone().bind(sum.clone())),
                        sum,
                    )
                }),
                Scope::make(ctx_len + 1, |never| {
                    let sum = never.clone().inj_lhs();
                    never
                    .explode(Scope::constant(
                        Ty::equal(
                            sum_ty,
                            rev.clone().bind(fwd.clone().bind(sum.clone())),
                            sum,
                        )
                    ))
                }),
                Scope::make(ctx_len + 1, |rhs| {
                    rhs.inj_rhs().refl()
                }),
            )
        });

        let rev_fwd = Scope::make(ctx_len, |rhs| {
            rhs.refl()
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
                    Ty::equal(
                        sum_ty.clone(),
                        rev.clone().bind(fwd.clone().bind(sum.clone())),
                        sum,
                    )
                }),
                Scope::make(ctx_len + 1, |lhs| {
                    lhs.inj_lhs().refl()
                }),
                Scope::make(ctx_len + 1, |never| {
                    let sum = never.clone().inj_rhs();
                    never
                    .explode(Scope::constant(
                        Ty::equal(
                            sum_ty,
                            rev.clone().bind(fwd.clone().bind(sum.clone())),
                            sum,
                        )
                    ))
                }),
            )
        });

        let rev_fwd = Scope::make(ctx_len, |lhs| {
            lhs.refl()
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

        let sigma_ty_0 = Ty::sigma(
            head_name.clone(),
            head_ty_0.clone(),
            tail_ty_0.clone(),
        );
        let sigma_ty_1 = Ty::sigma(
            head_name,
            head_ty_1.clone(),
            tail_ty_1.clone(),
        );

        let fwd = Scope::make(ctx_len, |pair_0| {
            let head_0 = pair_0.clone().proj_head();
            let tail_0 = pair_0.proj_tail();
            let head_1 = head_fwd.clone().bind(head_0.clone());
            let tail_1 = {
                tail_ty_0
                .clone()
                .bind_eq(
                    head_0.clone(),
                    head_fwd_rev
                    .clone()
                    .bind(head_0.clone())
                    .symmetry(
                        head_ty_0.clone(),
                        head_rev.clone().bind(head_1.clone()),
                    )
                )
                .transport(
                    tail_ty_0.clone().bind(head_0),
                    tail_0,
                    TAIL_NAME.clone(),
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
            let tail_0 = pair_0.clone().proj_tail();

            head_fwd_rev
            .clone()
            .bind(head_0.clone())
            .symmetry(
                head_ty_0.clone(),
                head_rev.clone().bind(head_fwd.clone().bind(head_0.clone())),
            )
            .cong(
                Scope::make(ctx_len + 1, |head_2| {
                    Scope::make(ctx_len + 2, |head_eq| {
                        Ty::equal(
                            sigma_ty_0,
                            head_2
                            .pair(
                                tail_ty_0
                                .clone()
                                .bind_eq(head_0.clone(), head_eq)
                                .transport(
                                    tail_ty_0.clone().bind(head_0),
                                    tail_0,
                                    TAIL_NAME.clone(),
                                )
                            ),
                            pair_0.clone(),
                        )
                    })
                }),
                pair_0.refl(),
            )
        });

        let rev_fwd = Scope::make(ctx_len, |pair_1| {
            let head_1 = pair_1.clone().proj_head();
            let tail_1 = pair_1.clone().proj_tail();

            let head_0 = head_rev.clone().bind(head_1.clone());
            let head_1_round_trip = head_fwd.bind(head_0.clone());
            let head_1_eq_head_1_round_trip = {
                head_rev_fwd
                .bind(head_1.clone())
                .symmetry(
                    head_ty_1,
                    head_1_round_trip.clone(),
                )
            };
            let tail_ty_at_head_0 = tail_ty_0.clone().bind(head_0.clone());

            let tail_ty_eq_0 = {
                tail_ty_0
                .bind_eq(
                    head_0.clone(),
                    head_fwd_rev
                    .bind(head_0)
                    .symmetry(
                        head_ty_0,
                        head_rev.bind(head_1_round_trip.clone()),
                    )
                )
            };
            let tail_ty_eq_1 = {
                tail_ty_1
                .clone()
                .bind_eq(
                    head_1.clone(),
                    head_1_eq_head_1_round_trip.clone(),
                )
            };

            Tm::equality_contractible(
                Ty::universe(),
                tail_ty_at_head_0.clone().into_tm(),
                tail_ty_eq_0.clone(),
                tail_ty_eq_1,
            )
            .map_eq(
                ctx_len + 1,
                sigma_ty_1.clone(),
                tail_ty_eq_0,
                |tail_ty_eq| {
                    head_1_round_trip
                    .pair(
                        tail_ty_eq
                        .transport(
                            tail_ty_at_head_0.clone(),
                            tail_1.clone(),
                            TAIL_NAME.clone(),
                        )
                    )
                },
            )
            .transitivity(
                head_1_eq_head_1_round_trip
                .cong(
                    Scope::make(ctx_len + 1, |head_2| {
                        Scope::make(ctx_len + 2, |head_eq| {
                            Ty::equal(
                                sigma_ty_1.clone(),
                                head_2
                                .pair(
                                    tail_ty_1
                                    .bind_eq(
                                        head_1,
                                        head_eq,
                                    )
                                    .transport(
                                        tail_ty_at_head_0,
                                        tail_1,
                                        TAIL_NAME.clone(),
                                    ),
                                ),
                                pair_1.clone(),
                            )
                        })
                    }),
                    pair_1.clone().refl(),
                ),
                sigma_ty_1,
                fwd.clone().bind(rev.clone().bind(pair_1.clone())),
                pair_1,
            )
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

            tail_fwd_rev
            .clone()
            .bind(head.clone())
            .bind(tail_0.clone())
            .map_eq(
                ctx_len + 1,
                Ty::sigma(head_name.clone(), head_ty.clone(), tail_ty_0),
                tail_rev
                .clone()
                .bind(head.clone())
                .bind(tail_fwd.clone().bind(head.clone()).bind(tail_0)),
                |tail| head.pair(tail),
            )
        });

        let rev_fwd = Scope::make(ctx_len, |pair_1| {
            let head = pair_1.clone().proj_head();
            let tail_1 = pair_1.proj_tail();

            tail_rev_fwd
            .clone()
            .bind(head.clone())
            .bind(tail_1.clone())
            .map_eq(
                ctx_len + 1,
                Ty::sigma(head_name, head_ty, tail_ty_1),
                tail_fwd
                .bind(head.clone())
                .bind(tail_rev.bind(head.clone()).bind(tail_1)),
                |tail| head.pair(tail),
            )
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

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
            pair.refl()
        });

        let rev_fwd = Scope::make(0, |tail| {
            tail.refl()
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
            pair.refl()
        });

        let rev_fwd = Scope::make(0, |head| {
            head.refl()
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

        let fwd = Scope::make(ctx_len, |pair| {
            let head = pair.clone().proj_head();
            let tail = pair.proj_tail();

            tail_ty
            .clone()
            .bind_eq(
                head.clone(),
                constrains.clone().bind(head.clone()).bind(tail.clone())
            )
            .transport(
                tail_ty.clone().bind(head.clone()),
                tail,
                TAIL_NAME.clone(),
            )
        });

        let rev = Scope::make(ctx_len, |tail| {
            unique_head.clone().pair(tail)
        });

        let fwd_rev = Scope::make(ctx_len, |pair| {
            let head = pair.clone().proj_head();
            let tail = pair.clone().proj_tail();

            constrains
            .clone()
            .bind(head.clone())
            .bind(tail.clone())
            .cong(
                Scope::make(ctx_len + 1, |head_1| {
                    Scope::make(ctx_len + 2, |head_eq| {
                        Ty::equal(
                            Ty::sigma(head_name, head_ty, tail_ty.clone()),
                            head_1
                            .pair(
                                tail_ty
                                .clone()
                                .bind_eq(
                                    head.clone(),
                                    head_eq,
                                )
                                .transport(
                                    tail_ty.clone().bind(head),
                                    tail,
                                    TAIL_NAME.clone(),
                                )
                            ),
                            pair.clone(),
                        )
                    })
                }),
                pair.refl(),
            )
        });

        let rev_fwd = Scope::make(ctx_len, |tail| {
            let bound_tail_ty = tail_ty.clone().bind(unique_head.clone());

            constrains
            .bind(unique_head.clone())
            .bind(tail.clone())
            .unique_identity(
                Scope::make(ctx_len + 1, |head_eq| {
                    Ty::equal(
                        bound_tail_ty.clone(),
                        tail_ty
                        .bind_eq(
                            unique_head.clone(),
                            head_eq,
                        )
                        .transport(
                            bound_tail_ty,
                            tail.clone(),
                            TAIL_NAME.clone(),
                        ),
                        tail.clone(),
                    )
                }),
                tail.refl(),
            )
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    pub fn dependent_pi_arg_congruence(
        funext: &Tm,
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
            Tm::func(Scope::make(ctx_len + 1, |arg_tm_1| {
                func.app(arg_rev.clone().bind(arg_tm_1))
            }))
        });

        let rev = Scope::make(ctx_len, |func| {
            Tm::func(Scope::make(ctx_len + 1, |arg_tm_0| {
                let arg_tm_1 = arg_fwd.clone().bind(arg_tm_0.clone());
                let arg_tm_0_round_trip = {
                    arg_rev.clone().bind(arg_tm_1.clone())
                };

                res_ty
                .clone()
                .bind_eq(
                    arg_tm_0_round_trip.clone(),
                    arg_fwd_rev.clone().bind(arg_tm_0),
                )
                .transport(
                    res_ty.clone().bind(arg_tm_0_round_trip),
                    func.app(arg_tm_1),
                    RES_NAME.clone(),
                )
            }))
        });

        let fwd_rev = Scope::make(ctx_len, |func| {
            funext
            .clone()
            .app(arg_name.clone().into_tm())
            .app(arg_ty_0.clone().into_tm())
            .app(Tm::func(res_ty.clone().map_without_capture(|res_ty| res_ty.into_tm())))
            .app(rev.clone().bind(fwd.clone().bind(func.clone())))
            .app(func.clone())
            .app(Tm::func(Scope::make(ctx_len + 1, |arg_tm_0| {
                let arg_tm_1 = arg_fwd.clone().bind(arg_tm_0.clone());
                let arg_tm_0_round_trip = arg_rev.clone().bind(arg_tm_1.clone());
                let res_round_trip = func.clone().app(arg_tm_0_round_trip.clone());

                arg_fwd_rev
                .clone()
                .bind(arg_tm_0)
                .cong(
                    Scope::make(ctx_len + 2, |arg_tm_2| {
                        Scope::make(ctx_len + 3, |arg_eq| {
                            Ty::equal(
                                res_ty.clone().bind(arg_tm_2.clone()),
                                res_ty
                                .clone()
                                .bind_eq(
                                    arg_tm_0_round_trip.clone(),
                                    arg_eq,
                                )
                                .transport(
                                    res_ty.clone().bind(arg_tm_0_round_trip.clone()),
                                    res_round_trip.clone(),
                                    RES_NAME.clone(),
                                ),
                                func.app(arg_tm_2),
                            )
                        })
                    }),
                    res_round_trip.refl(),
                )
            })))
        });

        let rev_fwd = Scope::make(ctx_len, |func| {
            funext
            .clone()
            .app(arg_name.clone().into_tm())
            .app(arg_ty_1.clone().into_tm())
            .app(Tm::func(Scope::make(ctx_len + 1, |arg_tm_1| {
                res_ty.clone().bind(arg_rev.clone().bind(arg_tm_1)).into_tm()
            })))
            .app(fwd.clone().bind(rev.clone().bind(func.clone())))
            .app(func.clone())
            .app(Tm::func(Scope::make(ctx_len + 1, |arg_tm_1| {
                let arg_tm_0 = arg_rev.clone().bind(arg_tm_1.clone());
                let arg_tm_1_round_trip = arg_fwd.clone().bind(arg_tm_0.clone());
                let arg_tm_0_round_trip = arg_rev.clone().bind(arg_tm_1_round_trip.clone());

                let arg_tm_1_round_trip_eq_arg_tm_1 = arg_rev_fwd.bind(arg_tm_1.clone());

                Tm::equality_contractible(
                    arg_ty_0.clone(),
                    arg_tm_0_round_trip.clone(),
                    arg_fwd_rev.clone().bind(arg_tm_0.clone()),
                    arg_rev
                    .clone()
                    .bind_eq(
                        arg_ty_0.clone(),
                        arg_tm_1_round_trip.clone(),
                        arg_tm_1_round_trip_eq_arg_tm_1.clone(),
                    ),
                )
                .map_eq(
                    ctx_len + 2,
                    res_ty.clone().bind(arg_tm_0.clone()),
                    arg_tm_0_round_trip.clone(),
                    |arg_eq| {
                        res_ty
                        .clone()
                        .bind_eq(
                            arg_tm_0_round_trip.clone(),
                            arg_eq,
                        )
                        .transport(
                            res_ty.clone().bind(arg_tm_0_round_trip.clone()),
                            func.clone().app(arg_tm_1_round_trip.clone()),
                            RES_NAME.clone(),
                        )
                    },
                )
                .transitivity(
                    arg_tm_1_round_trip_eq_arg_tm_1
                    .cong(
                        Scope::make(ctx_len + 2, |arg_tm_2| {
                            Scope::make(ctx_len + 3, |arg_eq| {
                                Ty::equal(
                                    res_ty.clone().bind(arg_rev.clone().bind(arg_tm_2.clone())),
                                    res_ty
                                    .clone()
                                    .bind_eq(
                                        arg_tm_0_round_trip.clone(),
                                        arg_rev
                                        .bind_eq(
                                            arg_ty_1,
                                            arg_tm_1_round_trip.clone(),
                                            arg_eq,
                                        )
                                    )
                                    .transport(
                                        res_ty.clone().bind(arg_tm_0_round_trip.clone()),
                                        func.clone().app(arg_tm_1_round_trip.clone()),
                                        RES_NAME.clone(),
                                    ),
                                    func.clone().app(arg_tm_2),
                                )
                            })
                        }),
                        func.clone().app(arg_tm_1_round_trip.clone()).refl(),
                    ),
                    res_ty.clone().bind(arg_tm_0.clone()),
                    res_ty
                    .clone()
                    .bind_eq(
                        arg_tm_0_round_trip.clone(),
                        arg_fwd_rev.bind(arg_tm_0),
                    )
                    .transport(
                        res_ty.bind(arg_tm_0_round_trip),
                        func.clone().app(arg_tm_1_round_trip.clone()),
                        RES_NAME.clone(),
                    ),
                    func.app(arg_tm_1),
                )
            })))
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    pub fn dependent_pi_res_congruence(
        funext: &Tm,
        arg_name: Name,
        arg_ty: Ty,
        res_ty_0: Scope<Ty>,
        res_ty_1: Scope<Ty>,
        res_iso: Scope<Iso>,
    ) -> Iso {
        let ctx_len = max_all([
            funext.ctx_len(),
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
            funext
            .clone()
            .app(arg_name.clone().into_tm())
            .app(arg_ty.clone().into_tm())
            .app(Tm::func(res_ty_0.clone().map_without_capture(|res_ty| res_ty.into_tm())))
            .app(rev.clone().bind(fwd.clone().bind(func.clone())))
            .app(func.clone())
            .app(Tm::func(Scope::make(ctx_len + 1, |arg| {
                res_fwd_rev
                .bind(arg.clone())
                .bind(func.app(arg))
            })))
        });

        let rev_fwd = Scope::make(ctx_len, |func| {
            funext
            .clone()
            .app(arg_name.clone().into_tm())
            .app(arg_ty.clone().into_tm())
            .app(Tm::func(res_ty_1.clone().map_without_capture(|res_ty| res_ty.into_tm())))
            .app(fwd.clone().bind(rev.clone().bind(func.clone())))
            .app(func.clone())
            .app(Tm::func(Scope::make(ctx_len + 1, |arg| {
                res_rev_fwd
                .bind(arg.clone())
                .bind(func.app(arg))
            })))
        });

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    pub fn pi_never_arg(
        funext: &Tm,
        arg_name: Name,
        res_ty: Scope<Ty>,
    ) -> Iso {
        let ctx_len = max_all([
            arg_name.ctx_len(),
            res_ty.ctx_len(),
        ]);

        let fwd = Scope::constant(Tm::unit());
        let rev = Scope::constant(Tm::func(Scope::make(ctx_len + 1, |never| {
            never.explode(res_ty.clone())
        })));

        let fwd_rev = Scope::make(ctx_len, |func| {
            funext
            .clone()
            .app(arg_name.into_tm())
            .app(Ty::never().into_tm())
            .app(Tm::func(res_ty.clone().map_without_capture(|res_ty| res_ty.into_tm())))
            .app(rev.clone().bind(fwd.clone().bind(func.clone())))
            .app(func.clone())
            .app(Tm::func(Scope::make(ctx_len + 1, |never| {
                never.clone().explode(Scope::constant(
                    Ty::equal(
                        res_ty.clone().bind(never.clone()),
                        never.clone().explode(res_ty),
                        func.app(never),
                    )
                ))
            })))
        });

        let rev_fwd = Scope::constant(Tm::unit().refl());

        Iso { fwd, rev, fwd_rev, rev_fwd }
    }


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

        let fwd_rev = Scope::make(ctx_len, |func| func.refl());

        let rev_fwd = Scope::make(ctx_len, |res| res.refl());

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
        let fwd_rev = Scope::make(0, |func| func.refl());
        let rev_fwd = Scope::constant(Tm::unit().refl());
        Iso { fwd, rev, fwd_rev, rev_fwd }
    }
}

