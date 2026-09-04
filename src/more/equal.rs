use crate::priv_prelude::*;

impl Tm {
    /// Convert an equality between types to a function.
    ///
    /// ```ignore
    /// Γ ⊢ from_ty : Type
    /// Γ ⊢ into_ty : Type
    /// Γ ⊢ from_name : Name
    /// Γ ⊢ self : from_ty == into_ty
    /// ----
    /// Γ ⊢ self.into_transport(from_ty, from_name) : Fn($from_name: from_ty) -> into_ty
    /// ```

    pub fn into_transport(
        self,
        from_ty: Ty,
        from_name: Name,
    ) -> Tm {
        let ctx_len = max_all([self.ctx_len(), from_ty.ctx_len(), from_name.ctx_len()]);
        self
        .cong(
            Scope::make(ctx_len, |into_ty| {
                Scope::constant(
                    Ty::pi(
                        from_name,
                        from_ty,
                        Scope::constant(into_ty.into_ty()),
                    ),
                )
            }),
            Tm::func(Scope::id()),
        )
    }

    /// Transport a term across a type-equality
    ///
    /// ```
    /// Γ ⊢ from_ty : Type
    /// Γ ⊢ into_ty : Type
    /// Γ ⊢ self : from_ty == into_ty
    /// Γ ⊢ tm : from_ty
    /// Γ ⊢ tm_name : Name
    /// ----
    /// Γ ⊢ self.transport(from_ty, tm, tm_name) : into_ty
    /// ```
    ///
    /// `tm_name` is used as the argument name for the intermediate function which is constructed to
    /// perform the transport.

    pub fn transport(
        self,
        from_ty: Ty,
        tm: Tm,
        tm_name: Name,
    ) -> Tm {
        self.into_transport(from_ty, tm_name).app(tm)
    }

    /// Reflect an equality.
    ///
    /// ```
    /// Γ ⊢ eq_ty : Type
    /// Γ ⊢ eq_tm_0 : eq_ty
    /// Γ ⊢ eq_tm_1 : eq_ty
    /// Γ ⊢ self : eq_tm_0 == eq_tm_1
    /// ----
    /// Γ ⊢ self.symmetry(eq_ty, eq_tm_0) : eq_tm_1 == eq_tm_0
    /// ```

    pub fn symmetry(self, eq_ty: Ty, eq_tm_0: Tm) -> Tm {
        let ctx_len = max_all([self.ctx_len(), eq_ty.ctx_len(), eq_tm_0.ctx_len()]);
        self
        .cong(
            Scope::make(ctx_len, |eq_tm_1| {
                Scope::constant(Ty::equal(eq_ty, eq_tm_1, eq_tm_0.clone()))
            }),
            eq_tm_0.refl(),
        )
    }

    /// Compose two equalities.
    ///
    /// ```
    /// Γ ⊢ eq_ty : Type
    /// Γ ⊢ eq_tm_0 : eq_ty
    /// Γ ⊢ eq_tm_1 : eq_ty
    /// Γ ⊢ eq_tm_2 : eq_ty
    /// Γ ⊢ self : eq_tm_0 == eq_tm_1
    /// Γ ⊢ other : eq_tm_1 == eq_tm_2
    /// ----
    /// Γ ⊢ self.transitivity(other, eq_ty, eq_tm_0, eq_tm_2) : eq_tm_0 == eq_tm_2
    /// ```

    pub fn transitivity(
        self,
        other: Tm,
        eq_ty: Ty,
        eq_tm_0: Tm,
        eq_tm_2: Tm,
    ) -> Tm {
        lazy_static! {
            static ref ELIM_1_NAME: Name = Name::from("eq_1");
        }

        let elim_0 = self;
        let elim_1 = other;

        let ctx_len = max_all([
            elim_0.ctx_len(),
            elim_1.ctx_len(),
            eq_ty.ctx_len(),
            eq_tm_0.ctx_len(),
            eq_tm_2.ctx_len(),
        ]);

        elim_0
        .cong(
            Scope::make(ctx_len, |eq_tm_1| {
                Scope::constant(
                    Ty::pi(
                        ELIM_1_NAME.clone(),
                        Ty::equal(
                            eq_ty.clone(),
                            eq_tm_1,
                            eq_tm_2.clone(),
                        ),
                        Scope::constant(
                            Ty::equal(eq_ty, eq_tm_0, eq_tm_2),
                        ),
                    )
                )
            }),
            Tm::func(Scope::id()),
        )
        .app(elim_1)
    }

    /// Remove `.succs(1)` from both sides of an equality.
    ///
    /// ```
    /// Γ ⊢ pred_tm_0 : Nat
    /// Γ ⊢ pred_tm_1 : Nat
    /// Γ ⊢ self : pred_tm_0.succs(1) == pred_tm_1.succs(1)
    /// ----
    /// Γ ⊢ self.succ_injective(pred_tm_0) : pred_tm_0 == pred_tm_1
    /// ```

    pub fn succ_injective(
        self,
        pred_tm_0: Tm,
    ) -> Tm {
        let ctx_len = max_all([pred_tm_0.ctx_len(), self.ctx_len()]);
        self
        .cong(
            Scope::make(ctx_len, |tm_1| Scope::constant(
                tm_1
                .fold(
                    Scope::constant(Ty::universe()),
                    Ty::never().into_tm(),
                    Scope::make(ctx_len + 2, |pred_tm_1| Scope::constant(
                        Ty::equal(Ty::nat(), pred_tm_0.clone(), pred_tm_1).into_tm(),
                    )),
                )
                .into_ty()
            )),
            pred_tm_0.refl(),
        )
    }

    /// Remove `.succs(succ_count)` from both sides of an equality.
    ///
    /// ```
    /// Γ ⊢ pred_tm_0 : Nat
    /// Γ ⊢ pred_tm_1 : Nat
    /// Γ ⊢ self : pred_tm_0.succs(succ_count) == pred_tm_1.succs(succ_count)
    /// ----
    /// Γ ⊢ self.succs_injective(pred_tm_0, succ_count) : pred_tm_0 == pred_tm_1
    /// ```

    pub fn succs_injective(
        self,
        pred_tm_0: Tm,
        succ_count: impl Into<Ubig>,
    ) -> Tm {
        let mut succ_count = succ_count.into();
        let mut tms_eq = self;
        while succ_count.decrement() {
            tms_eq = tms_eq.succ_injective(pred_tm_0.clone().succs(succ_count.clone()));
        }
        tms_eq
    }

    /// Convert a proof of `0 == x.succs(1)` into a proof of `Never`
    ///
    /// ```
    /// Γ ⊢ x : Nat
    /// Γ ⊢ self : 0 == x.succs(1)
    /// ----
    /// Γ ⊢ self.zero_isnt_succ() : Never
    /// ```

    pub fn zero_isnt_succ(self) -> Tm {
        self
        .cong(
            Scope::make(0, |nat_1| Scope::constant(
                nat_1
                .fold(
                    Scope::constant(Ty::universe()),
                    Ty::unit().into_tm(),
                    Scope::constant(Scope::constant(Ty::never().into_tm())),
                )
                .into_ty()
            )),
            Tm::unit(),
        )
    }

    /// Convert a proof of `x.succs(1) == 0` into a proof of `Never`
    ///
    /// ```
    /// Γ ⊢ x : Nat
    /// Γ ⊢ self : x.succs(1) == 0
    /// ----
    /// Γ ⊢ self.succ_isnt_zero() : Never
    /// ```

    pub fn succ_isnt_zero(self) -> Tm {
        self
        .cong(
            Scope::make(0, |nat_1| Scope::constant(
                nat_1
                .fold(
                    Scope::constant(Ty::universe()),
                    Ty::never().into_tm(),
                    Scope::constant(Scope::constant(Ty::unit().into_tm())),
                )
                .into_ty()
            )),
            Tm::unit(),
        )
    }

    
    /// Convert a proof that two unequal `Nat` constants are equal into a proof of `Never`.
    ///
    /// ```
    /// Γ ⊢ self : ubig_0 == ubig_1
    /// ----
    /// Γ ⊢ self.constants_apart(ubig_0, ubig_1) : Never
    /// ```
    ///
    /// # Panics 
    ///
    /// If `ubig_0 == ubig_1`

    pub fn constants_apart(
        self,
        ubig_0: Ubig,
        ubig_1: Ubig,
    ) -> Tm {
        match ubig_0.cmp(&ubig_1) {
            cmp::Ordering::Less => {
                self
                .succs_injective(Tm::zero(), ubig_0)
                .zero_isnt_succ()
            },
            cmp::Ordering::Equal => panic!("ubig_0 and ubig_1 must be different"),
            cmp::Ordering::Greater => {
                self
                .succs_injective(Tm::constant(ubig_0.strict_sub(&ubig_1)), ubig_1)
                .succ_isnt_zero()
            },
        }
    }

    /// Given two proofs equality between the same two endpoints, proves that the proofs are
    /// equal.
    ///
    /// ```
    /// Γ ⊢ eq_ty : Ty
    /// Γ ⊢ eq_tm_0 : eq_ty
    /// Γ ⊢ eq_tm_1 : eq_ty
    /// Γ ⊢ eq_0 : eq_tm_0 == eq_tm_1
    /// Γ ⊢ eq_1 : eq_tm_0 == eq_tm_1
    /// ----
    /// Γ ⊢ equality_contractible(eq_ty, eq_tm_0, eq_0, eq_1) : eq_0 == eq_1
    /// ```

    pub fn equality_contractible(
        eq_ty: Ty,
        eq_tm_0: Tm,
        eq_0: Tm,
        eq_1: Tm,
    ) -> Tm {
        let ctx_len = max_all([
            eq_ty.ctx_len(),
            eq_tm_0.ctx_len(),
            eq_0.ctx_len(),
            eq_1.ctx_len(),
        ]);
        lazy_static! {
            static ref EQ_1_NAME: Name = Name::from("eq_1");
        }

        eq_0
        .cong(
            Scope::make(ctx_len, |eq_tm_1| {
                Scope::make(ctx_len + 1, |eq_0| {
                    let eq_tms_equal_ty = Ty::equal(eq_ty.clone(), eq_tm_0.clone(), eq_tm_1);
                    Ty::pi(
                        EQ_1_NAME.clone(),
                        eq_tms_equal_ty.clone(),
                        Scope::make(ctx_len + 2, |eq_1| {
                            Ty::equal(
                                eq_tms_equal_ty,
                                eq_0,
                                eq_1,
                            )
                        })
                    )
                })
            }),
            Tm::func(Scope::make(ctx_len, |eq_1| {
                let eq_tm_0_refl = eq_tm_0.clone().refl();
                eq_1
                .unique_identity(
                    Scope::make(ctx_len + 1, |eq_1| {
                        Ty::equal(
                            Ty::equal(eq_ty, eq_tm_0.clone(), eq_tm_0),
                            eq_tm_0_refl.clone(),
                            eq_1,
                        )
                    }),
                    eq_tm_0_refl.refl(),
                )
            })),
        )
        .app(eq_1)
    }

    /// Proves that any two heterogeneous equalities over the same type equality between the same
    /// endpoints are equal.
    ///
    /// ```ignore
    /// Γ ⊢ ty_0 : Type
    /// Γ ⊢ ty_1 : Type
    /// Γ ⊢ tys_eq : ty_0 == ty_1
    /// Γ ⊢ tm_0 : ty_0
    /// Γ ⊢ tm_1 : ty_1
    /// Γ ⊢ het_eq_0 : Ty::heterogeneous_equal(ty_0, tys_eq, tm_0, tm_1)
    /// Γ ⊢ het_eq_1 : Ty::heterogeneous_equal(ty_0, tys_eq, tm_0, tm_1)
    /// ----
    /// Γ ⊢ Tm::heterogeneous_equality_contractible(
    ///     ty_0,
    ///     tys_eq,
    ///     tm_0,
    ///     tm_1,
    ///     het_eq_0,
    ///     het_eq_1,
    /// ) : het_eq_0 == het_eq_1
    /// ```

    pub fn heterogeneous_equality_contractible(
        ty_0: Ty,
        tys_eq: Tm,
        tm_0: Tm,
        tm_1: Tm,
        het_eq_0: Tm,
        het_eq_1: Tm,
    ) -> Tm {
        let ctx_len = max_all([
            ty_0.ctx_len(),
            tys_eq.ctx_len(),
            tm_0.ctx_len(),
            tm_1.ctx_len(),
            het_eq_0.ctx_len(),
            het_eq_1.ctx_len(),
        ]);

        lazy_static! {
            static ref TM_1_NAME: Name = Name::from("val_1");
            static ref HET_EQ_0_NAME: Name = Name::from("eq_0");
            static ref HET_EQ_1_NAME: Name = Name::from("eq_1");
        }

        tys_eq
        .cong(
            Scope::make(ctx_len, |ty_1| {
                Scope::make(ctx_len + 1, |tys_eq| {
                    Ty::pi(
                        TM_1_NAME.clone(),
                        ty_1.into_ty(),
                        Scope::make(ctx_len + 2, |tm_1| {
                            let het_eq_ty = Ty::heterogeneous_equal(
                                ty_0.clone(), tys_eq, tm_0.clone(), tm_1,
                            );
                            Ty::pi(
                                HET_EQ_0_NAME.clone(),
                                het_eq_ty.clone(),
                                Scope::make(ctx_len + 3, |het_eq_0| {
                                    Ty::pi(
                                        HET_EQ_1_NAME.clone(),
                                        het_eq_ty.clone(),
                                        Scope::make(ctx_len + 4, |het_eq_1| {
                                            Ty::equal(het_eq_ty, het_eq_0, het_eq_1)
                                        }),
                                    )
                                }),
                            )
                        }),
                    )
                })
            }),
            Tm::func(Scope::constant(
                Tm::func(Scope::make(ctx_len + 1, |het_eq_0| {
                    Tm::func(Scope::make(ctx_len + 2, |het_eq_1| {
                        Tm::equality_contractible(
                            ty_0, tm_0, het_eq_0, het_eq_1,
                        )
                    }))
                }))
            )),
        )
        .app(tm_1)
        .app(het_eq_0)
        .app(het_eq_1)
    }

    /// Given a proof that two left-injections are equal, prove that the terms being injected are
    /// equal.
    ///
    /// ```
    /// Γ ⊢ lhs_name : Name
    /// Γ ⊢ lhs_ty : Ty
    /// Γ ⊢ rhs_ty : Ty
    /// Γ ⊢ lhs_tm_0 : lhs_ty
    /// Γ ⊢ lhs_tm_1 : lhs_ty
    /// Γ ⊢ self : lhs_tm_0.inj_lhs() == lhs_tm_1.inj_lhs()
    /// ----
    /// Γ ⊢ self.inj_lhs_injective() : lhs_tm_0 == lhs_tm_1
    /// ```
    ///
    /// Alternatively, if `self` is an equality between a left and a right injection, this will
    /// return a proof of `Never`.
    ///
    /// ```
    /// Γ ⊢ lhs_name : Name
    /// Γ ⊢ lhs_ty : Ty
    /// Γ ⊢ rhs_ty : Ty
    /// Γ ⊢ lhs_tm_0 : lhs_ty
    /// Γ ⊢ rhs_tm_1 : rhs_ty
    /// Γ ⊢ self : lhs_tm_0.inj_lhs() == rhs_tm_1.inj_rhs()
    /// ----
    /// Γ ⊢ self.inj_lhs_injective() : Never
    /// ```

    pub fn inj_lhs_injective(
        self: Tm,
        lhs_ty: Ty,
        lhs_tm_0: Tm,
    ) -> Tm {
        let ctx_len = max_all([
            self.ctx_len(),
            lhs_ty.ctx_len(),
            lhs_tm_0.ctx_len(),
        ]);

        self
        .cong(
            Scope::make(ctx_len, |sum_1| {
                Scope::constant(
                    sum_1
                    .case(
                        Scope::constant(Ty::universe()),
                        Scope::make(ctx_len + 2, |lhs_tm_1| Ty::equal(lhs_ty, lhs_tm_0.clone(), lhs_tm_1).into_tm()),
                        Scope::constant(Ty::never().into_tm()),
                    )
                    .into_ty(),
                )
            }),
            lhs_tm_0.refl(),
        )
    }

    /// Given a proof that two right-injections are equal, prove that the terms being injected are
    /// equal.
    ///
    /// ```
    /// Γ ⊢ lhs_name : Name
    /// Γ ⊢ lhs_ty : Ty
    /// Γ ⊢ rhs_ty : Ty
    /// Γ ⊢ rhs_tm_0 : rhs_ty
    /// Γ ⊢ rhs_tm_1 : rhs_ty
    /// Γ ⊢ self : rhs_tm_0.inj_rhs() == rhs_tm_1.inj_rhs()
    /// ----
    /// Γ ⊢ self.inj_rhs_injective() : rhs_tm_0 == rhs_tm_1
    /// ```
    ///
    /// Alternatively, if `self` is an equality between a right and a left injection, this will
    /// return a proof of `Never`.
    ///
    /// ```
    /// Γ ⊢ lhs_name : Name
    /// Γ ⊢ lhs_ty : Ty
    /// Γ ⊢ rhs_ty : Ty
    /// Γ ⊢ rhs_tm_0 : rhs_ty
    /// Γ ⊢ lhs_tm_1 : lhs_ty
    /// Γ ⊢ self : rhs_tm_0.inj_rhs() == lhs_tm_1.inj_lhs()
    /// ----
    /// Γ ⊢ self.inj_rhs_injective() : Never
    /// ```

    pub fn inj_rhs_injective(
        self: Tm,
        rhs_ty: Ty,
        rhs_tm_0: Tm,
    ) -> Tm {
        let ctx_len = max_all([
            self.ctx_len(),
            rhs_ty.ctx_len(),
            rhs_tm_0.ctx_len(),
        ]);

        self
        .cong(
            Scope::make(ctx_len, |sum_1| {
                Scope::constant(
                    sum_1
                    .case(
                        Scope::constant(Ty::universe()),
                        Scope::constant(Ty::never().into_tm()),
                        Scope::make(ctx_len + 2, |rhs_tm_1| Ty::equal(rhs_ty, rhs_tm_0.clone(), rhs_tm_1).into_tm()),
                    )
                    .into_ty(),
                )
            }),
            rhs_tm_0.refl(),
        )
    }

    /// Convert an equality between two non-dependent pairs to a pair of equalities between their
    /// head and tail projections.
    ///
    /// ```ignore
    /// Γ ⊢ head_name : Name
    /// Γ ⊢ head_ty : Type
    /// Γ ⊢ tail_ty : Type
    /// Γ ⊢ head_0 : head_ty
    /// Γ ⊢ head_1 : head_ty
    /// Γ ⊢ tail_0 : tail_ty
    /// Γ ⊢ tail_1 : tail_ty
    /// Γ ⊢ pair_eq : head_0.pair(tail_0) == head_1.pair(tail_1)
    /// ----
    /// Γ ⊢ Tm::equality_of_non_dependent_pairs_to_non_dependent_pair_of_equalities(
    ///     head_name,
    ///     head_ty,
    ///     tail_ty,
    ///     head_0,
    ///     tail_0,
    ///     pair_eq,
    /// ) : Ty::sigma(
    ///     head_name,
    ///     Ty::equal(head_ty, head_0, head_1),
    ///     Scope::constant(Ty::equal(tail_ty, tail_0, tail_1)),
    /// )
    /// ```

    pub fn equality_of_non_dependent_pairs_to_non_dependent_pair_of_equalities(
        head_name: Name,
        head_ty: Ty,
        tail_ty: Ty,
        head_0: Tm,
        tail_0: Tm,
        pair_eq: Tm,
    ) -> Tm {
        let ctx_len = max_all([
            head_name.ctx_len(),
            head_ty.ctx_len(),
            tail_ty.ctx_len(),
            head_0.ctx_len(),
            tail_0.ctx_len(),
            pair_eq.ctx_len(),
        ]);

        pair_eq
        .cong(
            Scope::make(ctx_len, |pair_1| Scope::constant({
                let head_1 = pair_1.clone().proj_head();
                let tail_1 = pair_1.proj_tail();
                Ty::sigma(
                    head_name,
                    Ty::equal(head_ty, head_0.clone(), head_1),
                    Scope::constant(Ty::equal(tail_ty, tail_0.clone(), tail_1)),
                )
            })),
            head_0.refl().pair(tail_0.refl()),
        )
    }

    pub fn non_dependent_pair_of_equalities_to_equality_of_non_dependent_pairs(
        head_name: Name,
        head_ty: Ty,
        tail_ty: Ty,
        head_0: Tm,
        tail_0: Tm,
        tail_1: Tm,
        head_eq: Tm,
        tail_eq: Tm,
    ) -> Tm {
        let ctx_len = max_all([
            head_name.ctx_len(),
            head_ty.ctx_len(),
            tail_ty.ctx_len(),
            head_0.ctx_len(),
            tail_0.ctx_len(),
            tail_1.ctx_len(),
            head_eq.ctx_len(),
            tail_eq.ctx_len(),
        ]);

        let sigma_ty = Ty::sigma(head_name, head_ty, Scope::constant(tail_ty));
        let pair_0 = head_0.clone().pair(tail_0);

        head_eq
        .cong(
            Scope::make(ctx_len, |head_1| Scope::constant(
                Ty::equal(
                    sigma_ty.clone(),
                    pair_0.clone(),
                    head_1.pair(tail_1),
                )
            )),
            tail_eq
            .cong(
                Scope::make(ctx_len, |tail_1| Scope::constant(
                    Ty::equal(
                        sigma_ty,
                        pair_0.clone(),
                        head_0.pair(tail_1),
                    )
                )),
                pair_0.refl(),
            )
        )
    }

    pub fn equality_of_dependent_pairs_to_dependent_pair_of_equalities(
        head_name: Name,
        head_ty: Ty,
        tail_ty: Scope<Ty>,
        head_0: Tm,
        tail_0: Tm,
        pair_eq: Tm,
    ) -> Tm {
        let ctx_len = max_all([
            head_name.ctx_len(),
            head_ty.ctx_len(),
            tail_ty.ctx_len(),
            head_0.ctx_len(),
            tail_0.ctx_len(),
            pair_eq.ctx_len(),
        ]);

        pair_eq
        .cong(
            Scope::make(ctx_len + 1, |pair_1| Scope::constant({
                let head_1 = pair_1.clone().proj_head();
                let tail_1 = pair_1.proj_tail();
                Ty::sigma(
                    head_name,
                    Ty::equal(head_ty, head_0.clone(), head_1),
                    Scope::make(ctx_len + 3, |head_eq| {
                        Ty::heterogeneous_equal(
                            tail_ty.clone().bind(head_0.clone()),
                            tail_ty.bind_eq(head_0.clone(), head_eq),
                            tail_0.clone(),
                            tail_1,
                        )
                    }),
                )
            })),
            head_0.refl().pair(tail_0.refl()),
        )
    }

    pub fn dependent_pair_of_equalities_to_equality_of_dependent_pairs(
        head_name: Name,
        head_ty: Ty,
        tail_ty: Scope<Ty>,
        head_0: Tm,
        tail_0: Tm,
        tail_1: Tm,
        head_eq: Tm,
        tail_eq: Tm,
    ) -> Tm {
        let ctx_len = max_all([
            head_name.ctx_len(),
            head_ty.ctx_len(),
            tail_ty.ctx_len(),
            head_0.ctx_len(),
            tail_0.ctx_len(),
            tail_1.ctx_len(),
            head_eq.ctx_len(),
            tail_eq.ctx_len(),
        ]);

        lazy_static! {
            static ref TAIL_NAME: Name = Name::from("tail");
            static ref TAIL_EQ_NAME: Name = Name::from("tail_eq");
        }

        let sigma_ty = Ty::sigma(head_name, head_ty, tail_ty.clone());
        let pair_0 = head_0.clone().pair(tail_0.clone());

        head_eq
        .cong(
            Scope::make(ctx_len, |head_1| {
                Scope::make(ctx_len + 1, |head_eq| {
                    Ty::pi(
                        TAIL_NAME.clone(),
                        tail_ty.clone().bind(head_1.clone()),
                        Scope::make(ctx_len + 2, |tail_1| {
                            Ty::pi(
                                TAIL_EQ_NAME.clone(),
                                Ty::heterogeneous_equal(
                                    tail_ty.clone().bind(head_0.clone()),
                                    tail_ty.bind_eq(head_0.clone(), head_eq),
                                    tail_0,
                                    tail_1.clone(),
                                ),
                                Scope::constant(
                                    Ty::equal(
                                        sigma_ty.clone(),
                                        pair_0.clone(),
                                        head_1.pair(tail_1),
                                    )
                                ),
                            )
                        }),
                    )
                })
            }),
            Tm::func(Scope::constant(
                Tm::func(Scope::make(ctx_len + 1, |tail_eq| {
                    tail_eq
                    .cong(
                        Scope::make(ctx_len + 2, |tail_0_1| {
                            Scope::constant(
                                Ty::equal(
                                    sigma_ty,
                                    pair_0.clone(),
                                    head_0.pair(tail_0_1),
                                )
                            )
                        }),
                        pair_0.refl(),
                    )
                }))
            )),
        )
        .app(tail_1)
        .app(tail_eq)
    }

    pub fn map_eq(
        self,
        ctx_len: usize,
        res_ty: Ty,
        eq_tm_0: Tm,
        func: impl FnOnce(Tm) -> Tm,
    ) -> Tm {
        Scope::make(ctx_len, func).bind_eq(res_ty, eq_tm_0, self)
    }
}

impl Ty {
    pub fn heterogeneous_equal(
        ty_0: Ty,
        tys_eq: Tm,
        tm_0: Tm,
        tm_1: Tm,
    ) -> Ty {
        let ctx_len = max_all([
            ty_0.ctx_len(),
            tys_eq.ctx_len(),
            tm_0.ctx_len(),
            tm_1.ctx_len(),
        ]);
        
        let tm_1_name = Name::from("val_1");

        tys_eq
        .cong(
            Scope::make(ctx_len, |ty_1| Scope::constant(
                Ty::pi(tm_1_name, ty_1.into_ty(), Scope::constant(Ty::universe())),
            )),
            Tm::func(Scope::make(ctx_len, |tm_1| Ty::equal(ty_0, tm_0, tm_1).into_tm())),
        )
        .app(tm_1)
        .into_ty()
    }
}

