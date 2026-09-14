use crate::priv_prelude::*;

impl Tm {
    /// Compose two equalities.
    ///
    /// ```ignore
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
        .obs_cong(
            Scope::make(ctx_len, |eq_tm_1| {
                Scope::constant(
                    Ty::pi(
                        ELIM_1_NAME.clone(),
                        Ty::obs_equal(
                            eq_ty.clone(),
                            eq_tm_1,
                            eq_tm_2.clone(),
                        ),
                        Scope::constant(
                            Ty::obs_equal(eq_ty, eq_tm_0, eq_tm_2),
                        ),
                    )
                )
            }),
            Tm::func(Scope::id()),
        )
        .app(elim_1)
    }

    pub fn cast_round_trip(
        self,
        from_ty: Ty,
        into_ty: Ty,
        tm: Tm,
    ) -> Tm {
        let ctx_len = max_all([
            from_ty.ctx_len(),
            into_ty.ctx_len(),
            self.ctx_len(),
            tm.ctx_len(),
        ]);

        self
        .clone()
        .obs_cong(
            Scope::make(ctx_len, |into_ty| {
                let into_ty = into_ty.into_ty();
                Scope::make(ctx_len + 1, |tys_eq_fwd| {
                    Ty::pi(
                        Name::from("tys_eq_rev"),
                        Ty::obs_equal(
                            Ty::universe(),
                            into_ty.clone().into_tm(),
                            from_ty.clone().into_tm(),
                        ),
                        Scope::make(ctx_len + 2, |tys_eq_rev| {
                            Ty::obs_equal(
                                from_ty.clone(),
                                tys_eq_rev
                                .cast(
                                    into_ty.clone(),
                                    from_ty.clone(), 
                                    tys_eq_fwd.cast(from_ty.clone(), into_ty.clone(), tm.clone()),
                                ),
                                tm.clone(),
                            )
                        }),
                    )
                })
            }),
            Tm::func(Scope::make(ctx_len, |tys_eq_rev| {
                Tm::cast_refl()
                .transitivity(
                    Tm::cast_refl(),
                    from_ty.clone(),
                    tys_eq_rev
                    .cast(
                        into_ty.clone(),
                        from_ty.clone(), 
                        self.clone().cast(from_ty.clone(), into_ty.clone(), tm.clone()),
                    ),
                    tm,
                )
            })),
        )
        .app(self)
    }

    /*
    /// Apply a non-dependent function to both sides of an equality.
    ///
    /// ```ignore
    /// Γ ⊢ arg_ty : Type
    /// Γ ⊢ res_ty : Type
    /// Γ ⊢ arg_tm_0 : arg_ty
    /// Γ ⊢ arg_tm_1 : arg_ty
    /// Γ ⊢ func : (arg_tm : arg_ty) -> res_ty
    /// Γ ⊢ self : arg_tm_0 == arg_tm_1
    /// ----
    /// Γ ⊢ self.map_eq(Γ.len(), res_ty, arg_tm_0, func) : func(arg_tm_0) == func(arg_tm_1)
    /// ```

    pub fn map_eq(
        self,
        ctx_len: usize,
        res_ty: Ty,
        arg_tm_0: Tm,
        func: impl FnOnce(Tm) -> Tm,
    ) -> Tm {
        Scope::make(ctx_len, func).bind_eq(res_ty, arg_tm_0, self)
    }
    */
}

