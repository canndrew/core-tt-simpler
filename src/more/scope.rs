use crate::priv_prelude::*;

impl Scope<Tm> {
    /// Bind an equality to `self` to get an equality between the two bound scope bodies.
    ///
    /// `self` must not be dependently-typed.
    ///
    /// ```
    /// Γ ⊢ arg_ty : Ty
    /// Γ ⊢ res_ty : Ty
    /// Γ ⊢ self : (arg_tm : arg_ty) |- res_ty
    /// Γ ⊢ arg_tm_0 : arg_ty
    /// Γ ⊢ arg_tm_1 : arg_ty
    /// Γ ⊢ arg_eq : arg_tm_0 == arg_tm_1
    /// ----
    /// Γ ⊢ self.bind_eq(res_ty, arg_tm_0, arg_eq) : self.bind(arg_tm_0) == self.bind(arg_tm_1)
    /// ```

    pub fn bind_eq(
        self,
        res_ty: Ty,
        arg_tm_0: Tm,
        arg_eq: Tm,
    ) -> Tm {
        let ctx_len = max_all([
            arg_eq.ctx_len(), res_ty.ctx_len(), self.ctx_len(), arg_tm_0.ctx_len(),
        ]);

        let res_tm_0 = self.clone().bind(arg_tm_0);
        arg_eq
        .cong(
            Scope::make(ctx_len, |arg_tm_1| Scope::constant(
                Ty::equal(
                    res_ty,
                    res_tm_0.clone(),
                    self.bind(arg_tm_1),
                )
            )),
            res_tm_0.refl(),
        )
    }
}

impl Scope<Ty> {
    pub fn bind_eq(
        self,
        arg_tm_0: Tm,
        arg_eq: Tm,
    ) -> Tm {
        self.map_without_capture(|ty| ty.into_tm()).bind_eq(Ty::universe(), arg_tm_0, arg_eq)
    }
}

