use crate::priv_prelude::*;

#[derive(Clone, Debug, Contextual)]
pub struct Iso {
    pub(crate) fwd: Scope<Tm>,
    pub(crate) rev: Scope<Tm>,
}

impl Substitutable for Iso {
    type Output = Iso;

    fn subst(self, subst: &mut Subst) -> Iso {
        let Iso { fwd, rev } = self;
        let fwd = fwd.subst(subst);
        let rev = rev.subst(subst);
        Iso { fwd, rev }
    }

    fn into_output(self) -> Iso {
        self
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<Iso> {
        let Iso { fwd, rev } = self;
        let fwd = fwd.try_strengthen_index(var_index)?;
        let rev = rev.try_strengthen_index(var_index)?;
        Some(Iso { fwd, rev })
    }
}

impl Bindable for Iso {
    fn capture_subst(self, subst: Subst) -> Iso {
        let Iso { fwd, rev } = self;
        let fwd = fwd.capture_subst(subst.clone());
        let rev = rev.capture_subst(subst.clone());
        Iso { fwd, rev }
    }
}

impl Iso {
    pub fn into_scopes(self) -> (Scope<Tm>, Scope<Tm>) {
        (self.fwd, self.rev)
    }

    pub fn between_props() -> Iso {
        let scope = Scope::constant(Tm::proof());
        Iso { fwd: scope.clone(), rev: scope }
    }

    /// ```text
    /// Γ ⊢ ty : Type
    /// ----
    /// Γ ⊢ Iso::refl() : ty ≅ ty
    /// ```

    pub fn refl() -> Iso {
        Iso {
            fwd: Scope::id(),
            rev: Scope::id(),
        }
    }

    /// ```text
    /// Γ ⊢ ty_0 : Type
    /// Γ ⊢ ty_1 : Type
    /// Γ ⊢ self : ty_0 ≅ ty_1
    /// ----
    /// Γ ⊢ self.symmetry() : ty_1 ≅ ty_0
    /// ```

    pub fn symmetry(self) -> Iso {
        let Iso { fwd, rev } = self;
        Iso {
            fwd: rev,
            rev: fwd,
        }
    }

    /// ```text
    /// Γ ⊢ from_ty_0 : Type
    /// Γ ⊢ middle_ty : Type
    /// Γ ⊢ into_ty_1 : Type
    /// Γ ⊢ iso_0 : from_ty_0 ≅ middle_ty
    /// Γ ⊢ iso_1 : middle_ty ≅ into_ty_1
    /// ----
    /// Γ ⊢ Iso::transitivity(iso_0, iso_1) : from_ty_0 ≅ into_ty_1
    /// ```

    pub fn transitivity(
        iso_0: Iso,
        iso_1: Iso,
    ) -> Iso {
        let ctx_len = max_all([
            iso_0.ctx_len(),
            iso_1.ctx_len(),
        ]);

        let Iso { fwd: fwd_0, rev: rev_0 } = iso_0;
        let Iso { fwd: fwd_1, rev: rev_1 } = iso_1;

        let fwd = Scope::make(ctx_len, |tm| {
            fwd_1.clone().bind(fwd_0.clone().bind(tm))
        });

        let rev = Scope::make(ctx_len, |tm| {
            rev_0.clone().bind(rev_1.clone().bind(tm))
        });

        Iso { fwd, rev }
    }

    /// ```text
    /// Γ ⊢ from_ty : Type
    /// Γ, tm: from_ty ⊢ _ : Never
    /// ----
    /// Γ ⊢ Iso::scope_never_to_iso_never(from_ty) : from_ty ≅ Never
    /// ```

    pub fn scope_never_to_iso_never(
        from_ty: Ty,
    ) -> Iso {
        let fwd = Scope::constant(Tm::proof());
        let rev = Scope::constant(
            Tm::explode(Scope::constant(from_ty.clone()))
        );

        Iso { fwd, rev }
    }

    pub fn uniquely_inhabited_to_unit(unique_tm: Tm) -> Iso {
        let fwd = Scope::constant(Tm::proof());
        let rev = Scope::constant(unique_tm);
        Iso { fwd, rev }
    }

    /// ```text
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

    #[allow(clippy::too_many_arguments)]
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
            rhs_ty_1.ctx_len(),
            lhs_iso.ctx_len(),
            rhs_iso.ctx_len(),
        ]);

        let sum_ty_0 = Ty::sum(lhs_name_0.clone(), lhs_ty_0, rhs_ty_0);
        let sum_ty_1 = Ty::sum(lhs_name_1.clone(), lhs_ty_1, rhs_ty_1);

        let Iso { fwd: lhs_fwd, rev: lhs_rev } = lhs_iso;
        let Iso { fwd: rhs_fwd, rev: rhs_rev } = rhs_iso;

        let fwd = Scope::make(ctx_len, |sum_0| {
            sum_0
            .case(
                lhs_name_0,
                Scope::constant(sum_ty_1.clone()),
                Scope::make(ctx_len + 1, |lhs_0| lhs_fwd.clone().bind(lhs_0).inj_lhs()),
                Scope::make(ctx_len + 1, |rhs_0| rhs_fwd.clone().bind(rhs_0).inj_rhs()),
            )
        });

        let rev = Scope::make(ctx_len, |sum_1| {
            sum_1
            .case(
                lhs_name_1,
                Scope::constant(sum_ty_0.clone()),
                Scope::make(ctx_len + 1, |lhs_1| lhs_rev.clone().bind(lhs_1).inj_lhs()),
                Scope::make(ctx_len + 1, |rhs_1| rhs_rev.clone().bind(rhs_1).inj_rhs()),
            )
        });

        Iso { fwd, rev }
    }

    /// ```text
    /// Γ ⊢ lhs_name : Name
    /// Γ ⊢ rhs_ty : Type
    /// ----
    /// Γ ⊢ Iso::sum_never_lhs(rhs_ty) : Ty::sum(lhs_name, Never, rhs_ty) ≅ rhs_ty
    /// ```

    pub fn sum_never_lhs(
        lhs_name: Name,
        rhs_ty: Ty,
    ) -> Iso {
        let ctx_len = rhs_ty.ctx_len();

        let fwd = Scope::make(ctx_len, |sum| {
            sum
            .case(
                lhs_name,
                Scope::constant(rhs_ty.clone()),
                Scope::constant(
                    Tm::explode(Scope::constant(rhs_ty.clone()))
                ),
                Scope::make(ctx_len + 1, |rhs| rhs),
            )
        });
        
        let rev = Scope::make(ctx_len, |rhs| rhs.inj_rhs());

        Iso { fwd, rev }
    }

    /// ```text
    /// Γ ⊢ lhs_name : Name
    /// Γ ⊢ lhs_ty : Type
    /// ----
    /// Γ ⊢ Iso::sum_never_rhs(lhs_ty) : Ty::sum(lhs_name, lhs_ty, Never) ≅ lhs_ty
    /// ```

    pub fn sum_never_rhs(
        lhs_name: Name,
        lhs_ty: Ty,
    ) -> Iso {
        let ctx_len = lhs_ty.ctx_len();

        let fwd = Scope::make(ctx_len, |sum| {
            sum
            .case(
                lhs_name,
                Scope::constant(lhs_ty.clone()),
                Scope::make(ctx_len + 1, |lhs| lhs),
                Scope::constant(
                    Tm::explode(Scope::constant(lhs_ty.clone()))
                ),
            )
        });
        
        let rev = Scope::make(ctx_len, |lhs| lhs.inj_lhs());

        Iso { fwd, rev }
    }

    /// ```text
    /// Γ ⊢ head_name : Name
    /// Γ ⊢ head_ty_0 : Type
    /// Γ ⊢ head_ty_1 : Type
    /// Γ ⊢ tail_ty : head_ty_0 ⊢ Type
    /// Γ ⊢ head_iso : head_ty_0 ≅ head_ty_1
    /// ----
    /// Γ ⊢ Iso::dependent_sigma_head_congruence(tail_ty, head_iso)
    ///   : Ty::sigma(head_name, head_ty_0, tail_ty)
    ///   ≅ Ty::sigma(head_name, head_ty_1, Scope::make(Γ.len(), |head|
    ///     tail_ty.bind(head_eq.rev.bind(head))
    ///   })
    /// ```

    pub fn dependent_sigma_head_congruence(
        tail_ty: Scope<Ty>,
        head_iso: Iso,
    ) -> Iso {
        let ctx_len = max_all([
            tail_ty.ctx_len(),
            head_iso.ctx_len(),
        ]);

        let Iso { fwd: head_fwd, rev: head_rev } = head_iso;

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
            let tail_1 = Tm::cast(
                bound_tail_ty_0,
                bound_tail_ty_1,
                tail_0,
            );

            head_1.pair(tail_1)
        });

        let rev = Scope::make(ctx_len, |pair_1| {
            let head_1 = pair_1.clone().proj_head();
            let tail_1 = pair_1.proj_tail();

            let head_0 = head_rev.clone().bind(head_1);
            let tail_0 = tail_1;

            head_0.pair(tail_0)
        });

        Iso { fwd, rev }
    }

    /// ```text
    /// Γ ⊢ head_name : Name
    /// Γ ⊢ head_ty : Type
    /// Γ ⊢ tail_ty_0 : head_ty ⊢ Type
    /// Γ ⊢ tail_ty_1 : head_ty ⊢ Type
    /// Γ ⊢ tail_iso : head_ty ⊢ tail_ty_0 ≅ tail_ty_1
    /// ----
    /// Γ ⊢ Iso::dependent_sigma_tail_congruence(tail_iso)
    ///   : Ty::sigma(head_name, head_ty, tail_ty_0)
    ///   ≅ Ty::sigma(head_name, head_ty, tail_ty_1)
    /// ```

    pub fn dependent_sigma_tail_congruence(
        tail_iso: Scope<Iso>,
    ) -> Iso {
        let ctx_len = tail_iso.ctx_len();

        let (tail_fwd, tail_rev) = tail_iso.map_multi(
            ctx_len,
            |_, tail_iso| {
                let Iso { fwd, rev } = tail_iso;
                (fwd, rev)
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

        Iso { fwd, rev }
    }

    /// ```text
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
            Tm::proof().pair(tail)
        });

        Iso { fwd, rev }
    }

    /// ```text
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
                lhs_name.clone(),
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
                lhs_name,
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

        Iso { fwd, rev }
    }

    /// ```text
    /// Γ ⊢ head_name : Name
    /// Γ ⊢ head_head_name : Name
    /// Γ ⊢ head_head_ty : Type
    /// Γ, head_head: head_head_ty ⊢ head_tail_ty : Type
    /// Γ, head : Ty::sigma(head_head_name, head_head_ty, head_tail_ty) ⊢ tail_ty : Type
    /// ----
    /// Γ ⊢ Iso::sigma_sigma_head()
    ///   : Ty::sigma(
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

        Iso { fwd, rev }
    }

    /// ```text
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
            head.pair(Tm::proof())
        });

        Iso { fwd, rev }
    }

    /// ```text
    /// Γ ⊢ head_name : Name
    /// Γ ⊢ head_ty : Type
    /// Γ ⊢ tail_ty : head_ty ⊢ Type
    /// Γ ⊢ unique_head : head_ty
    /// Γ, head: head_ty, tail: tail_ty ⊢ constrains : head == unique_head
    /// ----
    /// Γ ⊢ Iso::sigma_tail_constrains_head(tail_ty, unique_head)
    ///   : Ty::sigma(head_name, head_ty, tail_ty)
    ///   ≅ tail_ty.bind(unique_head)
    /// ```

    pub fn sigma_tail_constrains_head(
        tail_ty: Scope<Ty>,
        unique_head: Tm,
    ) -> Iso {
        let ctx_len = max_all([
            tail_ty.ctx_len(),
            unique_head.ctx_len(),
        ]);

        lazy_static! {
            static ref TAIL_NAME: Name = Name::from("tail");
        }

        let unique_bound_tail_ty = tail_ty.clone().bind(unique_head.clone());

        let fwd = Scope::make(ctx_len, |pair| {
            let head = pair.clone().proj_head();
            let tail = pair.proj_tail();

            Tm::cast(
                tail_ty.clone().bind(head),
                unique_bound_tail_ty.clone(),
                tail,
            )
        });

        let rev = Scope::make(ctx_len, |tail| {
            unique_head.clone().pair(tail)
        });

        Iso { fwd, rev }
    }

    /// ```text
    /// Γ ⊢ arg_name : Name
    /// Γ ⊢ arg_ty_0 : Type
    /// Γ ⊢ arg_ty_1 : Type
    /// Γ ⊢ res_ty : arg_ty_0 ⊢ Type
    /// Γ ⊢ arg_iso : arg_ty_0 ≅ arg_ty_1
    /// ----
    /// Γ ⊢ Iso::dependent_pi_arg_congruence(res_ty, arg_iso)
    ///   : Ty::pi(arg_name, arg_ty_0, res_ty) ≅ Ty::pi(arg_name, arg_ty_1, res_ty)
    /// ```

    pub fn dependent_pi_arg_congruence(
        res_ty: Scope<Ty>,
        arg_iso: Iso,
    ) -> Iso {
        let ctx_len = max_all([
            res_ty.ctx_len(),
            arg_iso.ctx_len(),
        ]);

        let Iso {
            fwd: arg_fwd, rev: arg_rev,
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

                Tm::cast(
                    res_ty.clone().bind(arg_0_round_trip),
                    res_ty.clone().bind(arg_0),
                    func.app(arg_1),
                )
            }))
        });

        Iso { fwd, rev }
    }

    /// ```text
    /// Γ ⊢ arg_name : Name
    /// Γ ⊢ arg_ty : Type
    /// Γ ⊢ res_ty_0 : arg_ty ⊢ Type
    /// Γ ⊢ res_ty_1 : arg_ty ⊢ Type
    /// Γ ⊢ res_iso : arg_ty |- res_ty_0 ≅ res_ty_1
    /// ----
    /// Γ ⊢ Iso::dependent_pi_res_congruence(res_iso)
    ///   : Ty::pi(arg_name, arg_ty, res_ty_0) ≅ Ty::pi(arg_name, arg_ty, res_ty_1)
    /// ```

    pub fn dependent_pi_res_congruence(
        res_iso: Scope<Iso>,
    ) -> Iso {
        let ctx_len = res_iso.ctx_len();

        let (res_fwd, res_rev) = res_iso.map_multi(
            ctx_len,
            |_, res_iso| {
                let Iso { fwd, rev } = res_iso;
                (fwd, rev)
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

        Iso { fwd, rev }
    }

    /// ```text
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
        let fwd = Scope::constant(Tm::proof());
        let rev = Scope::constant(Tm::func(Scope::constant(
            Tm::explode(res_ty.clone())
        )));

        Iso { fwd, rev }
    }

    /// ```text
    /// Γ ⊢ arg_name : Name
    /// Γ ⊢ res_ty : Ty::unit() ⊢ Type
    /// ----
    /// Γ ⊢ Iso::pi_unit_arg()
    ///   : Ty::pi(arg_name, Ty::unit(), res_ty)
    ///   ≅ res_ty.bind(Tm::unit())
    /// ```

    pub fn pi_unit_arg() -> Iso {
        let fwd = Scope::make(0, |func| {
            func.app(Tm::proof())
        });

        let rev = Scope::make(0, |res| {
            Tm::func(Scope::constant(res))
        });

        Iso { fwd, rev }
    }

    /// ```text
    /// Γ ⊢ arg_name : Name
    /// Γ ⊢ lhs_name : Name
    /// Γ ⊢ lhs_ty : Type
    /// Γ ⊢ rhs_ty : Type
    /// Γ ⊢ res_ty : Ty::sum(lhs_name, lhs_ty, rhs_ty) ⊢ Type
    /// ----
    /// Γ ⊢ Iso::pi_sum_arg(lhs_name, res_ty)
    ///   : Ty::pi(arg_name, Ty::sum(lhs_name, lhs_ty, rhs_ty), res_ty)
    ///   ≅ Ty::sigma(
    ///     lhs_name,
    ///     Ty::pi(arg_name, lhs_ty, Scope::make(Γ.len(), |lhs| res_ty.bind(lhs.inj_lhs()))),
    ///     Scope::constant(
    ///         Ty::pi(arg_name, rhs_ty, Scope::make(Γ.len(), |rhs| res_ty.bind(rhs.inj_rhs()))),
    ///     ),
    ///   )
    /// ```

    pub fn pi_sum_arg(
        lhs_name: Name,
        res_ty: Scope<Ty>,
    ) -> Iso {
        let ctx_len = max_all([
            lhs_name.ctx_len(),
            res_ty.ctx_len(),
        ]);

        let fwd = Scope::make(ctx_len, |func| {
            let head = Tm::func(Scope::make(ctx_len + 1, |lhs| {
                func.clone().app(lhs.inj_lhs())
            }));
            let tail = Tm::func(Scope::make(ctx_len + 1, |rhs| {
                func.app(rhs.inj_rhs())
            }));
            head.pair(tail)
        });

        let rev = Scope::make(ctx_len, |pair| {
            let head = pair.clone().proj_head();
            let tail = pair.proj_tail();

            Tm::func(Scope::make(ctx_len + 1, |sum| {
                sum
                .case(
                    lhs_name,
                    res_ty.clone(),
                    Scope::make(ctx_len + 2, |lhs| head.app(lhs)),
                    Scope::make(ctx_len + 2, |rhs| tail.app(rhs)),
                )
            }))
        });

        Iso { fwd, rev }
    }


    /// ```text
    /// Γ ⊢ arg_name : Name
    /// Γ ⊢ head_name : Name
    /// Γ ⊢ head_ty : Type
    /// Γ ⊢ tail_ty : head : Head ⊢ Type
    /// Γ ⊢ res_ty : Ty::sigma(head_name, head_ty, tail_ty) ⊢ Type
    /// ----
    /// Γ ⊢ Iso::pi_sigma_arg()
    ///   : Ty::pi(
    ///         arg_name,
    ///         Ty::sigma(head_name, head_ty, tail_ty),
    ///         res_ty,
    ///     )
    ///   ≅ Ty::pi(
    ///         head_name,
    ///         head_ty,
    ///         |head| Ty::pi(
    ///             arg_name,
    ///             tail_ty.bind(head),
    ///             |tail| res_ty.bind(head.pair(tail)),
    ///         ),
    ///     )
    /// ```

    pub fn pi_sigma_arg() -> Iso {
        let ctx_len = 0;
        let fwd = Scope::make(ctx_len, |func| {
            Tm::func(Scope::make(ctx_len + 1, |head| {
                Tm::func(Scope::make(ctx_len + 2, |tail| {
                    func.app(head.pair(tail))
                }))
            }))
        });

        let rev = Scope::make(ctx_len, |func| {
            Tm::func(Scope::make(ctx_len + 1, |pair| {
                let head = pair.clone().proj_head();
                let tail = pair.proj_tail();
                func.app(head).app(tail)
            }))
        });

        Iso { fwd, rev }
    }

    /// ```text
    /// Γ ⊢ arg_name : Name
    /// Γ ⊢ head_name : Name
    /// Γ ⊢ arg_ty : Type
    /// Γ, arg : arg_ty ⊢ head_ty : Type
    /// Γ, arg : arg_ty, head : head_ty ⊢ tail_ty : Type
    /// ----
    /// Γ ⊢ Iso::pi_sigma_res()
    ///   : Ty::pi(
    ///     arg_name,
    ///     arg_ty,
    ///     Scope::make(Γ.len(), |arg| Ty::sigma(head_name, head_ty.bind(arg), tail_ty)),
    ///   )
    ///   ≅ Ty::sigma(
    ///     head_name,
    ///     Ty::pi(arg_name, arg_ty, head_ty),
    ///     Scope::make(Γ.len(), |head| Ty::pi(
    ///         arg_name,
    ///         arg_ty,
    ///         Scope::make(Γ.len(), |arg| res_ty.bind(arg).bind(head.app(arg))),
    ///     )),
    ///   )
    /// ```

    pub fn pi_sigma_res() -> Iso {
        let ctx_len = 0;

        let fwd = Scope::make(ctx_len, |func| {
            let head = Tm::func(Scope::make(ctx_len + 1, |arg| {
                func.clone().app(arg).proj_head()
            }));
            let tail = Tm::func(Scope::make(ctx_len + 1, |arg| {
                func.clone().app(arg).proj_tail()
            }));
            head.pair(tail)
        });

        let rev = Scope::make(ctx_len, |sigma| {
            let head = sigma.clone().proj_head();
            let tail = sigma.proj_tail();

            Tm::func(Scope::make(ctx_len + 1, |arg| {
                head.app(arg.clone()).pair(tail.app(arg))
            }))
        });

        Iso { fwd, rev }
    }

    /// ```text
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
        let zero_name = Name::from("zero");
        let succ_name = Name::from("succ");

        let output_ty = Ty::sum(
            zero_name.clone(),
            Ty::unit(),
            Ty::sum(
                succ_name.clone(),
                Ty::nat(),
                Ty::never(),
            ),
        );

        let fwd = Scope::make(0, |n| {
            n
            .fold(
                Scope::constant(output_ty.clone()),
                Tm::proof().inj_lhs(),
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
                zero_name,
                Scope::constant(Ty::nat()),
                Scope::constant(Tm::zero()),
                Scope::make(1, |sum| {
                    sum
                    .case(
                        succ_name,
                        Scope::constant(Ty::nat()),
                        Scope::make(2, |n| n.succs(Ubig::ONE)),
                        Scope::constant(
                            Tm::explode(Scope::constant(Ty::nat()))
                        ),
                    )
                }),
            )
        });

        Iso { fwd, rev }
    }

    pub fn sigma_head_nat_split(
        head_name: Name,
        tail_ty: Scope<Ty>,
    ) -> Iso {
        let ctx_len = max_all([
            head_name.ctx_len(),
            tail_ty.ctx_len(),
        ]);

        let zero_name = Name::from("zero");
        let succ_name = Name::from("succ");

        let tail_ty_zero = tail_ty.clone().bind(Tm::zero());
        let tail_ty_succ = Scope::make(tail_ty.ctx_len(), |n| {
            tail_ty.clone().bind(n.succs(Ubig::ONE))
        });

        let input_ty = Ty::sigma(
            head_name.clone(),
            Ty::nat(),
            tail_ty.clone(),
        );

        let output_ty = Ty::sum(
            zero_name.clone(),
            tail_ty_zero,
            Ty::sum(
                succ_name.clone(),
                Ty::sigma(
                    head_name.clone(),
                    Ty::nat(),
                    tail_ty_succ.clone(),
                ),
                Ty::never(),
            ),
        );

        let fwd = Scope::make(ctx_len, |sigma| {
            let head = sigma.clone().proj_head();
            let tail = sigma.proj_tail();

            head
            .fold(
                Scope::constant(output_ty.clone()),
                tail.clone().inj_lhs(),
                Scope::make(ctx_len + 1, |head| {
                    Scope::constant(head.pair(tail).inj_lhs().inj_rhs())
                }),
            )
        });

        let rev = Scope::make(ctx_len, |sum| {
            sum
            .case(
                zero_name,
                Scope::constant(input_ty.clone()),
                Scope::make(ctx_len + 1, |tail| Tm::zero().pair(tail)),
                Scope::make(ctx_len + 1, |sum| {
                    sum
                    .case(
                        succ_name,
                        Scope::constant(input_ty.clone()),
                        Scope::make(ctx_len + 2, |sigma| {
                            let n = sigma.clone().proj_head();
                            let tail = sigma.proj_tail();
                            n.succs(Ubig::ONE).pair(tail)
                        }),
                        Scope::constant(
                            Tm::explode(Scope::constant(input_ty))
                        ),
                    )
                }),
            )
        });

        Iso { fwd, rev }
    }
}

