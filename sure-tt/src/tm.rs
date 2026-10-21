use crate::priv_prelude::*;

pub type Tm = Wrapper<core_tt::Tm>;

impl Tm {
    pub fn into_ty(self) -> Ty {
        let (tm, ctx_params) = self.unwrap_parts();
        let ctx_params = ctx_params.map(|_, (ctx, ty)| {
            ty.as_universe().unwrap();
            (ctx, ())
        });
        let ty = tm.into_ty();
        Wrapper::new(ty, ctx_params)
    }

    pub fn tag(tag: Tag) -> Tm {
        let tm = core_tt::Tm::tag(tag);
        let ctx_params = DebugOnly::new(|_| (Ctx::root(), core_tt::Ty::name()));
        Wrapper::new(tm, ctx_params)
    }

    pub fn tags_apart(
        tag_0: DebugOnly<Tag>,
        tag_1: DebugOnly<Tag>,
        elim: DebugOnly<Tm>,
    ) -> Tm {
        let ctx_params = {
            (tag_0, tag_1, elim)
            .gather()
            .map(|lock, (tag_0, tag_1, elim)| {
                let (_, ctx_params) = elim.unwrap_parts();
                let (ctx, elim_ty) = ctx_params.unlock(lock);
                Unify::unify(
                    elim_ty,
                    core_tt::Ty::obs_equal(
                        core_tt::Ty::name(),
                        core_tt::Tm::tag(tag_0),
                        core_tt::Tm::tag(tag_1),
                    ),
                );
                let ty = core_tt::Ty::never();
                (ctx, ty)
            })
        };
        let tm = core_tt::Tm::proof();
        Wrapper::new(tm, ctx_params)
    }

    pub fn zero() -> Tm {
        let tm = core_tt::Tm::zero();
        let ctx_params = DebugOnly::new(|_| (Ctx::root(), core_tt::Ty::nat()));
        Wrapper::new(tm, ctx_params)
    }

    pub fn succs(self, succ_count: impl Into<Ubig>) -> Tm {
        let (tm, ctx_params) = self.unwrap_parts();
        let ctx_params = ctx_params.map(|_, (ctx, ty)| {
            ty.clone().as_nat().unwrap();
            (ctx, ty)
        });
        let tm = tm.succs(succ_count);
        Wrapper::new(tm, ctx_params)
    }

    pub fn fold(
        self,
        motive: Scope<Ty>,
        zero_inhab: Tm,
        succ_inhab: Scope<Scope<Tm>>,
    ) -> Tm {
        let ((elim, motive, zero_inhab, succ_inhab), ctx_params) = {
            (self, motive, zero_inhab, succ_inhab)
            .merge(|
                _,
                (elim, motive, _, _),
                ctx,
                (
                    elim_ty,
                    (motive_elim_ty, _),
                    zero_inhab_ty,
                    (succ_inhab_elim_ty, succ_inhab_params),
                ),
            | {
                let elim_ty = Unify::unify(core_tt::Ty::nat(), elim_ty).unwrap();
                let elim_ty = Unify::unify(elim_ty, motive_elim_ty).unwrap();
                Unify::unify(elim_ty, succ_inhab_elim_ty).unwrap();

                Unify::unify(
                    zero_inhab_ty,
                    motive.clone().bind(core_tt::Tm::zero()),
                ).unwrap();

                let (succ_inhab_state_ty, succ_inhab_ty) = succ_inhab_params.into_inner(ctx.len());
                Unify::unify(
                    succ_inhab_state_ty,
                    motive.clone().into_inner(ctx.len()),
                ).unwrap();
                let succ_inhab_ty = succ_inhab_ty.into_inner(ctx.len() + 1);
                Unify::unify(
                    succ_inhab_ty,
                    motive.clone().bind(core_tt::Tm::var(ctx.len()).succs(Ubig::ONE)),
                ).unwrap();

                let ty = motive.clone().bind(elim.clone());
                (ctx, ty)
            })
        };
        let tm = elim.fold(motive, zero_inhab, succ_inhab);
        Wrapper::new(tm, ctx_params)
    }

    pub fn refl(self) -> Tm {
        let (eq_tm, ctx_params) = self.unwrap_parts();
        let ctx_params = ctx_params.map(|_, (ctx, eq_ty)| {
            let ty = core_tt::Ty::obs_equal(eq_ty, eq_tm.clone(), eq_tm);
            (ctx, ty)
        });
        let tm = core_tt::Tm::proof();
        Wrapper::new(tm, ctx_params)
    }

    pub fn cong(
        eq_ty: DebugOnly<Ty>,
        eq_tm_0: DebugOnly<Tm>,
        eq_tm_1: DebugOnly<Tm>,
        elim: DebugOnly<Tm>,
        motive: DebugOnly<Scope<Scope<Ty>>>,
        inhab: DebugOnly<Tm>,
    ) -> Tm {
        let ctx_params = {
            (eq_ty, eq_tm_0, eq_tm_1, elim, motive, inhab)
            .gather()
            .map(|lock, wrapped| {
                let (
                    (eq_ty, eq_tm_0, eq_tm_1, elim, motive, _inhab),
                    ctx,
                    ((), eq_ty_0, eq_ty_1, elim_ty, (motive_eq_ty, motive_params), inhab_ty),
                ) = wrapped.unlock_merge(lock, Ctx::root());

                let eq_ty = Unify::unify(eq_ty, eq_ty_0).unwrap();
                let eq_ty = Unify::unify(eq_ty, eq_ty_1).unwrap();
                let eq_ty = Unify::unify(eq_ty, motive_eq_ty).unwrap();
                let (motive_elim_ty, _) = motive_params.into_inner(ctx.len());

                Unify::unify(
                    motive_elim_ty,
                    core_tt::Ty::obs_equal(
                        eq_ty.clone(),
                        eq_tm_0.clone(),
                        core_tt::Tm::var(ctx.len()),
                    ),
                ).unwrap();

                Unify::unify(
                    elim_ty,
                    core_tt::Ty::obs_equal(eq_ty, eq_tm_0.clone(), eq_tm_1.clone()),
                ).unwrap();

                Unify::unify(
                    inhab_ty,
                    motive.clone().bind(eq_tm_0).bind(core_tt::Tm::proof()),
                ).unwrap();

                let motive_inner = motive.clone().into_inner(ctx.len()).into_inner(ctx.len() + 1);
                assert!(motive_inner.is_prop(&mut Vec::new()));

                let ty = motive.bind(eq_tm_1).bind(elim);
                (ctx, ty)
            })
        };
        let tm = core_tt::Tm::proof();
        Wrapper::new(tm, ctx_params)
    }

    pub fn cast(
        ty_0: Ty,
        ty_1: Ty,
        tys_eq: DebugOnly<Tm>,
        tm_0: Tm,
    ) -> Tm {
        let ((ty_0, ty_1, tm_0), ctx_params) = {
            (ty_0, ty_1, tm_0)
            .merge(|lock, (ty_0, ty_1, _), ctx, ((), (), ty)| {
                let (_, ctx, (tys_eq_ty,)) = {
                    (tys_eq,).gather().unlock(lock).unlock_merge(lock, ctx)
                };

                Unify::unify(
                    tys_eq_ty,
                    core_tt::Ty::obs_equal(
                        core_tt::Ty::universe(),
                        ty_0.clone().into_tm(),
                        ty_1.clone().into_tm(),
                    ),
                ).unwrap();
                Unify::unify(ty_0.clone(), ty).unwrap();

                (ctx, ty_1.clone())
            })
        };
        let tm = core_tt::Tm::cast(ty_0, ty_1, tm_0);
        Wrapper::new(tm, ctx_params)
    }

    pub fn explode(
        elim: DebugOnly<Tm>,
        motive: Scope<Ty>,
    ) -> Tm {
        let (motive, ctx_params) = motive.unwrap_parts();
        let ctx_params = ctx_params.map(|lock, (ctx, (motive_elim_ty, _))| {
            let ((elim,), ctx, (elim_ty,)) = (elim,).gather().unlock(lock).unlock_merge(lock, ctx);

            let elim_ty = Unify::unify(core_tt::Ty::never(), elim_ty).unwrap();
            Unify::unify(elim_ty, motive_elim_ty).unwrap();

            let ty = motive.clone().bind(elim);
            (ctx, ty)
        });
        let tm = core_tt::Tm::explode(motive);
        Wrapper::new(tm, ctx_params)
    }

    pub fn unit() -> Tm {
        let tm = core_tt::Tm::proof();
        let ctx_params = DebugOnly::new(|_| (Ctx::root(), core_tt::Ty::unit()));
        Wrapper::new(tm, ctx_params)
    }

    pub fn inj_lhs(
        self,
        lhs_name: DebugOnly<Name>,
        rhs_ty: DebugOnly<Ty>,
    ) -> Tm {
        let (lhs_tm, ctx_params) = self.unwrap_parts();
        let ctx_params = ctx_params.map(|lock, (ctx, lhs_ty)| {
            let ((lhs_name, rhs_ty), ctx, ((), ())) = {
                (lhs_name, rhs_ty).gather().unlock(lock).unlock_merge(lock, ctx)
            };
            let ty = core_tt::Ty::sum(lhs_name, lhs_ty, rhs_ty);
            (ctx, ty)
        });
        let tm = lhs_tm.inj_lhs();
        Wrapper::new(tm, ctx_params)
    }

    pub fn inj_rhs(
        self,
        lhs_name: DebugOnly<Name>,
        lhs_ty: DebugOnly<Ty>,
    ) -> Tm {
        let (rhs_tm, ctx_params) = self.unwrap_parts();
        let ctx_params = ctx_params.map(|lock, (ctx, rhs_ty)| {
            let ((lhs_name, lhs_ty), ctx, ((), ())) = {
                (lhs_name, lhs_ty).gather().unlock(lock).unlock_merge(lock, ctx)
            };
            let ty = core_tt::Ty::sum(lhs_name, lhs_ty, rhs_ty);
            (ctx, ty)
        });
        let tm = rhs_tm.inj_rhs();
        Wrapper::new(tm, ctx_params)
    }

    pub fn case(
        self,
        lhs_name: Name,
        motive: Scope<Ty>,
        lhs_inhab: Scope<Tm>,
        rhs_inhab: Scope<Tm>,
    ) -> Tm {
        let ((elim, lhs_name, motive, lhs_inhab, rhs_inhab), ctx_params) = {
            (self, lhs_name, motive, lhs_inhab, rhs_inhab)
            .merge(|
                _,
                (elim, lhs_name, motive, _, _),
                ctx,
                (
                    elim_ty,
                    (),
                    (motive_elim_ty, _),
                    (lhs_inhab_lhs_ty, lhs_inhab_ty),
                    (rhs_inhab_rhs_ty, rhs_inhab_ty),
                ),
            | {
                let elim_ty = Unify::unify(elim_ty, motive_elim_ty).unwrap();
                let (elim_lhs_name, lhs_ty, rhs_ty) = elim_ty.as_sum().unwrap();

                Unify::unify(lhs_name.clone(), elim_lhs_name).unwrap();
                Unify::unify(lhs_ty, lhs_inhab_lhs_ty).unwrap();
                Unify::unify(rhs_ty, rhs_inhab_rhs_ty).unwrap();

                Unify::unify(
                    lhs_inhab_ty.into_inner(ctx.len()),
                    motive.clone().bind(core_tt::Tm::var(ctx.len()).inj_lhs()),
                ).unwrap();
                Unify::unify(
                    rhs_inhab_ty.into_inner(ctx.len()),
                    motive.clone().bind(core_tt::Tm::var(ctx.len()).inj_rhs()),
                ).unwrap();

                let ty = motive.clone().bind(elim.clone());
                (ctx, ty)
            })
        };
        let tm = elim.case(lhs_name, motive, lhs_inhab, rhs_inhab);
        Wrapper::new(tm, ctx_params)
    }

    pub fn pair(
        head_name: DebugOnly<Name>,
        tail_ty: DebugOnly<Scope<Ty>>,
        head_tm: Tm,
        tail_tm: Tm,
    ) -> Tm {
        let ((head_tm, tail_tm), ctx_params) = {
            (head_tm, tail_tm)
            .merge(|lock, (head_tm, _), ctx, (head_ty, bound_tail_ty)| {
                let ((head_name, tail_ty), ctx, ((), (tail_head_ty, _))) = {
                    (head_name, tail_ty).gather().unlock(lock).unlock_merge(lock, ctx)
                };

                let head_ty = Unify::unify(head_ty, tail_head_ty).unwrap();
                Unify::unify(
                    tail_ty.clone().bind(head_tm.clone()),
                    bound_tail_ty,
                ).unwrap();
                let ty = core_tt::Ty::sigma(head_name, head_ty, tail_ty);
                (ctx, ty)
            })
        };
        let tm = head_tm.pair(tail_tm);
        Wrapper::new(tm, ctx_params)
    }

    pub fn proj_head(self) -> Tm {
        let (tm, ctx_params) = self.unwrap_parts();
        let ctx_params = ctx_params.map(|_, (ctx, ty)| {
            let (_head_name, head_ty, _tail_ty) = ty.as_sigma().unwrap();
            (ctx, head_ty)
        });
        let tm = tm.proj_head();
        Wrapper::new(tm, ctx_params)
    }

    pub fn proj_tail(self) -> Tm {
        let (tm, ctx_params) = self.unwrap_parts();
        let ctx_params = ctx_params.map(|_, (ctx, ty)| {
            let (_head_name, _head_ty, tail_ty) = ty.as_sigma().unwrap();
            let bound_tail_ty = tail_ty.bind(tm.clone().proj_head());
            (ctx, bound_tail_ty)
        });
        let tm = tm.proj_tail();
        Wrapper::new(tm, ctx_params)
    }

    pub fn func(
        arg_name: DebugOnly<Name>,
        arg_ty: DebugOnly<Ty>,
        res_tm: Scope<Tm>,
    ) -> Tm {
        let (res_tm, ctx_params) = res_tm.unwrap_parts();
        let ctx_params = ctx_params.map(|lock, (ctx, (res_arg_ty, res_ty))| {
            let ((arg_name, arg_ty), ctx, ((), ())) = {
                (arg_name, arg_ty).gather().unlock(lock).unlock_merge(lock, ctx)
            };

            let arg_ty = Unify::unify(arg_ty, res_arg_ty).unwrap();
            let ty = core_tt::Ty::pi(arg_name, arg_ty, res_ty);
            (ctx, ty)
        });
        let tm = core_tt::Tm::func(res_tm);
        Wrapper::new(tm, ctx_params)
    }

    pub fn app(
        self,
        arg_tm: Tm,
    ) -> Tm {
        let ((elim, arg_tm), ctx_params) = {
            (self, arg_tm)
            .merge(|_, (_, arg_tm), ctx, (elim_ty, arg_ty)| {
                let (_, elim_arg_ty, res_ty) = elim_ty.as_pi().unwrap();
                Unify::unify(elim_arg_ty, arg_ty).unwrap();
                let ty = res_ty.bind(arg_tm.clone());
                (ctx, ty)
            })
        };
        let tm = elim.app(arg_tm);
        Wrapper::new(tm, ctx_params)
    }
}

