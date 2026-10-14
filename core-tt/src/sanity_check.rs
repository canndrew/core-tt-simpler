use crate::priv_prelude::*;

pub trait SanityCheck: WellFormed {
    fn sanity_check(self, ctx: &mut Vec<Ty>, params: Self::Params);
}

impl<T> SanityCheck for Weaken<T>
where
    T: Contextual,
    T: SanityCheck,
{
    fn sanity_check(self, ctx: &mut Vec<Ty>, params: T::Params) {
        assert!(self.ctx_len() <= ctx.len());
        self.into_inner().sanity_check(ctx, params)
    }
}

impl<T> SanityCheck for Arc<T>
where
    T: SanityCheck,
    T: Clone,
{
    fn sanity_check(self, ctx: &mut Vec<Ty>, params: T::Params) {
        Arc::unwrap_or_clone(self).sanity_check(ctx, params)
    }
}

impl SanityCheck for IntroKind {
    fn sanity_check(self, ctx: &mut Vec<Ty>, ty: Ty) {
        match self {
            IntroKind::Tag { .. } => {
                let () = ty.as_name().unwrap();
            },
            IntroKind::Form { form } => {
                let () = ty.as_universe().unwrap();
                form.sanity_check(ctx, ());
            },
            IntroKind::Constant { .. } => {
                let () = ty.as_nat().unwrap();
            },
            IntroKind::Succs { succ_count_m1: _, pred_tm } => {
                let () = ty.clone().as_nat().unwrap();
                pred_tm.sanity_check(ctx, ty);
            },

            IntroKind::InjLhs { lhs_tm } => {
                let (_lhs_name, lhs_ty, _rhs_ty) = ty.as_sum().unwrap();
                lhs_tm.sanity_check(ctx, lhs_ty);
            },
            IntroKind::InjRhs { rhs_tm } => {
                let (_lhs_name, _lhs_ty, rhs_ty) = ty.as_sum().unwrap();
                rhs_tm.sanity_check(ctx, rhs_ty);
            },
            IntroKind::Pair { head_tm, tail_tm } => {
                let (_head_name, head_ty, tail_ty) = ty.as_sigma().unwrap();
                head_tm.clone().sanity_check(ctx, head_ty);
                tail_tm.sanity_check(ctx, tail_ty.bind(head_tm));
            },
            IntroKind::Func { res_tm } => {
                let (_arg_name, arg_ty, res_ty) = ty.as_pi().unwrap();
                res_tm.sanity_check(ctx, (arg_ty, res_ty));
            },
        }
    }
}

impl SanityCheck for FormKind {
    fn sanity_check(self, ctx: &mut Vec<Ty>, (): ()) {
        match self {
            FormKind::Name => (),
            FormKind::Universe => (),
            FormKind::Nat => (),

            FormKind::Never => (),
            FormKind::Unit => (),
            FormKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                lhs_name.sanity_check(ctx, ());
                lhs_ty.sanity_check(ctx, ());
                rhs_ty.sanity_check(ctx, ());
            },
            FormKind::Sigma { head_name, head_ty, tail_ty } => {
                head_name.sanity_check(ctx, ());
                head_ty.clone().sanity_check(ctx, ());
                tail_ty.sanity_check(ctx, (head_ty, Scope::constant(())));
            },
            FormKind::Pi { arg_name, arg_ty, res_ty } => {
                arg_name.sanity_check(ctx, ());
                arg_ty.clone().sanity_check(ctx, ());
                res_ty.sanity_check(ctx, (arg_ty, Scope::constant(())));
            },
        }
    }
}

impl SanityCheck for NeutralKind {
    fn sanity_check(self, ctx: &mut Vec<Ty>, ty: Ty) {
        match self {
            NeutralKind::Var { index } => {
                let var_ty = ctx[index].clone();
                Unify::unify(var_ty, ty).unwrap();
            },
            NeutralKind::Bind { var_tms, truncated_body_usages, body: _ } => {
                assert!(truncated_body_usages.ctx_len() <= ctx.len());
                for var_tm in var_tms {
                    assert!(var_tm.ctx_len() <= ctx.len());
                }
            },

            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                elim.clone().sanity_check(ctx, Ty::nat());
                motive.clone().sanity_check(ctx, (Ty::nat(), Scope::constant(())));
                zero_inhab.sanity_check(ctx, motive.clone().bind(Tm::zero()));
                succ_inhab.sanity_check(
                    ctx, 
                    (
                        Ty::nat(),
                        Scope::make(ctx.len(), |elim| {
                            (
                                motive.clone().bind(elim.clone()),
                                Scope::constant(motive.clone().bind(elim.succs(1usize))),
                            )
                        }),
                    )
                );
                Unify::unify(motive.bind(elim), ty).unwrap();
            },

            NeutralKind::Explode { motive } => {
                let motive = Weaken::new(motive).lift_scope();
                motive.clone().sanity_check(ctx, (Ty::never(), Scope::constant(())));
                Unify::unify(motive.bind(Tm::proof()), ty).unwrap();
            },

            NeutralKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab } => {
                lhs_name.clone().sanity_check(ctx, ());

                if let Some(stuck) = elim.clone().as_stuck() {
                    let elim_ty = stuck.infer_ty(ctx);
                    let (actual_lhs_name, lhs_ty, rhs_ty) = elim_ty.clone().as_sum().unwrap();
                    Unify::unify(lhs_name, actual_lhs_name).unwrap();
                    elim.clone().sanity_check(ctx, elim_ty.clone());
                    motive.clone().sanity_check(ctx, (elim_ty, Scope::constant(())));
                    lhs_inhab.sanity_check(
                        ctx,
                        (
                            lhs_ty,
                            Scope::make(ctx.len(), |lhs| motive.clone().bind(lhs.inj_lhs())),
                        ),
                    );
                    rhs_inhab.sanity_check(
                        ctx,
                        (
                            rhs_ty,
                            Scope::make(ctx.len(), |rhs| motive.clone().bind(rhs.inj_rhs())),
                        ),
                    );
                    Unify::unify(motive.bind(elim), ty).unwrap();
                }
            },

            NeutralKind::ProjHead { elim } => {
                match elim {
                    OrLazy::Reduced(TmKind::Intro { intro }) => {
                        let IntroKind::Pair {
                            head_tm, tail_tm: _,
                        } = Arc::unwrap_or_clone(intro) else {
                            unreachable!();
                        };
                        head_tm.sanity_check(ctx, ty);
                    },
                    OrLazy::Reduced(TmKind::Proof) => {
                        assert!(ty.is_prop(&mut Vec::new()));
                    },
                    OrLazy::Reduced(TmKind::Stuck { stuck }) => {
                        stuck.sanity_check(ctx, ());
                    },
                    OrLazy::Lazy(lazy) => {
                        if let Some(elim_ty) = lazy.try_infer_ty(ctx) {
                            let (_head_name, head_ty, _tail_ty) = {
                                elim_ty
                                .clone()
                                .as_sigma()
                                .unwrap()
                            };
                            lazy.sanity_check(ctx, elim_ty);
                            Unify::unify(head_ty, ty).unwrap();
                        }
                    },
                }
            },

            NeutralKind::ProjTail { elim } => {
                match elim {
                    OrLazy::Reduced(TmKind::Intro { intro }) => {
                        let IntroKind::Pair {
                            head_tm: _, tail_tm,
                        } = Arc::unwrap_or_clone(intro) else {
                            unreachable!();
                        };
                        tail_tm.sanity_check(ctx, ty);
                    },
                    OrLazy::Reduced(TmKind::Proof) => {
                        assert!(ty.is_prop(&mut Vec::new()));
                    },
                    OrLazy::Reduced(TmKind::Stuck { stuck }) => {
                        stuck.sanity_check(ctx, ());
                    },
                    OrLazy::Lazy(lazy) => {
                        if let Some(elim_ty) = lazy.try_infer_ty(ctx) {
                            let (_head_name, _head_ty, tail_ty) = {
                                elim_ty
                                .clone()
                                .as_sigma()
                                .unwrap()
                            };
                            lazy.clone().sanity_check(ctx, elim_ty);
                            let head_tm = Weaken::new(OrLazy::Lazy(lazy)).proj_head();
                            Unify::unify(tail_ty.bind(head_tm), ty).unwrap();
                        }
                    },
                }
            },

            NeutralKind::App { elim, arg_tm } => {
                match elim.into_inner() {
                    OrLazy::Reduced(TmKind::Intro { intro }) => {
                        match Arc::unwrap_or_clone(intro) {
                            IntroKind::Func { .. } => (),
                            _ => unreachable!(),
                        }
                    },
                    OrLazy::Reduced(TmKind::Proof) => {
                        assert!(ty.is_prop(&mut Vec::new()));
                    },
                    OrLazy::Reduced(TmKind::Stuck { stuck }) => {
                        stuck.sanity_check(ctx, ());
                    },
                    OrLazy::Lazy(lazy) => {
                        if let Some(elim_ty) = lazy.try_infer_ty(ctx) {
                            let (_arg_name, arg_ty, res_ty) = elim_ty.clone().as_pi().unwrap();
                            lazy.sanity_check(ctx, elim_ty);
                            arg_tm.clone().sanity_check(ctx, arg_ty);
                            Unify::unify(res_ty.bind(arg_tm), ty).unwrap();
                        }
                    },
                }
            },

            NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 } => {
                eq_ty.clone().sanity_check(ctx, ());
                eq_tm_0.sanity_check(ctx, eq_ty.clone());
                eq_tm_1.sanity_check(ctx, eq_ty);
            },

            NeutralKind::Cast { ty_0, ty_1, tm_0 } => {
                ty_0.clone().sanity_check(ctx, ());
                ty_1.clone().sanity_check(ctx, ());
                tm_0.sanity_check(ctx, ty_0.clone());
            },
        }
    }
}

impl SanityCheck for LazyData {
    fn sanity_check(self, ctx: &mut Vec<Ty>, ty: Ty) {
        if let Some(tm) = self.cached_reduced() {
            tm.sanity_check(ctx, ty.clone());
        }
        self.neutral_kind().sanity_check(ctx, ty);
    }
}

impl<T> SanityCheck for OrLazy<T>
where
    T: SanityCheck,
    T: AsTmKind<Type = T::Params>,
{
    fn sanity_check(self, ctx: &mut Vec<Ty>, params: T::Params) {
        match self {
            OrLazy::Reduced(reduced) => {
                reduced.sanity_check(ctx, params);
            },
            OrLazy::Lazy(lazy) => {
                let ty = T::full_type(params);
                lazy.sanity_check(ctx, ty);
            },
        }
    }
}

impl SanityCheck for TmKind {
    fn sanity_check(self, ctx: &mut Vec<Ty>, ty: Ty) {
        match self {
            TmKind::Intro { intro } => {
                intro.sanity_check(ctx, ty)
            },
            TmKind::Proof => {
                assert!(ty.is_prop(&mut Vec::new()));
            },
            TmKind::Stuck { stuck } => {
                stuck.clone().sanity_check(ctx, ());
                Unify::unify(stuck.infer_ty(ctx), ty).unwrap();
            },
        }
    }
}

impl SanityCheck for StuckKind {
    fn sanity_check(self, ctx: &mut Vec<Ty>, (): ()) {
        assert!(self.kind.try_reduce().is_none());
        let ty = self.clone().infer_ty(ctx);
        self.kind.sanity_check(ctx, ty);
    }
}

impl SanityCheck for TyKind {
    fn sanity_check(self, ctx: &mut Vec<Ty>, (): ()) {
        match self {
            TyKind::Form { form } => {
                form.sanity_check(ctx, ())
            },
            TyKind::Stuck { stuck } => {
                stuck.clone().sanity_check(ctx, ());
                Unify::unify(stuck.infer_ty(ctx), Ty::universe()).unwrap();
            },
        }
    }
}

impl SanityCheck for NameKind {
    fn sanity_check(self, ctx: &mut Vec<Ty>, (): ()) {
        match self {
            NameKind::Tag { .. } => (),
            NameKind::Stuck { stuck } => {
                stuck.clone().sanity_check(ctx, ());
                Unify::unify(stuck.infer_ty(ctx), Ty::name()).unwrap();
            },
        }
    }
}

impl<T> SanityCheck for Scope<T>
where
    T: Contextual,
    T: SanityCheck<Params: Contextual>,
{
    fn sanity_check(self, ctx: &mut Vec<Ty>, (var_ty, params): (Ty, Scope<T::Params>)) {
        assert!(self.ctx_len <= ctx.len());
        let inner = self.into_inner(ctx.len());
        let params = params.into_inner(ctx.len());
        ctx.push(var_ty);
        inner.sanity_check(ctx, params);
        ctx.pop();
    }
}

impl Lazy {
    pub fn try_infer_ty(
        &self,
        ctx_tys: &mut Vec<Ty>,
    ) -> Option<Ty> {
        self.clone().into_inner().try_infer_ty(ctx_tys)
    }
}

impl LazyData {
    pub fn try_infer_ty(
        &self,
        ctx_tys: &mut Vec<Ty>,
    ) -> Option<Ty> {
        self.neutral_kind().into_inner().try_infer_ty(ctx_tys)
    }
}

