use crate::priv_prelude::*;

pub trait SanityCheck {
    type Meta;

    fn sanity_check(self, ctx: &mut Vec<Ty>, meta: Self::Meta);
}

impl<T> SanityCheck for Weaken<T>
where
    T: Contextual,
    T: SanityCheck,
{
    type Meta = T::Meta;

    fn sanity_check(self, ctx: &mut Vec<Ty>, meta: T::Meta) {
        assert!(self.ctx_len() <= ctx.len());
        self.into_inner().sanity_check(ctx, meta)
    }
}

impl<T> SanityCheck for Arc<T>
where
    T: SanityCheck,
    T: Clone,
{
    type Meta = T::Meta;

    fn sanity_check(self, ctx: &mut Vec<Ty>, meta: T::Meta) {
        Arc::unwrap_or_clone(self).sanity_check(ctx, meta)
    }
}

impl SanityCheck for IntroKind {
    type Meta = Ty;

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
    type Meta = ();

    fn sanity_check(self, ctx: &mut Vec<Ty>, (): ()) {
        match self {
            FormKind::Name => (),
            FormKind::Universe => (),
            FormKind::Nat => (),

            /*
            FormKind::Equal { eq_ty, eq_tm_0, eq_tm_1 } => {
                eq_ty.clone().sanity_check(ctx, ());
                eq_tm_0.sanity_check(ctx, eq_ty.clone());
                eq_tm_1.sanity_check(ctx, eq_ty);
            },
            */

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
    type Meta = Ty;

    fn sanity_check(self, ctx: &mut Vec<Ty>, ty: Ty) {
        match self {
            NeutralKind::Var { index } => {
                let var_ty = ctx[index].clone();
                Unify::unify(ctx, (), var_ty, ty).unwrap();
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
                Unify::unify(ctx, (), motive.bind(elim), ty).unwrap();
            },

            NeutralKind::Explode { motive } => {
                let motive = Weaken::new(motive).lift_scope();
                motive.clone().sanity_check(ctx, (Ty::never(), Scope::constant(())));
                Unify::unify(ctx, (), motive.bind(Tm::proof()), ty).unwrap();
            },

            NeutralKind::Case { elim, motive, lhs_inhab, rhs_inhab } => {
                if let Some(neutral) = elim.clone().as_neutral()
                && let Some(elim_ty) = neutral.try_infer_ty(ctx)
                {
                    let (_lhs_name, lhs_ty, rhs_ty) = elim_ty.clone().as_sum().unwrap();
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
                    Unify::unify(ctx, (), motive.bind(elim), ty).unwrap();
                }
            },

            NeutralKind::ProjHead { elim } => {
                match elim {
                    TmKind::Intro { intro } => {
                        let IntroKind::Pair {
                            head_tm, tail_tm: _,
                        } = Arc::unwrap_or_clone(intro) else {
                            unreachable!();
                        };
                        head_tm.sanity_check(ctx, ty);
                    },
                    TmKind::Neutral { neutral } => {
                        if let Some(elim_ty) = neutral.try_infer_ty(ctx) {
                            let (_head_name, head_ty, _tail_ty) = {
                                elim_ty
                                .clone()
                                .as_sigma()
                                .unwrap()
                            };
                            neutral.sanity_check(ctx, elim_ty);
                            Unify::unify(ctx, (), head_ty, ty).unwrap();
                        }
                    },
                    TmKind::Proof => {
                        assert!(ty.is_prop());
                    },
                }
            },

            NeutralKind::ProjTail { elim } => {
                match elim {
                    TmKind::Intro { intro } => {
                        let IntroKind::Pair {
                            head_tm: _, tail_tm,
                        } = Arc::unwrap_or_clone(intro) else {
                            unreachable!();
                        };
                        tail_tm.sanity_check(ctx, ty);
                    },
                    TmKind::Neutral { neutral } => {
                        if let Some(elim_ty) = neutral.try_infer_ty(ctx) {
                            let (_head_name, _head_ty, tail_ty) = {
                                elim_ty
                                .clone()
                                .as_sigma()
                                .unwrap()
                            };
                            neutral.clone().sanity_check(ctx, elim_ty);
                            let head_tm = Weaken::new(TmKind::Neutral { neutral }).proj_head();
                            Unify::unify(
                                ctx,
                                (),
                                tail_ty.bind(head_tm),
                                ty,
                            ).unwrap();
                        }
                    },
                    TmKind::Proof => {
                        assert!(ty.is_prop());
                    },
                }
            },

            NeutralKind::App { elim, arg_tm } => {
                match elim.clone().into_inner() {
                    TmKind::Intro { intro } => {
                        match Arc::unwrap_or_clone(intro) {
                            IntroKind::Func { .. } => (),
                            _ => unreachable!(),
                        }
                    },
                    TmKind::Neutral { neutral } => {
                        if let Some(elim_ty) = neutral.try_infer_ty(ctx) {
                            let (_arg_name, arg_ty, res_ty) = elim_ty.clone().as_pi().unwrap();
                            elim.sanity_check(ctx, elim_ty);
                            arg_tm.clone().sanity_check(ctx, arg_ty);
                            Unify::unify(ctx, (), res_ty.bind(arg_tm), ty).unwrap();
                        }
                    },
                    TmKind::Proof => {
                        assert!(ty.is_prop());
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

impl SanityCheck for NeutralData {
    type Meta = Ty;

    fn sanity_check(self, ctx: &mut Vec<Ty>, ty: Ty) {
        if let Some(tm) = self.get_cached_reduction() {
            tm.sanity_check(ctx, ty.clone());
        }
        self.kind.sanity_check(ctx, ty);
    }
}

impl SanityCheck for TmKind {
    type Meta = Ty;

    fn sanity_check(self, ctx: &mut Vec<Ty>, ty: Ty) {
        match self {
            TmKind::Intro { intro } => intro.sanity_check(ctx, ty),
            TmKind::Neutral { neutral } => neutral.sanity_check(ctx, ty),
            TmKind::Proof => {
                assert!(ty.is_prop());
            },
        }
    }
}

impl SanityCheck for TyKind {
    type Meta = ();

    fn sanity_check(self, ctx: &mut Vec<Ty>, (): ()) {
        match self {
            TyKind::Form { form } => form.sanity_check(ctx, ()),
            TyKind::Neutral { neutral } => neutral.sanity_check(ctx, Ty::universe()),
        }
    }
}

impl SanityCheck for NameKind {
    type Meta = ();

    fn sanity_check(self, ctx: &mut Vec<Ty>, (): ()) {
        match self {
            NameKind::Tag { .. } => (),
            NameKind::Neutral { neutral } => neutral.sanity_check(ctx, Ty::name()),
        }
    }
}

impl<T> SanityCheck for Scope<T>
where
    T: Contextual,
    T: SanityCheck<Meta: Contextual>,
{
    type Meta = (Ty, Scope<T::Meta>);

    fn sanity_check(self, ctx: &mut Vec<Ty>, (var_ty, meta): (Ty, Scope<T::Meta>)) {
        assert!(self.ctx_len <= ctx.len());
        let inner = self.into_inner(ctx.len());
        let meta = meta.into_inner(ctx.len());
        ctx.push(var_ty);
        inner.sanity_check(ctx, meta);
        ctx.pop();
    }
}

