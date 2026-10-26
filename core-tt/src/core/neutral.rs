use crate::priv_prelude::*;

#[derive(Clone, Debug)]
pub enum NeutralKind {
    Var {
        index: usize,
    },
    Bind {
        var_tms: Vec<Tm>,
        truncated_body_usages: Usages,
        body: OrLazy<TmKind>,
    },

    Fold {
        elim: Tm,
        motive: Scope<Ty>,
        zero_inhab: Tm,
        succ_inhab: Scope<Scope<Tm>>,
    },

    Add {
        tms: Vec<Tm>,
    },

    Explode {
        motive: Scope<OrLazy<TyKind>>,
    },
    Case {
        lhs_name: Name,
        elim: Tm,
        motive: Scope<Ty>,
        lhs_inhab: Scope<Tm>,
        rhs_inhab: Scope<Tm>,
    },
    ProjHead {
        elim: OrLazy<TmKind>,
    },
    ProjTail {
        elim: OrLazy<TmKind>,
    },
    App {
        elim: Tm,
        arg_tm: Tm,
    },

    ObsEqual {
        eq_ty: Ty,
        eq_tm_0: Tm,
        eq_tm_1: Tm,
    },

    Cast {
        ty_0: Ty,
        ty_1: Ty,
        tm_0: Tm,
    },
}

impl Contextual for NeutralKind {
    fn ctx_len(&self) -> usize {
        match self {
            NeutralKind::Var { index } => {
                index + 1
            },
            NeutralKind::Bind { var_tms, truncated_body_usages, body: _ } => {
                max_all([
                    var_tms.ctx_len(),
                    truncated_body_usages.ctx_len(),
                ])
            },

            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                max_all([
                    elim.ctx_len(),
                    motive.ctx_len(),
                    zero_inhab.ctx_len(),
                    succ_inhab.ctx_len(),
                ])
            },

            NeutralKind::Add { tms } => tms.ctx_len(),

            NeutralKind::Explode { motive } => {
                max_all([
                    motive.ctx_len(),
                ])
            },
            NeutralKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab } => {
                max_all([
                    lhs_name.ctx_len(),
                    elim.ctx_len(),
                    motive.ctx_len(),
                    lhs_inhab.ctx_len(),
                    rhs_inhab.ctx_len(),
                ])
            },
            NeutralKind::ProjHead { elim } => {
                elim.ctx_len()
            },
            NeutralKind::ProjTail { elim } => {
                elim.ctx_len()
            },
            NeutralKind::App { elim, arg_tm } => {
                max_all([
                    elim.ctx_len(),
                    arg_tm.ctx_len(),
                ])
            },

            NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 } => {
                max_all([
                    eq_ty.ctx_len(),
                    eq_tm_0.ctx_len(),
                    eq_tm_1.ctx_len(),
                ])
            },

            NeutralKind::Cast { ty_0, ty_1, tm_0 } => {
                max_all([
                    ty_0.ctx_len(),
                    ty_1.ctx_len(),
                    tm_0.ctx_len(),
                ])
            },
        }
    }

    fn collect_usages(&self, usages: &mut Usages) {
        match self {
            NeutralKind::Var { index } => {
                usages.set_to_one(*index);
            },
            NeutralKind::Bind { var_tms, truncated_body_usages, body: _ } => {
                var_tms.collect_usages(usages);
                usages.or_assign(truncated_body_usages);
            },

            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                elim.collect_usages(usages);
                motive.collect_usages(usages);
                zero_inhab.collect_usages(usages);
                succ_inhab.collect_usages(usages);
            },

            NeutralKind::Add { tms } => tms.collect_usages(usages),

            NeutralKind::Explode { motive } => {
                motive.collect_usages(usages);
            },
            NeutralKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab } => {
                lhs_name.collect_usages(usages);
                elim.collect_usages(usages);
                motive.collect_usages(usages);
                lhs_inhab.collect_usages(usages);
                rhs_inhab.collect_usages(usages);
            },
            NeutralKind::ProjHead { elim } => {
                elim.collect_usages(usages);
            },
            NeutralKind::ProjTail { elim } => {
                elim.collect_usages(usages);
            },
            NeutralKind::App { elim, arg_tm } => {
                elim.collect_usages(usages);
                arg_tm.collect_usages(usages);
            },

            NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 } => {
                eq_ty.collect_usages(usages);
                eq_tm_0.collect_usages(usages);
                eq_tm_1.collect_usages(usages);
            },
            NeutralKind::Cast { ty_0, ty_1, tm_0 } => {
                ty_0.collect_usages(usages);
                ty_1.collect_usages(usages);
                tm_0.collect_usages(usages);
            },
        }
    }

    fn filter_usages(&mut self, usages: &Usages) {
        match self {
            NeutralKind::Var { index } => {
                *index = usages.filter_index(*index);
            },
            NeutralKind::Bind { var_tms, truncated_body_usages, body: _ } => {
                var_tms.filter_usages(usages);
                truncated_body_usages.filter(usages);
            },

            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                elim.filter_usages(usages);
                motive.filter_usages(usages);
                zero_inhab.filter_usages(usages);
                succ_inhab.filter_usages(usages);
            },

            NeutralKind::Add { tms } => tms.filter_usages(usages),

            NeutralKind::Explode { motive } => {
                motive.filter_usages(usages);
            },
            NeutralKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab } => {
                lhs_name.filter_usages(usages);
                elim.filter_usages(usages);
                motive.filter_usages(usages);
                lhs_inhab.filter_usages(usages);
                rhs_inhab.filter_usages(usages);
            },
            NeutralKind::ProjHead { elim } => {
                elim.filter_usages(usages);
            },
            NeutralKind::ProjTail { elim } => {
                elim.filter_usages(usages);
            },
            NeutralKind::App { elim, arg_tm } => {
                elim.filter_usages(usages);
                arg_tm.filter_usages(usages);
            },

            NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 } => {
                eq_ty.filter_usages(usages);
                eq_tm_0.filter_usages(usages);
                eq_tm_1.filter_usages(usages);
            },
            NeutralKind::Cast { ty_0, ty_1, tm_0 } => {
                ty_0.filter_usages(usages);
                ty_1.filter_usages(usages);
                tm_0.filter_usages(usages);
            },
        }
    }

    fn unfilter_usages(&mut self, usages: &Usages) {
        match self {
            NeutralKind::Var { index } => {
                *index = usages.unfilter_index(*index);
            },
            NeutralKind::Bind { var_tms, truncated_body_usages, body: _ } => {
                var_tms.unfilter_usages(usages);
                truncated_body_usages.unfilter(usages);
            },

            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                elim.unfilter_usages(usages);
                motive.unfilter_usages(usages);
                zero_inhab.unfilter_usages(usages);
                succ_inhab.unfilter_usages(usages);
            },

            NeutralKind::Add { tms } => tms.unfilter_usages(usages),

            NeutralKind::Explode { motive } => {
                motive.unfilter_usages(usages);
            },
            NeutralKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab } => {
                lhs_name.unfilter_usages(usages);
                elim.unfilter_usages(usages);
                motive.unfilter_usages(usages);
                lhs_inhab.unfilter_usages(usages);
                rhs_inhab.unfilter_usages(usages);
            },
            NeutralKind::ProjHead { elim } => {
                elim.unfilter_usages(usages);
            },
            NeutralKind::ProjTail { elim } => {
                elim.unfilter_usages(usages);
            },
            NeutralKind::App { elim, arg_tm } => {
                elim.unfilter_usages(usages);
                arg_tm.unfilter_usages(usages);
            },

            NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 } => {
                eq_ty.unfilter_usages(usages);
                eq_tm_0.unfilter_usages(usages);
                eq_tm_1.unfilter_usages(usages);
            },
            NeutralKind::Cast { ty_0, ty_1, tm_0 } => {
                ty_0.unfilter_usages(usages);
                ty_1.unfilter_usages(usages);
                tm_0.unfilter_usages(usages);
            },
        }
    }
}

impl NeutralKind {
    pub fn var_0() -> Arc<NeutralKind> {
        lazy_static! {
            static ref VAR_0: Arc<NeutralKind> = Arc::new(NeutralKind::Var { index: 0 });
        }
        VAR_0.clone()
    }
    
    pub fn try_reduce(&self) -> Option<ValTm> {
        let tm = match self {
            NeutralKind::Var { .. } => return None,
            NeutralKind::Bind { var_tms, truncated_body_usages, body } => {
                let var_tms = var_tms.clone();
                let mut truncated_body_usages = truncated_body_usages.clone();
                let subst_index = cmp::max(var_tms.ctx_len(), truncated_body_usages.ctx_len());
                let subst_len = var_tms.len();

                truncated_body_usages.set_run_to_one(subst_index, subst_len);
                let body = Weaken::from_usages_and_weak(truncated_body_usages, body.clone());
                let mut subst = Subst::from_var_tms(subst_index, var_tms);
                let body = body.subst(&mut subst);
                debug_assert_eq!(subst.len(), subst_len);
                return Some(body);
            },

            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                if motive.inner.clone().is_prop(&mut Vec::new()) {
                    return Some(Weaken::new(TmKind::Proof));
                }
                let elim = elim.clone().try_reduce_to_intro_assuming_relevant()?;
                let (elim_usages, elim) = elim.into_usages_and_weak();
                match &*elim {
                    IntroKind::Constant { ubig } => {
                        let mut ubig = ubig.clone();
                        if ubig.decrement() {
                            let elim = Tm::constant(ubig);
                            let state = Tm::fold(
                                elim.clone(),
                                motive.clone(),
                                zero_inhab.clone(),
                                succ_inhab.clone(),
                            );
                            succ_inhab.clone().bind(elim).bind(state)
                        } else {
                            zero_inhab.clone()
                        }
                    },
                    IntroKind::Succs { succ_count_m1, pred_tm } => {
                        let mut succ_count_m1 = succ_count_m1.clone();
                        let elim = if succ_count_m1.decrement() {
                            Weaken::from_usages_and_weak(
                                elim_usages,
                                OrLazy::Reduced(TmKind::Intro {
                                    intro: Arc::new(IntroKind::Succs {
                                        succ_count_m1,
                                        pred_tm: pred_tm.clone(),
                                    }),
                                }),
                            )
                        } else {
                            Weaken::from_usages_and_weak(
                                elim_usages,
                                pred_tm.clone(),
                            )
                        };
                        let state = Tm::fold(
                            elim.clone(),
                            motive.clone(),
                            zero_inhab.clone(),
                            succ_inhab.clone(),
                        );
                        succ_inhab.clone().bind(elim).bind(state)
                    },
                    _ => unreachable!(),
                }
            },

            NeutralKind::Add { tms } => {
                if tms.is_empty() {
                    return Some(ValTm::zero());
                }

                let mut tms = tms.clone();
                let mut new_tms = Vec::new();
                let mut any_changes = false;
                let mut succ_count = Ubig::ZERO;

                while let Some(tm) = tms.pop() {
                    match tm.reduced().into_inner() {
                        TmKind::Proof => unreachable!(),
                        TmKind::Intro { intro } => {
                            any_changes = true;
                            match Arc::unwrap_or_clone(intro) {
                                IntroKind::Constant { ubig } => {
                                    succ_count += ubig;
                                },
                                IntroKind::Succs { succ_count_m1, pred_tm } => {
                                    succ_count += succ_count_m1 + 1usize;
                                    tms.push(Weaken::new(pred_tm));
                                },
                                _ => unreachable!(),
                            }
                        },
                        TmKind::Stuck { stuck } => {
                            if matches!(&**stuck.neutral_ref(), NeutralKind::Add { .. }) {
                                let NeutralKind::Add {
                                    tms: more_tms,
                                } = Arc::unwrap_or_clone(stuck.into_neutral()) else {
                                    unreachable!();
                                };
                                any_changes = true;
                                tms.extend(more_tms);
                            } else {
                                new_tms.push(
                                    Weaken::new(OrLazy::Reduced(TmKind::Stuck { stuck })),
                                )
                            }
                        },
                    }
                }

                if !any_changes {
                    return None;
                }
                new_tms.reverse();

                let pred_tm = match new_tms.len() {
                    0 => Tm::zero(),
                    1 => new_tms.into_iter().next().unwrap(),
                    _ => {
                        Weaken::new(OrLazy::Reduced(TmKind::Stuck {
                            stuck: StuckKind {
                                kind: Arc::new(NeutralKind::Add { tms: new_tms }),
                            },
                        }))
                    },
                };
                pred_tm.succs(succ_count)
            },

            NeutralKind::Explode { motive } => {
                if motive.inner.clone().reduced().is_prop(&mut Vec::new()) {
                    return Some(Weaken::new(TmKind::Proof));
                } else {
                    return None;
                }
            },

            NeutralKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab } => {
                if motive.inner.clone().is_prop(&mut Vec::new()) {
                    return Some(Weaken::new(TmKind::Proof));
                }

                if let Some(elim) = {
                    elim
                    .clone()
                    .try_reduce_to_intro_assuming_relevant()
                } {
                    let (usages, elim) = elim.into_usages_and_weak();
                    match &*elim {
                        IntroKind::InjLhs { lhs_tm } => {
                            let lhs_tm = Weaken::from_usages_and_weak(usages, lhs_tm.clone());
                            lhs_inhab.clone().bind(lhs_tm)
                        },
                        IntroKind::InjRhs { rhs_tm } => {
                            let rhs_tm = Weaken::from_usages_and_weak(usages, rhs_tm.clone());
                            rhs_inhab.clone().bind(rhs_tm)
                        },
                        _ => unreachable!(),
                    }
                } else {
                    let motive = motive.clone().try_strengthen().ok()?;
                    let (motive_lhs_name, _, _) = motive.as_sum()?;
                    Unify::unify(
                        lhs_name.clone(),
                        motive_lhs_name,
                    )?;

                    let lhs_inhab_ctx_len = lhs_inhab.ctx_len();
                    let lhs_inhab_inner = lhs_inhab.clone().into_inner(lhs_inhab_ctx_len);
                    let lhs_inhab_inner = lhs_inhab_inner.try_reduce_to_intro_assuming_relevant()?;
                    let lhs_tm = match Arc::unwrap_or_clone(lhs_inhab_inner.into_inner()) {
                        IntroKind::InjLhs { lhs_tm } => lhs_tm,
                        _ => return None,
                    };
                    let lhs_stuck = lhs_tm.reduced().as_stuck()?;
                    Unify::unify(lhs_stuck, StuckKind::var(lhs_inhab_ctx_len))?;

                    let rhs_inhab_ctx_len = rhs_inhab.ctx_len();
                    let rhs_inhab_inner = rhs_inhab.clone().into_inner(rhs_inhab_ctx_len);
                    let rhs_inhab_inner = rhs_inhab_inner.try_reduce_to_intro_assuming_relevant()?;
                    let rhs_tm = match Arc::unwrap_or_clone(rhs_inhab_inner.into_inner()) {
                        IntroKind::InjRhs { rhs_tm } => rhs_tm,
                        _ => return None,
                    };
                    let rhs_stuck = rhs_tm.reduced().as_stuck()?;
                    Unify::unify(rhs_stuck, StuckKind::var(rhs_inhab_ctx_len))?;

                    elim.clone()
                }
            },

            NeutralKind::ProjHead { elim } => {
                match elim.clone().reduced() {
                    TmKind::Intro { intro } => {
                        let IntroKind::Pair { head_tm, tail_tm: _ } = &*intro else {
                            unreachable!();
                        };
                        head_tm.clone()
                    },
                    TmKind::Proof => Tm::proof(),
                    TmKind::Stuck { .. } => return None,
                }
            },

            NeutralKind::ProjTail { elim } => {
                match elim.clone().reduced() {
                    TmKind::Intro { intro } => {
                        let IntroKind::Pair { head_tm: _, tail_tm } = &*intro else {
                            return None;
                        };
                        tail_tm.clone()
                    },
                    TmKind::Proof => Tm::proof(),
                    TmKind::Stuck { .. } => return None,
                }
            },

            NeutralKind::App { elim, arg_tm } => {
                let (usages, elim) = elim.clone().reduced().into_usages_and_weak();
                match elim {
                    TmKind::Intro { intro } => {
                        let IntroKind::Func { res_tm } = &*intro else {
                            unreachable!();
                        };
                        let res_tm = {
                            res_tm
                            .clone()
                            .map_without_capture(Weaken::new)
                            .unfiltered(&usages)
                        };
                        res_tm.bind(arg_tm.clone())
                    },
                    TmKind::Proof => Tm::proof(),
                    TmKind::Stuck { .. } => return None,
                }
            },

            NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 } => {
                let eq_ty = eq_ty.clone().try_reduce_to_form()?.into_inner_arc();
                let ty = match eq_ty {
                    FormKind::Name => {
                        let eq_tm_0 = eq_tm_0.clone().try_reduce_to_intro_assuming_relevant()?;
                        let eq_tm_1 = eq_tm_1.clone().try_reduce_to_intro_assuming_relevant()?;
                        let tag_0 = eq_tm_0.as_tag().unwrap();
                        let tag_1 = eq_tm_1.as_tag().unwrap();
                        if tag_0 == tag_1 {
                            Ty::unit()
                        } else {
                            Ty::never()
                        }
                    },

                    FormKind::Universe => {
                        let eq_tm_0 = eq_tm_0.clone().try_reduce_to_intro_assuming_relevant()?;
                        let eq_tm_1 = eq_tm_1.clone().try_reduce_to_intro_assuming_relevant()?;
                        let ty_0 = eq_tm_0.into_form().into_inner_arc();
                        let ty_1 = eq_tm_1.into_form().into_inner_arc();
                        match (ty_0, ty_1) {
                            | (FormKind::Name, FormKind::Name)
                            | (FormKind::Universe, FormKind::Universe)
                            | (FormKind::Nat, FormKind::Nat)
                            | (FormKind::Never, FormKind::Never)
                            | (FormKind::Unit, FormKind::Unit)
                            => Ty::unit(),

                            (
                                FormKind::Sum {
                                    lhs_name: lhs_name_0,
                                    lhs_ty: lhs_ty_0,
                                    rhs_ty: rhs_ty_0,
                                },
                                FormKind::Sum {
                                    lhs_name: lhs_name_1,
                                    lhs_ty: lhs_ty_1,
                                    rhs_ty: rhs_ty_1,
                                },
                            ) => {
                                Ty::sigma(
                                    Name::from("lhs_name"),
                                    Ty::obs_equal(
                                        Ty::name(),
                                        lhs_name_0.into_tm(),
                                        lhs_name_1.into_tm(),
                                    ),
                                    Scope::constant(
                                        Ty::sigma(
                                            Name::from("lhs_ty"),
                                            Ty::obs_equal(
                                                Ty::universe(),
                                                lhs_ty_0.into_tm(),
                                                lhs_ty_1.into_tm(),
                                            ),
                                            Scope::constant(
                                                Ty::sigma(
                                                    Name::from("rhs_ty"),
                                                    Ty::obs_equal(
                                                        Ty::universe(),
                                                        rhs_ty_0.into_tm(),
                                                        rhs_ty_1.into_tm(),
                                                    ),
                                                    Scope::constant(Ty::unit()),
                                                )
                                            ),
                                        )
                                    ),
                                )
                            },

                            (
                                FormKind::Sigma {
                                    head_name: head_name_0,
                                    head_ty: head_ty_0,
                                    tail_ty: tail_ty_0,
                                },
                                FormKind::Sigma {
                                    head_name: head_name_1,
                                    head_ty: head_ty_1,
                                    tail_ty: tail_ty_1,
                                },
                            ) => {
                                let ctx_len = max_all([
                                    head_name_0.ctx_len(),
                                    head_name_1.ctx_len(),
                                    head_ty_0.ctx_len(),
                                    head_ty_1.ctx_len(),
                                    tail_ty_0.ctx_len(),
                                    tail_ty_1.ctx_len(),
                                ]);

                                Ty::sigma(
                                    Name::from("head_name"),
                                    Ty::obs_equal(
                                        Ty::name(),
                                        head_name_0.clone().into_tm(),
                                        head_name_1.clone().into_tm(),
                                    ),
                                    Scope::make(ctx_len, |_head_name_eq| {
                                        Ty::sigma(
                                            Name::from("head_ty"),
                                            Ty::obs_equal(
                                                Ty::universe(),
                                                head_ty_0.clone().into_tm(),
                                                head_ty_1.clone().into_tm(),
                                            ),
                                            Scope::constant(
                                                Ty::sigma(
                                                    Name::from("tail_ty"),
                                                    Ty::pi(
                                                        head_name_0.clone(),
                                                        head_ty_0.clone(),
                                                        Scope::make(ctx_len + 2, |head_tm_0| {
                                                            Ty::obs_equal(
                                                                Ty::universe(),
                                                                tail_ty_0
                                                                .bind(head_tm_0.clone())
                                                                .into_tm(),
                                                                tail_ty_1
                                                                .bind(Tm::cast(
                                                                    head_ty_0,
                                                                    head_ty_1,
                                                                    head_tm_0,
                                                                ))
                                                                .into_tm(),
                                                            )
                                                        }),
                                                    ),
                                                    Scope::constant(Ty::unit()),
                                                )
                                            ),
                                        )
                                    }),
                                )
                            },

                            (
                                FormKind::Pi {
                                    arg_name: arg_name_0,
                                    arg_ty: arg_ty_0,
                                    res_ty: res_ty_0,
                                },
                                FormKind::Pi {
                                    arg_name: arg_name_1,
                                    arg_ty: arg_ty_1,
                                    res_ty: res_ty_1,
                                },
                            ) => {
                                let ctx_len = max_all([
                                    arg_name_0.ctx_len(),
                                    arg_name_1.ctx_len(),
                                    arg_ty_0.ctx_len(),
                                    arg_ty_1.ctx_len(),
                                    res_ty_0.ctx_len(),
                                    res_ty_1.ctx_len(),
                                ]);

                                Ty::sigma(
                                    Name::from("arg_name"),
                                    Ty::obs_equal(
                                        Ty::name(),
                                        arg_name_0.clone().into_tm(),
                                        arg_name_1.clone().into_tm(),
                                    ),
                                    Scope::make(ctx_len, |_arg_name_eq| {
                                        Ty::sigma(
                                            Name::from("arg_ty"),
                                            Ty::obs_equal(
                                                Ty::universe(),
                                                arg_ty_0.clone().into_tm(),
                                                arg_ty_1.clone().into_tm(),
                                            ),
                                            Scope::constant(
                                                Ty::sigma(
                                                    Name::from("res_ty"),
                                                    Ty::pi(
                                                        arg_name_1.clone(),
                                                        arg_ty_1.clone(),
                                                        Scope::make(ctx_len + 2, |arg_tm_1| {
                                                            Ty::obs_equal(
                                                                Ty::universe(),
                                                                res_ty_0
                                                                .bind(Tm::cast(
                                                                    arg_ty_1,
                                                                    arg_ty_0,
                                                                    arg_tm_1.clone(),
                                                                ))
                                                                .into_tm(),
                                                                res_ty_1
                                                                .bind(arg_tm_1)
                                                                .into_tm(),
                                                            )
                                                        }),
                                                    ),
                                                    Scope::constant(Ty::unit()),
                                                )
                                            ),
                                        )
                                    }),
                                )
                            },

                            _ => Ty::never(),
                        }
                    },

                    FormKind::Nat => {
                        let eq_tm_0 = eq_tm_0.clone().try_reduce_to_intro_assuming_relevant()?;
                        let eq_tm_1 = eq_tm_1.clone().try_reduce_to_intro_assuming_relevant()?;
                        match (eq_tm_0.into_inner_arc(), eq_tm_1.into_inner_arc()) {
                            (
                                IntroKind::Constant { ubig: ubig_0 },
                                IntroKind::Constant { ubig: ubig_1 },
                            ) => {
                                if ubig_0 == ubig_1 {
                                    Ty::unit()
                                } else {
                                    Ty::never()
                                }
                            },

                            (
                                IntroKind::Constant { ubig },
                                IntroKind::Succs { succ_count_m1, pred_tm },
                            ) => {
                                if ubig > succ_count_m1 {
                                    let ubig = ubig.strict_sub(&(succ_count_m1 + 1usize));
                                    Ty::obs_equal(
                                        Ty::nat(),
                                        Tm::constant(ubig),
                                        Weaken::new(pred_tm),
                                    )
                                } else {
                                    Ty::never()
                                }
                            },

                            (
                                IntroKind::Succs { succ_count_m1, pred_tm },
                                IntroKind::Constant { ubig },
                            ) => {
                                if ubig > succ_count_m1 {
                                    let ubig = ubig.strict_sub(&(succ_count_m1 + 1usize));
                                    Ty::obs_equal(
                                        Ty::nat(),
                                        Weaken::new(pred_tm),
                                        Tm::constant(ubig),
                                    )
                                } else {
                                    Ty::never()
                                }
                            },

                            (
                                IntroKind::Succs {
                                    succ_count_m1: succ_count_m1_0,
                                    pred_tm: pred_tm_0,
                                },
                                IntroKind::Succs {
                                    succ_count_m1: succ_count_m1_1,
                                    pred_tm: pred_tm_1,
                                },
                            ) => {
                                let (tm_0, tm_1) = match succ_count_m1_0.cmp(&succ_count_m1_1) {
                                    cmp::Ordering::Less => {
                                        let tm_0 = Weaken::new(pred_tm_0);
                                        let tm_1 = {
                                            Weaken::new_arc(IntroKind::Succs {
                                                succ_count_m1: {
                                                    succ_count_m1_1
                                                    .strict_sub(&(succ_count_m1_0 + 1usize))
                                                },
                                                pred_tm: pred_tm_1,
                                            })
                                            .map(|intro| {
                                                OrLazy::Reduced(TmKind::Intro { intro })
                                            })
                                        };
                                        (tm_0, tm_1)
                                    },
                                    cmp::Ordering::Equal => {
                                        let tm_0 = Weaken::new(pred_tm_0);
                                        let tm_1 = Weaken::new(pred_tm_1);
                                        (tm_0, tm_1)
                                    },
                                    cmp::Ordering::Greater => {
                                        let tm_0 = {
                                            Weaken::new_arc(IntroKind::Succs {
                                                succ_count_m1: {
                                                    succ_count_m1_0
                                                    .strict_sub(&(succ_count_m1_1 + 1usize))
                                                },
                                                pred_tm: pred_tm_0,
                                            })
                                            .map(|intro| {
                                                OrLazy::Reduced(TmKind::Intro { intro })
                                            })
                                        };
                                        let tm_1 = Weaken::new(pred_tm_1);
                                        (tm_0, tm_1)
                                    },
                                };
                                Ty::obs_equal(Ty::nat(), tm_0, tm_1)
                            },

                            _ => unreachable!(),
                        }
                    },

                    FormKind::Never => Ty::unit(),

                    FormKind::Unit => Ty::unit(),

                    FormKind::Sum { lhs_name: _, lhs_ty, rhs_ty } => {
                        let eq_tm_0 = eq_tm_0.clone().try_reduce_to_intro_assuming_relevant()?;
                        let eq_tm_1 = eq_tm_1.clone().try_reduce_to_intro_assuming_relevant()?;
                        match (eq_tm_0.into_inner_arc(), eq_tm_1.into_inner_arc()) {
                            (
                                IntroKind::InjLhs { lhs_tm: lhs_tm_0 },
                                IntroKind::InjLhs { lhs_tm: lhs_tm_1 },
                            ) => {
                                Ty::obs_equal(
                                    lhs_ty,
                                    Weaken::new(lhs_tm_0),
                                    Weaken::new(lhs_tm_1),
                                )
                            },

                            (
                                IntroKind::InjRhs { rhs_tm: rhs_tm_0 },
                                IntroKind::InjRhs { rhs_tm: rhs_tm_1 },
                            ) => {
                                Ty::obs_equal(
                                    rhs_ty,
                                    Weaken::new(rhs_tm_0),
                                    Weaken::new(rhs_tm_1),
                                )
                            },

                            | (IntroKind::InjLhs { .. }, IntroKind::InjRhs { .. })
                            | (IntroKind::InjRhs { .. }, IntroKind::InjLhs { .. })
                            => Ty::never(),

                            _ => unreachable!(),
                        }
                    },

                    FormKind::Sigma { head_name, head_ty, tail_ty } => {
                        let head_tm_0 = eq_tm_0.clone().proj_head();
                        let tail_tm_0 = eq_tm_0.clone().proj_tail();
                        let head_tm_1 = eq_tm_1.clone().proj_head();
                        let tail_tm_1 = eq_tm_1.clone().proj_tail();

                        let tail_ty_0 = tail_ty.clone().bind(head_tm_0.clone());
                        let tail_ty_1 = tail_ty.clone().bind(head_tm_1.clone());

                        Ty::sigma(
                            head_name,
                            Ty::obs_equal(
                                head_ty,
                                head_tm_0,
                                head_tm_1,
                            ),
                            Scope::constant(
                                Ty::obs_equal(
                                    tail_ty_1.clone(),
                                    Tm::cast(
                                        tail_ty_0,
                                        tail_ty_1,
                                        tail_tm_0,
                                    ),
                                    tail_tm_1,
                                )
                            ),
                        )
                    },

                    FormKind::Pi { arg_name, arg_ty, res_ty } => {
                        let ctx_len = max_all([
                            res_ty.ctx_len(),
                            eq_tm_0.ctx_len(),
                            eq_tm_1.ctx_len(),
                        ]);

                        Ty::pi(
                            arg_name,
                            arg_ty,
                            Scope::make(ctx_len, |arg_tm| {
                                Ty::obs_equal(
                                    res_ty.bind(arg_tm.clone()),
                                    eq_tm_0.clone().app(arg_tm.clone()),
                                    eq_tm_1.clone().app(arg_tm),
                                )
                            }),
                        )
                    },
                };
                ty.into_tm()
            },

            NeutralKind::Cast { ty_0, ty_1, tm_0 } => {
                if let Some(_) = Unify::unify(ty_0.clone(), ty_1.clone()) {
                    tm_0.clone()
                } else {
                    let form_0 = ty_0.clone().try_reduce_to_form()?.into_inner_arc();
                    let form_1 = ty_1.clone().try_reduce_to_form()?.into_inner_arc();

                    match (form_0, form_1) {
                        | (FormKind::Name, FormKind::Name)
                        | (FormKind::Universe, FormKind::Universe)
                        | (FormKind::Nat, FormKind::Nat)
                        | (FormKind::Never, FormKind::Never)
                        | (FormKind::Unit, FormKind::Unit)
                        => {
                            unreachable!()
                        },

                        (
                            FormKind::Sum {
                                lhs_name: lhs_name_0,
                                lhs_ty: lhs_ty_0,
                                rhs_ty: rhs_ty_0,
                            },
                            FormKind::Sum {
                                lhs_name: lhs_name_1,
                                lhs_ty: lhs_ty_1,
                                rhs_ty: rhs_ty_1,
                            },
                        ) => {
                            let lhs_name = Unify::unify(lhs_name_0, lhs_name_1)?;

                            let ctx_len = max_all([
                                lhs_ty_0.ctx_len(),
                                rhs_ty_0.ctx_len(),
                                lhs_ty_1.ctx_len(),
                                rhs_ty_1.ctx_len(),
                            ]);

                            tm_0
                            .clone()
                            .case(
                                lhs_name,
                                Scope::constant(ty_1.clone()),
                                Scope::make(ctx_len, |lhs_tm| {
                                    Tm::cast(lhs_ty_0, lhs_ty_1, lhs_tm)
                                    .inj_lhs()
                                }),
                                Scope::make(ctx_len, |rhs_tm| {
                                    Tm::cast(rhs_ty_0, rhs_ty_1, rhs_tm)
                                    .inj_rhs()
                                }),
                            )
                        },

                        (
                            FormKind::Sigma {
                                head_name: head_name_0,
                                head_ty: head_ty_0,
                                tail_ty: tail_ty_0,
                            },
                            FormKind::Sigma {
                                head_name: head_name_1,
                                head_ty: head_ty_1,
                                tail_ty: tail_ty_1,
                            },
                        ) => {
                            let _head_name = Unify::unify(head_name_0, head_name_1)?;

                            let head_tm_0 = tm_0.clone().proj_head();
                            let tail_tm_0 = tm_0.clone().proj_tail();

                            let head_tm_1 = {
                                Tm::cast(head_ty_0.clone(), head_ty_1.clone(), head_tm_0.clone())
                            };
                            let tail_tm_1 = {
                                Tm::cast(
                                    tail_ty_0.bind(head_tm_0),
                                    tail_ty_1.bind(head_tm_1.clone()),
                                    tail_tm_0,
                                )
                            };

                            head_tm_1.pair(tail_tm_1)
                        },

                        (
                            FormKind::Pi {
                                arg_name: arg_name_0,
                                arg_ty: arg_ty_0,
                                res_ty: res_ty_0,
                            },
                            FormKind::Pi {
                                arg_name: arg_name_1,
                                arg_ty: arg_ty_1,
                                res_ty: res_ty_1,
                            },
                        ) => {
                            let _arg_name = Unify::unify(arg_name_0, arg_name_1)?;

                            let ctx_len = max_all([
                                arg_ty_0.ctx_len(),
                                arg_ty_1.ctx_len(),
                                res_ty_0.ctx_len(),
                                res_ty_1.ctx_len(),
                                tm_0.ctx_len(),
                            ]);

                            Tm::func(Scope::make(ctx_len, |arg_tm_1| {
                                let arg_tm_0 = {
                                    Tm::cast(arg_ty_1, arg_ty_0, arg_tm_1.clone())
                                };
                                let res_tm_0 = tm_0.clone().app(arg_tm_0.clone());

                                Tm::cast(
                                    res_ty_0.bind(arg_tm_0),
                                    res_ty_1.bind(arg_tm_1),
                                    res_tm_0,
                                )
                            }))
                        },

                        _ => return None,
                    }
                }
            },
        };
        Some(tm.reduced())
    }

    pub fn reduced(self) -> ValTm {
        match self.try_reduce() {
            None => {
                Weaken::new_arc(self)
                .map(|kind| TmKind::Stuck {
                    stuck: StuckKind { kind },
                })
            },
            Some(tm) => tm,
        }
    }

    pub fn as_var(&self) -> Option<usize> {
        let NeutralKind::Var { index } = self else {
            return None;
        };
        Some(*index)
    }

    pub fn as_equal(self) -> Option<(Ty, Tm, Tm)> {
        let NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 } = self else {
            return None;
        };
        Some((eq_ty, eq_tm_0, eq_tm_1))
    }

    pub fn try_infer_ty(
        &self,
        ctx: &mut Vec<Ty>,
    ) -> Option<Ty> {
        let ty = match self {
            NeutralKind::Var { index } => ctx[*index].clone(),

            NeutralKind::Bind { .. } => return None,

            NeutralKind::Fold { elim, motive, .. } => {
                motive.clone().bind(elim.clone())
            },
            NeutralKind::Add { .. } => Ty::nat(),

            NeutralKind::Explode { motive } => {
                Weaken::new(motive.clone())
                .lift_scope()
                .bind(Tm::proof())
            },

            NeutralKind::Case { elim, motive, .. } => {
                motive.clone().bind(elim.clone())
            },

            NeutralKind::ProjHead { elim } => {
                let elim_ty = elim.clone().reduced().as_stuck()?.infer_ty(ctx);
                let (_head_name, head_ty, _tail_ty) = elim_ty.as_sigma().unwrap();
                head_ty
            },

            NeutralKind::ProjTail { elim } => {
                let elim_ty = elim.clone().reduced().as_stuck()?.infer_ty(ctx);
                let (_head_name, _head_ty, tail_ty) = elim_ty.as_sigma().unwrap();
                tail_ty.bind(Weaken::new(elim.clone()).proj_head())
            },

            NeutralKind::App { elim, arg_tm } => {
                let elim_ty = elim.clone().as_stuck()?.infer_ty(ctx);
                let (_arg_name, _arg_ty, res_ty) = elim_ty.as_pi().unwrap();
                res_ty.bind(arg_tm.clone())
            },

            NeutralKind::ObsEqual { .. } => {
                Ty::universe()
            },

            NeutralKind::Cast { ty_1, .. } => {
                ty_1.clone()
            },
        };
        Some(ty)
    }
}

impl Substitutable for NeutralKind {
    type Output = ValTm;

    fn subst(self, subst: &mut Subst) -> ValTm {
        let neutral_kind = match self {
            NeutralKind::Var { index } => {
                return subst.get_var_tm(index).reduced();
            },

            NeutralKind::Bind { var_tms, mut truncated_body_usages, body } => {
                let subst_index = subst.subst_index() + subst.len();
                debug_assert!(subst_index >= truncated_body_usages.ctx_len());

                truncated_body_usages.set_run_to_one(subst_index, var_tms.len());
                let pre_subst = Subst::from_var_tms(subst_index, var_tms);
                let body = Weaken::from_usages_and_weak(truncated_body_usages, body);
                return subst.with_composed(pre_subst, |subst| body.subst(subst));
            },

            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                let elim = elim.subst(subst).into_tm();
                let motive = motive.capture_subst(subst.clone());
                let zero_inhab = zero_inhab.capture_subst(subst.clone());
                let succ_inhab = succ_inhab.capture_subst(subst.clone());
                NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab }
            },

            NeutralKind::Add { tms } => {
                let tms = {
                    tms
                    .into_iter()
                    .map(|tm| tm.subst(&mut subst.clone()).into_tm())
                    .collect()
                };
                NeutralKind::Add { tms }
            },

            NeutralKind::Explode { motive } => {
                let motive = {
                    Weaken::new(motive)
                    .lift_scope()
                    .capture_subst(subst.clone())
                    .lift_weaken()
                    .into_inner()
                };
                NeutralKind::Explode { motive }
            },

            NeutralKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab } => {
                let lhs_name = lhs_name.capture_subst(subst.clone());
                let elim = elim.subst(subst).into_tm();
                let motive = motive.capture_subst(subst.clone());
                let lhs_inhab = lhs_inhab.capture_subst(subst.clone());
                let rhs_inhab = rhs_inhab.capture_subst(subst.clone());
                NeutralKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab }
            },

            NeutralKind::ProjHead { elim } => {
                let elim = elim.subst(subst).into_tm().into_inner();
                NeutralKind::ProjHead { elim }
            },

            NeutralKind::ProjTail { elim } => {
                let elim = elim.subst(subst).into_tm().into_inner();
                NeutralKind::ProjTail { elim }
            },

            NeutralKind::App { elim, arg_tm } => {
                let elim = elim.subst(subst).into_tm();
                let arg_tm = arg_tm.capture_subst(subst.clone());
                NeutralKind::App { elim, arg_tm }
            },

            NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 } => {
                let eq_ty = eq_ty.subst(subst).into_ty();
                let eq_tm_0 = eq_tm_0.subst(subst).into_tm();
                let eq_tm_1 = eq_tm_1.subst(subst).into_tm();
                NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 }
            },

            NeutralKind::Cast { ty_0, ty_1, tm_0 } => {
                let ty_0 = ty_0.subst(subst).into_ty();
                let ty_1 = ty_1.subst(subst).into_ty();
                let tm_0 = tm_0.capture_subst(subst.clone());
                NeutralKind::Cast { ty_0, ty_1, tm_0 }
            },
        };
        neutral_kind.reduced()
    }

    fn into_output(self) -> ValTm {
        self.reduced()
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<NeutralKind> {
        match self {
            NeutralKind::Var { index } => {
                match index.cmp(&var_index) {
                    cmp::Ordering::Less => Some(NeutralKind::Var { index }),
                    cmp::Ordering::Equal => None,
                    cmp::Ordering::Greater => Some(NeutralKind::Var { index: index - 1 }),
                }
            },

            NeutralKind::Bind { var_tms, truncated_body_usages, body } => {
                let (truncated_body_usages, bit) = truncated_body_usages.shift_remove(var_index);
                if bit {
                    return None;
                }

                let var_tms = {
                    var_tms
                    .into_iter()
                    .map(|var_tm| var_tm.try_strengthen_index(var_index))
                    .collect::<Option<Vec<Tm>>>()?
                };
                Some(NeutralKind::Bind { var_tms, truncated_body_usages, body })
            },

            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                let elim = elim.try_strengthen_index(var_index)?;
                let motive = motive.try_strengthen_index(var_index)?;
                let zero_inhab = zero_inhab.try_strengthen_index(var_index)?;
                let succ_inhab = succ_inhab.try_strengthen_index(var_index)?;
                Some(NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab })
            },

            NeutralKind::Add { tms } => {
                let tms = {
                    tms
                    .into_iter()
                    .map(|tm| tm.try_strengthen_index(var_index))
                    .collect::<Option<Vec<_>>>()?
                };
                Some(NeutralKind::Add { tms })
            },

            NeutralKind::Explode { motive } => {
                let motive = {
                    motive
                    .map_without_capture(Weaken::new)
                    .try_strengthen_index(var_index)?
                    .map_without_capture(Weaken::into_inner)
                };
                Some(NeutralKind::Explode { motive })
            },

            NeutralKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab } => {
                let lhs_name = lhs_name.try_strengthen_index(var_index)?;
                let elim = elim.try_strengthen_index(var_index)?;
                let motive = motive.try_strengthen_index(var_index)?;
                let lhs_inhab = lhs_inhab.try_strengthen_index(var_index)?;
                let rhs_inhab = rhs_inhab.try_strengthen_index(var_index)?;
                Some(NeutralKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab })
            },

            NeutralKind::ProjHead { elim } => {
                let elim = elim.try_strengthen_index(var_index)?;
                Some(NeutralKind::ProjHead { elim })
            },

            NeutralKind::ProjTail { elim } => {
                let elim = elim.try_strengthen_index(var_index)?;
                Some(NeutralKind::ProjTail { elim })
            },

            NeutralKind::App { elim, arg_tm } => {
                let elim = elim.try_strengthen_index(var_index)?;
                let arg_tm = arg_tm.try_strengthen_index(var_index)?;
                Some(NeutralKind::App { elim, arg_tm })
            },

            NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 } => {
                let eq_ty = eq_ty.try_strengthen_index(var_index)?;
                let eq_tm_0 = eq_tm_0.try_strengthen_index(var_index)?;
                let eq_tm_1 = eq_tm_1.try_strengthen_index(var_index)?;
                Some(NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 })
            },

            NeutralKind::Cast { ty_0, ty_1, tm_0 } => {
                let ty_0 = ty_0.try_strengthen_index(var_index)?;
                let ty_1 = ty_1.try_strengthen_index(var_index)?;
                let tm_0 = tm_0.try_strengthen_index(var_index)?;
                Some(NeutralKind::Cast { ty_0, ty_1, tm_0 })
            },
        }
    }
}

impl DeepNf for NeutralKind {
    type Output = ValTm;

    fn deep_nf(self) -> ValTm {
        self.reduced().deep_nf()
    }
}

impl TryUnswapVars for NeutralKind {
    fn try_unswap_vars(
        self,
        var_index: usize,
    ) -> Option<NeutralKind> {
        let neutral_kind = match self {
            NeutralKind::Var { index } => {
                if index == var_index {
                    return None;
                }
                if index == var_index + 1 {
                    NeutralKind::Var { index: var_index }
                } else {
                    NeutralKind::Var { index }
                }
            },

            NeutralKind::App { elim, arg_tm } => {
                if let Some(elim) = elim.clone().as_stuck()
                && let Some(_) = Unify::unify(elim, Stuck::var(var_index))
                && let Some(arg_tm) = arg_tm.clone().as_stuck()
                && let Some(_) = Unify::unify(arg_tm.clone(), Stuck::var(var_index + 1))
                {
                    return Some(NeutralKind::Var { index: var_index + 1});
                }

                let elim = elim.try_unswap_vars(var_index)?;
                let arg_tm = arg_tm.try_unswap_vars(var_index)?;
                NeutralKind::App { elim, arg_tm }
            },

            NeutralKind::Bind { .. } => unreachable!(),

            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                let elim = elim.try_unswap_vars(var_index)?;
                let motive = motive.try_unswap_vars(var_index)?;
                let zero_inhab = zero_inhab.try_unswap_vars(var_index)?;
                let succ_inhab = succ_inhab.try_unswap_vars(var_index)?;
                NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab }
            },

            NeutralKind::Add { tms } => {
                let tms = {
                    tms
                    .into_iter()
                    .map(|tm| tm.try_unswap_vars(var_index))
                    .collect::<Option<Vec<_>>>()?
                };
                NeutralKind::Add { tms }
            },

            NeutralKind::Explode { motive } => {
                let motive = motive.try_unswap_vars(var_index)?;
                NeutralKind::Explode { motive }
            },

            NeutralKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab } => {
                let lhs_name = lhs_name.try_unswap_vars(var_index)?;
                let elim = elim.try_unswap_vars(var_index)?;
                let motive = motive.try_unswap_vars(var_index)?;
                let lhs_inhab = lhs_inhab.try_unswap_vars(var_index)?;
                let rhs_inhab = rhs_inhab.try_unswap_vars(var_index)?;
                NeutralKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab }
            },

            NeutralKind::ProjHead { elim } => {
                let elim = elim.try_unswap_vars(var_index)?;
                NeutralKind::ProjHead { elim }
            },

            NeutralKind::ProjTail { elim } => {
                let elim = elim.try_unswap_vars(var_index)?;
                NeutralKind::ProjTail { elim }
            },

            NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 } => {
                let eq_ty = eq_ty.try_unswap_vars(var_index)?;
                let eq_tm_0 = eq_tm_0.try_unswap_vars(var_index)?;
                let eq_tm_1 = eq_tm_1.try_unswap_vars(var_index)?;
                NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 }
            },

            NeutralKind::Cast { ty_0, ty_1, tm_0 } => {
                let ty_0 = ty_0.try_unswap_vars(var_index)?;
                let ty_1 = ty_1.try_unswap_vars(var_index)?;
                let tm_0 = tm_0.try_unswap_vars(var_index)?;
                NeutralKind::Cast { ty_0, ty_1, tm_0 }
            },
        };
        Some(neutral_kind)
    }
}

