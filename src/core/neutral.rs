use crate::priv_prelude::*;

pub type Neutral = Weaken<Arc<NeutralData>>;

#[derive(Clone, Debug)]
pub struct NeutralData {
    pub reduced_filter: Usages,
    pub reduced_opt: Arc<OnceLock<Option<Tm>>>,
    pub kind: NeutralKind,
}

#[derive(Clone, Debug)]
pub enum NeutralKind {
    Var {
        index: usize,
    },
    Bind {
        var_tms: Vec<Tm>,
        truncated_body_usages: Usages,
        body: TmKind,
    },

    Fold {
        elim: Tm,
        motive: Scope<Ty>,
        zero_inhab: Tm,
        succ_inhab: Scope<Scope<Tm>>,
    },

    Explode {
        motive: Scope<TyKind>,
    },
    Case {
        elim: Tm,
        motive: Scope<Ty>,
        lhs_inhab: Scope<Tm>,
        rhs_inhab: Scope<Tm>,
    },
    ProjHead {
        elim: TmKind,
    },
    ProjTail {
        elim: TmKind,
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

impl Contextual for NeutralData {
    fn ctx_len(&self) -> usize {
        self.kind.ctx_len()
    }

    fn collect_usages(&self, usages: &mut Usages) {
        usages.or_assign(&self.reduced_filter);
    }

    fn filter_usages(&mut self, usages: &Usages) {
        self.reduced_filter.filter(usages);
        self.kind.filter_usages(usages);
    }

    fn unfilter_usages(&mut self, usages: &Usages) {
        self.reduced_filter.unfilter(usages);
        self.kind.unfilter_usages(usages);
    }
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

            NeutralKind::Explode { motive } => {
                max_all([
                    motive.ctx_len(),
                ])
            },
            NeutralKind::Case { elim, motive, lhs_inhab, rhs_inhab } => {
                max_all([
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

            NeutralKind::Explode { motive } => {
                motive.collect_usages(usages);
            },
            NeutralKind::Case { elim, motive, lhs_inhab, rhs_inhab } => {
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

            NeutralKind::Explode { motive } => {
                motive.filter_usages(usages);
            },
            NeutralKind::Case { elim, motive, lhs_inhab, rhs_inhab } => {
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

            NeutralKind::Explode { motive } => {
                motive.unfilter_usages(usages);
            },
            NeutralKind::Case { elim, motive, lhs_inhab, rhs_inhab } => {
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

impl NeutralData {
    pub fn new(kind: NeutralKind) -> NeutralData {
        let mut reduced_filter = Usages::empty();
        kind.collect_usages(&mut reduced_filter);
        NeutralData {
            reduced_filter,
            reduced_opt: Arc::new(OnceLock::new()),
            kind,
        }
    }

    pub fn new_arc(kind: NeutralKind) -> Arc<NeutralData> {
        Arc::new(NeutralData::new(kind))
    }

    pub fn unify_without_cached_reduction(
        ctx_tys: &mut Vec<Ty>,
        neutral_0: Arc<NeutralData>,
        neutral_1: Arc<NeutralData>,
    ) -> Option<Arc<NeutralData>> {
        if Arc::ptr_eq(&neutral_0, &neutral_1) {
            return Some(neutral_0);
        }
        let neutral_0 = Arc::unwrap_or_clone(neutral_0);
        let neutral_1 = Arc::unwrap_or_clone(neutral_1);
        let kind = Unify::unify(ctx_tys, (), neutral_0.kind, neutral_1.kind)?;
        Some(NeutralData::new_arc(kind))
    }

    pub fn get_cached_reduction(&self) -> Option<Tm> {
        self
        .reduced_opt
        .get()
        .map(|tm_opt| tm_opt.as_ref())
        .flatten()
        .map(|tm| tm.clone().unfiltered(&self.reduced_filter))
    }

    pub fn try_reduce(&self) -> Option<Tm> {
        self
        .reduced_opt
        .get_or_init(|| {
            self
            .kind
            .try_reduce()
            .map(|tm| {
                tm.filtered(&self.reduced_filter)
            })
        })
        .as_ref()
        .map(|tm| tm.clone().unfiltered(&self.reduced_filter))
    }

    pub fn try_reduce_to_intro_assuming_relevant(&self) -> Option<Intro> {
        let tm = self.try_reduce()?;
        tm.try_map(|tm_kind| {
            match tm_kind {
                TmKind::Intro { intro } => Some(intro),
                TmKind::Neutral { .. } => None,
                TmKind::Proof => unreachable!(),
            }
        })
    }

    pub fn try_infer_ty(
        &self,
        ctx_tys: &mut Vec<Ty>,
    ) -> Option<Ty> {
        self.kind.try_infer_ty(ctx_tys)
    }

    pub fn collect_stuck_vars(&self, usages: &mut Usages) {
        match self.get_cached_reduction() {
            Some(tm) => {
                tm.as_neutral().unwrap().into_inner().collect_stuck_vars(usages);
            },
            None => {
                self.kind.collect_stuck_vars(usages)
            },
        }
    }

    pub fn is_prop(&self) -> bool {
        match self.try_reduce() {
            Some(tm) => tm.into_ty().is_prop(),
            None => self.kind.is_prop(),
        }
    }

    pub fn deep_nf(self) -> Tm {
        match self.try_reduce() {
            Some(tm) => tm.deep_nf(),
            None => {
                let kind = self.kind.deep_nf_assuming_stuck();
                kind.map(|kind| {
                    TmKind::Neutral { neutral: NeutralData::new_arc(kind) }
                })
            },
        }
    }

    pub fn deep_nf_assuming_stuck(self) -> Neutral {
        match self.get_cached_reduction() {
            Some(tm) => {
                tm.as_neutral().unwrap().deep_nf_assuming_stuck()
            },
            None => {
                self.kind.deep_nf_assuming_stuck().map(|kind| NeutralData::new_arc(kind))
            },
        }
    }

    pub fn as_var(&self) -> Option<usize> {
        match self.try_reduce() {
            Some(tm) => tm.as_var(),
            None => self.kind.as_var(),
        }
    }
}

impl NeutralKind {
    pub fn try_reduce(&self) -> Option<Tm> {
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
                body
            },

            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                let elim = elim.clone().try_reduce_to_intro_assuming_relevant()?;
                let (elim_usages, elim) = elim.into_usages_and_weak();
                match &*elim {
                    IntroKind::Constant { ubig } => {
                        let mut val = Ubig::ZERO;
                        let mut state = zero_inhab.clone();
                        while val < *ubig {
                            let elim = TmKind::Intro {
                                intro: Arc::new(IntroKind::Constant {
                                    ubig: val.clone(),
                                }),
                            };
                            let elim = Weaken::from_usages_and_weak(Usages::empty(), elim);
                            state = succ_inhab.clone().bind(elim).bind(state);
                            val.increment();
                        }
                        state
                    },
                    IntroKind::Succs { succ_count_m1, pred_tm } => {
                        let elim = Weaken::from_usages_and_weak(
                            elim_usages.clone(),
                            TmKind::Neutral {
                                neutral: pred_tm.clone(),
                            },
                        );
                        let state = Weaken::from_usages_and_weak(
                            Usages::ones(self.ctx_len()),
                            TmKind::Neutral {
                                neutral: NeutralData::new_arc(NeutralKind::Fold {
                                    elim: elim.clone(),
                                    motive: motive.clone(),
                                    zero_inhab: zero_inhab.clone(),
                                    succ_inhab: succ_inhab.clone(),
                                }),
                            },
                        );
                        let mut state = succ_inhab.clone().bind(elim.clone()).bind(state);
                        let mut val = Ubig::ZERO;
                        while val < *succ_count_m1 {
                            let elim = Weaken::from_usages_and_weak(
                                elim_usages.clone(),
                                TmKind::Intro {
                                    intro: Arc::new(IntroKind::Succs {
                                        succ_count_m1: val.clone(),
                                        pred_tm: pred_tm.clone(),
                                    }),
                                },
                            );
                            state = succ_inhab.clone().bind(elim).bind(state);
                            val.increment();
                        }
                        state
                    },
                    _ => unreachable!(),
                }
            },

            NeutralKind::Explode { .. } => return None,

            NeutralKind::Case { elim, motive: _, lhs_inhab, rhs_inhab } => {
                let (usages, elim) = {
                    elim
                    .clone()
                    .try_reduce_to_intro_assuming_relevant()?
                    .into_usages_and_weak()
                };
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
            },

            NeutralKind::ProjHead { elim } => {
                match elim {
                    TmKind::Intro { intro } => {
                        let IntroKind::Pair { head_tm, tail_tm: _ } = &**intro else {
                            unreachable!();
                        };
                        head_tm.clone()
                    },
                    TmKind::Neutral { neutral } => {
                        let (usages, elim) = neutral.try_reduce()?.into_usages_and_weak();
                        match elim {
                            TmKind::Intro { intro } => {
                                let IntroKind::Pair { head_tm, tail_tm: _ } = &*intro else {
                                    unreachable!();
                                };
                                head_tm.clone().unfiltered(&usages)
                            },
                            TmKind::Neutral { .. } => return None,
                            TmKind::Proof => {
                                Tm::proof()
                            },
                        }
                    },
                    TmKind::Proof => Tm::proof(),
                }
            },
            NeutralKind::ProjTail { elim } => {
                match elim {
                    TmKind::Intro { intro } => {
                        let IntroKind::Pair { head_tm: _, tail_tm } = &**intro else {
                            return None;
                        };
                        tail_tm.clone()
                    },
                    TmKind::Neutral { neutral } => {
                        let (usages, elim) = neutral.try_reduce()?.into_usages_and_weak();
                        match elim {
                            TmKind::Intro { intro } => {
                                let IntroKind::Pair { head_tm: _, tail_tm } = &*intro else {
                                    unreachable!();
                                };
                                tail_tm.clone().unfiltered(&usages)
                            },
                            TmKind::Neutral { .. } => return None,
                            TmKind::Proof => {
                                Tm::proof()
                            },
                        }
                    },
                    TmKind::Proof => Tm::proof(),
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
                    TmKind::Neutral { .. } => return None,
                    TmKind::Proof => Tm::proof(),
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
                                        Weaken::new(TmKind::Neutral {
                                            neutral: pred_tm,
                                        }),
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
                                        Weaken::new(TmKind::Neutral {
                                            neutral: pred_tm,
                                        }),
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
                                        let tm_0 = Weaken::new(TmKind::Neutral {
                                            neutral: pred_tm_0,
                                        });
                                        let tm_1 = {
                                            Weaken::new_arc(IntroKind::Succs {
                                                succ_count_m1: {
                                                    succ_count_m1_1
                                                    .strict_sub(&(succ_count_m1_0 + 1usize))
                                                },
                                                pred_tm: pred_tm_1,
                                            })
                                            .map(|intro| TmKind::Intro { intro })
                                        };
                                        (tm_0, tm_1)
                                    },
                                    cmp::Ordering::Equal => {
                                        let tm_0 = Weaken::new(TmKind::Neutral {
                                            neutral: pred_tm_0,
                                        });
                                        let tm_1 = Weaken::new(TmKind::Neutral {
                                            neutral: pred_tm_1,
                                        });
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
                                            .map(|intro| TmKind::Intro { intro })
                                        };
                                        let tm_1 = Weaken::new(TmKind::Neutral {
                                            neutral: pred_tm_1,
                                        });
                                        (tm_0, tm_1)
                                    },
                                };
                                Ty::obs_equal(Ty::nat(), tm_0, tm_1)
                            },

                            _ => unreachable!(),
                        }
                    },

                    FormKind::Never => return None,

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
                let form_0 = ty_0.clone().try_reduce_to_form()?.into_inner_arc();
                let form_1 = ty_1.clone().try_reduce_to_form()?.into_inner_arc();

                match (form_0, form_1) {
                    | (FormKind::Name, FormKind::Name)
                    | (FormKind::Universe, FormKind::Universe)
                    | (FormKind::Nat, FormKind::Nat)
                    | (FormKind::Never, FormKind::Never)
                    | (FormKind::Unit, FormKind::Unit)
                    => {
                        tm_0.clone()
                    },

                    (
                        FormKind::Sum {
                            lhs_name: _,
                            lhs_ty: lhs_ty_0,
                            rhs_ty: rhs_ty_0,
                        },
                        FormKind::Sum {
                            lhs_name: _,
                            lhs_ty: lhs_ty_1,
                            rhs_ty: rhs_ty_1,
                        },
                    ) => {
                        let ctx_len = max_all([
                            lhs_ty_0.ctx_len(),
                            rhs_ty_0.ctx_len(),
                            lhs_ty_1.ctx_len(),
                            rhs_ty_1.ctx_len(),
                        ]);

                        tm_0
                        .clone()
                        .case(
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
                            head_name: _,
                            head_ty: head_ty_0,
                            tail_ty: tail_ty_0,
                        },
                        FormKind::Sigma {
                            head_name: _,
                            head_ty: head_ty_1,
                            tail_ty: tail_ty_1,
                        },
                    ) => {
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
                            arg_name: _,
                            arg_ty: arg_ty_0,
                            res_ty: res_ty_0,
                        },
                        FormKind::Pi {
                            arg_name: _,
                            arg_ty: arg_ty_1,
                            res_ty: res_ty_1,
                        },
                    ) => {
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
            },
        };
        Some(tm.reduced())
    }

    pub fn reduced(self) -> Tm {
        match self.try_reduce() {
            None => {
                Weaken::new_arc(NeutralData::new(self))
                .map(|neutral| TmKind::Neutral { neutral })
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

    pub fn try_infer_ty(
        &self,
        ctx_tys: &mut Vec<Ty>,
    ) -> Option<Ty> {
        match self {
            NeutralKind::Var { index } => Some(ctx_tys[*index].clone()),

            NeutralKind::Bind { .. } => None,

            NeutralKind::Fold { elim, motive, zero_inhab: _, succ_inhab: _ } => {
                Some(motive.clone().bind(elim.clone()))
            },

            NeutralKind::Explode { motive } => {
                Some(Weaken::new(motive.clone()).lift_scope().bind(Tm::proof()))
            },

            NeutralKind::Case { elim, motive, lhs_inhab: _, rhs_inhab: _ } => {
                Some(motive.clone().bind(elim.clone()))
            },

            NeutralKind::ProjHead { elim } => {
                let neutral = elim.clone().as_neutral()?;
                let elim_ty = neutral.try_infer_ty(ctx_tys)?;
                let (_head_name, head_ty, _tail_ty) = elim_ty.as_sigma().unwrap();
                Some(head_ty)
            },

            NeutralKind::ProjTail { elim } => {
                let neutral = elim.clone().as_neutral()?;
                let elim_ty = neutral.try_infer_ty(ctx_tys)?;
                let (_head_name, _head_ty, tail_ty) = elim_ty.as_sigma().unwrap();
                Some(tail_ty.bind(Weaken::new(elim.clone()).proj_head()))
            },

            NeutralKind::App { elim, arg_tm } => {
                let neutral = elim.clone().as_neutral()?;
                let elim_ty = neutral.try_infer_ty(ctx_tys)?;
                let (_arg_name, _arg_ty, res_ty) = elim_ty.as_pi().unwrap();
                Some(res_ty.bind(arg_tm.clone()))
            },

            NeutralKind::ObsEqual { .. } => {
                Some(Ty::universe())
            },

            NeutralKind::Cast { ty_0: _, ty_1, tm_0: _ } => {
                Some(ty_1.clone())
            },
        }
    }

    pub fn collect_stuck_vars(&self, usages: &mut Usages) {
        match self {
            NeutralKind::Explode { .. } => (),

            NeutralKind::Var { index } => {
                usages.set_to_one(*index);
            },

            NeutralKind::Bind { .. } => unreachable!(),

            | NeutralKind::ProjHead { elim }
            | NeutralKind::ProjTail { elim }
            => {
                elim.clone().as_neutral().unwrap().collect_stuck_vars(usages)
            },

            | NeutralKind::Fold { elim, .. }
            | NeutralKind::Case { elim, .. }
            | NeutralKind::App { elim, .. }
            => {
                elim.clone().as_neutral().unwrap().collect_stuck_vars(usages)
            },

            NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 } => {
                match eq_ty.clone().into_inner() {
                    TyKind::Neutral { neutral } => {
                        neutral.collect_stuck_vars(usages);
                    },
                    TyKind::Form { .. } => {
                        if let Some(neutral) = eq_tm_0.clone().as_neutral() {
                            neutral.collect_stuck_vars(usages);
                        }
                        if let Some(neutral) = eq_tm_1.clone().as_neutral() {
                            neutral.collect_stuck_vars(usages);
                        }
                    },
                }
            },

            NeutralKind::Cast { ty_0, ty_1, tm_0: _ } => {
                match (ty_0.clone().into_inner(), ty_1.clone().into_inner()) {
                    (
                        TyKind::Neutral { neutral: neutral_0 },
                        TyKind::Neutral { neutral: neutral_1 },
                    ) => {
                        neutral_0.collect_stuck_vars(usages);
                        neutral_1.collect_stuck_vars(usages);
                    },

                    (
                        TyKind::Neutral { neutral: neutral_0 },
                        TyKind::Form { .. },
                    ) => {
                        neutral_0.collect_stuck_vars(usages);
                    },

                    (
                        TyKind::Form { .. },
                        TyKind::Neutral { neutral: neutral_1 },
                    ) => {
                        neutral_1.collect_stuck_vars(usages);
                    },

                    (
                        TyKind::Form { .. },
                        TyKind::Form { .. },
                    ) => {
                        unreachable!()
                    },
                }
            },
        }
    }

    pub fn is_prop(&self) -> bool {
        match self {
            NeutralKind::Var { .. } => false,
            NeutralKind::Bind { .. } => unreachable!(),

            NeutralKind::Fold { elim: _, motive: _, zero_inhab, succ_inhab } => {
                zero_inhab.clone().into_ty().is_prop() &&
                succ_inhab.inner_ref().inner_ref().clone().into_ty().is_prop()
            },

            NeutralKind::Explode { motive: _ } => true,

            NeutralKind::Case { elim: _, motive: _, lhs_inhab, rhs_inhab } => {
                lhs_inhab.inner_ref().clone().into_ty().is_prop() &&
                rhs_inhab.inner_ref().clone().into_ty().is_prop()
            },

            NeutralKind::ProjHead { .. } => false,
            NeutralKind::ProjTail { .. } => false,
            NeutralKind::App { .. } => false,

            NeutralKind::ObsEqual { .. } => true,

            NeutralKind::Cast { .. } => false,
        }
    }

    pub fn deep_nf_assuming_stuck(self) -> Weaken<NeutralKind> {
        match self {
            NeutralKind::Var { index } => Weaken::new(NeutralKind::Var { index }),

            NeutralKind::Bind { .. } => unreachable!(),

            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                let elim = elim.as_neutral().unwrap().deep_nf_assuming_stuck().into_tm();
                let motive = motive.deep_nf();
                let zero_inhab = zero_inhab.deep_nf();
                let succ_inhab = succ_inhab.deep_nf();
                Weaken::new(NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab })
            },

            NeutralKind::Explode { motive } => {
                let motive = motive.map_without_capture(|motive| {
                    Weaken::new(motive).deep_nf().into_inner()
                });
                Weaken::new(NeutralKind::Explode { motive })
            },

            NeutralKind::Case { elim, motive, lhs_inhab, rhs_inhab } => {
                let elim = elim.as_neutral().unwrap().deep_nf_assuming_stuck().into_tm();
                let motive = motive.deep_nf();
                let lhs_inhab = lhs_inhab.deep_nf();
                let rhs_inhab = rhs_inhab.deep_nf();
                Weaken::new(NeutralKind::Case { elim, motive, lhs_inhab, rhs_inhab })
            },

            NeutralKind::ProjHead { elim } => {
                elim
                .deep_nf()
                .map(|elim| NeutralKind::ProjHead { elim })
            },

            NeutralKind::ProjTail { elim } => {
                elim
                .deep_nf()
                .map(|elim| NeutralKind::ProjTail { elim })
            },

            NeutralKind::App { elim, arg_tm } => {
                let elim = elim.deep_nf();
                let arg_tm = arg_tm.deep_nf();
                Weaken::new(NeutralKind::App { elim, arg_tm })
            },

            NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 } => {
                let eq_ty = eq_ty.deep_nf();
                let eq_tm_0 = eq_tm_0.deep_nf();
                let eq_tm_1 = eq_tm_1.deep_nf();
                Weaken::new(NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 })
            },

            NeutralKind::Cast { ty_0, ty_1, tm_0 } => {
                let ty_0 = ty_0.deep_nf();
                let ty_1 = ty_1.deep_nf();
                let tm_0 = tm_0.deep_nf();
                Weaken::new(NeutralKind::Cast { ty_0, ty_1, tm_0 })
            },
        }
    }
}

impl Unify for NeutralKind {
    type Meta = ();

    fn unify(
        ctx_tys: &mut Vec<Ty>,
        (): (),
        neutral_kind_0: NeutralKind,
        neutral_kind_1: NeutralKind,
    ) -> Option<NeutralKind> {
        match neutral_kind_0 {
            NeutralKind::Bind { .. } => unreachable!(),
            NeutralKind::Var { index: index_0 } => {
                if ctx_tys[index_0].is_prop() {
                    return Some(NeutralKind::Var { index: index_0 });
                }
                let NeutralKind::Var { index: index_1 } = neutral_kind_1 else {
                    return None;
                };
                let index = as_equal(index_0, &index_1)?;
                Some(NeutralKind::Var { index })
            },

            NeutralKind::Fold {
                elim: elim_0,
                motive: motive_0,
                zero_inhab: zero_inhab_0,
                succ_inhab: succ_inhab_0,
            } => {
                if motive_0.inner_ref().is_prop() {
                    return Some(NeutralKind::Fold {
                        elim: elim_0,
                        motive: motive_0,
                        zero_inhab: zero_inhab_0,
                        succ_inhab: succ_inhab_0,
                    });
                }

                let NeutralKind::Fold {
                    elim: elim_1,
                    motive: motive_1,
                    zero_inhab: zero_inhab_1,
                    succ_inhab: succ_inhab_1,
                } = neutral_kind_1 else {
                    return None;
                };

                let motive = Unify::unify(
                    ctx_tys, (Ty::nat(), Scope::constant(())), motive_0, motive_1,
                )?;

                let neutral_0 = elim_0.as_neutral().unwrap().into_inner();
                let neutral_1 = elim_1.as_neutral().unwrap().into_inner();
                let neutral = NeutralData::unify_without_cached_reduction(
                    ctx_tys, neutral_0, neutral_1,
                )?;

                let zero_inhab = Unify::unify(
                    ctx_tys,
                    motive.clone().bind(Tm::zero()),
                    zero_inhab_0,
                    zero_inhab_1,
                )?;
                let succ_inhab = Unify::unify(
                    ctx_tys,
                    (
                        Ty::nat(),
                        Scope::make(motive.ctx_len(), |elim| {
                            (
                                motive.clone().bind(elim.clone()),
                                Scope::constant(motive.clone().bind(elim.succs(1usize))),
                            )
                        }),
                    ),
                    succ_inhab_0,
                    succ_inhab_1
                )?;
                let elim = Weaken::new(TmKind::Neutral { neutral });
                Some(NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab })
            },

            NeutralKind::Explode { motive: motive_0 } => {
                if motive_0.inner_ref().is_prop() {
                    return Some(NeutralKind::Explode {
                        motive: motive_0,
                    });
                }
                let NeutralKind::Explode {
                    motive: motive_1,
                } = neutral_kind_1 else {
                    return None;
                };

                let motive = Unify::unify(
                    ctx_tys,
                    (Ty::never(), Scope::constant(())),
                    motive_0,
                    motive_1,
                )?;

                Some(NeutralKind::Explode { motive })
            },

            NeutralKind::Case {
                elim: elim_0,
                motive: motive_0,
                lhs_inhab: lhs_inhab_0,
                rhs_inhab: rhs_inhab_0,
            } => {
                if motive_0.inner_ref().is_prop() {
                    return Some(NeutralKind::Case {
                        elim: elim_0,
                        motive: motive_0,
                        lhs_inhab: lhs_inhab_0,
                        rhs_inhab: rhs_inhab_0,
                    });
                }

                let NeutralKind::Case {
                    elim: elim_1,
                    motive: motive_1,
                    lhs_inhab: lhs_inhab_1,
                    rhs_inhab: rhs_inhab_1,
                } = neutral_kind_1 else {
                    return None;
                };

                let neutral_0 = elim_0.as_neutral().unwrap().into_inner();
                let neutral_1 = elim_1.as_neutral().unwrap().into_inner();
                let elim_ty_0 = neutral_0.try_infer_ty(ctx_tys).unwrap();
                let elim_ty_1 = neutral_1.try_infer_ty(ctx_tys).unwrap();
                let elim_ty = Unify::unify(ctx_tys, (), elim_ty_0, elim_ty_1)?;
                let motive = Unify::unify(
                    ctx_tys,
                    (elim_ty.clone(), Scope::constant(())),
                    motive_0,
                    motive_1,
                )?;

                let neutral = NeutralData::unify_without_cached_reduction(
                    ctx_tys, neutral_0, neutral_1,
                )?;

                let (_lhs_name, lhs_ty, rhs_ty) = elim_ty.as_sum().unwrap();
                let lhs_inhab = Unify::unify(
                    ctx_tys,
                    (
                        lhs_ty,
                        Scope::make(motive.ctx_len(), |lhs_tm| motive.clone().bind(lhs_tm.inj_lhs())),
                    ),
                    lhs_inhab_0,
                    lhs_inhab_1,
                )?;
                let rhs_inhab = Unify::unify(
                    ctx_tys,
                    (
                        rhs_ty,
                        Scope::make(motive.ctx_len(), |rhs_tm| motive.clone().bind(rhs_tm.inj_rhs())),
                    ),
                    rhs_inhab_0,
                    rhs_inhab_1,
                )?;
                let elim = Weaken::new(TmKind::Neutral { neutral });
                Some(NeutralKind::Case { elim, motive, lhs_inhab, rhs_inhab })
            },

            NeutralKind::ProjHead { elim: elim_0 } => {
                let neutral_0 = elim_0.as_neutral().unwrap();
                let Some(elim_ty_0) = neutral_0.try_infer_ty(ctx_tys) else {
                    let elim = TmKind::Neutral { neutral: neutral_0 };
                    return Some(NeutralKind::ProjHead { elim });
                };

                let (_head_name, head_ty_0, _tail_ty_0) = elim_ty_0.clone().as_sigma().unwrap();
                if head_ty_0.is_prop() {
                    let elim = TmKind::Neutral { neutral: neutral_0 };
                    return Some(NeutralKind::ProjHead { elim });
                }

                let NeutralKind::ProjHead { elim: elim_1 } = neutral_kind_1 else {
                    return None;
                };

                let neutral_1 = elim_1.as_neutral().unwrap();
                let elim_ty_1 = neutral_1.try_infer_ty(ctx_tys).unwrap();

                let _elim_ty = Unify::unify(ctx_tys, (), elim_ty_0, elim_ty_1)?;
                let neutral = NeutralData::unify_without_cached_reduction(
                    ctx_tys, neutral_0, neutral_1,
                )?;

                let elim = TmKind::Neutral { neutral };
                Some(NeutralKind::ProjHead { elim })
            },

            NeutralKind::ProjTail { elim: elim_0 } => {
                let neutral_0 = elim_0.as_neutral().unwrap();
                let Some(elim_ty_0) = neutral_0.try_infer_ty(ctx_tys) else {
                    let elim = TmKind::Neutral { neutral: neutral_0 };
                    return Some(NeutralKind::ProjTail { elim });
                };

                let (_head_name, _head_ty, tail_ty) = elim_ty_0.clone().as_sigma().unwrap();
                if tail_ty.inner_ref().is_prop() {
                    let elim = TmKind::Neutral { neutral: neutral_0 };
                    return Some(NeutralKind::ProjTail { elim });
                }

                let NeutralKind::ProjTail { elim: elim_1 } = neutral_kind_1 else {
                    return None;
                };

                let neutral_1 = elim_1.as_neutral().unwrap();
                let elim_ty_1 = neutral_1.try_infer_ty(ctx_tys).unwrap();
                let _elim_ty = Unify::unify(ctx_tys, (), elim_ty_0, elim_ty_1)?;
                let neutral = NeutralData::unify_without_cached_reduction(
                    ctx_tys, neutral_0, neutral_1,
                )?;

                let elim = TmKind::Neutral { neutral };
                Some(NeutralKind::ProjTail { elim })
            },

            NeutralKind::App { elim: elim_0, arg_tm: arg_tm_0 } => {
                let neutral_0 = elim_0.as_neutral().unwrap().into_inner();
                let Some(elim_ty_0) = neutral_0.try_infer_ty(ctx_tys) else {
                    return Some(NeutralKind::App {
                        elim: Weaken::new(TmKind::Neutral {
                            neutral: neutral_0,
                        }),
                        arg_tm: arg_tm_0,
                    });
                };
                
                let (_arg_name, arg_ty, res_ty) = elim_ty_0.clone().as_pi().unwrap();
                if res_ty.bind(arg_tm_0.clone()).is_prop() {
                    return Some(NeutralKind::App {
                        elim: Weaken::new(TmKind::Neutral {
                            neutral: neutral_0,
                        }),
                        arg_tm: arg_tm_0,
                    });
                }
                
                let NeutralKind::App { elim: elim_1, arg_tm: arg_tm_1 } = neutral_kind_1 else {
                    return None;
                };

                let neutral_1 = elim_1.as_neutral().unwrap().into_inner();
                let elim_ty_1 = neutral_1.try_infer_ty(ctx_tys).unwrap();
                let _elim_ty = Unify::unify(ctx_tys, (), elim_ty_0, elim_ty_1)?;

                let elim = TmKind::Neutral {
                    neutral: NeutralData::unify_without_cached_reduction(
                        ctx_tys, neutral_0, neutral_1,
                    )?,
                };

                let arg_tm = Unify::unify(ctx_tys, arg_ty, arg_tm_0, arg_tm_1)?;
                let elim = Weaken::new(elim);
                Some(NeutralKind::App { elim, arg_tm })
            },

            NeutralKind::ObsEqual {
                eq_ty: eq_ty_0,
                eq_tm_0: eq_tm_0_0,
                eq_tm_1: eq_tm_1_0,
            } => {
                let NeutralKind::ObsEqual {
                    eq_ty: eq_ty_1,
                    eq_tm_0: eq_tm_0_1,
                    eq_tm_1: eq_tm_1_1,
                } = neutral_kind_1 else {
                    return None;
                };

                let eq_ty = Unify::unify(ctx_tys, (), eq_ty_0, eq_ty_1)?;

                let (eq_tm_0, eq_tm_1) = match Unify::unify(
                    ctx_tys, eq_ty.clone(), eq_tm_0_0.clone(), eq_tm_0_1.clone(),
                ) {
                    Some(eq_tm_0) => {
                        let eq_tm_1 = Unify::unify(
                            ctx_tys, eq_ty.clone(), eq_tm_1_0, eq_tm_1_1,
                        )?;
                        (eq_tm_0, eq_tm_1)
                    },
                    None => {
                        let eq_tm_0 = Unify::unify(
                            ctx_tys, eq_ty.clone(), eq_tm_0_0, eq_tm_1_1,
                        )?;
                        let eq_tm_1 = Unify::unify(
                            ctx_tys, eq_ty.clone(), eq_tm_1_0, eq_tm_0_1,
                        )?;
                        (eq_tm_0, eq_tm_1)
                    },
                };

                Some(NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 })
            },

            NeutralKind::Cast {
                ty_0: ty_0_0,
                ty_1: ty_1_0,
                tm_0: tm_0_0,
            } => {
                let NeutralKind::Cast {
                    ty_0: ty_0_1,
                    ty_1: ty_1_1,
                    tm_0: tm_0_1,
                } = neutral_kind_1 else {
                    return None;
                };

                let ty_0 = Unify::unify(ctx_tys, (), ty_0_0, ty_0_1)?;
                let ty_1 = Unify::unify(ctx_tys, (), ty_1_0, ty_1_1)?;
                let tm_0 = Unify::unify(ctx_tys, ty_0.clone(), tm_0_0, tm_0_1)?;
                Some(NeutralKind::Cast { ty_0, ty_1, tm_0 })
            },
        }
    }
}

impl Neutral {
    pub fn into_tm(self) -> Tm {
        self.map(|neutral| TmKind::Neutral { neutral })
    }

    pub fn into_ty(self) -> Ty {
        self.map(|neutral| TyKind::Neutral { neutral })
    }

    pub fn var(index: usize) -> Neutral {
        lazy_static! {
            static ref VAR_0: Arc<NeutralData> = {
                NeutralData::new_arc(NeutralKind::Var { index: 0 })
            };
        }

        let usages = Usages::single_var(index);
        Weaken::from_usages_and_weak(usages, VAR_0.clone())
    }

    pub fn fold(
        elim: Tm,
        motive: Scope<Ty>,
        zero_inhab: Tm,
        succ_inhab: Scope<Scope<Tm>>,
    ) -> Neutral {
        Weaken::new_arc(NeutralData::new(NeutralKind::Fold {
            elim, motive, zero_inhab, succ_inhab,
        }))
    }

    pub fn explode(
        motive: Scope<Ty>,
    ) -> Neutral {
        motive
        .lift_weaken()
        .map(|motive| Arc::new(NeutralData::new(NeutralKind::Explode { motive })))
    }

    pub fn case(
        elim: Tm,
        motive: Scope<Ty>,
        lhs_inhab: Scope<Tm>,
        rhs_inhab: Scope<Tm>,
    ) -> Neutral {
        Weaken::new_arc(NeutralData::new(NeutralKind::Case {
            elim, motive, lhs_inhab, rhs_inhab,
        }))
    }

    pub fn proj_head(elim: Tm) -> Neutral {
        elim.map(|elim| NeutralData::new_arc(NeutralKind::ProjHead { elim }))
    }

    pub fn proj_tail(elim: Tm) -> Neutral {
        elim.map(|elim| NeutralData::new_arc(NeutralKind::ProjTail { elim }))
    }

    pub fn app(elim: Tm, arg_tm: Tm) -> Neutral {
        Weaken::new_arc(NeutralData::new(NeutralKind::App { elim, arg_tm }))
    }

    pub fn obs_equal(eq_ty: Ty, eq_tm_0: Tm, eq_tm_1: Tm) -> Neutral {
        Weaken::new_arc(NeutralData::new(NeutralKind::ObsEqual {
            eq_ty, eq_tm_0, eq_tm_1,
        }))
    }

    pub fn cast(ty_0: Ty, ty_1: Ty, tm_0: Tm) -> Neutral {
        Weaken::new_arc(NeutralData::new(NeutralKind::Cast {
            ty_0, ty_1, tm_0,
        }))
    }

    pub fn try_infer_ty(
        &self,
        ctx_tys: &mut Vec<Ty>,
    ) -> Option<Ty> {
        self.clone().into_inner().try_infer_ty(ctx_tys)
    }

    pub fn collect_stuck_vars(&self, usages: &mut Usages) {
        self.clone().into_inner().collect_stuck_vars(usages);
    }

    pub fn is_prop(&self) -> bool {
        self.weak().is_prop()
    }

    pub fn deep_nf(self) -> Tm {
        self.map_out_unfiltered(|neutral| {
            Arc::unwrap_or_clone(neutral).deep_nf()
        })
    }

    pub fn deep_nf_assuming_stuck(self) -> Neutral {
        self.map_out_unfiltered(|neutral| {
            Arc::unwrap_or_clone(neutral).deep_nf_assuming_stuck()
        })
    }
}

impl Substitutable for Neutral {
    type Output = Tm;

    fn subst(self, subst: &mut Subst) -> Tm {
        if self.ctx_len() <= subst.subst_index() {
            return self.into_tm();
        }
        self.into_inner().subst(subst)
    }

    fn into_output(self) -> Tm {
        self.into_tm()
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<Tm> {
        Some(self.do_try_strengthen_index(var_index)?.flatten())
    }
}

impl Substitutable for Arc<NeutralData> {
    type Output = Tm;

    fn subst(self, subst: &mut Subst) -> Tm {
        if let Some(tm) = self.get_cached_reduction() {
            return tm.subst(subst);
        }
        let neutral_data = Arc::unwrap_or_clone(self);
        neutral_data.kind.subst(subst)
    }

    fn into_output(self) -> Tm {
        Weaken::new(TmKind::Neutral { neutral: self })
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<Tm> {
        match self.try_reduce() {
            None => {
                self.kind.clone().try_strengthen_index(var_index)
            },
            Some(tm) => {
                tm.try_strengthen_index(var_index)
            },
        }
    }
}

impl Substitutable for NeutralKind {
    type Output = Tm;

    fn subst(self, subst: &mut Subst) -> Tm {
        let neutral_kind = match self {
            NeutralKind::Var { index } => {
                return subst.get_var_tm(index);
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
                let elim = elim.subst(subst);
                let motive = motive.capture_subst(subst.clone());
                let zero_inhab = zero_inhab.capture_subst(subst.clone());
                let succ_inhab = succ_inhab.capture_subst(subst.clone());
                NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab }
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

            NeutralKind::Case { elim, motive, lhs_inhab, rhs_inhab } => {
                let elim = elim.subst(subst);
                let motive = motive.capture_subst(subst.clone());
                let lhs_inhab = lhs_inhab.capture_subst(subst.clone());
                let rhs_inhab = rhs_inhab.capture_subst(subst.clone());
                NeutralKind::Case { elim, motive, lhs_inhab, rhs_inhab }
            },

            NeutralKind::ProjHead { elim } => {
                let elim = elim.subst(subst).into_inner();
                NeutralKind::ProjHead { elim }
            },

            NeutralKind::ProjTail { elim } => {
                let elim = elim.subst(subst).into_inner();
                NeutralKind::ProjTail { elim }
            },

            NeutralKind::App { elim, arg_tm } => {
                let elim = elim.subst(subst);
                let arg_tm = arg_tm.capture_subst(subst.clone());
                NeutralKind::App { elim, arg_tm }
            },

            NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 } => {
                let eq_ty = eq_ty.subst(subst);
                let eq_tm_0 = eq_tm_0.subst(subst);
                let eq_tm_1 = eq_tm_1.subst(subst);
                NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 }
            },

            NeutralKind::Cast { ty_0, ty_1, tm_0 } => {
                let ty_0 = ty_0.subst(subst);
                let ty_1 = ty_1.subst(subst);
                let tm_0 = tm_0.capture_subst(subst.clone());
                NeutralKind::Cast { ty_0, ty_1, tm_0 }
            },
        };
        neutral_kind.reduced()
    }

    fn into_output(self) -> Tm {
        Weaken::new_arc(NeutralData::new(self))
        .map(|neutral| TmKind::Neutral { neutral })
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<Tm> {
        match self {
            NeutralKind::Var { index } => {
                match index.cmp(&var_index) {
                    cmp::Ordering::Less => Some(Tm::var(index)),
                    cmp::Ordering::Equal => None,
                    cmp::Ordering::Greater => Some(Tm::var(index - 1)),
                }
            },

            NeutralKind::Bind { .. } => unreachable!(),

            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                let elim = elim.try_strengthen_index(var_index)?;
                let motive = motive.try_strengthen_index(var_index)?;
                let zero_inhab = zero_inhab.try_strengthen_index(var_index)?;
                let succ_inhab = succ_inhab.try_strengthen_index(var_index)?;
                Some(elim.fold(motive, zero_inhab, succ_inhab))
            },

            NeutralKind::Explode { motive } => {
                let motive = {
                    Weaken::new(motive)
                    .lift_scope()
                    .try_strengthen_index(var_index)?
                };
                Some(Tm::explode(motive))
            },

            NeutralKind::Case { elim, motive, lhs_inhab, rhs_inhab } => {
                let elim = elim.try_strengthen_index(var_index)?;
                let motive = motive.try_strengthen_index(var_index)?;
                let lhs_inhab = lhs_inhab.try_strengthen_index(var_index)?;
                let rhs_inhab = rhs_inhab.try_strengthen_index(var_index)?;
                Some(elim.case(motive, lhs_inhab, rhs_inhab))
            },

            NeutralKind::ProjHead { elim } => {
                let elim = elim.try_strengthen_index(var_index)?;
                Some(elim.proj_head())
            },

            NeutralKind::ProjTail { elim } => {
                let elim = elim.try_strengthen_index(var_index)?;
                Some(elim.proj_tail())
            },

            NeutralKind::App { elim, arg_tm } => {
                let elim = elim.try_strengthen_index(var_index)?;
                let arg_tm = arg_tm.try_strengthen_index(var_index)?;
                Some(elim.app(arg_tm))
            },

            NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 } => {
                let eq_ty = eq_ty.try_strengthen_index(var_index)?;
                let eq_tm_0 = eq_tm_0.try_strengthen_index(var_index)?;
                let eq_tm_1 = eq_tm_1.try_strengthen_index(var_index)?;
                Some(Ty::obs_equal(eq_ty, eq_tm_0, eq_tm_1).into_tm())
            },

            NeutralKind::Cast { ty_0, ty_1, tm_0 } => {
                let ty_0 = ty_0.try_strengthen_index(var_index)?;
                let ty_1 = ty_1.try_strengthen_index(var_index)?;
                let tm_0 = tm_0.try_strengthen_index(var_index)?;
                Some(Neutral::cast(ty_0, ty_1, tm_0).into_tm())
            },
        }
    }
}

