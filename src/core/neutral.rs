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
    TagsApart {
        elim: TmKind,
    },
    Fold {
        elim: Tm,
        motive: Scope<Ty>,
        zero_inhab: Tm,
        succ_inhab: Scope<Scope<Tm>>,
    },
    UniqueIdentity {
        elim: Tm,
        motive: Scope<Ty>,
        inhab: Tm,
    },
    Cong {
        elim: Tm,
        motive: Scope<Scope<Ty>>,
        inhab: Tm,
    },
    Explode {
        elim: Tm,
        motive: Scope<Ty>,
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
            NeutralKind::TagsApart { elim } => {
                elim.ctx_len()
            },
            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                max_all([
                    elim.ctx_len(),
                    motive.ctx_len(),
                    zero_inhab.ctx_len(),
                    succ_inhab.ctx_len(),
                ])
            },
            NeutralKind::UniqueIdentity { elim, motive, inhab } => {
                max_all([
                    elim.ctx_len(),
                    motive.ctx_len(),
                    inhab.ctx_len(),
                ])
            },
            NeutralKind::Cong { elim, motive, inhab } => {
                max_all([
                    elim.ctx_len(),
                    motive.ctx_len(),
                    inhab.ctx_len(),
                ])
            },
            NeutralKind::Explode { elim, motive } => {
                max_all([
                    elim.ctx_len(),
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
            NeutralKind::TagsApart { elim } => {
                elim.collect_usages(usages);
            },
            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                elim.collect_usages(usages);
                motive.collect_usages(usages);
                zero_inhab.collect_usages(usages);
                succ_inhab.collect_usages(usages);
            },
            NeutralKind::UniqueIdentity { elim, motive, inhab } => {
                elim.collect_usages(usages);
                motive.collect_usages(usages);
                inhab.collect_usages(usages);
            },
            NeutralKind::Cong { elim, motive, inhab } => {
                elim.collect_usages(usages);
                motive.collect_usages(usages);
                inhab.collect_usages(usages);
            },
            NeutralKind::Explode { elim, motive } => {
                elim.collect_usages(usages);
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
            NeutralKind::TagsApart { elim } => {
                elim.filter_usages(usages);
            },
            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                elim.filter_usages(usages);
                motive.filter_usages(usages);
                zero_inhab.filter_usages(usages);
                succ_inhab.filter_usages(usages);
            },
            NeutralKind::UniqueIdentity { elim, motive, inhab } => {
                elim.filter_usages(usages);
                motive.filter_usages(usages);
                inhab.filter_usages(usages);
            },
            NeutralKind::Cong { elim, motive, inhab } => {
                elim.filter_usages(usages);
                motive.filter_usages(usages);
                inhab.filter_usages(usages);
            },
            NeutralKind::Explode { elim, motive } => {
                elim.filter_usages(usages);
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
            NeutralKind::TagsApart { elim } => {
                elim.unfilter_usages(usages);
            },
            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                elim.unfilter_usages(usages);
                motive.unfilter_usages(usages);
                zero_inhab.unfilter_usages(usages);
                succ_inhab.unfilter_usages(usages);
            },
            NeutralKind::UniqueIdentity { elim, motive, inhab } => {
                elim.unfilter_usages(usages);
                motive.unfilter_usages(usages);
                inhab.unfilter_usages(usages);
            },
            NeutralKind::Cong { elim, motive, inhab } => {
                elim.unfilter_usages(usages);
                motive.unfilter_usages(usages);
                inhab.unfilter_usages(usages);
            },
            NeutralKind::Explode { elim, motive } => {
                elim.unfilter_usages(usages);
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

    pub fn try_reduce_to_intro(&self) -> Option<Intro> {
        let tm = self.try_reduce()?;
        let Weaken { usages, weak } = tm;
        match weak {
            TmKind::Intro { intro } => {
                Some(Weaken { usages, weak: intro })
            },
            TmKind::Neutral { .. } => None,
        }
    }

    pub fn try_infer_ty(
        &self,
        ctx_tys: &mut Vec<Ty>,
    ) -> Option<Ty> {
        self.kind.try_infer_ty(ctx_tys)
    }

    pub fn collect_stuck_vars(&self, usages: &mut Usages) {
        self.kind.collect_stuck_vars(usages)
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
        debug_assert!(self.try_reduce().is_none());
        self.kind.deep_nf_assuming_stuck().map(|kind| NeutralData::new_arc(kind))
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
                let body = Weaken {
                    usages: truncated_body_usages,
                    weak: body.clone(),
                };
                let mut subst = Subst::from_var_tms(subst_index, var_tms);
                let body = body.subst(&mut subst);
                debug_assert_eq!(subst.len(), subst_len);
                body
            },
            NeutralKind::TagsApart { .. } => return None,

            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                let Weaken {
                    usages: elim_usages, weak: elim,
                } = elim.clone().try_reduce_to_intro()?;
                match &*elim {
                    IntroKind::Constant { ubig } => {
                        let mut val = Ubig::ZERO;
                        let mut state = zero_inhab.clone();
                        while val < *ubig {
                            let elim = Weaken {
                                usages: Usages::empty(),
                                weak: TmKind::Intro {
                                    intro: Arc::new(IntroKind::Constant {
                                        ubig: val.clone(),
                                    }),
                                },
                            };
                            state = succ_inhab.clone().bind(elim).bind(state);
                            val.increment();
                        }
                        state
                    },
                    IntroKind::Succs { succ_count_m1, pred_tm } => {
                        let elim = Weaken {
                            usages: elim_usages.clone(),
                            weak: TmKind::Neutral {
                                neutral: pred_tm.clone(),
                            },
                        };
                        let state = Weaken {
                            usages: Usages::ones(self.ctx_len()),
                            weak: TmKind::Neutral {
                                neutral: NeutralData::new_arc(NeutralKind::Fold {
                                    elim: elim.clone(),
                                    motive: motive.clone(),
                                    zero_inhab: zero_inhab.clone(),
                                    succ_inhab: succ_inhab.clone(),
                                }),
                            },
                        };
                        let mut state = succ_inhab.clone().bind(elim.clone()).bind(state);
                        let mut val = Ubig::ZERO;
                        while val < *succ_count_m1 {
                            let elim = Weaken {
                                usages: elim_usages.clone(),
                                weak: TmKind::Intro {
                                    intro: Arc::new(IntroKind::Succs {
                                        succ_count_m1: val.clone(),
                                        pred_tm: pred_tm.clone(),
                                    }),
                                },
                            };
                            state = succ_inhab.clone().bind(elim).bind(state);
                            val.increment();
                        }
                        state
                    },
                    _ => unreachable!(),
                }
            },

            NeutralKind::UniqueIdentity { elim, motive: _, inhab } => {
                let elim = elim.clone().try_reduce_to_intro()?;
                debug_assert!(matches!(&*elim.into_inner(), IntroKind::Refl { .. }));
                inhab.clone()
            },

            NeutralKind::Cong { elim, motive: _, inhab } => {
                let elim = elim.clone().try_reduce_to_intro()?;
                debug_assert!(matches!(&*elim.into_inner(), IntroKind::Refl { .. }));
                inhab.clone()
            },

            NeutralKind::Explode { .. } => return None,

            NeutralKind::Case { elim, motive: _, lhs_inhab, rhs_inhab } => {
                let Weaken { usages, weak: elim } = elim.clone().try_reduce_to_intro()?;
                match &*elim {
                    IntroKind::InjLhs { lhs_tm } => {
                        lhs_inhab.clone().bind(Weaken { usages, weak: lhs_tm.clone() })
                    },
                    IntroKind::InjRhs { rhs_tm } => {
                        rhs_inhab.clone().bind(Weaken { usages, weak: rhs_tm.clone() })
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
                        let intro = neutral.try_reduce_to_intro()?;
                        let Weaken { usages, weak: intro } = intro;
                        let IntroKind::Pair { head_tm, tail_tm: _ } = &*intro else {
                            unreachable!();
                        };
                        head_tm.clone().unfiltered(&usages)
                    },
                }
            },
            NeutralKind::ProjTail { elim } => {
                match elim {
                    TmKind::Intro { intro } => {
                        let IntroKind::Pair { head_tm: _, tail_tm } = &**intro else {
                            unreachable!();
                        };
                        tail_tm.clone()
                    },
                    TmKind::Neutral { neutral } => {
                        let intro = neutral.try_reduce_to_intro()?;
                        let Weaken { usages, weak: intro } = intro;
                        let IntroKind::Pair { head_tm: _, tail_tm } = &*intro else {
                            unreachable!();
                        };
                        tail_tm.clone().unfiltered(&usages)
                    },
                }
            },

            NeutralKind::App { elim, arg_tm } => {
                let elim = elim.clone().try_reduce_to_intro()?;
                let IntroKind::Func { res_tm } = &*elim.into_inner() else {
                    unreachable!();
                };
                let res_tm = res_tm.clone().map_without_capture(Weaken::new);
                res_tm.bind(arg_tm.clone())
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

            NeutralKind::TagsApart { .. } => Some(Ty::never()),

            NeutralKind::Fold { elim, motive, zero_inhab: _, succ_inhab: _ } => {
                Some(motive.clone().bind(elim.clone()))
            },

            NeutralKind::UniqueIdentity { elim, motive, inhab: _ } => {
                Some(motive.clone().bind(elim.clone()))
            },

            NeutralKind::Cong { elim, motive, inhab: _ } => {
                let neutral = elim.clone().as_neutral()?;
                let elim_ty = neutral.try_infer_ty(ctx_tys)?;
                let (_eq_ty, _eq_tm_0, eq_tm_1) = elim_ty.as_equal().unwrap();
                Some(motive.clone().bind(eq_tm_1).bind(elim.clone()))
            },

            NeutralKind::Explode { elim, motive } => {
                Some(motive.clone().bind(elim.clone()))
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
        }
    }

    pub fn collect_stuck_vars(&self, usages: &mut Usages) {
        match self {
            NeutralKind::Var { index } => {
                usages.set_to_one(*index);
            },

            NeutralKind::Bind { .. } => unreachable!(),

            | NeutralKind::TagsApart { elim }
            | NeutralKind::ProjHead { elim }
            | NeutralKind::ProjTail { elim }
            => {
                elim.clone().as_neutral().unwrap().collect_stuck_vars(usages)
            },

            | NeutralKind::Fold { elim, .. }
            | NeutralKind::UniqueIdentity { elim, .. }
            | NeutralKind::Cong { elim, .. }
            | NeutralKind::Explode { elim, .. }
            | NeutralKind::Case { elim, .. }
            | NeutralKind::App { elim, .. }
            => {
                elim.clone().as_neutral().unwrap().into_inner().collect_stuck_vars(usages)
            },
        }
    }

    pub fn deep_nf_assuming_stuck(self) -> Weaken<NeutralKind> {
        match self {
            NeutralKind::Var { index } => Weaken::new(NeutralKind::Var { index }),

            NeutralKind::Bind { .. } => unreachable!(),

            NeutralKind::TagsApart { elim } => {
                Arc::unwrap_or_clone(elim.as_neutral().unwrap())
                .deep_nf()
                .as_neutral()
                .unwrap()
                .map(|neutral| NeutralKind::TagsApart {
                    elim: TmKind::Neutral { neutral },
                })
            },

            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                let elim = elim.as_neutral().unwrap().deep_nf_assuming_stuck().into_tm();
                let motive = motive.deep_nf();
                let zero_inhab = zero_inhab.deep_nf();
                let succ_inhab = succ_inhab.deep_nf();
                Weaken::new(NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab })
            },

            NeutralKind::UniqueIdentity { elim, motive, inhab } => {
                let elim = elim.as_neutral().unwrap().deep_nf_assuming_stuck().into_tm();
                let motive = motive.deep_nf();
                let inhab = inhab.deep_nf();
                Weaken::new(NeutralKind::UniqueIdentity { elim, motive, inhab })
            },

            NeutralKind::Cong { elim, motive, inhab } => {
                let elim = elim.as_neutral().unwrap().deep_nf_assuming_stuck().into_tm();
                let motive = motive.deep_nf();
                let inhab = inhab.deep_nf();
                Weaken::new(NeutralKind::Cong { elim, motive, inhab })
            },

            NeutralKind::Explode { elim, motive } => {
                let elim = elim.as_neutral().unwrap().deep_nf();
                let motive = motive.deep_nf();
                Weaken::new(NeutralKind::Explode { elim, motive })
            },

            NeutralKind::Case { elim, motive, lhs_inhab, rhs_inhab } => {
                let elim = elim.as_neutral().unwrap().deep_nf_assuming_stuck().into_tm();
                let motive = motive.deep_nf();
                let lhs_inhab = lhs_inhab.deep_nf();
                let rhs_inhab = rhs_inhab.deep_nf();
                Weaken::new(NeutralKind::Case { elim, motive, lhs_inhab, rhs_inhab })
            },

            NeutralKind::ProjHead { elim } => {
                Arc::unwrap_or_clone(elim.as_neutral().unwrap())
                .deep_nf_assuming_stuck()
                .map(|neutral| NeutralKind::ProjHead {
                    elim: TmKind::Neutral { neutral },
                })
            },

            NeutralKind::ProjTail { elim } => {
                Arc::unwrap_or_clone(elim.as_neutral().unwrap())
                .deep_nf_assuming_stuck()
                .map(|neutral| NeutralKind::ProjTail {
                    elim: TmKind::Neutral { neutral },
                })
            },

            NeutralKind::App { elim, arg_tm } => {
                let elim = elim.as_neutral().unwrap().deep_nf_assuming_stuck().into_tm();
                let arg_tm = arg_tm.deep_nf();
                Weaken::new(NeutralKind::App { elim, arg_tm })
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
        match (neutral_kind_0, neutral_kind_1) {
            (NeutralKind::Bind { .. }, _) |
            (_, NeutralKind::Bind { .. }) => unreachable!(),

            (NeutralKind::Var { index: index_0 }, NeutralKind::Var { index: index_1 }) => {
                let index = as_equal(index_0, &index_1)?;
                Some(NeutralKind::Var { index })
            },

            (NeutralKind::TagsApart { elim: elim_0 }, NeutralKind::TagsApart { elim: elim_1 }) => {
                let neutral_0 = elim_0.as_neutral().unwrap();
                let neutral_1 = elim_1.as_neutral().unwrap();
                let elim_ty_0 = neutral_0.try_infer_ty(ctx_tys).unwrap();
                let elim_ty_1 = neutral_1.try_infer_ty(ctx_tys).unwrap();
                let _elim_ty = Unify::unify(ctx_tys, (), elim_ty_0, elim_ty_1)?;

                let elim = TmKind::Neutral {
                    neutral: NeutralData::unify_without_cached_reduction(ctx_tys, neutral_0, neutral_1)?,
                };
                Some(NeutralKind::TagsApart { elim })
            },

            (
                NeutralKind::Fold {
                    elim: elim_0,
                    motive: motive_0,
                    zero_inhab: zero_inhab_0,
                    succ_inhab: succ_inhab_0,
                },
                NeutralKind::Fold {
                    elim: elim_1,
                    motive: motive_1,
                    zero_inhab: zero_inhab_1,
                    succ_inhab: succ_inhab_1,
                },
            ) => {
                let neutral_0 = elim_0.as_neutral().unwrap().into_inner();
                let neutral_1 = elim_1.as_neutral().unwrap().into_inner();
                let neutral = NeutralData::unify_without_cached_reduction(
                    ctx_tys, neutral_0, neutral_1,
                )?;
                let motive = Unify::unify(ctx_tys, (Ty::nat(), Scope::constant(())), motive_0, motive_1)?;
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

            (
                NeutralKind::UniqueIdentity { elim: elim_0, motive: motive_0, inhab: inhab_0 },
                NeutralKind::UniqueIdentity { elim: elim_1, motive: motive_1, inhab: inhab_1 },
            ) => {
                let neutral_0 = elim_0.as_neutral().unwrap().into_inner();
                let neutral_1 = elim_1.as_neutral().unwrap().into_inner();
                let elim_ty_0 = neutral_0.try_infer_ty(ctx_tys).unwrap();
                let elim_ty_1 = neutral_1.try_infer_ty(ctx_tys).unwrap();
                let elim_ty = Unify::unify(ctx_tys, (), elim_ty_0, elim_ty_1)?;
                let neutral = NeutralData::unify_without_cached_reduction(
                    ctx_tys, neutral_0, neutral_1,
                )?;

                let motive = Unify::unify(
                    ctx_tys,
                    (elim_ty.clone(), Scope::constant(())),
                    motive_0,
                    motive_1,
                )?;
                let (_eq_ty, eq_tm, _) = elim_ty.as_equal().unwrap();
                let inhab = Unify::unify(ctx_tys, motive.clone().bind(eq_tm.refl()), inhab_0, inhab_1)?;
                let elim = Weaken::new(TmKind::Neutral { neutral });
                Some(NeutralKind::UniqueIdentity { elim, motive, inhab })
            },

            (
                NeutralKind::Cong { elim: elim_0, motive: motive_0, inhab: inhab_0 },
                NeutralKind::Cong { elim: elim_1, motive: motive_1, inhab: inhab_1 },
            ) => {
                let neutral_0 = elim_0.as_neutral().unwrap().into_inner();
                let neutral_1 = elim_1.as_neutral().unwrap().into_inner();
                let elim_ty_0 = neutral_0.try_infer_ty(ctx_tys).unwrap();
                let elim_ty_1 = neutral_1.try_infer_ty(ctx_tys).unwrap();
                let elim_ty = Unify::unify(ctx_tys, (), elim_ty_0, elim_ty_1)?;
                let neutral = NeutralData::unify_without_cached_reduction(
                    ctx_tys, neutral_0, neutral_1,
                )?;

                let (eq_ty, eq_tm_0, _eq_tm_1) = elim_ty.as_equal().unwrap();
                let motive = Unify::unify(
                    ctx_tys,
                    (
                        eq_ty.clone(),
                        Scope::make(cmp::max(eq_ty.ctx_len(), eq_tm_0.ctx_len()), |eq_tm_1| (
                            Ty::equal(eq_ty, eq_tm_0.clone(), eq_tm_1),
                            Scope::constant(()),
                        )),
                    ),
                    motive_0,
                    motive_1,
                )?;
                let inhab = Unify::unify(
                    ctx_tys,
                    motive.clone().bind(eq_tm_0.clone()).bind(eq_tm_0.refl()),
                    inhab_0,
                    inhab_1,
                )?;
                let elim = Weaken::new(TmKind::Neutral { neutral });
                Some(NeutralKind::Cong { elim, motive, inhab })
            },

            (
                NeutralKind::Explode { elim: elim_0, motive: motive_0 },
                NeutralKind::Explode { elim: elim_1, motive: motive_1 },
            ) => {
                let neutral_0 = elim_0.as_neutral().unwrap().into_inner();
                let neutral_1 = elim_1.as_neutral().unwrap().into_inner();
                let neutral = NeutralData::unify_without_cached_reduction(
                    ctx_tys, neutral_0, neutral_1,
                )?;

                let motive = Unify::unify(
                    ctx_tys,
                    (Ty::never(), Scope::constant(())),
                    motive_0,
                    motive_1,
                )?;
                let elim = Weaken::new(TmKind::Neutral { neutral });
                Some(NeutralKind::Explode { elim, motive })
            },

            (
                NeutralKind::Case {
                    elim: elim_0,
                    motive: motive_0,
                    lhs_inhab: lhs_inhab_0,
                    rhs_inhab: rhs_inhab_0,
                },
                NeutralKind::Case {
                    elim: elim_1,
                    motive: motive_1,
                    lhs_inhab: lhs_inhab_1,
                    rhs_inhab: rhs_inhab_1,
                },
            ) => {
                let neutral_0 = elim_0.as_neutral().unwrap().into_inner();
                let neutral_1 = elim_1.as_neutral().unwrap().into_inner();
                let elim_ty_0 = neutral_0.try_infer_ty(ctx_tys).unwrap();
                let elim_ty_1 = neutral_1.try_infer_ty(ctx_tys).unwrap();
                let elim_ty = Unify::unify(ctx_tys, (), elim_ty_0, elim_ty_1)?;
                let neutral = NeutralData::unify_without_cached_reduction(
                    ctx_tys, neutral_0, neutral_1,
                )?;

                let motive = Unify::unify(
                    ctx_tys,
                    (elim_ty.clone(), Scope::constant(())),
                    motive_0,
                    motive_1,
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

            (NeutralKind::ProjHead { elim: elim_0 }, NeutralKind::ProjHead { elim: elim_1 }) => {
                let neutral_0 = elim_0.as_neutral().unwrap();
                let neutral_1 = elim_1.as_neutral().unwrap();
                let elim_ty_0 = neutral_0.try_infer_ty(ctx_tys).unwrap();
                let elim_ty_1 = neutral_1.try_infer_ty(ctx_tys).unwrap();
                let _elim_ty = Unify::unify(ctx_tys, (), elim_ty_0, elim_ty_1)?;
                let neutral = NeutralData::unify_without_cached_reduction(
                    ctx_tys, neutral_0, neutral_1,
                )?;

                let elim = TmKind::Neutral { neutral };
                Some(NeutralKind::ProjHead { elim })
            },

            (NeutralKind::ProjTail { elim: elim_0 }, NeutralKind::ProjTail { elim: elim_1 }) => {
                let neutral_0 = elim_0.as_neutral().unwrap();
                let neutral_1 = elim_1.as_neutral().unwrap();
                let elim_ty_0 = neutral_0.try_infer_ty(ctx_tys).unwrap();
                let elim_ty_1 = neutral_1.try_infer_ty(ctx_tys).unwrap();
                let _elim_ty = Unify::unify(ctx_tys, (), elim_ty_0, elim_ty_1)?;
                let neutral = NeutralData::unify_without_cached_reduction(
                    ctx_tys, neutral_0, neutral_1,
                )?;

                let elim = TmKind::Neutral { neutral };
                Some(NeutralKind::ProjTail { elim })
            },

            (
                NeutralKind::App { elim: elim_0, arg_tm: arg_tm_0 },
                NeutralKind::App { elim: elim_1, arg_tm: arg_tm_1 },
            ) => {
                let neutral_0 = elim_0.as_neutral().unwrap().into_inner();
                let neutral_1 = elim_1.as_neutral().unwrap().into_inner();
                let elim_ty_0 = neutral_0.try_infer_ty(ctx_tys).unwrap();
                let elim_ty_1 = neutral_1.try_infer_ty(ctx_tys).unwrap();
                let elim_ty = Unify::unify(ctx_tys, (), elim_ty_0, elim_ty_1)?;

                let elim = TmKind::Neutral {
                    neutral: NeutralData::unify_without_cached_reduction(ctx_tys, neutral_0, neutral_1)?,
                };

                let (_arg_name, arg_ty, _res_ty) = elim_ty.as_pi().unwrap();
                let arg_tm = Unify::unify(ctx_tys, arg_ty, arg_tm_0, arg_tm_1)?;
                let elim = Weaken::new(elim);
                Some(NeutralKind::App { elim, arg_tm })
            },

            _ => None,
        }
    }
}

impl Neutral {
    pub fn into_tm(self) -> Tm {
        self.map(|neutral| TmKind::Neutral { neutral })
    }

    pub fn var(index: usize) -> Neutral {
        lazy_static! {
            static ref VAR_0: Arc<NeutralData> = {
                NeutralData::new_arc(NeutralKind::Var { index: 0 })
            };
        }

        let usages = Usages::single_var(index);
        Weaken { usages, weak: VAR_0.clone() }
    }

    pub fn tags_apart(elim: Tm) -> Neutral {
        elim.map(|elim| NeutralData::new_arc(NeutralKind::TagsApart { elim }))
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

    pub fn unique_identity(
        elim: Tm,
        motive: Scope<Ty>,
        inhab: Tm,
    ) -> Neutral {
        Weaken::new_arc(NeutralData::new(NeutralKind::UniqueIdentity {
            elim, motive, inhab,
        }))
    }

    pub fn cong(
        elim: Tm,
        motive: Scope<Scope<Ty>>,
        inhab: Tm,
    ) -> Neutral {
        Weaken::new_arc(NeutralData::new(NeutralKind::Cong {
            elim, motive, inhab,
        }))
    }

    pub fn explode(
        elim: Tm,
        motive: Scope<Ty>,
    ) -> Neutral {
        Weaken::new_arc(NeutralData::new(NeutralKind::Explode {
            elim, motive,
        }))
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

    pub fn try_infer_ty(
        &self,
        ctx_tys: &mut Vec<Ty>,
    ) -> Option<Ty> {
        self.clone().into_inner().try_infer_ty(ctx_tys)
    }

    pub fn deep_nf(self) -> Tm {
        let Weaken { usages, weak: neutral } = self;
        let neutral = Arc::unwrap_or_clone(neutral);
        neutral.deep_nf().unfiltered(&usages)
    }

    pub fn deep_nf_assuming_stuck(self) -> Neutral {
        let Weaken { usages, weak: neutral } = self;
        let neutral = Arc::unwrap_or_clone(neutral);
        neutral.deep_nf_assuming_stuck().unfiltered(&usages)
    }
}

impl Substitutable for Neutral {
    type Output = Tm;

    fn subst(self, subst: &mut Subst) -> Tm {
        if self.usages.ctx_len() <= subst.subst_index() {
            return self.into_tm();
        }
        self.into_inner().subst(subst)
    }

    fn into_output(self) -> Tm {
        self.into_tm()
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
                let body = Weaken { usages: truncated_body_usages, weak: body };
                return subst.with_composed(pre_subst, |subst| body.subst(subst));
            },

            NeutralKind::TagsApart { elim } => {
                let elim = elim.subst(subst).into_inner();
                NeutralKind::TagsApart { elim }
            },

            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                let elim = elim.subst(subst);
                let motive = motive.capture_subst(subst.clone());
                let zero_inhab = zero_inhab.capture_subst(subst.clone());
                let succ_inhab = succ_inhab.capture_subst(subst.clone());
                NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab }
            },

            NeutralKind::UniqueIdentity { elim, motive, inhab } => {
                let elim = elim.subst(subst);
                let motive = motive.capture_subst(subst.clone());
                let inhab = inhab.capture_subst(subst.clone());
                NeutralKind::UniqueIdentity { elim, motive, inhab }
            },

            NeutralKind::Cong { elim, motive, inhab } => {
                let elim = elim.subst(subst);
                let motive = motive.capture_subst(subst.clone());
                let inhab = inhab.capture_subst(subst.clone());
                NeutralKind::Cong { elim, motive, inhab }
            },

            NeutralKind::Explode { elim, motive } => {
                let elim = elim.subst(subst);
                let motive = motive.capture_subst(subst.clone());
                NeutralKind::Explode { elim, motive }
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
        };
        neutral_kind.reduced()
    }

    fn into_output(self) -> Tm {
        Weaken::new_arc(NeutralData::new(self))
        .map(|neutral| TmKind::Neutral { neutral })
    }
}

