use crate::priv_prelude::*;

pub type Intro = Weaken<Arc<IntroKind>>;

#[derive(Clone, Debug, Contextual)]
pub enum IntroKind {
    Tag {
        #[contextual(ignore)]
        tag: Tag,
    },
    Form {
        form: Arc<FormKind>,
    },
    Constant {
        #[contextual(ignore)]
        ubig: Ubig,
    },
    Succs {
        #[contextual(ignore)]
        succ_count_m1: Ubig,
        pred_tm: OrLazy<TmKind>,
    },
    InjLhs {
        lhs_tm: OrLazy<TmKind>,
    },
    InjRhs {
        rhs_tm: OrLazy<TmKind>,
    },
    Pair {
        head_tm: Tm,
        tail_tm: Tm,
    },
    Func {
        res_tm: Scope<OrLazy<TmKind>>,
    },
}

impl Unify for IntroKind {
    fn unify(
        intro_kind_0: IntroKind,
        intro_kind_1: IntroKind,
    ) -> Option<IntroKind> {
        fn unify_succs_lazy_and_succs_lazy(
            mut succ_count_m1_0: Ubig,
            mut succ_count_m1_1: Ubig,
            mut pred_tm_0: OrLazy<TmKind>,
            mut pred_tm_1: OrLazy<TmKind>,
        ) -> Option<IntroKind> {
            loop {
                match succ_count_m1_0.cmp(&succ_count_m1_1) {
                    cmp::Ordering::Less => {
                        match pred_tm_0.reduced() {
                            TmKind::Intro { intro } => {
                                match Arc::unwrap_or_clone(intro) {
                                    IntroKind::Constant { ubig } => {
                                        let ubig_0 = succ_count_m1_0 + ubig + 1usize;
                                        break unify_constant_and_succs_lazy(
                                            ubig_0,
                                            succ_count_m1_1,
                                            pred_tm_1,
                                        );
                                    },
                                    IntroKind::Succs {
                                        succ_count_m1: additional,
                                        pred_tm: new_pred_tm,
                                    } => {
                                        succ_count_m1_0 += additional + 1usize;
                                        pred_tm_0 = new_pred_tm;
                                    },
                                    _ => unreachable!(),
                                }
                            },
                            TmKind::Proof => unreachable!(),
                            TmKind::Stuck { stuck } => {
                                break unify_succs_stuck_and_succs_lazy(
                                    succ_count_m1_0,
                                    succ_count_m1_1,
                                    stuck,
                                    pred_tm_1,
                                );
                            },
                        }
                    },
                    cmp::Ordering::Equal => {
                        let pred_tm = Unify::unify(pred_tm_0, pred_tm_1)?;
                        break Some(IntroKind::Succs {
                            succ_count_m1: succ_count_m1_0,
                            pred_tm,
                        });
                    },
                    cmp::Ordering::Greater => {
                        match pred_tm_1.reduced() {
                            TmKind::Intro { intro } => {
                                match Arc::unwrap_or_clone(intro) {
                                    IntroKind::Constant { ubig } => {
                                        let ubig_1 = succ_count_m1_1 + ubig + 1usize;
                                        break unify_constant_and_succs_lazy(
                                            ubig_1,
                                            succ_count_m1_0,
                                            pred_tm_0,
                                        );
                                    },
                                    IntroKind::Succs {
                                        succ_count_m1: additional,
                                        pred_tm: new_pred_tm,
                                    } => {
                                        succ_count_m1_1 += additional + 1usize;
                                        pred_tm_1 = new_pred_tm;
                                    },
                                    _ => unreachable!(),
                                }
                            },
                            TmKind::Proof => unreachable!(),
                            TmKind::Stuck { stuck } => {
                                break unify_succs_stuck_and_succs_lazy(
                                    succ_count_m1_1,
                                    succ_count_m1_0,
                                    stuck,
                                    pred_tm_0,
                                );
                            },
                        }
                    },
                }
            }
        }

        fn unify_succs_stuck_and_succs_lazy(
            succ_count_m1_0: Ubig,
            mut succ_count_m1_1: Ubig,
            pred_stuck_0: StuckKind,
            mut pred_tm_1: OrLazy<TmKind>,
        ) -> Option<IntroKind> {
            loop {
                if succ_count_m1_0 < succ_count_m1_1 {
                    return None;
                }
                match pred_tm_1.reduced() {
                    TmKind::Intro { intro } => {
                        match Arc::unwrap_or_clone(intro) {
                            IntroKind::Constant { .. } => return None,
                            IntroKind::Succs {
                                succ_count_m1: additional,
                                pred_tm: new_pred_tm,
                            } => {
                                succ_count_m1_1 += additional + 1usize;
                                pred_tm_1 = new_pred_tm;
                            },
                            _ => unreachable!(),
                        }
                    },
                    TmKind::Proof => unreachable!(),
                    TmKind::Stuck { stuck } => {
                        let succ_count_m1 = as_equal(
                            succ_count_m1_0,
                            &succ_count_m1_1,
                        )?;
                        let stuck = Unify::unify(
                            pred_stuck_0,
                            stuck,
                        )?;
                        break Some(IntroKind::Succs {
                            succ_count_m1,
                            pred_tm: OrLazy::Reduced(TmKind::Stuck {
                                stuck,
                            }),
                        });
                    },
                }
            }
        }

        fn unify_constant_and_succs_lazy(
            ubig_0: Ubig,
            mut succ_count_m1_1: Ubig,
            mut pred_tm_1: OrLazy<TmKind>,
        ) -> Option<IntroKind> {
            loop {
                if ubig_0 <= succ_count_m1_1 {
                    return None;
                }
                match pred_tm_1.reduced() {
                    TmKind::Intro { intro } => {
                        match Arc::unwrap_or_clone(intro) {
                            IntroKind::Constant { ubig } => {
                                let ubig_1 = succ_count_m1_1 + ubig + 1usize;
                                let ubig = as_equal(
                                    ubig_0,
                                    &ubig_1,
                                )?;
                                break Some(IntroKind::Constant { ubig });
                            },
                            IntroKind::Succs {
                                succ_count_m1: additional,
                                pred_tm: new_pred_tm,
                            } => {
                                succ_count_m1_1 += additional + 1usize;
                                pred_tm_1 = new_pred_tm;
                            },
                            _ => unreachable!(),
                        }
                    },
                    TmKind::Proof => unreachable!(),
                    TmKind::Stuck { .. } => return None,
                }
            }
        }

        match (intro_kind_0, intro_kind_1) {
            (IntroKind::Tag { tag: tag_0 }, IntroKind::Tag { tag: tag_1 }) => {
                let tag = as_equal(tag_0, &tag_1)?;
                Some(IntroKind::Tag { tag })
            },
            
            (IntroKind::Form { form: form_0 }, IntroKind::Form { form: form_1 }) => {
                let form = Unify::unify(form_0, form_1)?;
                Some(IntroKind::Form { form })
            },

            (IntroKind::Constant { ubig: ubig_0 }, IntroKind::Constant { ubig: ubig_1 }) => {
                let ubig = as_equal(ubig_0, &ubig_1)?;
                Some(IntroKind::Constant { ubig })
            },

            (
                IntroKind::Succs { succ_count_m1: succ_count_m1_0, pred_tm: pred_tm_0 },
                IntroKind::Succs { succ_count_m1: succ_count_m1_1, pred_tm: pred_tm_1 },
            ) => {
                unify_succs_lazy_and_succs_lazy(
                    succ_count_m1_0,
                    succ_count_m1_1,
                    pred_tm_0,
                    pred_tm_1,
                )
            },

            (
                IntroKind::Constant { ubig },
                IntroKind::Succs { succ_count_m1, pred_tm },
            ) => {
                unify_constant_and_succs_lazy(ubig, succ_count_m1, pred_tm)
            },

            (
                IntroKind::Succs { succ_count_m1, pred_tm },
                IntroKind::Constant { ubig },
            ) => {
                unify_constant_and_succs_lazy(ubig, succ_count_m1, pred_tm)
            },

            (IntroKind::InjLhs { lhs_tm: lhs_tm_0 }, IntroKind::InjLhs { lhs_tm: lhs_tm_1 }) => {
                let lhs_tm = Unify::unify(lhs_tm_0, lhs_tm_1)?;
                Some(IntroKind::InjLhs { lhs_tm })
            },

            (IntroKind::InjRhs { rhs_tm: rhs_tm_0 }, IntroKind::InjRhs { rhs_tm: rhs_tm_1 }) => {
                let rhs_tm = Unify::unify(rhs_tm_0, rhs_tm_1)?;
                Some(IntroKind::InjRhs { rhs_tm })
            },

            (
                IntroKind::Pair { head_tm: head_tm_0, tail_tm: tail_tm_0 },
                IntroKind::Pair { head_tm: head_tm_1, tail_tm: tail_tm_1 },
            ) => {
                let head_tm = Unify::unify(head_tm_0, head_tm_1)?;
                let tail_tm = Unify::unify(tail_tm_0, tail_tm_1)?;
                Some(IntroKind::Pair { head_tm, tail_tm })
            },

            (IntroKind::Func { res_tm: res_tm_0 }, IntroKind::Func { res_tm: res_tm_1 }) => {
                let res_tm = Unify::unify(res_tm_0, res_tm_1)?;
                Some(IntroKind::Func { res_tm })
            },

            _ => None,
        }
    }
}

impl Intro {
    pub fn into_tm(self) -> Tm {
        self.map(|intro| OrLazy::Reduced(TmKind::Intro { intro }))
    }

    pub fn into_ty(self) -> Ty {
        self.into_form().into_ty()
    }

    pub fn into_form(self) -> Form {
        self.map(|intro| Arc::unwrap_or_clone(intro).into_form_kind())
    }

    pub fn tag(tag: Tag) -> Intro {
        Weaken::new_arc(IntroKind::Tag { tag })
    }

    pub fn zero() -> Intro {
        Weaken::new(IntroKind::zero())
    }

    pub fn succs_m1(pred_tm: Tm, succ_count_m1: Ubig) -> Intro {
        let (usages, pred_tm) = pred_tm.into_usages_and_weak();
        let intro = match pred_tm {
            OrLazy::Reduced(reduced) => {
                match reduced {
                    TmKind::Intro { intro } => {
                        match Arc::unwrap_or_clone(intro) {
                            IntroKind::Constant { ubig } => {
                                let ubig = ubig + succ_count_m1 + 1usize;
                                IntroKind::Constant { ubig }
                            },
                            IntroKind::Succs { succ_count_m1: additional, pred_tm } => {
                                let succ_count_m1 = succ_count_m1 + additional + 1usize;
                                IntroKind::Succs { succ_count_m1, pred_tm }
                            },
                            _ => unreachable!(),
                        }
                    },
                    TmKind::Proof => unreachable!(),
                    TmKind::Stuck { stuck } => {
                        let pred_tm = OrLazy::Reduced(TmKind::Stuck { stuck });
                        IntroKind::Succs { succ_count_m1, pred_tm }
                    },
                }
            },
            OrLazy::Lazy { .. } => {
                IntroKind::Succs { succ_count_m1, pred_tm }
            },
        };
        Weaken::from_usages_and_weak(usages, Arc::new(intro))
    }

    pub fn constant(ubig: Ubig) -> Intro {
        Weaken::new_arc(IntroKind::Constant { ubig })
    }

    pub fn inj_lhs(lhs_tm: Tm) -> Intro {
        lhs_tm.map(|lhs_tm| Arc::new(IntroKind::InjLhs { lhs_tm }))
    }

    pub fn inj_rhs(rhs_tm: Tm) -> Intro {
        rhs_tm.map(|rhs_tm| Arc::new(IntroKind::InjRhs { rhs_tm }))
    }

    pub fn pair(head_tm: Tm, tail_tm: Tm) -> Intro {
        Weaken::new_arc(IntroKind::Pair { head_tm, tail_tm })
    }

    pub fn func(res_tm: Scope<Tm>) -> Intro {
        res_tm
        .lift_weaken()
        .map(|res_tm| Arc::new(IntroKind::Func { res_tm }))
    }

    pub fn as_tag(self) -> Option<Tag> {
        Arc::unwrap_or_clone(self.into_weak()).as_tag()
    }

    pub fn as_form(self) -> Option<Form> {
        self.try_map(|intro_kind| {
            Arc::unwrap_or_clone(intro_kind).as_form()
        })
    }

    pub fn as_constant(self) -> Option<Ubig> {
        Arc::unwrap_or_clone(self.into_weak()).as_constant()
    }

    pub fn as_succs_m1(self) -> Option<(Ubig, Tm)> {
        let (usages, intro_kind) = self.into_usages_and_weak();
        let (succ_count_m1, pred_tm) = Arc::unwrap_or_clone(intro_kind).as_succs_m1()?;
        let pred_tm = Weaken::from_usages_and_weak(usages, pred_tm);
        Some((succ_count_m1, pred_tm))
    }

    pub fn as_inj_lhs(self) -> Option<Tm> {
        self.try_map(|intro_kind| {
            Some(Arc::unwrap_or_clone(intro_kind).as_inj_lhs()?)
        })
    }

    pub fn as_inj_rhs(self) -> Option<Tm> {
        self.try_map(|intro_kind| {
            Some(Arc::unwrap_or_clone(intro_kind).as_inj_rhs()?)
        })
    }

    pub fn as_pair(self) -> Option<(Tm, Tm)> {
        self.map_out_unfiltered(|intro| Arc::unwrap_or_clone(intro).as_pair())
    }

    pub fn as_func(self) -> Option<Scope<Tm>> {
        let res_tm = self.try_map(|intro_kind| {
            Some(Arc::unwrap_or_clone(intro_kind).as_func()?)
        })?;
        Some(res_tm.lift_scope())
    }
}

impl IntroKind {
    pub fn into_form_kind(self) -> Arc<FormKind> {
        self.as_form().unwrap()
    }

    pub fn zero() -> Arc<IntroKind> {
        lazy_static! {
            static ref ZERO: Arc<IntroKind> = Arc::new(IntroKind::Constant { ubig: Ubig::ZERO });
        }

        ZERO.clone()
    }

    pub fn as_tag(self) -> Option<Tag> {
        let IntroKind::Tag { tag } = self else {
            return None;
        };
        Some(tag)
    }

    pub fn as_form(self) -> Option<Arc<FormKind>> {
        let IntroKind::Form { form } = self else {
            return None;
        };
        Some(form)
    }

    pub fn as_constant(self) -> Option<Ubig> {
        let IntroKind::Constant { ubig } = self else {
            return None;
        };
        Some(ubig)
    }

    pub fn as_succs_m1(self) -> Option<(Ubig, OrLazy<TmKind>)> {
        let IntroKind::Succs { succ_count_m1, pred_tm } = self else {
            return None;
        };
        Some((succ_count_m1, pred_tm))
    }

    pub fn as_inj_lhs(self) -> Option<OrLazy<TmKind>> {
        let IntroKind::InjLhs { lhs_tm } = self else {
            return None;
        };
        Some(lhs_tm)
    }

    pub fn as_inj_rhs(self) -> Option<OrLazy<TmKind>> {
        let IntroKind::InjRhs { rhs_tm } = self else {
            return None;
        };
        Some(rhs_tm)
    }

    pub fn as_pair(self) -> Option<(Tm, Tm)> {
        match self {
            IntroKind::Pair { head_tm, tail_tm } => {
                Some((head_tm, tail_tm))
            },

            _ => None,
        }
    }

    pub fn as_func(self) -> Option<Scope<OrLazy<TmKind>>> {
        let IntroKind::Func { res_tm } = self else {
            return None;
        };
        Some(res_tm)
    }
}

impl DeepNf for IntroKind {
    type Output = Intro;

    fn deep_nf(self) -> Intro {
        match self {
            IntroKind::Tag { tag } => {
                Weaken::new_arc(IntroKind::Tag { tag })
            },

            IntroKind::Form { form } => {
                Arc::unwrap_or_clone(form).deep_nf().map(|form| Arc::new(IntroKind::Form { form }))
            },

            IntroKind::Constant { ubig } => {
                Weaken::new_arc(IntroKind::Constant { ubig })
            },

            IntroKind::Succs { succ_count_m1, pred_tm } => {
                let pred_tm = pred_tm.deep_nf();
                let (usages, tm_kind) = pred_tm.into_usages_and_weak();
                let intro_kind = match tm_kind {
                    TmKind::Intro { intro } => {
                        match Arc::unwrap_or_clone(intro) {
                            IntroKind::Constant { ubig } => {
                                IntroKind::Constant {
                                    ubig: ubig + succ_count_m1 + 1usize,
                                }
                            },
                            IntroKind::Succs { succ_count_m1: succ_count_m1_inner, pred_tm } => {
                                IntroKind::Succs {
                                    succ_count_m1: succ_count_m1_inner + succ_count_m1 + 1usize,
                                    pred_tm,
                                }
                            },
                            _ => unreachable!(),
                        }
                    },
                    TmKind::Proof => unreachable!(),
                    TmKind::Stuck { stuck } => {
                        let pred_tm = OrLazy::Reduced(TmKind::Stuck { stuck });
                        IntroKind::Succs { succ_count_m1, pred_tm }
                    },
                };
                Weaken::from_usages_and_weak(usages, Arc::new(intro_kind))
            },

            IntroKind::InjLhs { lhs_tm } => {
                lhs_tm
                .deep_nf()
                .into_tm()
                .map(|lhs_tm| {
                    Arc::new(IntroKind::InjLhs { lhs_tm })
                })
            },

            IntroKind::InjRhs { rhs_tm } => {
                rhs_tm
                .deep_nf()
                .into_tm()
                .map(|rhs_tm| {
                    Arc::new(IntroKind::InjRhs { rhs_tm })
                })
            },

            IntroKind::Pair { head_tm, tail_tm } => {
                let head_tm = head_tm.deep_nf().into_tm();
                let tail_tm = tail_tm.deep_nf().into_tm();
                Weaken::new_arc(IntroKind::Pair { head_tm, tail_tm })
            },

            IntroKind::Func { res_tm } => {
                res_tm
                .map_without_capture(|res_tm| res_tm.deep_nf().into_tm())
                .lift_weaken()
                .map(|res_tm| Arc::new(IntroKind::Func { res_tm }))
            },
        }
    }
}

impl Substitutable for IntroKind {
    type Output = Weaken<IntroKind>;

    fn subst(self, subst: &mut Subst) -> Weaken<IntroKind> {
        match self {
            IntroKind::Tag { tag } => {
                Weaken::new(IntroKind::Tag { tag })
            },

            IntroKind::Form { form } => {
                form
                .subst(subst)
                .map(|form| IntroKind::Form { form })
            },

            IntroKind::Constant { ubig } => {
                Weaken::new(IntroKind::Constant { ubig })
            },

            IntroKind::Succs { succ_count_m1, pred_tm } => {
                Weaken::new(pred_tm)
                .capture_subst(subst.clone())
                .map(|pred_tm| {
                    IntroKind::Succs { succ_count_m1, pred_tm }
                })
            },

            IntroKind::InjLhs { lhs_tm } => {
                Weaken::new(lhs_tm)
                .capture_subst(subst.clone())
                .map(|lhs_tm| {
                    IntroKind::InjLhs { lhs_tm }
                })
            },

            IntroKind::InjRhs { rhs_tm } => {
                Weaken::new(rhs_tm)
                .capture_subst(subst.clone())
                .map(|rhs_tm| {
                    IntroKind::InjRhs { rhs_tm }
                })
            },

            IntroKind::Pair { head_tm, tail_tm } => {
                let head_tm = head_tm.capture_subst(subst.clone());
                let tail_tm = tail_tm.capture_subst(subst.clone());
                Weaken::new(IntroKind::Pair { head_tm, tail_tm })
            },

            IntroKind::Func { res_tm } => {
                res_tm
                .map_without_capture(Weaken::new)
                .capture_subst(subst.clone())
                .lift_weaken()
                .map(|res_tm| IntroKind::Func { res_tm })
            },
        }
    }

    fn into_output(self) -> Weaken<IntroKind> {
        Weaken::new(self)
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<IntroKind> {
        let intro = match self {
            IntroKind::Tag { tag } => {
                IntroKind::Tag { tag }
            },

            IntroKind::Form { form } => {
                let form = form.try_strengthen_index(var_index)?;
                IntroKind::Form { form }
            },

            IntroKind::Constant { ubig } => {
                IntroKind::Constant { ubig }
            },

            IntroKind::Succs { succ_count_m1, pred_tm } => {
                let pred_tm = pred_tm.try_strengthen_index(var_index)?;
                IntroKind::Succs { succ_count_m1, pred_tm }
            },

            IntroKind::InjLhs { lhs_tm } => {
                let lhs_tm = lhs_tm.try_strengthen_index(var_index)?;
                IntroKind::InjLhs { lhs_tm }
            },

            IntroKind::InjRhs { rhs_tm } => {
                let rhs_tm = rhs_tm.try_strengthen_index(var_index)?;
                IntroKind::InjRhs { rhs_tm }
            },

            IntroKind::Pair { head_tm, tail_tm } => {
                let head_tm = head_tm.try_strengthen_index(var_index)?;
                let tail_tm = tail_tm.try_strengthen_index(var_index)?;
                IntroKind::Pair { head_tm, tail_tm }
            },

            IntroKind::Func { res_tm } => {
                let res_tm = {
                    res_tm
                    .map_without_capture(Weaken::new)
                    .try_strengthen_index(var_index)?
                    .map_without_capture(Weaken::into_inner)
                };
                IntroKind::Func { res_tm }
            },
        };
        Some(intro)
    }
}
