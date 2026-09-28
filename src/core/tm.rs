use crate::priv_prelude::*;

pub type Tm = Weaken<TmKind>;

#[derive(Clone, Debug, Contextual)]
pub enum TmKind {
    Intro {
        intro: Arc<IntroKind>,
    },
    Neutral {
        neutral: Arc<NeutralData>,
    },
    Proof,
}

impl Bindable for Tm {
    fn capture_subst(self, subst: Subst) -> Tm {
        let (subst_index, var_tms) = subst.remove_unused_vars(self.usages());
        if var_tms.is_empty() {
            return self;
        }

        let (mut truncated_body_usages, body) = self.into_usages_and_weak();
        truncated_body_usages.truncate(subst_index);

        Weaken::new_arc(NeutralData::new(NeutralKind::Bind {
            var_tms, truncated_body_usages, body,
        }))
        .map(|neutral| TmKind::Neutral { neutral })
    }
}

impl Substitutable for Tm {
    type Output = Tm;

    fn subst(self, subst: &mut Subst) -> Tm {
        if self.ctx_len() <= subst.subst_index() {
            return self;
        }
        self.into_inner().subst(subst)
    }

    fn into_output(self) -> Tm {
        self
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<Tm> {
        Some(self.do_try_strengthen_index(var_index)?.flatten())
    }
}

impl Substitutable for TmKind {
    type Output = Tm;

    fn subst(self, subst: &mut Subst) -> Tm {
        match self {
            TmKind::Intro { intro } => {
                intro.subst(subst).into_tm()
            },
            TmKind::Neutral { neutral } => {
                neutral.subst(subst)
            },
            TmKind::Proof => Tm::proof(),
        }
    }

    fn into_output(self) -> Tm {
        Weaken::new(self)
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<Tm> {
        match self {
            TmKind::Intro { intro } => {
                Some(intro.try_strengthen_index(var_index)?.map(|intro| TmKind::Intro { intro }))
            },
            TmKind::Neutral { neutral } => {
                neutral.try_strengthen_index(var_index)
            },
            TmKind::Proof => Some(Tm::proof()),
        }
    }
}

impl Tm {
    pub fn reduced(self) -> Tm {
        match self.weak() {
            TmKind::Intro { .. } => self,
            TmKind::Neutral { neutral } => {
                match neutral.try_reduce() {
                    None => self,
                    Some(new_tm) => new_tm.unfiltered(self.usages()),
                }
            },
            TmKind::Proof => self,
        }
    }

    pub fn try_reduce_to_intro_assuming_relevant(self) -> Option<Intro> {
        let (usages, tm_kind) = self.into_usages_and_weak();
        match tm_kind {
            TmKind::Intro { intro } => {
                Some(Weaken::from_usages_and_weak(usages, intro))
            },
            TmKind::Neutral { neutral } => {
                let intro = neutral.try_reduce_to_intro_assuming_relevant()?;
                Some(intro.unfiltered(&usages))
            },
            TmKind::Proof => unreachable!(),
        }
    }

    pub fn into_name(self) -> Name {
        self.map(TmKind::into_name_kind)
    }

    pub fn into_ty(self) -> Ty {
        self.map(TmKind::into_ty_kind)
    }

    pub fn var(index: usize) -> Tm {
        Neutral::var(index).into_tm()
    }

    pub fn tag(tag: Tag) -> Tm {
        Intro::tag(tag).into_tm()
    }

    pub fn zero() -> Tm {
        Intro::zero().into_tm()
    }

    pub fn constant(ubig: Ubig) -> Tm {
        Intro::constant(ubig).into_tm()
    }

    pub fn succs(self, succ_count: impl Into<Ubig>) -> Tm {
        let mut succ_count_m1 = succ_count.into();
        if !succ_count_m1.decrement() {
            return self;
        }
        let (usages, tm_kind) = self.into_usages_and_weak();
        let intro_kind = match tm_kind {
            TmKind::Intro { intro } => {
                let intro = Arc::unwrap_or_clone(intro);
                match intro {
                    IntroKind::Constant { ubig } => {
                        let ubig = ubig + succ_count_m1 + 1usize;
                        IntroKind::Constant { ubig }
                    },
                    IntroKind::Succs { succ_count_m1: additional, pred_tm } => {
                        let succ_count_m1 = succ_count_m1 + additional + 1usize;
                        IntroKind::Succs { succ_count_m1, pred_tm }
                    },
                    _ => panic!("Tm::succs(): self is not a nat"),
                }
            },
            TmKind::Neutral { neutral: pred_tm } => {
                IntroKind::Succs { succ_count_m1, pred_tm }
            },
            TmKind::Proof => unreachable!(),
        };
        let tm_kind = TmKind::Intro { intro: Arc::new(intro_kind) };
        Weaken::from_usages_and_weak(usages, tm_kind)
    }

    pub fn fold(
        self,
        motive: Scope<Ty>,
        zero_inhab: Tm,
        succ_inhab: Scope<Scope<Tm>>,
    ) -> Tm {
        Neutral::fold(self, motive, zero_inhab, succ_inhab).into_tm()
    }

    pub fn explode(
        motive: Scope<Ty>,
    ) -> Tm {
        Neutral::explode(motive).into_tm()
    }

    pub fn inj_lhs(self) -> Tm {
        Intro::inj_lhs(self).into_tm()
    }

    pub fn inj_rhs(self) -> Tm {
        Intro::inj_rhs(self).into_tm()
    }

    pub fn case(
        self,
        motive: Scope<Ty>,
        lhs_inhab: Scope<Tm>,
        rhs_inhab: Scope<Tm>,
    ) -> Tm {
        Neutral::case(self, motive, lhs_inhab, rhs_inhab).into_tm()
    }

    pub fn pair(self, tail_tm: Tm) -> Tm {
        Intro::pair(self, tail_tm).into_tm()
    }

    pub fn proj_head(self) -> Tm {
        Neutral::proj_head(self).into_tm()
    }

    pub fn proj_tail(self) -> Tm {
        Neutral::proj_tail(self).into_tm()
    }

    pub fn func(res_tm: Scope<Tm>) -> Tm {
        Intro::func(res_tm).into_tm()
    }

    pub fn app(self, arg_tm: Tm) -> Tm {
        Neutral::app(self, arg_tm).into_tm()
    }

    pub fn cast(ty_0: Ty, ty_1: Ty, tm_0: Tm) -> Tm {
        Neutral::cast(ty_0, ty_1, tm_0).into_tm()
    }

    pub fn proof() -> Tm {
        Weaken::new(TmKind::Proof)
    }

    pub fn as_var(&self) -> Option<usize> {
        let index = self.weak().clone().as_var()?;
        Some(self.usages().unfilter_index(index))
    }

    pub fn as_tag(self) -> Option<Tag> {
        let (_usages, tm) = self.into_usages_and_weak();
        match tm {
            TmKind::Intro { intro } => Arc::unwrap_or_clone(intro).as_tag(),
            TmKind::Neutral { .. } => None,
            TmKind::Proof => None,
        }
    }

    pub fn as_intro(self) -> Option<Intro> {
        self.try_map(|tm_kind| tm_kind.as_intro())
    }

    pub fn as_neutral(self) -> Option<Neutral> {
        self.try_map(|tm_kind| tm_kind.as_neutral())
    }

    /*
    pub fn as_repeated_app(self) -> (Tm, Vec<Tm>) {
        self.into_inner().as_repeated_app()
    }
    */
}

impl Unify for TmKind {
    fn unify(
        tm_kind_0: TmKind,
        tm_kind_1: TmKind,
    ) -> Option<TmKind> {
        fn unify_intro_and_stuck_neutral(
            intro: Arc<IntroKind>,
            neutral: Arc<NeutralData>,
        ) -> Option<TmKind> {
            let tm_kind_1 = TmKind::Neutral { neutral };
            let intro_0 = Arc::unwrap_or_clone(intro);
            match intro_0 {
                IntroKind::Pair { head_tm: head_tm_0, tail_tm: tail_tm_0 } => {
                    let tm_1 = Weaken::new(tm_kind_1.clone());
                    let head_tm_1 = tm_1.clone().proj_head();
                    let tail_tm_1 = tm_1.proj_tail();

                    let _head_tm = Unify::unify(head_tm_0, head_tm_1)?;
                    let _tail_tm = Unify::unify(tail_tm_0, tail_tm_1)?;
                    Some(tm_kind_1)
                },
                IntroKind::Func { res_tm: res_tm_0 } => {
                    let tm_1 = Weaken::new(tm_kind_1.clone());
                    let res_tm_1 = Scope::make(tm_1.ctx_len(), |arg_tm| {
                        tm_1.app(arg_tm).into_inner()
                    });
                    let _res_tm = Unify::unify(res_tm_0, res_tm_1)?;
                    Some(tm_kind_1)
                },
                _ => None,
            }
        }

        match (tm_kind_0, tm_kind_1) {
            (TmKind::Proof, _) |
            (_, TmKind::Proof) => Some(TmKind::Proof),

            (TmKind::Intro { intro: intro_0 }, TmKind::Intro { intro: intro_1 }) => {
                let intro = Unify::unify(intro_0, intro_1)?;
                Some(TmKind::Intro { intro })
            },

            (TmKind::Intro { intro: intro_0 }, TmKind::Neutral { neutral }) => {
                let tm_kind_1 = match neutral.try_reduce() {
                    None => TmKind::Neutral { neutral },
                    Some(tm_1) => tm_1.into_inner(),
                };
                match tm_kind_1 {
                    TmKind::Proof => Some(TmKind::Proof),
                    TmKind::Intro { intro: intro_1 } => {
                        let intro = Unify::unify(intro_0, intro_1)?;
                        Some(TmKind::Intro { intro })
                    },
                    TmKind::Neutral { neutral } => {
                        unify_intro_and_stuck_neutral(intro_0, neutral)
                    },
                }
            },

            (TmKind::Neutral { neutral }, TmKind::Intro { intro: intro_1 }) => {
                let tm_kind_0 = match neutral.try_reduce() {
                    None => TmKind::Neutral { neutral },
                    Some(tm_0) => tm_0.into_inner(),
                };
                match tm_kind_0 {
                    TmKind::Proof => Some(TmKind::Proof),
                    TmKind::Intro { intro: intro_0 } => {
                        let intro = Unify::unify(intro_0, intro_1)?;
                        Some(TmKind::Intro { intro })
                    },
                    TmKind::Neutral { neutral } => {
                        unify_intro_and_stuck_neutral(intro_1, neutral)
                    },
                }
            },
            
            (TmKind::Neutral { neutral: neutral_0 }, TmKind::Neutral { neutral: neutral_1 }) => {
                if Arc::ptr_eq(&neutral_0, &neutral_1) {
                    return Some(TmKind::Neutral { neutral: neutral_0 });
                }
                match (neutral_0.try_reduce(), neutral_1.try_reduce()) {
                    (None, None) => {
                        let neutral_0 = Arc::unwrap_or_clone(neutral_0);
                        let neutral_1 = Arc::unwrap_or_clone(neutral_1);
                        let kind = Unify::unify(neutral_0.kind, neutral_1.kind)?;
                        let neutral = NeutralData::new_arc(kind);
                        Some(TmKind::Neutral { neutral })
                    },
                    (None, Some(tm_1)) => {
                        match tm_1.into_inner() {
                            TmKind::Proof => Some(TmKind::Proof),
                            TmKind::Intro { intro } => {
                                unify_intro_and_stuck_neutral(intro, neutral_0)
                            },
                            TmKind::Neutral { neutral: neutral_1 } => {
                                let neutral = NeutralData::unify_without_cached_reduction(
                                    neutral_0,
                                    neutral_1,
                                )?;
                                Some(TmKind::Neutral { neutral })
                            },
                        }
                    },
                    (Some(tm_0), None) => {
                        match tm_0.into_inner() {
                            TmKind::Proof => Some(TmKind::Proof),
                            TmKind::Intro { intro } => {
                                unify_intro_and_stuck_neutral(intro, neutral_1)
                            },
                            TmKind::Neutral { neutral: neutral_0 } => {
                                let neutral = NeutralData::unify_without_cached_reduction(
                                    neutral_0,
                                    neutral_1,
                                )?;
                                Some(TmKind::Neutral { neutral })
                            },
                        }
                    },
                    (Some(tm_0), Some(tm_1)) => {
                        let tm = Unify::unify(tm_0, tm_1)?;
                        Some(tm.into_inner())
                    },
                }
            },
        }
    }
}

impl TmKind {
    pub fn into_name_kind(self) -> NameKind {
        match self {
            TmKind::Intro { intro } => {
                let intro = Arc::unwrap_or_clone(intro);
                let IntroKind::Tag { tag } = intro else {
                    unreachable!();
                };
                NameKind::Tag { tag }
            },
            TmKind::Neutral { neutral } => {
                NameKind::Neutral { neutral }
            },
            TmKind::Proof => unreachable!(),
        }
    }

    pub fn into_ty_kind(self) -> TyKind {
        match self {
            TmKind::Intro { intro } => {
                let intro = Arc::unwrap_or_clone(intro);
                let IntroKind::Form { form } = intro else {
                    panic!("TmKind::into_ty_kind(): tm is not a type");
                };
                TyKind::Form { form }
            },
            TmKind::Neutral { neutral } => {
                TyKind::Neutral { neutral }
            },
            TmKind::Proof => unreachable!(),
        }
    }

    pub fn as_intro(self) -> Option<Arc<IntroKind>> {
        match self {
            TmKind::Intro { intro } => Some(intro),
            TmKind::Neutral { .. } => None,
            TmKind::Proof => None,
        }
    }

    pub fn as_neutral(self) -> Option<Arc<NeutralData>> {
        match self {
            TmKind::Intro { .. } => None,
            TmKind::Neutral { neutral } => Some(neutral),
            TmKind::Proof => None,
        }
    }

    /*
    pub fn as_repeated_app(self) -> (Tm, Vec<Tm>) {
        let base = match self {
            TmKind::Intro { intro } => TmKind::Intro { intro },
            TmKind::Neutral { neutral } => {
                if let NeutralKind::App { elim, arg_tm } = neutral.kind.clone() {
                    let (base, mut args) = elim.as_repeated_app();
                    args.push(arg_tm);
                    return (base, args);
                } else {
                    TmKind::Neutral { neutral }
                }
            },
            TmKind::Proof => TmKind::Proof,
        };
        let base = Weaken::new(base);
        let args = Vec::new();
        (base, args)
    }
    */

    pub fn as_var(self) -> Option<usize> {
        match self {
            TmKind::Intro { .. } => None,
            TmKind::Neutral { neutral } => neutral.as_var(),
            TmKind::Proof => None,
        }
    }
}

impl DeepNf for TmKind {
    type Output = Tm;

    fn deep_nf(self) -> Tm {
        match self {
            TmKind::Intro { intro } => {
                intro.deep_nf().into_tm()
            },
            TmKind::Neutral { neutral } => {
                neutral.deep_nf()
            },
            TmKind::Proof => Tm::proof(),
        }
    }
}

