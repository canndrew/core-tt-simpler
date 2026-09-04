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
}

impl Bindable for Tm {
    fn capture_subst(self, subst: Subst) -> Tm {
        let (subst_index, var_tms) = subst.remove_unused_vars(&self.usages);
        if var_tms.is_empty() {
            return self;
        }

        let Weaken { usages: mut truncated_body_usages, weak: body } = self;
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
        if self.usages.ctx_len() <= subst.subst_index() {
            return self;
        }
        self.into_inner().subst(subst)
    }

    fn into_output(self) -> Tm {
        self
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
        }
    }

    fn into_output(self) -> Tm {
        Weaken::new(self)
    }
}

impl Tm {
    pub fn reduced(self) -> Tm {
        match &self.weak {
            TmKind::Intro { .. } => self,
            TmKind::Neutral { neutral } => {
                match neutral.try_reduce() {
                    None => self,
                    Some(new_tm) => new_tm.unfiltered(&self.usages),
                }
            },
        }
    }

    pub fn try_reduce_to_intro(self) -> Option<Intro> {
        match self.weak {
            TmKind::Intro { intro } => {
                Some(Weaken { usages: self.usages, weak: intro })
            },
            TmKind::Neutral { neutral } => {
                let intro = neutral.try_reduce_to_intro()?;
                Some(intro.unfiltered(&self.usages))
            },
        }
    }

    pub fn deep_nf(self) -> Tm {
        let Weaken { usages, weak: tm_kind } = self;
        tm_kind.deep_nf().unfiltered(&usages)
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

    pub fn tags_apart(self) -> Tm {
        Neutral::tags_apart(self).into_tm()
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
        let Weaken { usages, weak: tm_kind } = self;
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
        };
        let tm_kind = TmKind::Intro { intro: Arc::new(intro_kind) };
        Weaken { usages, weak: tm_kind }
    }

    pub fn fold(
        self,
        motive: Scope<Ty>,
        zero_inhab: Tm,
        succ_inhab: Scope<Scope<Tm>>,
    ) -> Tm {
        Neutral::fold(self, motive, zero_inhab, succ_inhab).into_tm()
    }

    pub fn refl(self) -> Tm {
        Intro::refl(self).into_tm()
    }

    pub fn unique_identity(
        self,
        motive: Scope<Ty>,
        inhab: Tm,
    ) -> Tm {
        Neutral::unique_identity(self, motive, inhab).into_tm()
    }

    pub fn cong(
        self,
        motive: Scope<Scope<Ty>>,
        inhab: Tm,
    ) -> Tm {
        Neutral::cong(self, motive, inhab).into_tm()
    }

    pub fn explode(
        self,
        motive: Scope<Ty>,
    ) -> Tm {
        Neutral::explode(self, motive).into_tm()
    }

    pub fn unit() -> Tm {
        Intro::unit().into_tm()
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

    pub fn as_var(&self) -> Option<usize> {
        match &self.weak {
            TmKind::Intro { .. } => None,
            TmKind::Neutral { neutral } => {
                match neutral.try_reduce() {
                    Some(tm) => {
                        let index = tm.as_var()?;
                        Some(self.usages.unfilter_index(index))
                    },
                    None => {
                        let index = neutral.kind.as_var()?;
                        debug_assert_eq!(index, 0);
                        Some(self.usages.as_single_var().unwrap())
                    },
                }
            },
        }
    }

    pub fn as_tag(self) -> Option<Tag> {
        let intro = self.try_reduce_to_intro()?;
        intro.as_tag()
    }

    pub fn as_neutral(self) -> Option<Neutral> {
        let Weaken { usages, weak: tm_kind } = self;
        let neutral = tm_kind.as_neutral()?;
        Some(Weaken { usages, weak: neutral })
    }

    /*
    pub fn try_infer_ty(
        &self,
        ctx_tys: &mut impl FnMut(usize) -> Ty,
    ) -> Option<Ty> {
        self.clone().into_inner().try_infer_ty(ctx_tys)
    }
    */
}

impl Unify for TmKind {
    type Meta = Ty;

    fn unify(
        ctx_tys: &mut Vec<Ty>,
        ty: Ty,
        tm_kind_0: TmKind,
        tm_kind_1: TmKind,
    ) -> Option<TmKind> {
        match (tm_kind_0, tm_kind_1) {
            (TmKind::Intro { intro: intro_0 }, TmKind::Intro { intro: intro_1 }) => {
                let intro = Unify::unify(ctx_tys, ty, intro_0, intro_1)?;
                Some(TmKind::Intro { intro })
            },

            (TmKind::Intro { intro: intro_0 }, TmKind::Neutral { neutral }) => {
                match neutral.try_reduce_to_intro() {
                    Some(intro_1) => {
                        let intro_1 = intro_1.into_inner();
                        let intro = Unify::unify(ctx_tys, ty, intro_0, intro_1)?;
                        Some(TmKind::Intro { intro })
                    },
                    None => {
                        let tm_kind_1 = TmKind::Neutral { neutral };
                        let intro_0 = Arc::unwrap_or_clone(intro_0);
                        match intro_0 {
                            IntroKind::Unit => {
                                Some(tm_kind_1)
                            },
                            IntroKind::Pair { head_tm: head_tm_0, tail_tm: tail_tm_0 } => {
                                let tm_1 = Weaken::new(tm_kind_1.clone());
                                let head_tm_1 = tm_1.clone().proj_head();
                                let tail_tm_1 = tm_1.proj_tail();
                                let (_head_name, head_ty, tail_ty) = ty.as_sigma().unwrap();

                                let head_tm = Unify::unify(ctx_tys, head_ty, head_tm_0, head_tm_1)?;
                                let _tail_tm = Unify::unify(
                                    ctx_tys, tail_ty.bind(head_tm), tail_tm_0, tail_tm_1,
                                )?;
                                Some(tm_kind_1)
                            },
                            IntroKind::Func { res_tm: res_tm_0 } => {
                                let tm_1 = Weaken::new(tm_kind_1.clone());
                                let res_tm_1 = Scope::make(tm_1.ctx_len(), |arg_tm| {
                                    tm_1.app(arg_tm).into_inner()
                                });
                                let (_arg_name, arg_ty, res_ty) = ty.as_pi().unwrap();

                                let _res_tm = Unify::unify(ctx_tys, (arg_ty, res_ty), res_tm_0, res_tm_1)?;
                                Some(tm_kind_1)
                            },
                            _ => None,
                        }
                    },
                }
            },

            (TmKind::Neutral { neutral }, TmKind::Intro { intro: intro_1 }) => {
                match neutral.try_reduce_to_intro() {
                    Some(intro_0) => {
                        let intro_0 = intro_0.into_inner();
                        let intro = Unify::unify(ctx_tys, ty, intro_0, intro_1)?;
                        Some(TmKind::Intro { intro })
                    },
                    None => {
                        let tm_kind_0 = TmKind::Neutral { neutral };
                        let intro_1 = Arc::unwrap_or_clone(intro_1);
                        match intro_1 {
                            IntroKind::Unit => {
                                Some(tm_kind_0)
                            },
                            IntroKind::Pair { head_tm: head_tm_1, tail_tm: tail_tm_1 } => {
                                let tm_0 = Weaken::new(tm_kind_0.clone());
                                let head_tm_0 = tm_0.clone().proj_head();
                                let tail_tm_0 = tm_0.proj_tail();
                                let (_head_name, head_ty, tail_ty) = ty.as_sigma().unwrap();

                                let head_tm = Unify::unify(ctx_tys, head_ty, head_tm_0, head_tm_1)?;
                                let _tail_tm = Unify::unify(
                                    ctx_tys, tail_ty.bind(head_tm), tail_tm_0, tail_tm_1,
                                )?;
                                Some(tm_kind_0)
                            },
                            IntroKind::Func { res_tm: res_tm_1 } => {
                                let tm_0 = Weaken::new(tm_kind_0.clone());
                                let res_tm_0 = Scope::make(tm_0.ctx_len(), |arg_tm| {
                                    tm_0.app(arg_tm).into_inner()
                                });
                                let (_arg_name, arg_ty, res_ty) = ty.as_pi().unwrap();

                                let _res_tm = Unify::unify(ctx_tys, (arg_ty, res_ty), res_tm_0, res_tm_1)?;
                                Some(tm_kind_0)
                            },
                            _ => None,
                        }
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
                        let kind = Unify::unify(ctx_tys, (), neutral_0.kind, neutral_1.kind)?;
                        let neutral = NeutralData::new_arc(kind);
                        Some(TmKind::Neutral { neutral })
                    },
                    (None, Some(tm_1)) => {
                        match tm_1.into_inner() {
                            TmKind::Intro { .. } => None,
                            TmKind::Neutral { neutral: neutral_1 } => {
                                let neutral = NeutralData::unify_without_cached_reduction(
                                    ctx_tys,
                                    neutral_0,
                                    neutral_1,
                                )?;
                                Some(TmKind::Neutral { neutral })
                            },
                        }
                    },
                    (Some(tm_0), None) => {
                        match tm_0.into_inner() {
                            TmKind::Intro { .. } => None,
                            TmKind::Neutral { neutral: neutral_0 } => {
                                let neutral = NeutralData::unify_without_cached_reduction(
                                    ctx_tys,
                                    neutral_0,
                                    neutral_1,
                                )?;
                                Some(TmKind::Neutral { neutral })
                            },
                        }
                    },
                    (Some(tm_0), Some(tm_1)) => {
                        let tm = Unify::unify(ctx_tys, ty, tm_0.clone(), tm_1.clone())?;
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
        }
    }

    pub fn as_neutral(self) -> Option<Arc<NeutralData>> {
        match self {
            TmKind::Intro { .. } => None,
            TmKind::Neutral { neutral } => Some(neutral),
        }
    }

    pub fn deep_nf(self) -> Tm {
        match self {
            TmKind::Intro { intro } => {
                Arc::unwrap_or_clone(intro).deep_nf().into_tm()
            },
            TmKind::Neutral { neutral } => {
                Arc::unwrap_or_clone(neutral).deep_nf()
            },
        }
    }
}

