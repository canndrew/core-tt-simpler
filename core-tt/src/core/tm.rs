use crate::priv_prelude::*;

pub type Tm = Weaken<OrLazy<TmKind>>;
pub type ValTm = Weaken<TmKind>;

#[derive(Clone, Debug, Contextual)]
pub enum TmKind {
    Intro {
        intro: Arc<IntroKind>,
    },
    Stuck {
        stuck: StuckKind,
    },
    Proof,
}

impl Substitutable for TmKind {
    type Output = ValTm;

    fn subst(self, subst: &mut Subst) -> ValTm {
        match self {
            TmKind::Intro { intro } => {
                intro.subst(subst).map(|intro| TmKind::Intro { intro })
            },
            TmKind::Proof => Weaken::new(TmKind::Proof),
            TmKind::Stuck { stuck } => {
                stuck.subst(subst)
            },
        }
    }

    fn into_output(self) -> ValTm {
        Weaken::new(self)
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<TmKind> {
        let tm_kind = match self {
            TmKind::Intro { intro } => {
                let intro = intro.try_strengthen_index(var_index)?;
                TmKind::Intro { intro }
            },
            TmKind::Proof => TmKind::Proof,
            TmKind::Stuck { stuck } => {
                let stuck = stuck.try_strengthen_index(var_index)?;
                TmKind::Stuck { stuck }
            },
        };
        Some(tm_kind)
    }
}

impl Tm {
    pub fn try_reduce_to_intro_assuming_relevant(self) -> Option<Intro> {
        let (usages, tm_kind) = self.reduced().into_usages_and_weak();
        match tm_kind {
            TmKind::Intro { intro } => {
                Some(Weaken::from_usages_and_weak(usages, intro))
            },
            TmKind::Proof => unreachable!(),
            TmKind::Stuck { .. } => None,
        }
    }

    pub fn into_name(self) -> Name {
        self.reduced().map(|tm_kind| OrLazy::Reduced(tm_kind.into_name_kind()))
    }

    pub fn into_ty(self) -> Ty {
        self.reduced().map(|tm_kind| OrLazy::Reduced(tm_kind.into_ty_kind()))
    }

    pub fn var(index: usize) -> Tm {
        Stuck::var(index).into_tm()
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
        let (usages, lazy_tm_kind) = self.into_usages_and_weak();

        let intro_kind = match lazy_tm_kind {
            OrLazy::Reduced(tm_kind) => {
                match tm_kind {
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
                    TmKind::Proof => unreachable!(),
                    TmKind::Stuck { stuck } => {
                        let pred_tm = OrLazy::Reduced(TmKind::Stuck { stuck });
                        IntroKind::Succs { succ_count_m1, pred_tm }
                    },
                }
            },
            OrLazy::Lazy(lazy) => {
                IntroKind::Succs { succ_count_m1, pred_tm: OrLazy::Lazy(lazy) }
            },
        };
        let tm_kind = TmKind::Intro { intro: Arc::new(intro_kind) };
        Weaken::from_usages_and_weak(usages, OrLazy::Reduced(tm_kind))
    }

    pub fn fold(
        self,
        motive: Scope<Ty>,
        zero_inhab: Tm,
        succ_inhab: Scope<Scope<Tm>>,
    ) -> Tm {
        Lazy::fold(self, motive, zero_inhab, succ_inhab).into_tm()
    }

    pub fn explode(
        motive: Scope<Ty>,
    ) -> Tm {
        Lazy::explode(motive).into_tm()
    }

    pub fn inj_lhs(self) -> Tm {
        Intro::inj_lhs(self).into_tm()
    }

    pub fn inj_rhs(self) -> Tm {
        Intro::inj_rhs(self).into_tm()
    }

    pub fn case(
        self,
        lhs_name: Name,
        motive: Scope<Ty>,
        lhs_inhab: Scope<Tm>,
        rhs_inhab: Scope<Tm>,
    ) -> Tm {
        Lazy::case(self, lhs_name, motive, lhs_inhab, rhs_inhab).into_tm()
    }

    pub fn pair(self, tail_tm: Tm) -> Tm {
        Intro::pair(self, tail_tm).into_tm()
    }

    pub fn proj_head(self) -> Tm {
        Lazy::proj_head(self).into_tm()
    }

    pub fn proj_tail(self) -> Tm {
        Lazy::proj_tail(self).into_tm()
    }

    pub fn func_eta_short(res_tm: Scope<Tm>) -> Tm {
        let ctx_len = res_tm.ctx_len();
        if let TmKind::Stuck { stuck } = res_tm.inner_ref().clone().reduced().into_inner()
        && let NeutralKind::App { elim, arg_tm } = Arc::unwrap_or_clone(stuck.into_neutral())
        && let TmKind::Stuck { stuck } = arg_tm.reduced().into_inner()
        && let Some(_) = Unify::unify(stuck, StuckKind::var(ctx_len))
        && let Some(elim) = elim.try_strengthen_index(ctx_len)
        {
            elim
        } else {
            Tm::func(res_tm)
        }
    }

    pub fn func(res_tm: Scope<Tm>) -> Tm {
        Intro::func(res_tm).into_tm()
    }

    pub fn app(self, arg_tm: Tm) -> Tm {
        Lazy::app(self, arg_tm).into_tm()
    }

    pub fn cast(ty_0: Ty, ty_1: Ty, tm_0: Tm) -> Tm {
        Lazy::cast(ty_0, ty_1, tm_0).into_tm()
    }

    pub fn proof() -> Tm {
        Weaken::new(OrLazy::Reduced(TmKind::Proof))
    }

    pub fn as_var(&self) -> Option<usize> {
        let index = self.weak().clone().reduced().as_var()?;
        Some(self.usages().unfilter_index(index))
    }

    pub fn as_tag(self) -> Option<Tag> {
        let tm = self.reduced().into_weak();
        match tm {
            TmKind::Intro { intro } => Arc::unwrap_or_clone(intro).as_tag(),
            TmKind::Proof => None,
            TmKind::Stuck { .. } => None,
        }
    }

    pub fn as_intro(self) -> Option<Intro> {
        self.reduced().try_map(|tm_kind| tm_kind.as_intro())
    }

    pub fn as_stuck(self) -> Option<Stuck> {
        self.reduced().try_map(|tm_kind| tm_kind.as_stuck())
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
            TmKind::Proof => unreachable!(),
            TmKind::Stuck { stuck } => NameKind::Stuck { stuck }
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
            TmKind::Proof => unreachable!(),
            TmKind::Stuck { stuck } => TyKind::Stuck { stuck },
        }
    }

    pub fn as_intro(self) -> Option<Arc<IntroKind>> {
        match self {
            TmKind::Intro { intro } => Some(intro),
            TmKind::Proof => None,
            TmKind::Stuck { .. } => None,
        }
    }

    pub fn as_intro_assuming_relevant(self) -> Option<Arc<IntroKind>> {
        match self {
            TmKind::Intro { intro } => Some(intro),
            TmKind::Proof => unreachable!(),
            TmKind::Stuck { .. } => None,
        }
    }

    pub fn as_stuck(self) -> Option<StuckKind> {
        match self {
            TmKind::Intro { .. } => None,
            TmKind::Proof => None,
            TmKind::Stuck { stuck } => Some(stuck),
        }
    }

    pub fn as_var(self) -> Option<usize> {
        match self {
            TmKind::Intro { .. } => None,
            TmKind::Proof => None,
            TmKind::Stuck { stuck } => stuck.as_var(),
        }
    }
}

impl ValTm {
    pub fn into_tm(self) -> Tm {
        self.map(|tm_kind| OrLazy::Reduced(tm_kind))
    }

    pub fn into_val_ty(self) -> ValTy {
        self.map(|tm_kind| tm_kind.into_ty_kind())
    }

    pub fn as_stuck(self) -> Option<Stuck> {
        self.try_map(|tm_kind| tm_kind.as_stuck())
    }

    pub fn as_var(self) -> Option<usize> {
        self.into_inner().as_var()
    }

    pub fn proof() -> ValTm {
        Weaken::new(TmKind::Proof)
    }
}

impl Unify for TmKind {
    fn unify(
        tm_kind_0: TmKind,
        tm_kind_1: TmKind,
    ) -> Option<TmKind> {
        fn unify_intro_and_stuck(
            intro: IntroKind,
            stuck: StuckKind,
        ) -> Option<TmKind> {
            let tm_kind_1 = TmKind::Stuck { stuck };
            match intro {
                IntroKind::Pair { head_tm: head_tm_0, tail_tm: tail_tm_0 } => {
                    let tm_1 = Weaken::new(OrLazy::Reduced(tm_kind_1.clone()));
                    let head_tm_1 = tm_1.clone().proj_head();
                    let tail_tm_1 = tm_1.proj_tail();

                    let _head_tm = Unify::unify(head_tm_0, head_tm_1)?;
                    let _tail_tm = Unify::unify(tail_tm_0, tail_tm_1)?;
                    Some(tm_kind_1)
                },
                IntroKind::Func { res_tm: res_tm_0 } => {
                    let tm_1 = Weaken::new(OrLazy::Reduced(tm_kind_1.clone()));
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

            (TmKind::Intro { intro }, TmKind::Stuck { stuck }) => {
                unify_intro_and_stuck(Arc::unwrap_or_clone(intro), stuck)
            },

            (TmKind::Stuck { stuck }, TmKind::Intro { intro }) => {
                unify_intro_and_stuck(Arc::unwrap_or_clone(intro), stuck)
            },
            
            (TmKind::Stuck { stuck: stuck_0 }, TmKind::Stuck { stuck: stuck_1 }) => {
                let stuck = Unify::unify(stuck_0, stuck_1)?;
                Some(TmKind::Stuck { stuck })
            },
        }
    }
}

impl DeepNf for TmKind {
    type Output = ValTm;

    fn deep_nf(self) -> ValTm {
        match self {
            TmKind::Intro { intro } => {
                intro.deep_nf().map(|intro| TmKind::Intro { intro })
            },
            TmKind::Proof => Weaken::new(TmKind::Proof),
            TmKind::Stuck { stuck } => {
                stuck.deep_nf().map(|stuck| TmKind::Stuck { stuck })
            },
        }
    }
}

impl TryUnswapVars for TmKind {
    fn try_unswap_vars(
        self,
        var_index: usize,
    ) -> Option<TmKind> {
        let tm_kind = match self {
            TmKind::Intro { intro } => {
                let intro = intro.try_unswap_vars(var_index)?;
                TmKind::Intro { intro }
            },
            TmKind::Proof => TmKind::Proof,
            TmKind::Stuck { stuck } => {
                let stuck = stuck.try_unswap_vars(var_index)?;
                TmKind::Stuck { stuck }
            },
        };
        Some(tm_kind)
    }
}

