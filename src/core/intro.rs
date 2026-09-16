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
        pred_tm: Arc<NeutralData>,
    },
    InjLhs {
        lhs_tm: TmKind,
    },
    InjRhs {
        rhs_tm: TmKind,
    },
    Pair {
        head_tm: Tm,
        tail_tm: Tm,
    },
    Func {
        res_tm: Scope<TmKind>,
    },
}

impl Unify for IntroKind {
    type Meta = Ty;

    fn unify(
        ctx_tys: &mut Vec<Ty>,
        ty: Ty,
        intro_kind_0: IntroKind,
        intro_kind_1: IntroKind,
    ) -> Option<IntroKind> {
        // TODO: do I still need to do this now that I have TmKind::Proof? Or can we avoid calling
        // this in the first place?
        if ty.is_prop() {
            return Some(intro_kind_0);
        }

        match (intro_kind_0, intro_kind_1) {
            (IntroKind::Tag { tag: tag_0 }, IntroKind::Tag { tag: tag_1 }) => {
                let tag = as_equal(tag_0, &tag_1)?;
                Some(IntroKind::Tag { tag })
            },
            
            (IntroKind::Form { form: form_0 }, IntroKind::Form { form: form_1 }) => {
                let form = Unify::unify(ctx_tys, (), form_0, form_1)?;
                Some(IntroKind::Form { form })
            },

            (IntroKind::Constant { ubig: ubig_0 }, IntroKind::Constant { ubig: ubig_1 }) => {
                let ubig = as_equal(ubig_0, &ubig_1)?;
                Some(IntroKind::Constant { ubig })
            },

            (
                IntroKind::Succs { succ_count_m1: mut succ_count_m1_0, pred_tm: mut pred_tm_0 },
                IntroKind::Succs { succ_count_m1: mut succ_count_m1_1, pred_tm: mut pred_tm_1 },
            ) => {
                let (succ_count_m1_0, pred_tm_opt_0) = loop {
                    match pred_tm_0.try_reduce() {
                        None => break (succ_count_m1_0, Some(Arc::unwrap_or_clone(pred_tm_0))),
                        Some(tm_0) => match tm_0.into_inner() {
                            TmKind::Intro { intro: intro_0 } => {
                                let intro_0 = Arc::unwrap_or_clone(intro_0);
                                match intro_0 {
                                    IntroKind::Constant { ubig } => {
                                        succ_count_m1_0 += ubig;
                                        break (succ_count_m1_0, None);
                                    },
                                    IntroKind::Succs {
                                        succ_count_m1: additional,
                                        pred_tm: new_pred_tm_0,
                                    } => {
                                        succ_count_m1_0 += additional + 1usize;
                                        pred_tm_0 = new_pred_tm_0;
                                    },
                                    _ => unreachable!(),
                                }
                            },
                            TmKind::Neutral { neutral: pred_tm_0 } => {
                                let pred_tm_0 = Arc::unwrap_or_clone(pred_tm_0);
                                break (succ_count_m1_0, Some(pred_tm_0));
                            },
                            TmKind::Proof => unreachable!(),
                        }
                    }
                };
                let (succ_count_m1_1, pred_tm_opt_1) = loop {
                    match pred_tm_1.try_reduce() {
                        None => break (succ_count_m1_1, Some(Arc::unwrap_or_clone(pred_tm_1))),
                        Some(tm_1) => match tm_1.into_inner() {
                            TmKind::Intro { intro: intro_1 } => {
                                let intro_1 = Arc::unwrap_or_clone(intro_1);
                                match intro_1 {
                                    IntroKind::Constant { ubig } => {
                                        succ_count_m1_1 += ubig;
                                        break (succ_count_m1_1, None);
                                    },
                                    IntroKind::Succs {
                                        succ_count_m1: additional,
                                        pred_tm: new_pred_tm_1,
                                    } => {
                                        succ_count_m1_1 += additional + 1usize;
                                        pred_tm_1 = new_pred_tm_1;
                                    },
                                    _ => unreachable!(),
                                }
                            },
                            TmKind::Neutral { neutral: pred_tm_1 } => {
                                let pred_tm_1 = Arc::unwrap_or_clone(pred_tm_1);
                                break (succ_count_m1_1, Some(pred_tm_1));
                            },
                            TmKind::Proof => unreachable!(),
                        }
                    }
                };
                let succ_count_m1 = as_equal(succ_count_m1_0, &succ_count_m1_1)?;
                match (pred_tm_opt_0, pred_tm_opt_1) {
                    (None, None) => {
                        let ubig = succ_count_m1 + 1usize;
                        Some(IntroKind::Constant { ubig })
                    },
                    (None, Some(_)) | (Some(_), None) => None,
                    (Some(pred_tm_0), Some(pred_tm_1)) => {
                        let kind = Unify::unify(ctx_tys, (), pred_tm_0.kind, pred_tm_1.kind)?;
                        let pred_tm = NeutralData::new_arc(kind);
                        Some(IntroKind::Succs { succ_count_m1, pred_tm })
                    },
                }
            },

            (
                IntroKind::Constant { ubig: ubig_0 },
                IntroKind::Succs { mut succ_count_m1, mut pred_tm },
            ) => {
                loop {
                    let intro = pred_tm.try_reduce_to_intro_assuming_relevant()?;
                    match &**intro.weak() {
                        IntroKind::Constant { ubig: additional } => {
                            let ubig_1 = succ_count_m1 + additional + 1usize;
                            let ubig = as_equal(ubig_0, &ubig_1)?;
                            break Some(IntroKind::Constant { ubig });
                        },
                        IntroKind::Succs { succ_count_m1: additional, pred_tm: new_pred_tm } => {
                            succ_count_m1 += additional + 1usize;
                            pred_tm = new_pred_tm.clone();
                        },
                        _ => unreachable!(),
                    }
                }
            },

            (
                IntroKind::Succs { mut succ_count_m1, mut pred_tm },
                IntroKind::Constant { ubig: ubig_1 },
            ) => {
                loop {
                    let intro = pred_tm.try_reduce_to_intro_assuming_relevant()?;
                    match &**intro.weak() {
                        IntroKind::Constant { ubig: additional } => {
                            let ubig_0 = succ_count_m1 + additional + 1usize;
                            let ubig = as_equal(ubig_0, &ubig_1)?;
                            break Some(IntroKind::Constant { ubig });
                        },
                        IntroKind::Succs { succ_count_m1: additional, pred_tm: new_pred_tm } => {
                            succ_count_m1 += additional + 1usize;
                            pred_tm = new_pred_tm.clone();
                        },
                        _ => unreachable!(),
                    }
                }
            },

            (IntroKind::InjLhs { lhs_tm: lhs_tm_0 }, IntroKind::InjLhs { lhs_tm: lhs_tm_1 }) => {
                let (_lhs_name, lhs_ty, _rhs_ty) = ty.as_sum().unwrap();
                let lhs_tm = Unify::unify(ctx_tys, lhs_ty, lhs_tm_0, lhs_tm_1)?;
                Some(IntroKind::InjLhs { lhs_tm })
            },

            (IntroKind::InjRhs { rhs_tm: rhs_tm_0 }, IntroKind::InjRhs { rhs_tm: rhs_tm_1 }) => {
                let (_lhs_name, _lhs_ty, rhs_ty) = ty.as_sum().unwrap();
                let rhs_tm = Unify::unify(ctx_tys, rhs_ty, rhs_tm_0, rhs_tm_1)?;
                Some(IntroKind::InjRhs { rhs_tm })
            },

            (
                IntroKind::Pair { head_tm: head_tm_0, tail_tm: tail_tm_0 },
                IntroKind::Pair { head_tm: head_tm_1, tail_tm: tail_tm_1 },
            ) => {
                let (_head_name, head_ty, tail_ty) = ty.as_sigma().unwrap();
                let head_tm = Unify::unify(ctx_tys, head_ty, head_tm_0, head_tm_1)?;
                let tail_tm = Unify::unify(ctx_tys, tail_ty.bind(head_tm.clone()), tail_tm_0, tail_tm_1)?;
                Some(IntroKind::Pair { head_tm, tail_tm })
            },

            (IntroKind::Func { res_tm: res_tm_0 }, IntroKind::Func { res_tm: res_tm_1 }) => {
                let (_arg_name, arg_ty, res_ty) = ty.as_pi().unwrap();
                let res_tm = Unify::unify(ctx_tys, (arg_ty, res_ty), res_tm_0, res_tm_1)?;
                Some(IntroKind::Func { res_tm })
            },

            _ => None,
        }
    }
}

impl Intro {
    pub fn into_tm(self) -> Tm {
        self.map(|intro| TmKind::Intro { intro })
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
            TmKind::Neutral { neutral } => {
                IntroKind::Succs { succ_count_m1, pred_tm: neutral }
            },
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

    pub fn as_succs_m1(self) -> Option<(Ubig, Neutral)> {
        let (usages, intro_kind) = self.into_usages_and_weak();
        let (succ_count_m1, pred_tm) = Arc::unwrap_or_clone(intro_kind).as_succs_m1()?;
        let pred_tm = Weaken::from_usages_and_weak(usages, pred_tm);
        Some((succ_count_m1, pred_tm))
    }

    pub fn as_inj_lhs(self) -> Option<Tm> {
        self.try_map(|intro_kind| {
            Arc::unwrap_or_clone(intro_kind).as_inj_lhs()
        })
    }

    pub fn as_inj_rhs(self) -> Option<Tm> {
        self.try_map(|intro_kind| {
            Arc::unwrap_or_clone(intro_kind).as_inj_rhs()
        })
    }

    pub fn as_pair(self) -> Option<(Tm, Tm)> {
        self.map_out_unfiltered(|intro| Arc::unwrap_or_clone(intro).as_pair())
    }

    pub fn as_func(self) -> Option<Scope<Tm>> {
        let res_tm = self.try_map(|intro_kind| {
            Arc::unwrap_or_clone(intro_kind).as_func()
        })?;
        Some(res_tm.lift_scope())
    }

    pub fn deep_nf(self) -> Intro {
        self.map_out_unfiltered(|intro_kind| {
            Arc::unwrap_or_clone(intro_kind).deep_nf()
        })
    }
}

impl IntroKind {
    pub fn into_form_kind(self) -> Arc<FormKind> {
        self.as_form().unwrap().clone()
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

    pub fn as_succs_m1(self) -> Option<(Ubig, Arc<NeutralData>)> {
        let IntroKind::Succs { succ_count_m1, pred_tm } = self else {
            return None;
        };
        Some((succ_count_m1, pred_tm))
    }

    pub fn as_inj_lhs(self) -> Option<TmKind> {
        let IntroKind::InjLhs { lhs_tm } = self else {
            return None;
        };
        Some(lhs_tm)
    }

    pub fn as_inj_rhs(self) -> Option<TmKind> {
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

    pub fn as_func(self) -> Option<Scope<TmKind>> {
        let IntroKind::Func { res_tm } = self else {
            return None;
        };
        Some(res_tm)
    }

    pub fn deep_nf(self) -> Intro {
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
                let pred_tm = Arc::unwrap_or_clone(pred_tm).deep_nf();
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
                    TmKind::Neutral { neutral: pred_tm } => {
                        IntroKind::Succs { succ_count_m1, pred_tm }
                    },
                    TmKind::Proof => unreachable!(),
                };
                Weaken::from_usages_and_weak(usages, Arc::new(intro_kind))
            },

            IntroKind::InjLhs { lhs_tm } => {
                lhs_tm
                .deep_nf()
                .map(|lhs_tm| Arc::new(IntroKind::InjLhs { lhs_tm }))
            },

            IntroKind::InjRhs { rhs_tm } => {
                rhs_tm
                .deep_nf()
                .map(|rhs_tm| Arc::new(IntroKind::InjRhs { rhs_tm }))
            },

            IntroKind::Pair { head_tm, tail_tm } => {
                let head_tm = head_tm.deep_nf();
                let tail_tm = tail_tm.deep_nf();
                Weaken::new_arc(IntroKind::Pair { head_tm, tail_tm })
            },

            IntroKind::Func { res_tm } => {
                res_tm
                .map_without_capture(|res_tm| res_tm.deep_nf())
                .lift_weaken()
                .map(|res_tm| Arc::new(IntroKind::Func { res_tm }))
            },
        }
    }
}

impl Substitutable for Intro {
    type Output = Intro;

    fn subst(self, subst: &mut Subst) -> Intro {
        if self.ctx_len() <= subst.subst_index() {
            return self;
        }
        self.into_inner().subst(subst)
    }

    fn into_output(self) -> Intro {
        self
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<Intro> {
        Some(self.do_try_strengthen_index(var_index)?.flatten())
    }
}

impl Substitutable for Arc<IntroKind> {
    type Output = Intro;

    fn subst(self, subst: &mut Subst) -> Intro {
        let intro_kind = Arc::unwrap_or_clone(self);
        intro_kind.subst(subst)
    }

    fn into_output(self) -> Intro {
        Weaken::new(self)
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<Intro> {
        let intro_kind = Arc::unwrap_or_clone(self);
        intro_kind.try_strengthen_index(var_index)
    }
}

impl Substitutable for IntroKind {
    type Output = Intro;

    fn subst(self, subst: &mut Subst) -> Intro {
        match self {
            IntroKind::Tag { tag } => {
                Weaken::new_arc(IntroKind::Tag { tag })
            },

            IntroKind::Form { form } => {
                let form = form.subst(subst);
                Weaken::new_arc(IntroKind::Form { form })
            },

            IntroKind::Constant { ubig } => {
                Weaken::new_arc(IntroKind::Constant { ubig })
            },

            IntroKind::Succs { succ_count_m1, pred_tm } => {
                let pred_tm = pred_tm.subst(subst);
                match pred_tm.into_inner() {
                    TmKind::Intro { intro } => {
                        let intro = Arc::unwrap_or_clone(intro);
                        match intro {
                            IntroKind::Constant { ubig } => {
                                let ubig = succ_count_m1 + ubig + 1usize;
                                Weaken::new_arc(IntroKind::Constant { ubig })
                            },
                            IntroKind::Succs { succ_count_m1: additional, pred_tm } => {
                                let succ_count_m1 = succ_count_m1 + additional + 1usize;
                                Weaken::new_arc(IntroKind::Succs { succ_count_m1, pred_tm })
                            },
                            _ => unreachable!(),
                        }
                    },
                    TmKind::Neutral { neutral: pred_tm } => {
                        Weaken::new_arc(IntroKind::Succs { succ_count_m1, pred_tm })
                    },
                    TmKind::Proof => unreachable!(),
                }
            },

            IntroKind::InjLhs { lhs_tm } => {
                lhs_tm.subst(subst).map(|lhs_tm| Arc::new(IntroKind::InjLhs { lhs_tm }))
            },

            IntroKind::InjRhs { rhs_tm } => {
                rhs_tm.subst(subst).map(|rhs_tm| Arc::new(IntroKind::InjRhs { rhs_tm }))
            },

            IntroKind::Pair { head_tm, tail_tm } => {
                let head_tm = head_tm.subst(subst);
                let tail_tm = tail_tm.subst(subst);
                Weaken::new_arc(IntroKind::Pair { head_tm, tail_tm })
            },

            IntroKind::Func { res_tm } => {
                res_tm
                .map_without_capture(Weaken::new)
                .subst(subst)
                .lift_weaken()
                .map(|res_tm| Arc::new(IntroKind::Func { res_tm }))
            },
        }
    }

    fn into_output(self) -> Intro {
        Weaken::new_arc(self)
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<Intro> {
        let intro = match self {
            IntroKind::Tag { tag } => {
                Weaken::new_arc(IntroKind::Tag { tag })
            },

            IntroKind::Form { form } => {
                let form = form.try_strengthen_index(var_index)?;
                Weaken::new_arc(IntroKind::Form { form })
            },

            IntroKind::Constant { ubig } => {
                Weaken::new_arc(IntroKind::Constant { ubig })
            },

            IntroKind::Succs { succ_count_m1, pred_tm } => {
                let pred_tm = pred_tm.try_strengthen_index(var_index)?;
                Intro::succs_m1(pred_tm, succ_count_m1)
            },

            IntroKind::InjLhs { lhs_tm } => {
                lhs_tm
                .try_strengthen_index(var_index)?
                .map(|lhs_tm| Arc::new(IntroKind::InjLhs { lhs_tm }))
            },

            IntroKind::InjRhs { rhs_tm } => {
                rhs_tm
                .try_strengthen_index(var_index)?
                .map(|rhs_tm| Arc::new(IntroKind::InjRhs { rhs_tm }))
            },

            IntroKind::Pair { head_tm, tail_tm } => {
                let head_tm = head_tm.try_strengthen_index(var_index)?;
                let tail_tm = tail_tm.try_strengthen_index(var_index)?;
                Weaken::new_arc(IntroKind::Pair { head_tm, tail_tm })
            },

            IntroKind::Func { res_tm } => {
                res_tm
                .map_without_capture(Weaken::new)
                .try_strengthen_index(var_index)?
                .lift_weaken()
                .map(|res_tm| Arc::new(IntroKind::Func { res_tm }))
            },
        };
        Some(intro)
    }
}

