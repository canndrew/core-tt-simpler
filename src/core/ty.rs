use crate::priv_prelude::*;

pub type Ty = Weaken<TyKind>;

#[derive(Clone, Debug, Contextual)]
pub enum TyKind {
    Form {
        form: Arc<FormKind>,
    },
    Neutral {
        neutral: Arc<NeutralData>,
    },
}

impl Ty {
    pub fn into_tm(self) -> Tm {
        self.map(TyKind::into_tm_kind)
    }

    pub fn reduced(self) -> Ty {
        match &self.weak {
            TyKind::Form { .. } => self,
            TyKind::Neutral { neutral } => {
                match neutral.try_reduce() {
                    None => self,
                    Some(new_tm) => new_tm.unfiltered(&self.usages).into_ty(),
                }
            },
        }
    }

    pub fn try_reduce_to_form(self) -> Option<Form> {
        match self.weak {
            TyKind::Form { form } => {
                Some(Weaken { usages: self.usages, weak: form })
            },
            TyKind::Neutral { neutral } => {
                let intro = neutral.try_reduce_to_intro()?;
                Some(intro.unfiltered(&self.usages).into_form())
            },
        }
    }

    pub fn name() -> Ty {
        Form::name().into_ty()
    }

    pub fn universe() -> Ty {
        Form::universe().into_ty()
    }

    pub fn nat() -> Ty {
        Form::nat().into_ty()
    }

    pub fn equal(eq_ty: Ty, eq_tm_0: Tm, eq_tm_1: Tm) -> Ty {
        Form::equal(eq_ty, eq_tm_0, eq_tm_1).into_ty()
    }

    pub fn never() -> Ty {
        Form::never().into_ty()
    }

    pub fn unit() -> Ty {
        Form::unit().into_ty()
    }

    pub fn sum(lhs_name: Name, lhs_ty: Ty, rhs_ty: Ty) -> Ty {
        Form::sum(lhs_name, lhs_ty, rhs_ty).into_ty()
    }

    pub fn sigma(head_name: Name, head_ty: Ty, tail_ty: Scope<Ty>) -> Ty {
        Form::sigma(head_name, head_ty, tail_ty).into_ty()
    }

    pub fn pi(arg_name: Name, arg_ty: Ty, res_ty: Scope<Ty>) -> Ty {
        Form::pi(arg_name, arg_ty, res_ty).into_ty()
    }

    pub fn as_name(self) -> Option<()> {
        let form = self.try_reduce_to_form()?;
        form.as_name()
    }

    pub fn as_universe(self) -> Option<()> {
        let form = self.try_reduce_to_form()?;
        form.as_universe()
    }

    pub fn as_nat(self) -> Option<()> {
        let form = self.try_reduce_to_form()?;
        form.as_nat()
    }

    pub fn as_equal(self) -> Option<(Ty, Tm, Tm)> {
        let form = self.try_reduce_to_form()?;
        form.as_equal()
    }

    pub fn as_never(self) -> Option<()> {
        let form = self.try_reduce_to_form()?;
        form.as_never()
    }

    pub fn as_unit(self) -> Option<()> {
        let form = self.try_reduce_to_form()?;
        form.as_unit()
    }

    pub fn as_sum(self) -> Option<(Name, Ty, Ty)> {
        let form = self.try_reduce_to_form()?;
        form.as_sum()
    }

    pub fn as_sigma(self) -> Option<(Name, Ty, Scope<Ty>)> {
        let form = self.try_reduce_to_form()?;
        form.as_sigma()
    }

    pub fn as_pi(self) -> Option<(Name, Ty, Scope<Ty>)> {
        let form = self.try_reduce_to_form()?;
        form.as_pi()
    }
}

impl TyKind {
    pub fn into_tm_kind(self) -> TmKind {
        match self {
            TyKind::Form { form } => {
                let intro = Arc::new(IntroKind::Form { form });
                TmKind::Intro { intro }
            },
            TyKind::Neutral { neutral } => {
                TmKind::Neutral { neutral }
            },
        }
    }
}

impl Bindable for Ty {
    fn capture_subst(self, subst: Subst) -> Ty {
        let tm = self.into_tm();
        let tm = tm.capture_subst(subst);
        tm.into_ty()
    }
}

impl Unify for TyKind {
    fn unify(ty_kind_0: TyKind, ty_kind_1: TyKind) -> Option<TyKind> {
        match (ty_kind_0, ty_kind_1) {
            (TyKind::Form { form: form_0 }, TyKind::Form { form: form_1 }) => {
                let form = Unify::unify(form_0, form_1)?;
                Some(TyKind::Form { form })
            },

            (TyKind::Form { form: form_0 }, TyKind::Neutral { neutral }) => {
                let intro_1 = neutral.try_reduce_to_intro()?.into_inner();
                let intro_1 = Arc::unwrap_or_clone(intro_1);
                let IntroKind::Form { form: form_1 } = intro_1 else {
                    unreachable!();
                };
                let form = Unify::unify(form_0, form_1)?;
                Some(TyKind::Form { form })
            },

            (TyKind::Neutral { neutral }, TyKind::Form { form: form_1 }) => {
                let intro_0 = neutral.try_reduce_to_intro()?.into_inner();
                let intro_0 = Arc::unwrap_or_clone(intro_0);
                let IntroKind::Form { form: form_0 } = intro_0 else {
                    unreachable!();
                };
                let form = Unify::unify(form_0, form_1)?;
                Some(TyKind::Form { form })
            },
            
            (TyKind::Neutral { neutral: neutral_0 }, TyKind::Neutral { neutral: neutral_1 }) => {
                if Arc::ptr_eq(&neutral_0, &neutral_1) {
                    return Some(TyKind::Neutral { neutral: neutral_0 });
                }
                match (neutral_0.try_reduce(), neutral_1.try_reduce()) {
                    (None, None) => {
                        let neutral_0 = Arc::unwrap_or_clone(neutral_0);
                        let neutral_1 = Arc::unwrap_or_clone(neutral_1);
                        let kind = Unify::unify(neutral_0.kind, neutral_1.kind)?;
                        let neutral = NeutralData::new_arc(kind);
                        Some(TyKind::Neutral { neutral })
                    },
                    (None, Some(tm_1)) => {
                        match tm_1.into_inner() {
                            TmKind::Intro { .. } => None,
                            TmKind::Neutral { neutral: neutral_1 } => {
                                let neutral = NeutralData::unify_without_cached_reduction(
                                    neutral_0,
                                    neutral_1,
                                )?;
                                Some(TyKind::Neutral { neutral })
                            },
                        }
                    },
                    (Some(tm_0), None) => {
                        match tm_0.into_inner() {
                            TmKind::Intro { .. } => None,
                            TmKind::Neutral { neutral: neutral_0 } => {
                                let neutral = NeutralData::unify_without_cached_reduction(
                                    neutral_0,
                                    neutral_1,
                                )?;
                                Some(TyKind::Neutral { neutral })
                            },
                        }
                    },
                    (Some(tm_0), Some(tm_1)) => {
                        let tm = Unify::unify(tm_0.clone(), tm_1.clone())?;
                        Some(tm.into_inner().into_ty_kind())
                    },
                }
            },
        }
    }
}

impl Substitutable for Ty {
    type Output = Ty;

    fn subst(self, subst: &mut Subst) -> Ty {
        if self.usages.ctx_len() <= subst.subst_index() {
            return self;
        }
        self.into_inner().subst(subst)
    }

    fn into_output(self) -> Ty {
        self
    }
}

impl Substitutable for TyKind {
    type Output = Ty;

    fn subst(self, subst: &mut Subst) -> Ty {
        match self {
            TyKind::Form { form } => {
                let form = form.subst(subst);
                Weaken::new(TyKind::Form { form })
            },
            TyKind::Neutral { neutral } => {
                neutral.subst(subst).into_ty()
            },
        }
    }

    fn into_output(self) -> Ty {
        Weaken::new(self)
    }
}

