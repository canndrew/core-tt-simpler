use crate::priv_prelude::*;

pub type Form = Weaken<Arc<FormKind>>;

#[derive(Clone, Debug, Contextual)]
pub enum FormKind {
    Name,
    Universe,
    Nat,
    Equal {
        eq_ty: Ty,
        eq_tm_0: Tm,
        eq_tm_1: Tm,
    },
    Never,
    Unit,
    Sum {
        lhs_name: Name,
        lhs_ty: Ty,
        rhs_ty: Ty,
    },
    Sigma {
        head_name: Name,
        head_ty: Ty,
        tail_ty: Scope<Ty>,
    },
    Pi {
        arg_name: Name,
        arg_ty: Ty,
        res_ty: Scope<Ty>,
    },
}

impl Unify for FormKind {
    type Meta = ();

    fn unify(
        ctx_tys: &mut Vec<Ty>,
        (): (),
        form_kind_0: FormKind,
        form_kind_1: FormKind,
    ) -> Option<FormKind> {
        match (form_kind_0, form_kind_1) {
            (FormKind::Name, FormKind::Name) => Some(FormKind::Name),

            (FormKind::Universe, FormKind::Universe) => Some(FormKind::Universe),

            (FormKind::Nat, FormKind::Nat) => Some(FormKind::Nat),

            (
                FormKind::Equal { eq_ty: eq_ty_0, eq_tm_0: eq_tm_0_0, eq_tm_1: eq_tm_1_0 },
                FormKind::Equal { eq_ty: eq_ty_1, eq_tm_0: eq_tm_0_1, eq_tm_1: eq_tm_1_1 },
            ) => {
                let eq_ty = Unify::unify(ctx_tys, (), eq_ty_0, eq_ty_1)?;
                let eq_tm_0 = Unify::unify(ctx_tys, eq_ty.clone(), eq_tm_0_0, eq_tm_0_1)?;
                let eq_tm_1 = Unify::unify(ctx_tys, eq_ty.clone(), eq_tm_1_0, eq_tm_1_1)?;
                Some(FormKind::Equal { eq_ty, eq_tm_0, eq_tm_1 })
            },

            (FormKind::Never, FormKind::Never) => Some(FormKind::Never),

            (FormKind::Unit, FormKind::Unit) => Some(FormKind::Unit),

            (
                FormKind::Sum { lhs_name: lhs_name_0, lhs_ty: lhs_ty_0, rhs_ty: rhs_ty_0 },
                FormKind::Sum { lhs_name: lhs_name_1, lhs_ty: lhs_ty_1, rhs_ty: rhs_ty_1 },
            ) => {
                let lhs_name = Unify::unify(ctx_tys, (), lhs_name_0, lhs_name_1)?;
                let lhs_ty = Unify::unify(ctx_tys, (), lhs_ty_0, lhs_ty_1)?;
                let rhs_ty = Unify::unify(ctx_tys, (), rhs_ty_0, rhs_ty_1)?;
                Some(FormKind::Sum { lhs_name, lhs_ty, rhs_ty })
            },

            (
                FormKind::Sigma { head_name: head_name_0, head_ty: head_ty_0, tail_ty: tail_ty_0 },
                FormKind::Sigma { head_name: head_name_1, head_ty: head_ty_1, tail_ty: tail_ty_1 },
            ) => {
                let head_name = Unify::unify(ctx_tys, (), head_name_0, head_name_1)?;
                let head_ty = Unify::unify(ctx_tys, (), head_ty_0, head_ty_1)?;
                let tail_ty = Unify::unify(
                    ctx_tys, (head_ty.clone(), Scope::constant(())), tail_ty_0, tail_ty_1,
                )?;
                Some(FormKind::Sigma { head_name, head_ty, tail_ty })
            },

            (
                FormKind::Pi { arg_name: arg_name_0, arg_ty: arg_ty_0, res_ty: res_ty_0 },
                FormKind::Pi { arg_name: arg_name_1, arg_ty: arg_ty_1, res_ty: res_ty_1 },
            ) => {
                let arg_name = Unify::unify(ctx_tys, (), arg_name_0, arg_name_1)?;
                let arg_ty = Unify::unify(ctx_tys, (), arg_ty_0, arg_ty_1)?;
                let res_ty = Unify::unify(
                    ctx_tys, (arg_ty.clone(), Scope::constant(())), res_ty_0, res_ty_1,
                )?;
                Some(FormKind::Pi { arg_name, arg_ty, res_ty })
            },

            _ => None,
        }
    }
}

impl Substitutable for Form {
    type Output = Form;

    fn subst(self, subst: &mut Subst) -> Form {
        if self.usages.ctx_len() <= subst.subst_index() {
            return self;
        }
        Weaken::new(self.into_inner().subst(subst))
    }

    fn into_output(self) -> Form {
        self
    }
}

impl Substitutable for Arc<FormKind> {
    type Output = Arc<FormKind>;

    fn subst(self, subst: &mut Subst) -> Arc<FormKind> {
        let intro_kind = Arc::unwrap_or_clone(self);
        let intro_kind = intro_kind.subst(subst);
        Arc::new(intro_kind)
    }

    fn into_output(self) -> Arc<FormKind> {
        self
    }
}

impl Substitutable for FormKind {
    type Output = FormKind;

    fn subst(self, subst: &mut Subst) -> FormKind {
        match self {
            FormKind::Name => FormKind::Name,
            
            FormKind::Universe => FormKind::Universe,

            FormKind::Nat => FormKind::Nat,

            FormKind::Equal { eq_ty, eq_tm_0, eq_tm_1 } => {
                let eq_ty = eq_ty.subst(subst);
                let eq_tm_0 = eq_tm_0.subst(subst);
                let eq_tm_1 = eq_tm_1.subst(subst);
                FormKind::Equal { eq_ty, eq_tm_0, eq_tm_1 }
            },

            FormKind::Never => FormKind::Never,

            FormKind::Unit => FormKind::Unit,

            FormKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                let lhs_name = lhs_name.subst(subst);
                let lhs_ty = lhs_ty.subst(subst);
                let rhs_ty = rhs_ty.subst(subst);
                FormKind::Sum { lhs_name, lhs_ty, rhs_ty }
            },

            FormKind::Sigma { head_name, head_ty, tail_ty } => {
                let head_name = head_name.subst(subst);
                let head_ty = head_ty.subst(subst);
                let tail_ty = tail_ty.subst(subst);
                FormKind::Sigma { head_name, head_ty, tail_ty }
            },

            FormKind::Pi { arg_name, arg_ty, res_ty } => {
                let arg_name = arg_name.subst(subst);
                let arg_ty = arg_ty.subst(subst);
                let res_ty = res_ty.subst(subst);
                FormKind::Pi { arg_name, arg_ty, res_ty }
            },
        }
    }

    fn into_output(self) -> FormKind {
        self
    }
}

impl Form {
    pub fn into_ty(self) -> Ty {
        self.map(|form| TyKind::Form { form })
    }

    pub fn into_intro(self) -> Intro {
        self.map(|form| Arc::new(IntroKind::Form { form }))
    }

    pub fn name() -> Form {
        Weaken::new(FormKind::name())
    }

    pub fn universe() -> Form {
        Weaken::new(FormKind::universe())
    }

    pub fn nat() -> Form {
        Weaken::new(FormKind::nat())
    }

    pub fn equal(eq_ty: Ty, eq_tm_0: Tm, eq_tm_1: Tm) -> Form {
        Weaken::new_arc(FormKind::Equal { eq_ty, eq_tm_0, eq_tm_1 })
    }

    pub fn never() -> Form {
        Weaken::new(FormKind::never())
    }

    pub fn unit() -> Form {
        Weaken::new(FormKind::unit())
    }

    pub fn sum(lhs_name: Name, lhs_ty: Ty, rhs_ty: Ty) -> Form {
        Weaken::new_arc(FormKind::Sum { lhs_name, lhs_ty, rhs_ty })
    }

    pub fn sigma(head_name: Name, head_ty: Ty, tail_ty: Scope<Ty>) -> Form {
        Weaken::new_arc(FormKind::Sigma { head_name, head_ty, tail_ty })
    }

    pub fn pi(arg_name: Name, arg_ty: Ty, res_ty: Scope<Ty>) -> Form {
        Weaken::new_arc(FormKind::Pi { arg_name, arg_ty, res_ty })
    }

    pub fn as_name(&self) -> Option<()> {
        self.weak.as_name()
    }

    pub fn as_universe(&self) -> Option<()> {
        self.weak.as_universe()
    }

    pub fn as_nat(&self) -> Option<()> {
        self.weak.as_nat()
    }

    pub fn as_equal(self) -> Option<(Ty, Tm, Tm)> {
        self.map_out_unfiltered(|form| Arc::unwrap_or_clone(form).as_equal())
    }

    pub fn as_never(self) -> Option<()> {
        self.weak.as_never()
    }

    pub fn as_unit(self) -> Option<()> {
        self.weak.as_unit()
    }

    pub fn as_sum(self) -> Option<(Name, Ty, Ty)> {
        self.map_out_unfiltered(|form| Arc::unwrap_or_clone(form).as_sum())
    }

    pub fn as_sigma(self) -> Option<(Name, Ty, Scope<Ty>)> {
        self.map_out_unfiltered(|form| Arc::unwrap_or_clone(form).as_sigma())
    }

    pub fn as_pi(self) -> Option<(Name, Ty, Scope<Ty>)> {
        self.map_out_unfiltered(|form| Arc::unwrap_or_clone(form).as_pi())
    }

    pub fn deep_nf(self) -> Form {
        let Weaken { usages, weak: form_kind } = self;
        let form_kind = Arc::unwrap_or_clone(form_kind);
        let form_kind = form_kind.deep_nf();
        form_kind.unfiltered(&usages)
    }
}

impl FormKind {
    pub fn name() -> Arc<FormKind> {
        lazy_static! {
            static ref NAME: Arc<FormKind> = Arc::new(FormKind::Name);
        }

        NAME.clone()
    }

    pub fn universe() -> Arc<FormKind> {
        lazy_static! {
            static ref UNIVERSE: Arc<FormKind> = Arc::new(FormKind::Universe);
        }

        UNIVERSE.clone()
    }

    pub fn nat() -> Arc<FormKind> {
        lazy_static! {
            static ref NAT: Arc<FormKind> = Arc::new(FormKind::Nat);
        }

        NAT.clone()
    }

    pub fn never() -> Arc<FormKind> {
        lazy_static! {
            static ref NEVER: Arc<FormKind> = Arc::new(FormKind::Never);
        }

        NEVER.clone()
    }

    pub fn unit() -> Arc<FormKind> {
        lazy_static! {
            static ref UNIT: Arc<FormKind> = Arc::new(FormKind::Unit);
        }

        UNIT.clone()
    }

    pub fn as_name(&self) -> Option<()> {
        let FormKind::Name = self else {
            return None;
        };
        Some(())
    }

    pub fn as_universe(&self) -> Option<()> {
        let FormKind::Universe = self else {
            return None;
        };
        Some(())
    }

    pub fn as_nat(&self) -> Option<()> {
        let FormKind::Nat = self else {
            return None;
        };
        Some(())
    }

    pub fn as_equal(self) -> Option<(Ty, Tm, Tm)> {
        let FormKind::Equal { eq_ty, eq_tm_0, eq_tm_1 } = self else {
            return None;
        };
        Some((eq_ty, eq_tm_0, eq_tm_1))
    }

    pub fn as_never(&self) -> Option<()> {
        let FormKind::Never = self else {
            return None;
        };
        Some(())
    }

    pub fn as_unit(&self) -> Option<()> {
        let FormKind::Unit = self else {
            return None;
        };
        Some(())
    }

    pub fn as_sum(self) -> Option<(Name, Ty, Ty)> {
        let FormKind::Sum { lhs_name, lhs_ty, rhs_ty } = self else {
            return None;
        };
        Some((lhs_name, lhs_ty, rhs_ty))
    }

    pub fn as_sigma(self) -> Option<(Name, Ty, Scope<Ty>)> {
        let FormKind::Sigma { head_name, head_ty, tail_ty } = self else {
            return None;
        };
        Some((head_name, head_ty, tail_ty))
    }

    pub fn as_pi(self) -> Option<(Name, Ty, Scope<Ty>)> {
        let FormKind::Pi { arg_name, arg_ty, res_ty } = self else {
            return None;
        };
        Some((arg_name, arg_ty, res_ty))
    }

    pub fn deep_nf(self) -> Form {
        match self {
            FormKind::Name => Weaken::new_arc(FormKind::Name),

            FormKind::Universe => Weaken::new_arc(FormKind::Universe),

            FormKind::Nat => Weaken::new_arc(FormKind::Nat),

            FormKind::Equal { eq_ty, eq_tm_0, eq_tm_1 } => {
                let eq_ty = eq_ty.deep_nf();
                let eq_tm_0 = eq_tm_0.deep_nf();
                let eq_tm_1 = eq_tm_1.deep_nf();
                Weaken::new_arc(FormKind::Equal { eq_ty, eq_tm_0, eq_tm_1 })
            },

            FormKind::Never => Weaken::new_arc(FormKind::Never),

            FormKind::Unit => Weaken::new_arc(FormKind::Unit),

            FormKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                let lhs_name = lhs_name.deep_nf();
                let lhs_ty = lhs_ty.deep_nf();
                let rhs_ty = rhs_ty.deep_nf();
                Weaken::new_arc(FormKind::Sum { lhs_name, lhs_ty, rhs_ty })
            },

            FormKind::Sigma { head_name, head_ty, tail_ty } => {
                let head_name = head_name.deep_nf();
                let head_ty = head_ty.deep_nf();
                let tail_ty = tail_ty.deep_nf();
                Weaken::new_arc(FormKind::Sigma { head_name, head_ty, tail_ty })
            },

            FormKind::Pi { arg_name, arg_ty, res_ty } => {
                let arg_name = arg_name.deep_nf();
                let arg_ty = arg_ty.deep_nf();
                let res_ty = res_ty.deep_nf();
                Weaken::new_arc(FormKind::Pi { arg_name, arg_ty, res_ty })
            },
        }
    }
}

