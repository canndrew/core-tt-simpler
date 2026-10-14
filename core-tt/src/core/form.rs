use crate::priv_prelude::*;

pub type Form = Weaken<Arc<FormKind>>;

#[derive(Clone, Debug, Contextual)]
pub enum FormKind {
    Name,
    Universe,
    Nat,

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
    fn unify(
        form_kind_0: FormKind,
        form_kind_1: FormKind,
    ) -> Option<FormKind> {
        match (form_kind_0, form_kind_1) {
            (FormKind::Name, FormKind::Name) => Some(FormKind::Name),

            (FormKind::Universe, FormKind::Universe) => Some(FormKind::Universe),

            (FormKind::Nat, FormKind::Nat) => Some(FormKind::Nat),

            (FormKind::Never, FormKind::Never) => Some(FormKind::Never),

            (FormKind::Unit, FormKind::Unit) => Some(FormKind::Unit),

            (
                FormKind::Sum { lhs_name: lhs_name_0, lhs_ty: lhs_ty_0, rhs_ty: rhs_ty_0 },
                FormKind::Sum { lhs_name: lhs_name_1, lhs_ty: lhs_ty_1, rhs_ty: rhs_ty_1 },
            ) => {
                let lhs_name = Unify::unify(lhs_name_0, lhs_name_1)?;
                let lhs_ty = Unify::unify(lhs_ty_0, lhs_ty_1)?;
                let rhs_ty = Unify::unify(rhs_ty_0, rhs_ty_1)?;
                Some(FormKind::Sum { lhs_name, lhs_ty, rhs_ty })
            },

            (
                FormKind::Sigma { head_name: head_name_0, head_ty: head_ty_0, tail_ty: tail_ty_0 },
                FormKind::Sigma { head_name: head_name_1, head_ty: head_ty_1, tail_ty: tail_ty_1 },
            ) => {
                let head_name = Unify::unify(head_name_0, head_name_1)?;
                let head_ty = Unify::unify(head_ty_0, head_ty_1)?;
                let tail_ty = Unify::unify(
                    tail_ty_0, tail_ty_1,
                )?;
                Some(FormKind::Sigma { head_name, head_ty, tail_ty })
            },

            (
                FormKind::Pi { arg_name: arg_name_0, arg_ty: arg_ty_0, res_ty: res_ty_0 },
                FormKind::Pi { arg_name: arg_name_1, arg_ty: arg_ty_1, res_ty: res_ty_1 },
            ) => {
                let arg_name = Unify::unify(arg_name_0, arg_name_1)?;
                let arg_ty = Unify::unify(arg_ty_0, arg_ty_1)?;
                let res_ty = Unify::unify(
                    res_ty_0, res_ty_1,
                )?;
                Some(FormKind::Pi { arg_name, arg_ty, res_ty })
            },

            _ => None,
        }
    }
}

impl Substitutable for FormKind {
    type Output = Weaken<FormKind>;

    fn subst(self, subst: &mut Subst) -> Weaken<FormKind> {
        match self {
            FormKind::Name => Weaken::new(FormKind::Name),
            
            FormKind::Universe => Weaken::new(FormKind::Universe),

            FormKind::Nat => Weaken::new(FormKind::Nat),

            FormKind::Never => Weaken::new(FormKind::Never),

            FormKind::Unit => Weaken::new(FormKind::Unit),

            FormKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                let lhs_name = lhs_name.capture_subst(subst.clone());
                let lhs_ty = lhs_ty.capture_subst(subst.clone());
                let rhs_ty = rhs_ty.capture_subst(subst.clone());
                Weaken::new(FormKind::Sum { lhs_name, lhs_ty, rhs_ty })
            },

            FormKind::Sigma { head_name, head_ty, tail_ty } => {
                let head_name = head_name.capture_subst(subst.clone());
                let head_ty = head_ty.capture_subst(subst.clone());
                let tail_ty = tail_ty.capture_subst(subst.clone());
                Weaken::new(FormKind::Sigma { head_name, head_ty, tail_ty })
            },

            FormKind::Pi { arg_name, arg_ty, res_ty } => {
                let arg_name = arg_name.capture_subst(subst.clone());
                let arg_ty = arg_ty.capture_subst(subst.clone());
                let res_ty = res_ty.capture_subst(subst.clone());
                Weaken::new(FormKind::Pi { arg_name, arg_ty, res_ty })
            },
        }
    }

    fn into_output(self) -> Weaken<FormKind> {
        Weaken::new(self)
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<FormKind> {
        let form_kind = match self {
            FormKind::Name => FormKind::Name,

            FormKind::Universe => FormKind::Universe,

            FormKind::Nat => FormKind::Nat,

            FormKind::Never => FormKind::Never,

            FormKind::Unit => FormKind::Unit,

            FormKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                let lhs_name = lhs_name.try_strengthen_index(var_index)?;
                let lhs_ty = lhs_ty.try_strengthen_index(var_index)?;
                let rhs_ty = rhs_ty.try_strengthen_index(var_index)?;
                FormKind::Sum { lhs_name, lhs_ty, rhs_ty }
            },

            FormKind::Sigma { head_name, head_ty, tail_ty } => {
                let head_name = head_name.try_strengthen_index(var_index)?;
                let head_ty = head_ty.try_strengthen_index(var_index)?;
                let tail_ty = tail_ty.try_strengthen_index(var_index)?;
                FormKind::Sigma { head_name, head_ty, tail_ty }
            },

            FormKind::Pi { arg_name, arg_ty, res_ty } => {
                let arg_name = arg_name.try_strengthen_index(var_index)?;
                let arg_ty = arg_ty.try_strengthen_index(var_index)?;
                let res_ty = res_ty.try_strengthen_index(var_index)?;
                FormKind::Pi { arg_name, arg_ty, res_ty }
            },
        };
        Some(form_kind)
    }
}

impl Form {
    pub fn into_ty(self) -> Ty {
        self.map(|form| OrLazy::Reduced(TyKind::Form { form }))
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

    /*
    pub fn equal(eq_ty: Ty, eq_tm_0: Tm, eq_tm_1: Tm) -> Form {
        Weaken::new_arc(FormKind::Equal { eq_ty, eq_tm_0, eq_tm_1 })
    }
    */

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
        self.weak().as_name()
    }

    pub fn as_universe(&self) -> Option<()> {
        self.weak().as_universe()
    }

    pub fn as_nat(&self) -> Option<()> {
        self.weak().as_nat()
    }

    pub fn as_never(self) -> Option<()> {
        self.weak().as_never()
    }

    pub fn as_unit(self) -> Option<()> {
        self.weak().as_unit()
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

    pub fn as_equal(self) -> Option<(Ty, Tm, Tm)> {
        let FormKind::Pi { arg_name, arg_ty, res_ty } = self else {
            return None;
        };
        let ctx_len = max_all([arg_name.ctx_len(), arg_ty.ctx_len(), res_ty.ctx_len()]);
        let res_ty_inner = res_ty.into_inner(ctx_len);
        let (eq_ty, eq_tm_0, eq_tm_1) = res_ty_inner.as_equal()?;
        let eq_ty = Ty::pi(arg_name, arg_ty, Scope::new(ctx_len, eq_ty));
        let eq_tm_0 = Tm::func(Scope::new(ctx_len, eq_tm_0));
        let eq_tm_1 = Tm::func(Scope::new(ctx_len, eq_tm_1));
        Some((eq_ty, eq_tm_0, eq_tm_1))
    }

    pub fn is_prop(self, prop_ty_vars: &mut Vec<usize>) -> bool {
        let ctx_len = prop_ty_vars.last().map_or(0, |index| index + 1);
        match self {
            | FormKind::Name
            | FormKind::Universe
            | FormKind::Nat
            | FormKind::Sum { .. }
            => false,

            | FormKind::Never
            | FormKind::Unit
            => true,

            FormKind::Sigma { head_name: _, head_ty, tail_ty } => {
                let ctx_len = cmp::max(tail_ty.ctx_len(), ctx_len);

                head_ty.is_prop(prop_ty_vars) &&
                tail_ty.into_inner(ctx_len).is_prop(prop_ty_vars)
            },

            FormKind::Pi { arg_name: _, arg_ty: _, res_ty } => {
                let ctx_len = cmp::max(res_ty.ctx_len(), ctx_len);

                res_ty.into_inner(ctx_len).is_prop(prop_ty_vars)
            },
        }
    }

    pub fn is_discrete(self) -> bool {
        match self {
            | FormKind::Name
            | FormKind::Nat
            | FormKind::Never
            | FormKind::Unit
            => true,

            FormKind::Universe => false,

            FormKind::Sum { lhs_name: _, lhs_ty, rhs_ty } => {
                lhs_ty.is_discrete() && rhs_ty.is_discrete()
            },

            FormKind::Sigma { head_name: _, head_ty, tail_ty } => {
                head_ty.is_discrete() && tail_ty.inner.is_discrete()
            },

            FormKind::Pi { arg_name: _, arg_ty: _, res_ty } => {
                res_ty.inner.is_discrete()
            },
        }
    }

    pub fn is_functorial(self, ty_var_index: usize, negative: bool) -> bool {
        match self {
            | FormKind::Name
            | FormKind::Universe
            | FormKind::Nat
            | FormKind::Never
            | FormKind::Unit
            => true,

            FormKind::Sum { lhs_name: _, lhs_ty, rhs_ty } => {
                lhs_ty.is_functorial(ty_var_index, negative) &&
                rhs_ty.is_functorial(ty_var_index, negative)
            },

            FormKind::Sigma { head_name: _, head_ty, tail_ty } => {
                head_ty.is_functorial(ty_var_index, negative) &&
                tail_ty.is_functorial(ty_var_index, negative)
            },

            FormKind::Pi { arg_name: _, arg_ty, res_ty } => {
                arg_ty.is_functorial(ty_var_index, !negative) &&
                res_ty.is_functorial(ty_var_index, negative)
            },
        }
    }
}

impl DeepNf for FormKind {
    type Output = Form;

    fn deep_nf(self) -> Form {
        match self {
            FormKind::Name => Weaken::new_arc(FormKind::Name),

            FormKind::Universe => Weaken::new_arc(FormKind::Universe),

            FormKind::Nat => Weaken::new_arc(FormKind::Nat),

            FormKind::Never => Weaken::new_arc(FormKind::Never),

            FormKind::Unit => Weaken::new_arc(FormKind::Unit),

            FormKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                let lhs_name = lhs_name.deep_nf().into_name();
                let lhs_ty = lhs_ty.deep_nf().into_ty();
                let rhs_ty = rhs_ty.deep_nf().into_ty();
                Weaken::new_arc(FormKind::Sum { lhs_name, lhs_ty, rhs_ty })
            },

            FormKind::Sigma { head_name, head_ty, tail_ty } => {
                let head_name = head_name.deep_nf().into_name();
                let head_ty = head_ty.deep_nf().into_ty();
                let tail_ty = tail_ty.deep_nf().map_without_capture(ValTy::into_ty);
                Weaken::new_arc(FormKind::Sigma { head_name, head_ty, tail_ty })
            },

            FormKind::Pi { arg_name, arg_ty, res_ty } => {
                let arg_name = arg_name.deep_nf().into_name();
                let arg_ty = arg_ty.deep_nf().into_ty();
                let res_ty = res_ty.deep_nf().map_without_capture(ValTy::into_ty);
                Weaken::new_arc(FormKind::Pi { arg_name, arg_ty, res_ty })
            },
        }
    }
}

