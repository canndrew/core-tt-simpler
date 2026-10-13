use crate::priv_prelude::*;

pub type Ty = Weaken<OrLazy<TyKind>>;
pub type ValTy = Weaken<TyKind>;

#[derive(Clone, Debug, Contextual)]
pub enum TyKind {
    Form {
        form: Arc<FormKind>,
    },
    Stuck {
        stuck: StuckKind,
    },
}

impl Ty {
    pub fn into_tm(self) -> Tm {
        self.map(|or_lazy| {
            match or_lazy {
                OrLazy::Reduced(ty_kind) => OrLazy::Reduced(ty_kind.into_tm_kind()),
                OrLazy::Lazy(lazy) => OrLazy::Lazy(lazy),
            }
        })
    }

    pub fn try_reduce_to_form(self) -> Option<Form> {
        let (usages, ty_kind) = self.reduced().into_usages_and_weak();
        match ty_kind {
            TyKind::Form { form } => {
                Some(Weaken::from_usages_and_weak(usages, form))
            },
            TyKind::Stuck { .. } => None,
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

    pub fn obs_equal(eq_ty: Ty, eq_tm_0: Tm, eq_tm_1: Tm) -> Ty {
        Lazy::obs_equal(eq_ty, eq_tm_0, eq_tm_1).into_ty()
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

    pub fn as_stuck(self) -> Option<Stuck> {
        self.try_map(|ty_kind| ty_kind.reduced().as_stuck())
    }

    pub fn as_equal(self) -> Option<(Ty, Tm, Tm)> {
        self.into_inner().reduced().as_equal()
    }

    pub fn is_prop(self) -> bool {
        self.into_weak().is_prop()
    }
}

impl OrLazy<TyKind> {
    pub fn is_prop(self) -> bool {
        self.reduced().is_prop()
    }
}

impl TyKind {
    pub fn into_tm_kind(self) -> TmKind {
        match self {
            TyKind::Form { form } => {
                let intro = Arc::new(IntroKind::Form { form });
                TmKind::Intro { intro }
            },
            TyKind::Stuck { stuck } => {
                TmKind::Stuck { stuck }
            },
        }
    }

    pub fn as_form(self) -> Option<Arc<FormKind>> {
        match self {
            TyKind::Form { form } => Some(form),
            TyKind::Stuck { .. } => None,
        }
    }

    pub fn as_stuck(self) -> Option<StuckKind> {
        match self {
            TyKind::Form { .. } => None,
            TyKind::Stuck { stuck } => Some(stuck),
        }
    }

    pub fn is_prop(self) -> bool {
        match self {
            TyKind::Form { form } => Arc::unwrap_or_clone(form).is_prop(),
            TyKind::Stuck { stuck } => stuck.is_prop(),
        }
    }

    pub fn as_equal(self) -> Option<(Ty, Tm, Tm)> {
        match self {
            TyKind::Form { form } => Arc::unwrap_or_clone(form).as_equal(),
            TyKind::Stuck { stuck } => stuck.as_equal(),
        }
    }
}

impl ValTy {
    pub fn into_ty(self) -> Ty {
        self.map(|ty_kind| OrLazy::Reduced(ty_kind))
    }

    pub fn as_equal(self) -> Option<(Ty, Tm, Tm)> {
        self.into_inner().as_equal()
    }
}

impl DeepNf for TyKind {
    type Output = ValTy;

    fn deep_nf(self) -> ValTy {
        match self {
            TyKind::Form { form } => {
                form.deep_nf().map(|form| TyKind::Form { form })
            },
            TyKind::Stuck { stuck } => {
                stuck.deep_nf().map(|stuck| TyKind::Stuck { stuck })
            },
        }
    }
}

impl Unify for TyKind {
    fn unify(
        ty_kind_0: TyKind,
        ty_kind_1: TyKind,
    ) -> Option<TyKind> {
        match (ty_kind_0, ty_kind_1) {
            (TyKind::Form { form: form_0 }, TyKind::Form { form: form_1 }) => {
                let form = Unify::unify(form_0, form_1)?;
                Some(TyKind::Form { form })
            },

            (TyKind::Stuck { stuck: stuck_0 }, TyKind::Stuck { stuck: stuck_1 }) => {
                let stuck = Unify::unify(stuck_0, stuck_1)?;
                Some(TyKind::Stuck { stuck })
            },

            | (TyKind::Form { .. }, TyKind::Stuck { .. })
            | (TyKind::Stuck { .. }, TyKind::Form { .. })
            => None,
        }
    }
}

impl Substitutable for TyKind {
    type Output = ValTy;

    fn subst(self, subst: &mut Subst) -> ValTy {
        match self {
            TyKind::Form { form } => {
                form.subst(subst).map(|form| TyKind::Form { form })
            },
            TyKind::Stuck { stuck } => {
                stuck.subst(subst).map(|tm_kind| tm_kind.into_ty_kind())
            },
        }
    }

    fn into_output(self) -> ValTy {
        Weaken::new(self)
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<TyKind> {
        let ty_kind = match self {
            TyKind::Form { form } => {
                let form = form.try_strengthen_index(var_index)?;
                TyKind::Form { form }
            },
            TyKind::Stuck { stuck } => {
                let stuck = stuck.try_strengthen_index(var_index)?;
                TyKind::Stuck { stuck }
            },
        };
        Some(ty_kind)
    }
}

