use crate::priv_prelude::*;

pub type Lazy = Weaken<Arc<LazyData>>;

#[derive(Clone, Debug)]
pub struct LazyData {
    pub(crate) reduced_filter: Usages,
    pub(crate) reduced_opt: Arc<OnceLock<Option<ValTm>>>,
    pub(crate) neutral_kind: Arc<NeutralKind>,
}

#[derive(Clone, Debug)]
pub enum OrLazy<T> {
    Reduced(T),
    Lazy(Arc<LazyData>),
}

impl Contextual for LazyData {
    fn ctx_len(&self) -> usize {
        self.reduced_filter.ctx_len()
    }

    fn collect_usages(&self, usages: &mut Usages) {
        usages.or_assign(&self.reduced_filter);
    }

    fn filter_usages(&mut self, usages: &Usages) {
        self.reduced_filter.filter(usages);
    }

    fn unfilter_usages(&mut self, usages: &Usages) {
        self.reduced_filter.unfilter(usages);
    }
}

impl LazyData {
    pub fn new(neutral_kind: NeutralKind) -> LazyData {
        let (reduced_filter, neutral_kind) = Weaken::new(neutral_kind).into_usages_and_weak();
        let neutral_kind = Arc::new(neutral_kind);
        LazyData {
            reduced_filter,
            reduced_opt: Arc::new(OnceLock::new()),
            neutral_kind,
        }
    }

    pub(crate) fn new_arc(neutral_kind: NeutralKind) -> Arc<LazyData> {
        Arc::new(LazyData::new(neutral_kind))
    }

    /// Returns the reduced term only if its already been computed.
    pub fn cached_reduced(&self) -> Option<ValTm> {
        self
        .reduced_opt
        .get()
        .and_then(|tm_opt| tm_opt.as_ref())
        .map(|val| val.clone().unfiltered(&self.reduced_filter))
    }

    /// Computes the reduced term or returns the cached reduced term if its already been computed.
    pub fn reduced(&self) -> ValTm {
        match self.try_reduce() {
            Some(val_tm) => val_tm,
            None => {
                let stuck = StuckKind {
                    kind: self.neutral_kind.clone(),
                };
                let tm_kind = TmKind::Stuck { stuck };
                Weaken::from_usages_and_weak(self.reduced_filter.clone(), tm_kind)
            },
        }
    }

    fn try_reduce(&self) -> Option<ValTm> {
        self
        .reduced_opt
        .get_or_init(|| {
            self
            .neutral_kind
            .try_reduce()
        })
        .as_ref()
        .map(|tm| tm.clone().unfiltered(&self.reduced_filter))
    }

    /// Computes the reduced term and performs substitution on it.
    pub fn subst(&self, subst: &mut Subst) -> ValTm {
        if let Some(val) = self.cached_reduced() {
            return val.subst(subst);
        }
        let neutral = Weaken::from_usages_and_weak(
            self.reduced_filter.clone(),
            (*self.neutral_kind).clone(),
        );
        neutral.subst(subst)
    }

    /// Attempts to return `self` with the variable at `var_index` removed from the context. May
    /// compute the reduced term if necessary.
    pub fn try_strengthen_index(self, var_index: usize) -> Option<OrLazy<TmKind>> {
        if !self.reduced_filter.get(var_index) {
            let LazyData { reduced_filter, reduced_opt, neutral_kind } = self;
            let (reduced_filter, _) = reduced_filter.shift_remove(var_index);
            return Some(OrLazy::Lazy(Arc::new(LazyData {
                reduced_filter, reduced_opt, neutral_kind,
            })));
        }

        let reduced = self.reduced().try_strengthen_index(var_index)?.into_inner();
        Some(OrLazy::Reduced(reduced))
    }

    pub fn into_cached_reduced_or_neutral(
        self,
    ) -> Result<Weaken<TmKind>, Weaken<Arc<NeutralKind>>> {
        match self.cached_reduced() {
            Some(tm) => Ok(tm),
            None => {
                let LazyData { reduced_filter, reduced_opt: _, neutral_kind } = self;
                Err(Weaken::from_usages_and_weak(reduced_filter, neutral_kind))
            },
        }
    }

    pub fn neutral_kind(&self) -> Weaken<Arc<NeutralKind>> {
        Weaken::from_usages_and_weak(
            self.reduced_filter.clone(),
            self.neutral_kind.clone(),
        )
    }

    pub fn weak_neutral_kind(&self) -> &Arc<NeutralKind> {
        &self.neutral_kind
    }
}

impl Lazy {
    pub fn into_tm(self) -> Tm {
        self.map(|lazy| OrLazy::Lazy(lazy))
    }

    pub fn into_ty(self) -> Ty {
        self.map(|lazy| OrLazy::Lazy(lazy))
    }

    pub fn into_name(self) -> Name {
        self.map(|lazy| OrLazy::Lazy(lazy))
    }

    pub fn fold(
        elim: Tm,
        motive: Scope<Ty>,
        zero_inhab: Tm,
        succ_inhab: Scope<Scope<Tm>>,
    ) -> Lazy {
        Weaken::new_arc(LazyData::new(NeutralKind::Fold {
            elim, motive, zero_inhab, succ_inhab,
        }))
    }

    pub fn explode(
        motive: Scope<Ty>,
    ) -> Lazy {
        motive
        .lift_weaken()
        .map(|motive| Arc::new(LazyData::new(NeutralKind::Explode { motive })))
    }

    pub fn case(
        elim: Tm,
        lhs_name: Name,
        motive: Scope<Ty>,
        lhs_inhab: Scope<Tm>,
        rhs_inhab: Scope<Tm>,
    ) -> Lazy {
        Weaken::new_arc(LazyData::new(NeutralKind::Case {
            lhs_name, elim, motive, lhs_inhab, rhs_inhab,
        }))
    }

    pub fn proj_head(elim: Tm) -> Lazy {
        elim.map(|elim| LazyData::new_arc(NeutralKind::ProjHead { elim }))
    }

    pub fn proj_tail(elim: Tm) -> Lazy {
        elim.map(|elim| LazyData::new_arc(NeutralKind::ProjTail { elim }))
    }

    pub fn app(elim: Tm, arg_tm: Tm) -> Lazy {
        Weaken::new_arc(LazyData::new(NeutralKind::App { elim, arg_tm }))
    }

    pub fn obs_equal(eq_ty: Ty, eq_tm_0: Tm, eq_tm_1: Tm) -> Lazy {
        Weaken::new_arc(LazyData::new(NeutralKind::ObsEqual {
            eq_ty, eq_tm_0, eq_tm_1,
        }))
    }

    pub fn cast(ty_0: Ty, ty_1: Ty, tm_0: Tm) -> Lazy {
        Weaken::new_arc(LazyData::new(NeutralKind::Cast {
            ty_0, ty_1, tm_0,
        }))
    }
}

impl DeepNf for LazyData {
    type Output = ValTm;

    fn deep_nf(self) -> ValTm {
        match self.cached_reduced() {
            Some(tm) => tm.deep_nf(),
            None => self.neutral_kind.deep_nf().unfiltered(&self.reduced_filter),
        }
    }
}

pub trait AsTmKind: Sized {
    type Type;

    fn into_tm_kind(self) -> TmKind;
    fn from_tm_kind(tm_kind: TmKind) -> Self;
    fn full_type(ty: Self::Type) -> Ty;
}

impl AsTmKind for TmKind {
    type Type = Ty;

    fn into_tm_kind(self) -> TmKind {
        self
    }

    fn from_tm_kind(tm_kind: TmKind) -> TmKind {
        tm_kind
    }

    fn full_type(ty: Ty) -> Ty {
        ty
    }
}

impl AsTmKind for NameKind {
    type Type = ();

    fn into_tm_kind(self) -> TmKind {
        match self {
            NameKind::Tag { tag } => {
                let intro = Arc::new(IntroKind::Tag { tag });
                TmKind::Intro { intro }
            },
            NameKind::Stuck { stuck } => {
                TmKind::Stuck { stuck }
            },
        }
    }

    fn from_tm_kind(tm_kind: TmKind) -> NameKind {
        match tm_kind {
            TmKind::Intro { intro } => {
                let tag = Arc::unwrap_or_clone(intro).as_tag().unwrap();
                NameKind::Tag { tag }
            },
            TmKind::Proof => unreachable!(),
            TmKind::Stuck { stuck } => NameKind::Stuck { stuck },
        }
    }

    fn full_type((): ()) -> Ty {
        Ty::name()
    }
}

impl AsTmKind for TyKind {
    type Type = ();

    fn into_tm_kind(self) -> TmKind {
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

    fn from_tm_kind(tm_kind: TmKind) -> TyKind {
        match tm_kind {
            TmKind::Intro { intro } => {
                let form = Arc::unwrap_or_clone(intro).as_form().unwrap();
                TyKind::Form { form }
            },
            TmKind::Proof => unreachable!(),
            TmKind::Stuck { stuck } => TyKind::Stuck { stuck },
        }
    }

    fn full_type((): ()) -> Ty {
        Ty::universe()
    }
}

impl<T> Weaken<OrLazy<T>> {
    pub fn reduced(self) -> Weaken<T>
    where
        T: Contextual + AsTmKind,
    {
        let (usages, or_lazy) = self.into_usages_and_weak();
        match or_lazy {
            OrLazy::Reduced(reduced) => Weaken::from_usages_and_weak(usages, reduced),
            OrLazy::Lazy(lazy) => {
                lazy.reduced().unfiltered(&usages).map(T::from_tm_kind)
            },
        }
    }
}

impl<T> OrLazy<T> {
    pub fn map<U>(self, func: impl FnOnce(T) -> U) -> OrLazy<U> {
        match self {
            OrLazy::Reduced(reduced) => OrLazy::Reduced(func(reduced)),
            OrLazy::Lazy(lazy) => OrLazy::Lazy(lazy),
        }
    }

    pub fn reduced(self) -> T
    where
        T: AsTmKind,
    {
        match self {
            OrLazy::Reduced(reduced) => reduced,
            OrLazy::Lazy(lazy) => T::from_tm_kind(lazy.reduced().into_inner()),
        }
    }
}

impl<T> Contextual for OrLazy<T>
where
    T: Contextual,
{
    fn ctx_len(&self) -> usize {
        match self {
            OrLazy::Reduced(reduced) => reduced.ctx_len(),
            OrLazy::Lazy(lazy) => lazy.ctx_len(),
        }
    }

    fn collect_usages(&self, usages: &mut Usages) {
        match self {
            OrLazy::Reduced(reduced) => reduced.collect_usages(usages),
            OrLazy::Lazy(lazy) => lazy.collect_usages(usages),
        }
    }

    fn filter_usages(&mut self, usages: &Usages) {
        match self {
            OrLazy::Reduced(reduced) => reduced.filter_usages(usages),
            OrLazy::Lazy(lazy) => lazy.filter_usages(usages),
        }
    }

    fn unfilter_usages(&mut self, usages: &Usages) {
        match self {
            OrLazy::Reduced(reduced) => reduced.unfilter_usages(usages),
            OrLazy::Lazy(lazy) => lazy.unfilter_usages(usages),
        }
    }
}

impl<T, U> Substitutable for OrLazy<T>
where
    T: Substitutable<Output = Weaken<U>> + AsTmKind,
    U: Contextual + AsTmKind,
{
    type Output = Weaken<U>;

    fn subst(self, subst: &mut Subst) -> Weaken<U> {
        match self {
            OrLazy::Reduced(reduced) => reduced.subst(subst),
            OrLazy::Lazy(lazy) => {
                lazy.subst(subst).map(AsTmKind::from_tm_kind)
            },
        }
    }

    fn into_output(self) -> Weaken<U> {
        match self {
            OrLazy::Reduced(reduced) => reduced.into_output(),
            OrLazy::Lazy(lazy) => lazy.reduced().map(AsTmKind::from_tm_kind),
        }
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<OrLazy<T>> {
        let or_lazy = match self {
            OrLazy::Reduced(reduced) => {
                let reduced = reduced.try_strengthen_index(var_index)?;
                OrLazy::Reduced(reduced)
            },
            OrLazy::Lazy(lazy) => {
                match Arc::unwrap_or_clone(lazy).try_strengthen_index(var_index)? {
                    OrLazy::Reduced(reduced) => {
                        let reduced = AsTmKind::from_tm_kind(reduced);
                        OrLazy::Reduced(reduced)
                    },
                    OrLazy::Lazy(lazy) => OrLazy::Lazy(lazy),
                }
            },
        };
        Some(or_lazy)
    }
}

impl<T> Bindable for Weaken<OrLazy<T>>
where
    T: Contextual + AsTmKind,
{
    fn capture_subst(self, subst: Subst) -> Weaken<OrLazy<T>> {
        let (subst_index, var_tms) = subst.remove_unused_vars(self.usages());
        if var_tms.is_empty() {
            return self;
        }

        let (mut truncated_body_usages, body) = self.into_usages_and_weak();
        truncated_body_usages.truncate(subst_index);
        let body = match body {
            OrLazy::Reduced(reduced) => OrLazy::Reduced(reduced.into_tm_kind()),
            OrLazy::Lazy(lazy) => OrLazy::Lazy(lazy),
        };

        Weaken::new_arc(LazyData::new(NeutralKind::Bind {
            var_tms, truncated_body_usages, body,
        }))
        .map(OrLazy::Lazy)
    }
}

impl<T> Unify for OrLazy<T>
where
    T: Unify + AsTmKind,
{
    fn unify(
        or_lazy_0: OrLazy<T>,
        or_lazy_1: OrLazy<T>,
    ) -> Option<OrLazy<T>> {
        let (reduced_0, reduced_1) = match (or_lazy_0, or_lazy_1) {
            (OrLazy::Reduced(reduced_0), OrLazy::Reduced(reduced_1)) => {
                (reduced_0, reduced_1)
            },
            (OrLazy::Reduced(reduced_0), OrLazy::Lazy(lazy_1)) => {
                let reduced_1 = T::from_tm_kind(lazy_1.reduced().into_inner());
                (reduced_0, reduced_1)
            },
            
            (OrLazy::Lazy(lazy_0), OrLazy::Reduced(reduced_1)) => {
                let reduced_0 = T::from_tm_kind(lazy_0.reduced().into_inner());
                (reduced_0, reduced_1)
            },

            (OrLazy::Lazy(lazy_0), OrLazy::Lazy(lazy_1)) => {
                if Arc::ptr_eq(&lazy_0, &lazy_1) {
                    return Some(OrLazy::Lazy(lazy_0));
                }
                let reduced_0 = T::from_tm_kind(lazy_0.reduced().into_inner());
                let reduced_1 = T::from_tm_kind(lazy_1.reduced().into_inner());
                (reduced_0, reduced_1)
            },
        };
        let reduced = Unify::unify(reduced_0, reduced_1)?;
        Some(OrLazy::Reduced(reduced))
    }
}

impl<T> DeepNf for OrLazy<T>
where
    T: DeepNf<Output: Contextual> + Contextual + AsTmKind,
{
    type Output = T::Output;

    fn deep_nf(self) -> T::Output {
        match self {
            OrLazy::Reduced(reduced) => reduced.deep_nf(),
            OrLazy::Lazy(lazy) => {
                lazy.reduced().map(|tm_kind| T::from_tm_kind(tm_kind)).deep_nf()
            },
        }
    }
}

impl<T> TryUnswapVars for OrLazy<T>
where
    T: TryUnswapVars,
    T: AsTmKind,
{
    fn try_unswap_vars(
        self,
        var_index: usize,
    ) -> Option<OrLazy<T>> {
        let reduced = self.reduced().try_unswap_vars(var_index)?;
        Some(OrLazy::Reduced(reduced))
    }
}

