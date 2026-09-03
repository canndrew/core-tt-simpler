use crate::priv_prelude::*;

#[derive(Clone, Debug)]
pub struct Scope<T> {
    pub ctx_len: usize,
    pub inner: T,
}

impl<T: Contextual> Contextual for Scope<T> {
    fn ctx_len(&self) -> usize {
        self.ctx_len
    }

    fn collect_usages(&self, usages: &mut Usages) {
        let mut inner_usages = Usages::empty();
        self.inner.collect_usages(&mut inner_usages);
        usages.or_assign_truncated(&inner_usages, self.ctx_len);
    }

    fn filter_usages(&mut self, usages: &Usages) {
        let mut usages = usages.clone_truncate(self.ctx_len);
        let new_ctx_len = usages.count_ones();
        usages.set_to_one(self.ctx_len);
        self.ctx_len = new_ctx_len;
        self.inner.filter_usages(&usages);
    }

    fn unfilter_usages(&mut self, usages: &Usages) {
        let Some(ctx_len_m1) = self.ctx_len.checked_sub(1) else {
            return;
        };
        let new_ctx_len = usages.unfilter_index(ctx_len_m1).strict_add(1);
        let mut usages = usages.clone_truncate(new_ctx_len);
        usages.set_to_one(new_ctx_len);
        self.ctx_len = new_ctx_len;
        self.inner.unfilter_usages(&usages);
    }
}

impl<T> Scope<T> {
    pub fn new(ctx_len: usize, mut inner: T) -> Scope<T>
    where
        T: Contextual,
    {
        let inner_ctx_len = inner.ctx_len();
        match ctx_len.strict_add(1).cmp(&inner.ctx_len()) {
            cmp::Ordering::Less => panic!("inner ctx_len too large to be scoped"),
            cmp::Ordering::Greater => {
                Scope {
                    ctx_len: inner_ctx_len,
                    inner,
                }
            },
            cmp::Ordering::Equal => {
                let mut usages = Usages::empty();
                inner.collect_usages(&mut usages);
                usages.set_to_zero(ctx_len);
                let new_ctx_len = usages.ctx_len();
                usages.set_to_one(ctx_len);
                usages.set_run_to_one(0, new_ctx_len);
                inner.filter_usages(&usages);
                Scope { ctx_len: new_ctx_len, inner }
            },
        }
    }

    pub fn constant(inner: T) -> Scope<T>
    where
        T: Contextual,
    {
        let ctx_len = inner.ctx_len();
        Scope { ctx_len, inner }
    }

    pub fn make(ctx_len: usize, func: impl FnOnce(Tm) -> T) -> Scope<T>
    where
        T: Contextual,
    {
        let tm = Tm::var(ctx_len);
        let inner = func(tm);
        Scope::new(ctx_len, inner)
    }

    pub fn try_strengthen(self) -> Result<T, Scope<T>>
    where
        T: Contextual,
    {
        if self.ctx_len == self.inner.ctx_len() {
            Ok(self.inner)
        } else {
            debug_assert_eq!(self.inner.ctx_len(), self.ctx_len.strict_add(1));
            Err(self)
        }
    }

    pub fn into_inner(mut self, ctx_len: usize) -> T
    where
        T: Contextual,
    {
        debug_assert!(self.ctx_len <= ctx_len);
        if ctx_len > self.ctx_len {
            let mut filter = Usages::ones(self.ctx_len);
            filter.set_to_one(ctx_len);
            self.inner.unfilter_usages(&filter)
        }
        self.inner
    }

    pub fn bind(self, var_tm: Tm) -> T
    where
        T: Contextual + Bindable,
    {
        if self.ctx_len == self.inner.ctx_len() {
            self.inner
        } else {
            debug_assert_eq!(self.inner.ctx_len(), self.ctx_len.strict_add(1));
            let new_ctx_len = cmp::max(self.ctx_len, var_tm.ctx_len());
            let inner = self.into_inner(new_ctx_len);
            let subst = Subst::single_var(new_ctx_len, var_tm);
            inner.capture_subst(subst)
        }
    }

    pub fn map_without_capture<U>(
        self,
        func: fn(T) -> U,
    ) -> Scope<U> {
        let Scope { ctx_len, inner } = self;
        let inner = func(inner);
        Scope { ctx_len, inner }
    }

    pub fn try_map_without_capture<U>(
        self,
        func: fn(T) -> Option<U>,
    ) -> Option<Scope<U>> {
        let Scope { ctx_len, inner } = self;
        let inner = func(inner)?;
        Some(Scope { ctx_len, inner })
    }

    pub fn map<U>(
        self,
        ctx_len: usize,
        func: impl FnOnce(Tm, T) -> U,
    ) -> Scope<U>
    where
        T: Contextual,
        U: Contextual,
    {
        let inner = self.into_inner(ctx_len);
        let var_tm = Tm::var(ctx_len);
        let inner = func(var_tm, inner);
        Scope::new(ctx_len, inner)
    }

    pub fn try_map<U>(
        self,
        ctx_len: usize,
        func: impl FnOnce(Tm, T) -> Option<U>,
    ) -> Option<Scope<U>>
    where
        T: Contextual,
        U: Contextual,
    {
        let inner = self.into_inner(ctx_len);
        let var_tm = Tm::var(ctx_len);
        let inner = func(var_tm, inner)?;
        Some(Scope::new(ctx_len, inner))
    }

    pub fn map_multi<Us>(
        self,
        ctx_len: usize,
        func: impl FnOnce(Tm, T) -> Us,
    ) -> Us::ScopeEach
    where
        T: Contextual,
        Us: TupleOfContextual,
    {
        let inner = self.into_inner(ctx_len);
        let var_tm = Tm::var(ctx_len);
        let inners = func(var_tm, inner);
        inners.scope_each(ctx_len)
    }

    pub fn try_map_multi<Us>(
        self,
        ctx_len: usize,
        func: impl FnOnce(Tm, T) -> Option<Us>,
    ) -> Option<Us::ScopeEach>
    where
        T: Contextual,
        Us: TupleOfContextual,
    {
        let inner = self.into_inner(ctx_len);
        let var_tm = Tm::var(ctx_len);
        let inners = func(var_tm, inner)?;
        Some(inners.scope_each(ctx_len))
    }
}

impl<Ts> Scope<Ts>
where
    Ts: TupleOfContextual,
{
    pub fn lift_tuple(self) -> Ts::ScopeEach {
        let Scope { ctx_len, inner } = self;
        inner.scope_each(ctx_len)
    }
}

impl<T> Scope<Weaken<T>> {
    // More efficient than Weaken::new(self.map(Weaken::into_inner))
    pub fn lift_weaken(self) -> Weaken<Scope<T>> {
        let Scope { ctx_len, inner: Weaken { mut usages, weak } } = self;
        usages.set_to_zero(ctx_len);
        let ctx_len = usages.count_ones();
        Weaken { usages, weak: Scope { ctx_len, inner: weak } }
    }
}

impl<T: Contextual + Bindable> Bindable for Scope<T> {
    fn capture_subst(
        self,
        mut subst: Subst,
    ) -> Scope<T> {
        let Scope { ctx_len, mut inner } = self;

        subst.truncate(self.ctx_len);
        if subst.is_id() {
            return Scope { ctx_len, inner };
        }

        let subst_index = subst.subst_index();
        let subst = subst.lift(1);
        let mut filter = Usages::ones(subst_index);
        filter.set_run_to_one(subst.subst_index(), subst.len());
        inner.unfilter_usages(&filter);

        let inner = inner.capture_subst(subst);
        Scope::new(subst_index, inner)
    }
}

pub trait Bindable {
    fn capture_subst(
        self,
        subst: Subst,
    ) -> Self;
}

impl<T> Unify for Scope<T>
where
    T: Contextual + Unify<Meta: Contextual>,
{
    type Meta = (Ty, Scope<T::Meta>);

    fn unify(
        ctx_tys: &mut Vec<Ty>,
        (var_ty, body_meta): (Ty, Scope<T::Meta>),
        scope_0: Scope<T>,
        scope_1: Scope<T>,
    ) -> Option<Scope<T>> {
        let Scope { ctx_len: ctx_len_meta, inner: inner_meta } = body_meta;
        let Scope { ctx_len: ctx_len_0, inner: inner_0 } = scope_0;
        let Scope { ctx_len: ctx_len_1, inner: inner_1 } = scope_1;

        let ctx_len = ctx_tys.len();
        let inner_meta = {
            let mut usages = Usages::ones(ctx_len_meta);
            usages.set_to_one(ctx_len);
            inner_meta.unfiltered(&usages)
        };
        let inner_0 = {
            let mut usages = Usages::ones(ctx_len_0);
            usages.set_to_one(ctx_len);
            inner_0.unfiltered(&usages)
        };
        let inner_1 = {
            let mut usages = Usages::ones(ctx_len_1);
            usages.set_to_one(ctx_len);
            inner_1.unfiltered(&usages)
        };

        ctx_tys.push(var_ty);
        let inner_opt = Unify::unify(ctx_tys, inner_meta, inner_0, inner_1);
        ctx_tys.pop();
        let inner = inner_opt?;

        Some(Scope::new(ctx_len, inner))
    }
}

impl<T: Contextual + Bindable> Substitutable for Scope<T> {
    type Output = Scope<T>;

    fn subst(self, subst: &mut Subst) -> Scope<T> {
        self.capture_subst(subst.clone())
    }

    fn into_output(self) -> Scope<T> {
        self
    }
}

impl Scope<Tm> {
    pub fn into_func(self) -> Tm {
        Tm::func(self)
    }

    pub fn id() -> Scope<Tm> {
        Scope::new(0, Tm::var(0))
    }

    pub fn deep_nf(self) -> Scope<Tm> {
        self.map_without_capture(|tm| tm.deep_nf())
    }
}

impl Scope<Ty> {
    pub fn deep_nf(self) -> Scope<Ty> {
        self.map_without_capture(|ty| ty.deep_nf())
    }
}

impl Scope<Scope<Tm>> {
    pub fn deep_nf(self) -> Scope<Scope<Tm>> {
        self.map_without_capture(|scope| scope.deep_nf())
    }
}

impl Scope<Scope<Ty>> {
    pub fn deep_nf(self) -> Scope<Scope<Ty>> {
        self.map_without_capture(|scope| scope.deep_nf())
    }
}

macro_rules! impl_bindable_tuple {
    ($($ty:ident,)*) => {
        impl<$($ty,)*> Bindable for ($($ty,)*)
        where
            $($ty: Bindable,)*
        {
            #[allow(non_snake_case)]
            #[allow(unused_variables)]
            fn capture_subst(self, subst: Subst) -> ($($ty,)*) {
                let ($($ty,)*) = self;
                $(
                    let $ty = $ty.capture_subst(subst.clone());
                )*
                ($($ty,)*)
            }
        }
    };
}

impl_bindable_tuple!();
impl_bindable_tuple!(T0,);
impl_bindable_tuple!(T0, T1,);
impl_bindable_tuple!(T0, T1, T2,);
impl_bindable_tuple!(T0, T1, T2, T3,);
impl_bindable_tuple!(T0, T1, T2, T3, T4,);
impl_bindable_tuple!(T0, T1, T2, T3, T4, T5,);
impl_bindable_tuple!(T0, T1, T2, T3, T4, T5, T6,);
impl_bindable_tuple!(T0, T1, T2, T3, T4, T5, T6, T7,);
impl_bindable_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8,);
impl_bindable_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9,);
impl_bindable_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10,);
impl_bindable_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11,);
impl_bindable_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12,);
impl_bindable_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13,);
impl_bindable_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14,);
impl_bindable_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15,);


