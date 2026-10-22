use crate::priv_prelude::*;

#[derive(Clone, Debug)]
pub struct Weaken<T> {
    usages: Usages,
    weak: T,
}

impl<T> Weaken<T> {
    pub fn new(mut weak: T) -> Weaken<T>
    where
        T: Contextual,
    {
        let mut usages = Usages::empty();
        weak.collect_usages(&mut usages);
        weak.filter_usages(&usages);
        Weaken { usages, weak }
    }

    pub fn into_inner(self) -> T
    where
        T: Contextual,
    {
        let Weaken { usages, mut weak } = self;
        weak.unfilter_usages(&usages);
        weak
    }

    pub fn map<U>(self, func: impl FnOnce(T) -> U) -> Weaken<U>
    where
        U: Contextual,
    {
        let Weaken { usages, weak } = self;
        let weak = func(weak);
        let ret = Weaken { usages, weak };
        debug_assert_eq!(ret.weak.ctx_len(), ret.usages.count_ones());
        ret
    }

    pub fn map_out_unfiltered<U: Contextual>(self, func: impl FnOnce(T) -> U) -> U {
        let Weaken { usages, weak } = self;
        let ret = func(weak);
        ret.unfiltered(&usages)
    }

    pub fn try_map<U: Contextual>(
        self,
        func: impl FnOnce(T) -> Option<U>,
    ) -> Option<Weaken<U>> {
        let Weaken { usages, weak } = self;
        let weak = func(weak)?;
        Some(Weaken { usages, weak })
    }

    pub fn into_usages_and_weak(self) -> (Usages, T) {
        let Weaken { usages, weak } = self;
        (usages, weak)
    }

    pub fn from_usages_and_weak(usages: Usages, weak: T) -> Weaken<T>
    where
        T: Contextual,
    {
        debug_assert_eq!(usages.count_ones(), weak.ctx_len());
        Weaken { usages, weak }
    }

    pub fn usages(&self) -> &Usages {
        &self.usages
    }

    pub fn weak(&self) -> &T {
        &self.weak
    }

    pub fn into_weak(self) -> T {
        self.weak
    }
}

impl<T> Weaken<Weaken<T>> {
    pub fn flatten(self) -> Weaken<T> {
        let Weaken { usages, weak } = self;
        weak.unfiltered(&usages)
    }
}

impl<T: Contextual> Weaken<Scope<T>> {
    pub fn lift_scope(self) -> Scope<Weaken<T>> {
        let Weaken { mut usages, weak: Scope { ctx_len, inner } } = self;
        let mut inner_usages = Usages::empty();
        inner.collect_usages(&mut inner_usages);
        let outer_ctx_len = usages.ctx_len();
        if inner_usages.get(ctx_len) {
            usages.set_to_one(outer_ctx_len);
        }
        Scope { ctx_len: outer_ctx_len, inner: Weaken { usages, weak: inner } }
    }
}

impl<T> Weaken<Arc<T>> {
    pub fn new_arc(weak: T) -> Weaken<Arc<T>>
    where
        T: Contextual + Clone,
    {
        Weaken::new(weak).map(Arc::new)
    }

    pub fn into_inner_arc(self) -> T
    where
        T: Contextual + Clone,
    {
        let Weaken { usages, weak } = self;
        Arc::unwrap_or_clone(weak).unfiltered(&usages)
    }
}

impl<T> Contextual for Weaken<T> {
    fn ctx_len(&self) -> usize {
        self.usages.ctx_len()
    }

    fn collect_usages(&self, usages: &mut Usages) {
        usages.or_assign(&self.usages);
    }

    fn filter_usages(&mut self, usages: &Usages) {
        self.usages.filter(usages);
    }

    fn unfilter_usages(&mut self, usages: &Usages) {
        self.usages.unfilter(usages);
    }
}

impl<T> Substitutable for Weaken<T>
where
    T: Contextual + Substitutable<Output: Contextual>,
{
    type Output = T::Output;

    fn subst(self, subst: &mut Subst) -> T::Output {
        if self.ctx_len() <= subst.subst_index() {
            return self.into_output();
        }
        self.into_inner().subst(subst)
    }

    fn into_output(self) -> T::Output {
        let (usages, weak) = self.into_usages_and_weak();
        weak.into_output().unfiltered(&usages)
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<Weaken<T>> {
        let Weaken { usages, weak } = self;
        let (usages, bit) = usages.shift_remove(var_index);
        let weak = if bit {
            let sub_index = usages.filter_index(var_index);
            weak.try_strengthen_index(sub_index)?
        } else {
            weak
        };
        Some(Weaken { usages, weak })
    }
}

impl<T> Unify for Weaken<T>
where
    T: Contextual + Unify + Sized,
{
    fn unify(
        weaken_0: Weaken<T>,
        weaken_1: Weaken<T>,
    ) -> Option<Weaken<T>> {
        let thing_0 = weaken_0.into_inner();
        let thing_1 = weaken_1.into_inner();
        let thing = T::unify(thing_0, thing_1)?;
        Some(Weaken::new(thing))

        /*
         * TODO: is it worth filtering here?
         *
        let usages = Usages::merge_all_mut([&mut weaken_0.usages, &mut weaken_1.usages]);
        let thing_0 = weaken_0.into_inner();
        let thing_1 = weaken_1.into_inner();
        let thing = T::unify(thing_0, thing_1)?;
        let mut weaken = Weaken::new(thing);
        weaken.usages.unfilter(&usages);
        Some(weaken)
        */
    }
}

impl<T> DeepNf for Weaken<T>
where
    T: DeepNf<Output: Contextual>,
{
    type Output = T::Output;

    fn deep_nf(self) -> T::Output {
        self.map_out_unfiltered(|inner| {
            inner.deep_nf()
        })
    }
}

impl<T> TryUnswapVars for Weaken<T>
where
    T: TryUnswapVars,
    T: Contextual,
{
    fn try_unswap_vars(
        mut self,
        var_index: usize,
    ) -> Option<Weaken<T>> {
        if !self.usages.get(var_index) {
            if self.usages.get(var_index + 1) {
                self.usages.set_to_one(var_index);
                self.usages.set_to_zero(var_index + 1);
            }
            return Some(self);
        }

        let inner = self.into_inner().try_unswap_vars(var_index)?;
        Some(Weaken::new(inner))
    }
}

