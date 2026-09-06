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

    pub fn from_usages_and_weak(usages: Usages, weak: T) -> Weaken<T> {
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

impl<T: Clone> Weaken<Arc<T>> {
    pub fn new_arc(weak: T) -> Weaken<Arc<T>>
    where
        T: Contextual,
    {
        let blah_0 = Weaken::new(weak);
        debug_assert_eq!(blah_0.usages.count_ones(), blah_0.weak.ctx_len());
        blah_0.map(Arc::new)


        //Weaken::new(weak).map(Arc::new)
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

impl<T> Unify for Weaken<T>
where
    T: Contextual + Unify + Sized,
{
    type Meta = T::Meta;

    fn unify(
        ctx_tys: &mut Vec<Ty>,
        meta: T::Meta,
        weaken_0: Weaken<T>,
        weaken_1: Weaken<T>,
    ) -> Option<Weaken<T>> {
        let thing_0 = weaken_0.into_inner();
        let thing_1 = weaken_1.into_inner();
        let thing = T::unify(ctx_tys, meta, thing_0, thing_1)?;
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

