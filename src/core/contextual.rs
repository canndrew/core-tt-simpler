use crate::priv_prelude::*;

pub trait Contextual {
    fn ctx_len(&self) -> usize;
    fn collect_usages(&self, usages: &mut Usages);
    fn filter_usages(&mut self, usages: &Usages);
    fn unfilter_usages(&mut self, usages: &Usages);

    fn filtered(mut self, usages: &Usages) -> Self
    where
        Self: Sized,
    {
        self.filter_usages(usages);
        self
    }

    fn unfiltered(mut self, usages: &Usages) -> Self
    where
        Self: Sized,
    {
        self.unfilter_usages(usages);
        self
    }
}

impl<T: Clone + Contextual> Contextual for Box<T> {
    fn ctx_len(&self) -> usize {
        (&**self).ctx_len()
    }

    fn collect_usages(&self, usages: &mut Usages) {
        (&**self).collect_usages(usages)
    }

    fn filter_usages(&mut self, usages: &Usages) {
        (&mut **self).filter_usages(usages)
    }

    fn unfilter_usages(&mut self, usages: &Usages) {
        (&mut **self).unfilter_usages(usages)
    }
}

impl<T: Clone + Contextual> Contextual for Arc<T> {
    fn ctx_len(&self) -> usize {
        (&**self).ctx_len()
    }

    fn collect_usages(&self, usages: &mut Usages) {
        (&**self).collect_usages(usages)
    }

    fn filter_usages(&mut self, usages: &Usages) {
        Arc::make_mut(self).filter_usages(usages)
    }

    fn unfilter_usages(&mut self, usages: &Usages) {
        Arc::make_mut(self).unfilter_usages(usages)
    }
}

impl<T: Contextual> Contextual for Option<T> {
    fn ctx_len(&self) -> usize {
        match self {
            None => 0,
            Some(val) => val.ctx_len(),
        }
    }

    fn collect_usages(&self, usages: &mut Usages) {
        if let Some(val) = self {
            val.collect_usages(usages);
        }
    }

    fn filter_usages(&mut self, usages: &Usages) {
        if let Some(val) = self {
            val.filter_usages(usages);
        }
    }

    fn unfilter_usages(&mut self, usages: &Usages) {
        if let Some(val) = self {
            val.unfilter_usages(usages);
        }
    }
}

impl<T: Contextual> Contextual for [T] {
    fn ctx_len(&self) -> usize {
        self
        .iter()
        .map(|val| val.ctx_len())
        .max()
        .unwrap_or(0)
    }

    fn collect_usages(&self, usages: &mut Usages) {
        self
        .iter()
        .for_each(|val| val.collect_usages(usages))
    }

    fn filter_usages(&mut self, usages: &Usages) {
        self
        .iter_mut()
        .for_each(|val| val.filter_usages(usages))
    }

    fn unfilter_usages(&mut self, usages: &Usages) {
        self
        .iter_mut()
        .for_each(|val| val.unfilter_usages(usages))
    }
}

pub trait TupleOfContextual {
    type ScopeEach;
    fn scope_each(self, ctx_len: usize) -> Self::ScopeEach;
}

macro_rules! impl_contextual_tuple {
    ($($ty:ident,)*) => {
        impl<$($ty,)*> Contextual for ($($ty,)*)
        where
            $($ty: Contextual,)*
        {
            #[allow(non_snake_case)]
            #[allow(unused_variables)]
            fn ctx_len(&self) -> usize {
                let ($($ty,)*) = self;
                let ctx_len = 0;
                $(
                    let ctx_len = cmp::max(ctx_len, $ty.ctx_len());
                )*
                ctx_len
            }

            #[allow(non_snake_case)]
            #[allow(unused_variables)]
            fn collect_usages(&self, usages: &mut Usages) {
                let ($($ty,)*) = self;
                $(
                    $ty.collect_usages(usages);
                )*
            }

            #[allow(non_snake_case)]
            #[allow(unused_variables)]
            fn filter_usages(&mut self, usages: &Usages) {
                let ($($ty,)*) = self;
                $(
                    $ty.filter_usages(usages);
                )*
            }

            #[allow(non_snake_case)]
            #[allow(unused_variables)]
            fn unfilter_usages(&mut self, usages: &Usages) {
                let ($($ty,)*) = self;
                $(
                    $ty.unfilter_usages(usages);
                )*
            }
        }

        impl<$($ty,)*> TupleOfContextual for ($($ty,)*)
        where
            $($ty: Contextual,)*
        {
            type ScopeEach = ($(Scope<$ty>,)*);

            #[allow(non_snake_case)]
            #[allow(unused_variables)]
            fn scope_each(self, ctx_len: usize) -> ($(Scope<$ty>,)*) {
                let ($($ty,)*) = self;
                $(
                    let $ty = Scope::new(ctx_len, $ty);
                )*
                ($($ty,)*)
            }
        }
    };
}

impl_contextual_tuple!();
impl_contextual_tuple!(T0,);
impl_contextual_tuple!(T0, T1,);
impl_contextual_tuple!(T0, T1, T2,);
impl_contextual_tuple!(T0, T1, T2, T3,);
impl_contextual_tuple!(T0, T1, T2, T3, T4,);
impl_contextual_tuple!(T0, T1, T2, T3, T4, T5,);
impl_contextual_tuple!(T0, T1, T2, T3, T4, T5, T6,);
impl_contextual_tuple!(T0, T1, T2, T3, T4, T5, T6, T7,);
impl_contextual_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8,);
impl_contextual_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9,);
impl_contextual_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10,);
impl_contextual_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11,);
impl_contextual_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12,);
impl_contextual_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13,);
impl_contextual_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14,);
impl_contextual_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15,);



