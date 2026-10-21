use crate::priv_prelude::*;

const DEBUG_ASSERTIONS_ENABLED: bool = cfg!(debug_assertions);
const NUM_VALS: usize = DEBUG_ASSERTIONS_ENABLED as usize;
const NOT_NUM_VALS: usize = 1 - NUM_VALS;

#[derive(Clone)]
pub struct DebugOnly<T> {
    val: [T; NUM_VALS],
}

#[derive(Clone, Copy)]
pub struct DebugLock {
    #[allow(dead_code)]
    nevers: [!; NOT_NUM_VALS],
}

impl<T> DebugOnly<T> {
    pub fn new(func: impl FnOnce(DebugLock) -> T) -> DebugOnly<T> {
        let mut func = Some(func);
        let val = array::from_fn(|_| {
            func.take().unwrap()(DebugLock::new())
        });
        DebugOnly { val }
    }

    pub fn map<U>(self, func: impl FnOnce(DebugLock, T) -> U) -> DebugOnly<U> {
        let DebugOnly { val } = self;
        let mut func = Some(func);
        let val = val.map(|val| func.take().unwrap()(DebugLock::new(), val));
        DebugOnly { val }
    }

    pub fn map_multi<U, S>(self, func: impl FnOnce(DebugLock, T) -> U) -> S
    where
        S: GatherDebugOnly<Gather = U>,
        U: ScatterDebugOnly<S>,
    {
        self.map(func).scatter()
    }

    pub fn flat_map<U>(self, func: impl FnOnce(DebugLock, T) -> DebugOnly<U>) -> DebugOnly<U> {
        self.map(func).flatten()
    }

    pub fn flat_map_multi<U, S>(self, func: impl FnOnce(DebugLock, T) -> DebugOnly<U>) -> S
    where
        S: GatherDebugOnly<Gather = U>,
        U: ScatterDebugOnly<S>,
    {
        self.flat_map(func).scatter()
    }

    pub fn as_ref(&self) -> DebugOnly<&T> {
        let DebugOnly { val } = self;
        let val = val.each_ref();
        DebugOnly { val }
    }

    pub fn as_mut(&mut self) -> DebugOnly<&mut T> {
        let DebugOnly { val } = self;
        let val = val.each_mut();
        DebugOnly { val }
    }

    #[inline(always)]
    pub fn unlock(self, _lock: DebugLock) -> T {
        let DebugOnly { val } = self;
        val.into_iter().next().unwrap()
    }

    pub fn scatter<S>(self) -> S
    where
        S: GatherDebugOnly<Gather = T>,
        T: ScatterDebugOnly<S>,
    {
        ScatterDebugOnly::scatter(self)
    }

    pub fn or_default(self) -> T
    where
        T: Default,
    {
        self.val.into_iter().next().unwrap_or_default()
    }
}

impl<T> DebugOnly<DebugOnly<T>> {
    pub fn flatten(self) -> DebugOnly<T> {
        let DebugOnly { val } = self;
        let mut val = Some(val);
        let val = array::from_fn(|_| {
            let DebugOnly { val } = val.take().unwrap().into_iter().next().unwrap();
            val.into_iter().next().unwrap()
        });
        DebugOnly { val }
    }
}

impl<T: WellFormed> DebugOnly<Wrapper<T>> {
    pub fn unlock_unwrap(self, lock: DebugLock) -> (T, Ctx, T::Params) {
        let (val, ctx_params) = self.unlock(lock).unwrap_parts();
        let (ctx, params) = ctx_params.unlock(lock);
        (val, ctx, params)
    }
}

impl DebugLock {
    #[inline(always)]
    fn new() -> DebugLock {
        let nevers = array::from_fn(|_| unreachable!());
        DebugLock { nevers }
    }

    #[inline(always)]
    pub fn try_new() -> Result<DebugLock, fn(DebugLock) -> !> {
        match DEBUG_ASSERTIONS_ENABLED {
            true => {
                Ok(DebugLock::new())
            },
            false => {
                Err(|lock| lock.nevers.into_iter().next().unwrap())
            },
        }
    }
}

impl<T> Contextual for DebugOnly<T>
where
    T: Contextual,
{
    fn ctx_len(&self) -> usize {
        self.as_ref().map(|_, inner| inner.ctx_len()).or_default()
    }

    fn collect_usages(&self, usages: &mut Usages) {
        self.as_ref().map(|_, inner| inner.collect_usages(usages));
    }

    fn filter_usages(&mut self, usages: &Usages) {
        self.as_mut().map(|_, inner| inner.filter_usages(usages));
    }

    fn unfilter_usages(&mut self, usages: &Usages) {
        self.as_mut().map(|_, inner| inner.unfilter_usages(usages));
    }
}

pub trait GatherDebugOnly {
    type Gather;
    fn gather(self) -> DebugOnly<Self::Gather>;
}

impl<T> GatherDebugOnly for DebugOnly<T> {
    type Gather = T;

    fn gather(self) -> DebugOnly<T> {
        self
    }
}

impl<const N: usize, T> GatherDebugOnly for [T; N]
where
    T: GatherDebugOnly,
{
    type Gather = [T::Gather; N];

    fn gather(self) -> DebugOnly<[T::Gather; N]> {
        DebugOnly::new(|lock| {
            self.map(|val| val.gather().unlock(lock))
        })
    }
}

pub trait ScatterDebugOnly<S>
where
    S: GatherDebugOnly<Gather = Self>,
{
    fn scatter(this: DebugOnly<Self>) -> S
    where
        Self: Sized;
}

impl<T> ScatterDebugOnly<DebugOnly<T>> for T {
    fn scatter(this: DebugOnly<T>) -> DebugOnly<T> {
        this
    }
}

impl<const N: usize, T> ScatterDebugOnly<[DebugOnly<T>; N]> for [T; N] {
    fn scatter(this: DebugOnly<[T; N]>) -> [DebugOnly<T>; N] {
        let mut this = this.map(|_, val| val.into_iter());
        array::from_fn(|_| {
            DebugOnly::new(|lock| {
                this.as_mut().unlock(lock).next().unwrap()
            })
        })
    }
}

macro_rules! tuple_impl_gather_scatter_debug_only {
    ($($ty:ident,$s:ident,)*) => {
        impl<$($ty,)*> GatherDebugOnly for ($($ty,)*)
        where
            $($ty: GatherDebugOnly,)*
        {
            type Gather = ($($ty::Gather,)*);

            #[allow(unused_variables)]
            #[allow(non_snake_case)]
            fn gather(self) -> DebugOnly<($($ty::Gather,)*)> {
                DebugOnly::new(|lock| {
                    let ($($ty,)*) = self;
                    $(
                        let $ty = $ty.gather().unlock(lock);
                    )*
                    ($($ty,)*)
                })
            }
        }

        impl<$($ty,$s,)*> ScatterDebugOnly<($($s,)*)> for ($($ty,)*)
        where
            $(
                $s: GatherDebugOnly<Gather = $ty>,
                $ty: ScatterDebugOnly<$s>,
            )*
        {
            #[allow(unused_variables)]
            #[allow(non_snake_case)]
            fn scatter(this: DebugOnly<($($ty,)*)>) -> ($($s,)*) {
                match DebugLock::try_new() {
                    Ok(lock) => {
                        let ($($ty,)*) = this.unlock(lock);
                        $(
                            let $ty = ScatterDebugOnly::scatter(
                                DebugOnly::new(|_| $ty),
                            );
                        )*
                        ($($ty,)*)
                    },
                    Err(no_lock) => {
                        $(
                            let $ty: $s = ScatterDebugOnly::scatter(
                                DebugOnly::new(|lock| no_lock(lock))
                            );
                        )*
                        ($($ty,)*)
                    },
                }
            }
        }
    };
}

tuple_impl_gather_scatter_debug_only!();
tuple_impl_gather_scatter_debug_only!(T0,S0,);
tuple_impl_gather_scatter_debug_only!(T0,S0,T1,S1,);
tuple_impl_gather_scatter_debug_only!(T0,S0,T1,S1,T2,S2,);
tuple_impl_gather_scatter_debug_only!(T0,S0,T1,S1,T2,S2,T3,S3,);
tuple_impl_gather_scatter_debug_only!(T0,S0,T1,S1,T2,S2,T3,S3,T4,S4,);
tuple_impl_gather_scatter_debug_only!(T0,S0,T1,S1,T2,S2,T3,S3,T4,S4,T5,S5,);
tuple_impl_gather_scatter_debug_only!(T0,S0,T1,S1,T2,S2,T3,S3,T4,S4,T5,S5,T6,S6,);
tuple_impl_gather_scatter_debug_only!(T0,S0,T1,S1,T2,S2,T3,S3,T4,S4,T5,S5,T6,S6,T7,S7,);
tuple_impl_gather_scatter_debug_only!(T0,S0,T1,S1,T2,S2,T3,S3,T4,S4,T5,S5,T6,S6,T7,S7,T8,S8,);
tuple_impl_gather_scatter_debug_only!(T0,S0,T1,S1,T2,S2,T3,S3,T4,S4,T5,S5,T6,S6,T7,S7,T8,S8,T9,S9,);
tuple_impl_gather_scatter_debug_only!(T0,S0,T1,S1,T2,S2,T3,S3,T4,S4,T5,S5,T6,S6,T7,S7,T8,S8,T9,S9,T10,S10,);
tuple_impl_gather_scatter_debug_only!(T0,S0,T1,S1,T2,S2,T3,S3,T4,S4,T5,S5,T6,S6,T7,S7,T8,S8,T9,S9,T10,S10,T11,S11,);
tuple_impl_gather_scatter_debug_only!(T0,S0,T1,S1,T2,S2,T3,S3,T4,S4,T5,S5,T6,S6,T7,S7,T8,S8,T9,S9,T10,S10,T11,S11,T12,S12,);
tuple_impl_gather_scatter_debug_only!(T0,S0,T1,S1,T2,S2,T3,S3,T4,S4,T5,S5,T6,S6,T7,S7,T8,S8,T9,S9,T10,S10,T11,S11,T12,S12,T13,S13,);
tuple_impl_gather_scatter_debug_only!(T0,S0,T1,S1,T2,S2,T3,S3,T4,S4,T5,S5,T6,S6,T7,S7,T8,S8,T9,S9,T10,S10,T11,S11,T12,S12,T13,S13,T14,S14,);
tuple_impl_gather_scatter_debug_only!(T0,S0,T1,S1,T2,S2,T3,S3,T4,S4,T5,S5,T6,S6,T7,S7,T8,S8,T9,S9,T10,S10,T11,S11,T12,S12,T13,S13,T14,S14,T15,S15,);


