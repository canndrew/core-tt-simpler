use crate::priv_prelude::*;

#[derive(Clone)]
pub struct Wrapper<T: WellFormed> {
    wrapped: T,
    ctx_params: DebugOnly<(Ctx, T::Params)>,
}

impl<T: WellFormed> Wrapper<T> {
    pub fn new(wrapped: T, ctx_params: DebugOnly<(Ctx, T::Params)>) -> Wrapper<T> {
        Wrapper { wrapped, ctx_params }
    }

    pub fn unwrap_parts(self) -> (T, DebugOnly<(Ctx, T::Params)>) {
        (self.wrapped, self.ctx_params)
    }

    pub fn into_wrapped(self) -> T {
        self.wrapped
    }

    pub fn wrapped_ref(&self) -> &T {
        &self.wrapped
    }

    pub fn debug_pprint(
        self,
        mut ctx_names: Vec<Name>,
        lock: DebugLock,
    ) -> impl fmt::Debug + fmt::Display
    where
        T: Pprint,
    {
        let (wrapped, ctx_params) = self.unwrap_parts();
        let (ctx, params) = ctx_params.unlock(lock);

        ctx_names.truncate(ctx.len());

        let mut current_ctx = ctx.clone();
        let mut ctx_names: Vec<_> = {
            ctx_names
            .into_iter()
            .rev()
            .map(|name| {
                let (name, name_ctx_params) = name.unwrap_parts();
                let (name_ctx, ()) = name_ctx_params.unlock(lock);
                current_ctx = current_ctx.parent().unwrap();
                assert!(name_ctx.is_subctx_of(&current_ctx));
                name
            })
            .collect()
        };
        ctx_names.reverse();
        assert!(current_ctx.is_root());

        let mut ctx = ctx.as_var_ty_vec();
        wrapped.pprint(&mut ctx_names, &mut ctx, params)
    }
}

pub trait IsWrapper {
    type Wrapped: WellFormed;
}

impl<T: WellFormed> IsWrapper for Wrapper<T> {
    type Wrapped = T;
}

pub trait TupleOfWrapper {
    type Wrapped: WellFormed;

    fn merge<T>(
        self,
        func: impl FnOnce(
            DebugLock,
            &Self::Wrapped,
            Ctx,
            <Self::Wrapped as WellFormed>::Params,
        ) -> T,
    ) -> (Self::Wrapped, DebugOnly<T>);

    fn unlock_merge(
        self,
        lock: DebugLock,
        ctx: Ctx,
    ) -> (Self::Wrapped, Ctx, <Self::Wrapped as WellFormed>::Params);
}

macro_rules! tuple_impl_tuple_of_wrapper {
    ($($ty:ident,)*) => {
        impl<$($ty,)*> TupleOfWrapper for ($(Wrapper<$ty>,)*)
        where
            $($ty: WellFormed,)*
        {
            type Wrapped = ($($ty,)*);

            #[allow(non_snake_case)]
            fn merge<T>(
                self,
                func: impl FnOnce(
                    DebugLock,
                    &($($ty,)*),
                    Ctx,
                    ($($ty::Params,)*),
                ) -> T,
            ) -> (($($ty,)*), DebugOnly<T>) {
                let ($($ty,)*) = self;
                let wrapped = ($($ty.wrapped,)*);
                $(
                    let $ty: (DebugOnly<Ctx>, DebugOnly<_>) = $ty.ctx_params.scatter();
                )*

                let ctxs: [DebugOnly<Ctx>; _] = [$($ty.0,)*];
                let ctxs = ctxs.gather();
                let params = ($($ty.1,)*).gather();
                let merged = (ctxs, params).gather().map(|lock, (ctxs, params)| {
                    let ctx = Ctx::common_super_ctx(ctxs);
                    func(lock, &wrapped, ctx, params)
                });

                (wrapped, merged)
            }

            #[allow(unused_variables)]
            #[allow(non_snake_case)]
            fn unlock_merge(
                self,
                lock: DebugLock,
                ctx: Ctx,
            ) -> (
                ($($ty,)*),
                Ctx,
                ($($ty::Params,)*),
            ) {
                let ($($ty,)*) = self;
                let wrapped = ($($ty.wrapped,)*);
                $(
                    let $ty: (Ctx, _) = $ty.ctx_params.unlock(lock);
                )*

                let ctxs: [Ctx; _] = [$($ty.0,)*];
                let more_ctx = Ctx::common_super_ctx(ctxs);
                let ctx = Ctx::common_super_ctx_2(ctx, more_ctx);
                let params = ($($ty.1,)*);
                (wrapped, ctx, params)
            }
        }
    };
}

tuple_impl_tuple_of_wrapper!();
tuple_impl_tuple_of_wrapper!(T0,);
tuple_impl_tuple_of_wrapper!(T0,T1,);
tuple_impl_tuple_of_wrapper!(T0,T1,T2,);
tuple_impl_tuple_of_wrapper!(T0,T1,T2,T3,);
tuple_impl_tuple_of_wrapper!(T0,T1,T2,T3,T4,);
tuple_impl_tuple_of_wrapper!(T0,T1,T2,T3,T4,T5,);
tuple_impl_tuple_of_wrapper!(T0,T1,T2,T3,T4,T5,T6,);
tuple_impl_tuple_of_wrapper!(T0,T1,T2,T3,T4,T5,T6,T7,);
tuple_impl_tuple_of_wrapper!(T0,T1,T2,T3,T4,T5,T6,T7,T8,);
tuple_impl_tuple_of_wrapper!(T0,T1,T2,T3,T4,T5,T6,T7,T8,T9,);
tuple_impl_tuple_of_wrapper!(T0,T1,T2,T3,T4,T5,T6,T7,T8,T9,T10,);
tuple_impl_tuple_of_wrapper!(T0,T1,T2,T3,T4,T5,T6,T7,T8,T9,T10,T11,);
tuple_impl_tuple_of_wrapper!(T0,T1,T2,T3,T4,T5,T6,T7,T8,T9,T10,T11,T12,);
tuple_impl_tuple_of_wrapper!(T0,T1,T2,T3,T4,T5,T6,T7,T8,T9,T10,T11,T12,T13,);
tuple_impl_tuple_of_wrapper!(T0,T1,T2,T3,T4,T5,T6,T7,T8,T9,T10,T11,T12,T13,T14,);
tuple_impl_tuple_of_wrapper!(T0,T1,T2,T3,T4,T5,T6,T7,T8,T9,T10,T11,T12,T13,T14,T15,);

impl<T: WellFormed> Unify for Wrapper<T>
where
    T: Unify,
    T::Params: Unify,
{
    fn unify(wrapper_0: Wrapper<T>, wrapper_1: Wrapper<T>) -> Option<Wrapper<T>> {
        let ((thing_0, thing_1), ctx_params) = {
            (wrapper_0, wrapper_1)
            .merge(|_, _, ctx, (params_0, params_1)| {
                let params = Unify::unify(params_0, params_1).unwrap();
                (ctx, params)
            })
        };
        let thing = Unify::unify(thing_0, thing_1)?;
        Some(Wrapper::new(thing, ctx_params))
    }
}

impl<T: WellFormed> DeepNf for Wrapper<T>
where
    T: DeepNf,
    T::Output: WellFormed<Params = T::Params>,
{
    type Output = Wrapper<T::Output>;

    fn deep_nf(self) -> Wrapper<T::Output> {
        let (wrapped, ctx_params) = self.unwrap_parts();
        let wrapped = wrapped.deep_nf();
        Wrapper::new(wrapped, ctx_params)
    }
}

