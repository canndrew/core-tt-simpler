use crate::priv_prelude::*;

pub type Scope<T> = Wrapper<core_tt::Scope<<T as IsWrapper>::Wrapped>>;

impl<T> Wrapper<core_tt::Scope<T>>
where
    T: WellFormed,
{
    pub fn bind(self, var_tm: Tm) -> Wrapper<T>
    where
        T: Contextual + Bindable,
        T::Params: Contextual + Bindable,
    {
        let ((scope, var_tm), ctx_params) = {
            (self, var_tm)
            .merge(|_, (_, var_tm), ctx, ((scope_var_ty, inner_params), var_ty)| {
                Unify::unify(scope_var_ty, var_ty).unwrap();
                let params = inner_params.bind(var_tm.clone());
                (ctx, params)
            })
        };
        let thing = scope.bind(var_tm);
        Wrapper::new(thing, ctx_params)
    }
}

