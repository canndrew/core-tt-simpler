use crate::priv_prelude::*;

pub trait WellFormed {
    type Params;
}

impl<T> WellFormed for Weaken<T>
where
    T: WellFormed,
{
    type Params = T::Params;
}

impl<T> WellFormed for Arc<T>
where
    T: WellFormed,
{
    type Params = T::Params;
}

impl WellFormed for FormKind {
    type Params = ();
}

impl WellFormed for IntroKind {
    type Params = Ty;
}

impl WellFormed for LazyData {
    type Params = Ty;
}

impl<T> WellFormed for OrLazy<T>
where
    T: AsTmKind + WellFormed,
{
    type Params = T::Params;
}

impl WellFormed for NameKind {
    type Params = ();
}

impl WellFormed for TyKind {
    type Params = ();
}

impl<T> WellFormed for Scope<T>
where
    T: WellFormed,
{
    type Params = (Ty, Scope<T::Params>);
}

impl WellFormed for StuckKind {
    type Params = ();
}

impl WellFormed for Subst {
    type Params = Vec<Ty>;
}

impl WellFormed for TmKind {
    type Params = Ty;
}

impl WellFormed for NeutralKind {
    type Params = Ty;
}

macro_rules! tuple_impl_well_formed {
    ($($ty:ident,)*) => {
        impl<$($ty,)*> WellFormed for ($($ty,)*)
        where
            $($ty: WellFormed,)*
        {
            type Params = ($($ty::Params,)*);
        }
    };
}

tuple_impl_well_formed!();
tuple_impl_well_formed!(T0,);
tuple_impl_well_formed!(T0,T1,);
tuple_impl_well_formed!(T0,T1,T2,);
tuple_impl_well_formed!(T0,T1,T2,T3,);
tuple_impl_well_formed!(T0,T1,T2,T3,T4,);
tuple_impl_well_formed!(T0,T1,T2,T3,T4,T5,);
tuple_impl_well_formed!(T0,T1,T2,T3,T4,T5,T6,);
tuple_impl_well_formed!(T0,T1,T2,T3,T4,T5,T6,T7,);
tuple_impl_well_formed!(T0,T1,T2,T3,T4,T5,T6,T7,T8,);
tuple_impl_well_formed!(T0,T1,T2,T3,T4,T5,T6,T7,T8,T9,);
tuple_impl_well_formed!(T0,T1,T2,T3,T4,T5,T6,T7,T8,T9,T10,);
tuple_impl_well_formed!(T0,T1,T2,T3,T4,T5,T6,T7,T8,T9,T10,T11,);
tuple_impl_well_formed!(T0,T1,T2,T3,T4,T5,T6,T7,T8,T9,T10,T11,T12,);
tuple_impl_well_formed!(T0,T1,T2,T3,T4,T5,T6,T7,T8,T9,T10,T11,T12,T13,);
tuple_impl_well_formed!(T0,T1,T2,T3,T4,T5,T6,T7,T8,T9,T10,T11,T12,T13,T14,);
tuple_impl_well_formed!(T0,T1,T2,T3,T4,T5,T6,T7,T8,T9,T10,T11,T12,T13,T14,T15,);

