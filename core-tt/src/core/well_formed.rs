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

