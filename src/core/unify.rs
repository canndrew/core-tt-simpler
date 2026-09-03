use crate::priv_prelude::*;

pub trait Unify {
    type Meta;

    fn unify(
        ctx_tys: &mut Vec<Ty>,
        meta: Self::Meta,
        thing_0: Self,
        thing_1: Self,
    ) -> Option<Self>
    where
        Self: Sized;
}

impl<T> Unify for Arc<T>
where
    T: Clone,
    T: Unify,
{
    type Meta = T::Meta;

    fn unify(
        ctx_tys: &mut Vec<Ty>,
        meta: T::Meta,
        thing_0: Arc<T>,
        thing_1: Arc<T>,
    ) -> Option<Arc<T>> {
        if Arc::ptr_eq(&thing_0, &thing_1) {
            return Some(thing_0);
        }

        let thing_0 = Arc::unwrap_or_clone(thing_0);
        let thing_1 = Arc::unwrap_or_clone(thing_1);
        let thing = Unify::unify(ctx_tys, meta, thing_0, thing_1)?;
        Some(Arc::new(thing))
    }
}

