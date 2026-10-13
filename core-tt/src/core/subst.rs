use crate::priv_prelude::*;

#[derive(Clone, Debug)]
pub struct Subst {
    subst_index: usize,
    var_tms: Vec<Tm>,
}

impl Subst {
    pub fn id(ctx_len: usize) -> Subst {
        Subst {
            subst_index: ctx_len,
            var_tms: Vec::new(),
        }
    }

    pub fn subst_index(&self) -> usize {
        self.subst_index
    }

    pub fn from_var_tms(subst_index: usize, var_tms: Vec<Tm>) -> Subst {
        debug_assert!(var_tms.iter().all(|var_tm| var_tm.ctx_len() <= subst_index));
        Subst { subst_index, var_tms }
    }

    pub fn lift(mut self, amount: usize) -> Subst {
        self.var_tms.extend(
            (0..amount)
            .map(|offset| Tm::var(self.subst_index.strict_add(offset)))
        );
        self.subst_index = self.subst_index.strict_add(amount);
        self
    }

    pub fn is_id(&self) -> bool {
        self.var_tms.is_empty()
    }

    pub fn single_var(index: usize, var_tm: Tm) -> Subst {
        debug_assert!(var_tm.ctx_len() <= index);
        Subst {
            subst_index: index,
            var_tms: vec![var_tm],
        }
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.var_tms.len()
    }

    pub fn get_var_tm(&self, index: usize) -> Tm {
        match index.checked_sub(self.subst_index) {
            None => {
                Tm::var(index)
            },
            Some(var_tms_index) => {
                self.var_tms[var_tms_index].clone()
            },
        }
    }

    pub fn truncate(&mut self, ctx_len: usize) {
        let var_tms_len = ctx_len.saturating_sub(self.subst_index);
        debug_assert!(var_tms_len <= self.var_tms.len());
        self.var_tms.truncate(var_tms_len);
    }

    pub fn remove_unused_vars(self, usages: &Usages) -> (usize, Vec<Tm>) {
        let Subst { subst_index, mut var_tms} = self;
        debug_assert!(usages.ctx_len() <= subst_index + var_tms.len());

        let mut var_tm_index = subst_index;
        var_tms.retain(|_| {
            let ret = usages.get(var_tm_index);
            var_tm_index += 1;
            ret
        });
        (subst_index, var_tms)
    }

    pub fn with_composed<T>(
        &mut self,
        pre_subst: Subst,
        func: impl FnOnce(&mut Subst) -> T,
    ) -> T {
        debug_assert_eq!(self.subst_index + self.var_tms.len(), pre_subst.subst_index);
        let pre_subst = pre_subst.subst(self);
        let original_len = self.var_tms.len();
        self.var_tms.extend(pre_subst.var_tms);
        let ret = func(self);
        self.var_tms.truncate(original_len);
        ret
    }

    pub fn compose(
        self,
        other: Subst,
    ) -> Subst {
        let mut subst_1 = other;
        debug_assert_eq!(subst_1.subst_index + subst_1.var_tms.len(), self.subst_index);
        let subst_0 = self.subst(&mut subst_1);
        subst_1.var_tms.extend(subst_0.var_tms);
        subst_1
    }

    pub fn subst(mut self, subst: &mut Subst) -> Subst {
        self.var_tms = {
            self
            .var_tms
            .into_iter()
            .map(|var_tm| var_tm.capture_subst(subst.clone()))
            .collect()
        };
        self
    }

    pub fn iter_tms(&self) -> impl Iterator<Item = &Tm> {
        self.var_tms.iter()
    }
}

pub trait Substitutable: Sized {
    type Output;

    fn subst(self, subst: &mut Subst) -> Self::Output;
    fn into_output(self) -> Self::Output;
    fn try_strengthen_index(self, var_index: usize) -> Option<Self>;
}

impl<T, U> Substitutable for Arc<T>
where
    T: Clone + Substitutable<Output = Weaken<U>>,
    U: Clone + Contextual,
{
    type Output = Weaken<Arc<U>>;

    fn subst(self, subst: &mut Subst) -> Weaken<Arc<U>> {
        Arc::unwrap_or_clone(self).subst(subst).map(Arc::new)
    }

    fn into_output(self) -> Weaken<Arc<U>> {
        Arc::unwrap_or_clone(self).into_output().map(Arc::new)
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<Arc<T>> {
        Some(Arc::new(Arc::unwrap_or_clone(self).try_strengthen_index(var_index)?))
    }
}

macro_rules! impl_substitutable_tuple {
    ($($ty:ident,)*) => {
        impl<$($ty,)*> Substitutable for ($($ty,)*)
        where
            $($ty: Substitutable,)*
        {
            type Output = ($($ty::Output,)*);

            #[allow(non_snake_case)]
            #[allow(unused_variables)]
            #[allow(clippy::unused_unit)]
            fn subst(self, subst: &mut Subst) -> Self::Output {
                let ($($ty,)*) = self;
                $(
                    let $ty = $ty.subst(subst);
                )*
                ($($ty,)*)
            }

            #[allow(non_snake_case)]
            #[allow(clippy::unused_unit)]
            fn into_output(self) -> Self::Output {
                let ($($ty,)*) = self;
                $(
                    let $ty = $ty.into_output();
                )*
                ($($ty,)*)
            }

            #[allow(non_snake_case)]
            #[allow(unused_variables)]
            fn try_strengthen_index(self, var_index: usize) -> Option<Self> {
                let ($($ty,)*) = self;
                $(
                    let $ty = $ty.try_strengthen_index(var_index)?;
                )*
                Some(($($ty,)*))
            }
        }
    };
}

impl_substitutable_tuple!();
impl_substitutable_tuple!(T0,);
impl_substitutable_tuple!(T0, T1,);
impl_substitutable_tuple!(T0, T1, T2,);
impl_substitutable_tuple!(T0, T1, T2, T3,);
impl_substitutable_tuple!(T0, T1, T2, T3, T4,);
impl_substitutable_tuple!(T0, T1, T2, T3, T4, T5,);
impl_substitutable_tuple!(T0, T1, T2, T3, T4, T5, T6,);
impl_substitutable_tuple!(T0, T1, T2, T3, T4, T5, T6, T7,);
impl_substitutable_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8,);
impl_substitutable_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9,);
impl_substitutable_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10,);
impl_substitutable_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11,);
impl_substitutable_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12,);
impl_substitutable_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13,);
impl_substitutable_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14,);
impl_substitutable_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15,);



