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

    /*
    pub fn ctx_len(&self) -> usize {
        self.var_tms.ctx_len()
    }

    pub fn collect_usages(&self, usages: &mut Usages) {
        self.var_tms.collect_usages(usages);
    }
    */
}

/*
impl Contextual for Subst {
    fn ctx_len(&self) -> usize {
        self.var_tms.ctx_len()
    }

    fn collect_usages(&self, usages: &mut Usages) {
        self.var_tms.collect_usages(usages);
    }

    fn filter_usages(&mut self, usages: &Usages) {
        self.subst_index = usages.filter_index(self.subst_index);
        self.var_tms.filter_usages(usages);
    }

    fn unfilter_usages(&mut self, usages: &Usages) {
        self.subst_index = {
            usages
            .unfilter_index(self.subst_index)
            .unwrap_or_else(|| {
                debug_assert_eq!(self.subst_index, usages.count_ones());
                usages.ctx_len()
            })
        };
        self.var_tms.unfilter_usages(usages);
    }
}
*/

pub trait Substitutable {
    type Output;

    fn subst(self, subst: &mut Subst) -> Self::Output;
    fn into_output(self) -> Self::Output;
}

