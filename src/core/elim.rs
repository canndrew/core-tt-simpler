use crate::priv_prelude::*;

pub type Elim = Weaken<ElimKind>;

#[derive(Clone, Debug, Contextual)]
pub enum ElimKind {
    TagsApart,
    Fold {
        motive: Scope<Ty>,
        zero_inhab: Tm,
        succ_inhab: Scope<Scope<Tm>>,
    },
    UniqueIdentity {
        motive: Scope<Ty>,
        inhab: Tm,
    },
    Cong {
        motive: Scope<Scope<Ty>>,
        inhab: Tm,
    },
    Explode {
        motive: Scope<Ty>,
    },
    Case {
        motive: Scope<Ty>,
        lhs_inhab: Scope<Tm>,
        rhs_inhab: Scope<Tm>,
    },
    ProjHead,
    ProjTail,
    App {
        arg_tm: Tm,
    },
}

pub type Stuck = Weaken<Arc<StuckData>>;

pub struct StuckData {
    root_var_index: usize,
    elims: Vec<Elim>,
}

impl Contextual for StuckData {
    fn ctx_len(&self) -> usize {
        cmp::max(self.root_var_index, self.elims.ctx_len())
    }

    fn collect_usages(&self, usages: &mut Usages) {
        usages.set_to_one(self.root_var_index);
        self.elims.collect_usages(usages);
    }

    fn filter_usages(&mut self, usages: &Usages) {
        self.root_var_index = usages.filter_index(self.root_var_index);
        self.elims.filter_usages(usages);
    }

    fn unfilter_usages(&mut self, usages: &Usages) {
        self.root_var_index = usages.unfilter_index(self.root_var_index);
        self.elims.unfilter_usages(usages);
    }
}


