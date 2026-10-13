use crate::priv_prelude::*;

pub type Stuck = Weaken<StuckKind>;

#[derive(Clone, Debug)]
pub struct StuckKind {
    pub(crate) kind: Arc<NeutralKind>,
}

impl Contextual for StuckKind {
    fn ctx_len(&self) -> usize {
        self.kind.ctx_len()
    }

    fn collect_usages(&self, usages: &mut Usages) {
        self.kind.collect_usages(usages)
    }

    fn filter_usages(&mut self, usages: &Usages) {
        self.kind.filter_usages(usages)
    }

    fn unfilter_usages(&mut self, usages: &Usages) {
        self.kind.unfilter_usages(usages)
    }
}

impl Stuck {
    pub fn var(index: usize) -> Stuck {
        let usages = Usages::single_var(index);
        Weaken::from_usages_and_weak(usages, StuckKind::var_0())
    }

    pub fn into_tm(self) -> Tm {
        self.map(|stuck| OrLazy::Reduced(TmKind::Stuck { stuck }))
    }

    pub fn into_name(self) -> Name {
        self.map(|stuck| OrLazy::Reduced(NameKind::Stuck { stuck }))
    }

    pub fn into_ty(self) -> Ty {
        self.map(|stuck| OrLazy::Reduced(TyKind::Stuck { stuck }))
    }

    pub fn infer_ty(self, ctx: &mut Vec<Ty>) -> Ty {
        self.into_inner().infer_ty(ctx)
    }

    pub fn into_val_tm(self) -> ValTm {
        self.map(|stuck| TmKind::Stuck { stuck })
    }

    pub fn collect_stuck_vars(self, usages: &mut Usages) {
        self.into_inner().collect_stuck_vars(usages)
    }
}

impl StuckKind {
    pub fn var_0() -> StuckKind {
        StuckKind {
            kind: NeutralKind::var_0(),
        }
    }

    pub fn collect_stuck_vars(self, usages: &mut Usages) {
        Arc::unwrap_or_clone(self.kind).collect_stuck_vars_assuming_stuck(usages)
    }

    pub fn infer_ty(self, ctx: &mut Vec<Ty>) -> Ty {
        // stuck neutrals can always have their type inferred
        Arc::unwrap_or_clone(self.kind).try_infer_ty(ctx).unwrap()
    }

    pub fn is_prop(&self) -> bool {
        self.kind.is_prop()
    }

    pub fn as_equal(self) -> Option<(Ty, Tm, Tm)> {
        Arc::unwrap_or_clone(self.kind).as_equal()
    }

    pub fn as_var(&self) -> Option<usize> {
        self.kind.as_var()
    }

    pub fn into_neutral(self) -> Arc<NeutralKind> {
        self.kind
    }
}

impl Unify for StuckKind {
    fn unify(
        stuck_kind_0: StuckKind,
        stuck_kind_1: StuckKind,
    ) -> Option<StuckKind> {
        fn unify_neutral_kind(
            neutral_kind_0: NeutralKind,
            neutral_kind_1: NeutralKind,
        ) -> Option<NeutralKind> {
            if let Some(neutral_kind) = unify_structurally_equal(
                neutral_kind_0.clone(),
                neutral_kind_1.clone(),
            ) {
                return Some(neutral_kind);
            }

            if let Some(neutral_kind_0) = neutral_kind_0.clone().try_commuting_conversions() {
                return unify_neutral_kind(neutral_kind_0, neutral_kind_1);
            }

            if let Some(neutral_kind_1) = neutral_kind_1.try_commuting_conversions() {
                return unify_neutral_kind(neutral_kind_0, neutral_kind_1);
            }

            None
        }

        fn unify_structurally_equal(
            neutral_kind_0: NeutralKind,
            neutral_kind_1: NeutralKind,
        ) -> Option<NeutralKind> {
            match neutral_kind_0 {
                NeutralKind::Bind { .. } => unreachable!(),
                NeutralKind::Var { index: index_0 } => {
                    let NeutralKind::Var { index: index_1 } = neutral_kind_1 else {
                        return None;
                    };
                    let index = as_equal(index_0, &index_1)?;
                    Some(NeutralKind::Var { index })
                },

                NeutralKind::Fold {
                    elim: elim_0,
                    motive: motive_0,
                    zero_inhab: zero_inhab_0,
                    succ_inhab: succ_inhab_0,
                } => {
                    let NeutralKind::Fold {
                        elim: elim_1,
                        motive: motive_1,
                        zero_inhab: zero_inhab_1,
                        succ_inhab: succ_inhab_1,
                    } = neutral_kind_1 else {
                        return None;
                    };

                    let stuck_0 = elim_0.as_stuck().unwrap();
                    let stuck_1 = elim_1.as_stuck().unwrap();
                    let stuck = Stuck::unify(
                        stuck_0, stuck_1,
                    )?;
                    let motive = Unify::unify(motive_0, motive_1)?;
                    let zero_inhab = Unify::unify(zero_inhab_0, zero_inhab_1)?;
                    let succ_inhab = Unify::unify(succ_inhab_0, succ_inhab_1)?;
                    let elim = stuck.into_tm();
                    Some(NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab })
                },

                NeutralKind::Explode { motive: motive_0 } => {
                    let NeutralKind::Explode {
                        motive: motive_1,
                    } = neutral_kind_1 else {
                        return None;
                    };

                    let motive = Unify::unify(motive_0, motive_1)?;

                    Some(NeutralKind::Explode { motive })
                },

                NeutralKind::Case {
                    lhs_name,
                    elim: elim_0,
                    motive: motive_0,
                    lhs_inhab: lhs_inhab_0,
                    rhs_inhab: rhs_inhab_0,
                } => {
                    let NeutralKind::Case {
                        lhs_name: _,
                        elim: elim_1,
                        motive: motive_1,
                        lhs_inhab: lhs_inhab_1,
                        rhs_inhab: rhs_inhab_1,
                    } = neutral_kind_1 else {
                        return None;
                    };

                    let stuck_0 = elim_0.as_stuck().unwrap();
                    let stuck_1 = elim_1.as_stuck().unwrap();
                    let stuck = Stuck::unify(
                        stuck_0, stuck_1,
                    )?;

                    let motive = Unify::unify(motive_0, motive_1)?;

                    let lhs_inhab = Unify::unify(lhs_inhab_0, lhs_inhab_1)?;
                    let rhs_inhab = Unify::unify(rhs_inhab_0, rhs_inhab_1)?;
                    let elim = stuck.into_tm();
                    Some(NeutralKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab })
                },

                NeutralKind::ProjHead { elim: elim_0 } => {
                    let NeutralKind::ProjHead { elim: elim_1 } = neutral_kind_1 else {
                        return None;
                    };

                    let stuck_0 = elim_0.as_stuck().unwrap();
                    let stuck_1 = elim_1.as_stuck().unwrap();
                    let stuck = StuckKind::unify(
                        stuck_0, stuck_1,
                    )?;

                    let elim = OrLazy::Reduced(TmKind::Stuck { stuck });
                    Some(NeutralKind::ProjHead { elim })
                },

                NeutralKind::ProjTail { elim: elim_0 } => {
                    let NeutralKind::ProjTail { elim: elim_1 } = neutral_kind_1 else {
                        return None;
                    };

                    let stuck_0 = elim_0.as_stuck().unwrap();
                    let stuck_1 = elim_1.as_stuck().unwrap();
                    let stuck = StuckKind::unify(
                        stuck_0, stuck_1,
                    )?;

                    let elim = OrLazy::Reduced(TmKind::Stuck { stuck });
                    Some(NeutralKind::ProjTail { elim })
                },

                NeutralKind::App { elim: elim_0, arg_tm: arg_tm_0 } => {
                    let NeutralKind::App { elim: elim_1, arg_tm: arg_tm_1 } = neutral_kind_1 else {
                        return None;
                    };

                    let stuck_0 = elim_0.as_stuck().unwrap();
                    let stuck_1 = elim_1.as_stuck().unwrap();
                    let stuck = Stuck::unify(
                        stuck_0, stuck_1,
                    )?;
                    let arg_tm = Unify::unify(arg_tm_0, arg_tm_1)?;

                    let elim = stuck.into_tm();
                    Some(NeutralKind::App { elim, arg_tm })
                },

                NeutralKind::ObsEqual {
                    eq_ty: eq_ty_0,
                    eq_tm_0: eq_tm_0_0,
                    eq_tm_1: eq_tm_1_0,
                } => {
                    let NeutralKind::ObsEqual {
                        eq_ty: eq_ty_1,
                        eq_tm_0: eq_tm_0_1,
                        eq_tm_1: eq_tm_1_1,
                    } = neutral_kind_1 else {
                        return None;
                    };

                    let eq_ty = Unify::unify(eq_ty_0, eq_ty_1)?;
                    let eq_tm_0 = Unify::unify(eq_tm_0_0, eq_tm_0_1)?;
                    let eq_tm_1 = Unify::unify(eq_tm_1_0, eq_tm_1_1)?;

                    Some(NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 })
                },

                NeutralKind::Cast {
                    ty_0: ty_0_0,
                    ty_1: ty_1_0,
                    tm_0: tm_0_0,
                } => {
                    let NeutralKind::Cast {
                        ty_0: ty_0_1,
                        ty_1: ty_1_1,
                        tm_0: tm_0_1,
                    } = neutral_kind_1 else {
                        return None;
                    };

                    let ty_0 = Unify::unify(ty_0_0, ty_0_1)?;
                    let ty_1 = Unify::unify(ty_1_0, ty_1_1)?;
                    let tm_0 = Unify::unify(tm_0_0, tm_0_1)?;
                    Some(NeutralKind::Cast { ty_0, ty_1, tm_0 })
                },
            }
        }

        let StuckKind { kind: neutral_kind_0 } = stuck_kind_0;
        let StuckKind { kind: neutral_kind_1 } = stuck_kind_1;
        let neutral_kind_0 = Arc::unwrap_or_clone(neutral_kind_0);
        let neutral_kind_1 = Arc::unwrap_or_clone(neutral_kind_1);

        let neutral_kind = unify_neutral_kind(neutral_kind_0, neutral_kind_1)?;
        Some(StuckKind { kind: Arc::new(neutral_kind) })
    }
}

impl Substitutable for StuckKind {
    type Output = ValTm;

    fn subst(self, subst: &mut Subst) -> ValTm {
        Arc::unwrap_or_clone(self.kind).subst(subst)
    }

    fn into_output(self) -> ValTm {
        Weaken::new(self)
        .map(|stuck| TmKind::Stuck { stuck })
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<StuckKind> {
        let kind = Arc::new(Arc::unwrap_or_clone(self.kind).try_strengthen_index(var_index)?);
        Some(StuckKind { kind })
    }
}

impl DeepNf for StuckKind {
    type Output = Stuck;

    fn deep_nf(self) -> Stuck {
        let StuckKind { kind } = self;
        Arc::unwrap_or_clone(kind)
        .deep_nf_assuming_stuck()
        .map(|kind| {
            StuckKind { kind: Arc::new(kind) }
        })
    }
}

