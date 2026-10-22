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

    pub fn as_var(&self) -> Option<usize> {
        let index = self.weak().as_var()?;
        Some(self.usages().unfilter_index(index))
    }
}

impl StuckKind {
    pub fn var_0() -> StuckKind {
        StuckKind {
            kind: NeutralKind::var_0(),
        }
    }

    pub fn var(index: usize) -> StuckKind {
        StuckKind {
            kind: Arc::new(NeutralKind::Var { index }),
        }
    }

    pub fn collect_stuck_vars(self, usages: &mut Usages) {
        Arc::unwrap_or_clone(self.kind).collect_stuck_vars_assuming_stuck(usages)
    }

    pub fn infer_ty(self, ctx: &mut Vec<Ty>) -> Ty {
        // stuck neutrals can always have their type inferred
        Arc::unwrap_or_clone(self.kind).try_infer_ty(ctx).unwrap()
    }

    pub fn is_prop(self, prop_ty_vars: &mut Vec<usize>) -> bool {
        Arc::unwrap_or_clone(self.kind).is_prop_assuming_stuck_ty(prop_ty_vars)
    }

    pub fn is_discrete(&self) -> bool {
        self.kind.is_discrete_assuming_stuck_ty()
    }

    pub fn is_functorial(self, ty_var_index: usize, negative: bool) -> bool {
        Arc::unwrap_or_clone(self.kind).is_functorial_assuming_stuck_ty(ty_var_index, negative)
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

    pub fn neutral_ref(&self) -> &Arc<NeutralKind> {
        &self.kind
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

            if let Some(neutral_kind_0) = {
                neutral_kind_0
                .clone()
                .try_commuting_conversions_assuming_stuck()
            } {
                let neutral_kind_0 = Arc::unwrap_or_clone(
                    neutral_kind_0
                    .reduced()
                    .into_inner()
                    .as_stuck()
                    .unwrap()
                    .into_neutral()
                );
                return unify_neutral_kind(neutral_kind_0, neutral_kind_1);
            }

            if let Some(neutral_kind_1) = {
                neutral_kind_1
                .try_commuting_conversions_assuming_stuck()
            } {
                let neutral_kind_1 = Arc::unwrap_or_clone(
                    neutral_kind_1
                    .reduced()
                    .into_inner()
                    .as_stuck()
                    .unwrap()
                    .into_neutral()
                );
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

                    let stuck_0 = elim_0.reduced().as_stuck().unwrap();
                    let stuck_1 = elim_1.reduced().as_stuck().unwrap();
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

                    let stuck_0 = elim_0.reduced().as_stuck().unwrap();
                    let stuck_1 = elim_1.reduced().as_stuck().unwrap();
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

impl NeutralKind {
    fn collect_stuck_vars_assuming_stuck(self, usages: &mut Usages) {
        match self {
            NeutralKind::Explode { .. } => (),

            NeutralKind::Var { index } => {
                usages.set_to_one(index);
            },

            NeutralKind::Bind { .. } => unreachable!(),

            | NeutralKind::ProjHead { elim }
            | NeutralKind::ProjTail { elim }
            => {
                elim.reduced().as_stuck().unwrap().collect_stuck_vars(usages)
            },

            | NeutralKind::Fold { elim, .. }
            | NeutralKind::Case { elim, .. }
            | NeutralKind::App { elim, .. }
            => {
                elim
                .into_inner()
                .reduced()
                .as_stuck()
                .unwrap()
                .collect_stuck_vars(usages)
            },

            NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 } => {
                match eq_ty.into_inner().reduced() {
                    TyKind::Form { .. } => {
                        if let Some(stuck) = eq_tm_0.clone().as_stuck() {
                            stuck.collect_stuck_vars(usages);
                        }
                        if let Some(stuck) = eq_tm_1.clone().as_stuck() {
                            stuck.collect_stuck_vars(usages);
                        }
                    },
                    TyKind::Stuck { stuck } => {
                        stuck.collect_stuck_vars(usages);
                    },
                }
            },

            NeutralKind::Cast { ty_0, ty_1, tm_0: _ } => {
                if let Some(stuck) = ty_0.as_stuck() {
                    stuck.collect_stuck_vars(usages);
                }
                if let Some(stuck) = ty_1.as_stuck() {
                    stuck.collect_stuck_vars(usages);
                }
            },
        }
    }

    fn is_prop_assuming_stuck_ty(self, prop_ty_vars: &mut Vec<usize>) -> bool {
        let ctx_len = prop_ty_vars.last().map_or(0, |index| index + 1);
        match self {
            NeutralKind::Bind { .. } => unreachable!(),

            | NeutralKind::Var { index } => {
                let mut prop_ty_vars = prop_ty_vars.iter().rev().copied();
                loop {
                    match prop_ty_vars.next() {
                        None => break false,
                        Some(var_index) => match index.cmp(&var_index) {
                            cmp::Ordering::Less => break false,
                            cmp::Ordering::Equal => break true,
                            cmp::Ordering::Greater => (),
                        },
                    }
                }
            },

            | NeutralKind::Explode { motive: _ }
            | NeutralKind::ObsEqual { .. }
            => true,

            NeutralKind::Fold { elim: _, motive: _, zero_inhab, succ_inhab } => {
                let ctx_len = cmp::max(succ_inhab.ctx_len(), ctx_len);

                zero_inhab.into_ty().is_prop(prop_ty_vars) && {
                    prop_ty_vars.push(ctx_len + 1);
                    let ret = {
                        succ_inhab
                        .into_inner(ctx_len)
                        .into_inner(ctx_len + 1)
                        .into_ty()
                        .is_prop(prop_ty_vars)
                    };
                    prop_ty_vars.pop();
                    ret
                }
            },

            NeutralKind::Case { lhs_name: _, elim: _, motive: _, lhs_inhab, rhs_inhab } => {
                let ctx_len = cmp::max(
                    cmp::max(lhs_inhab.ctx_len(), rhs_inhab.ctx_len()),
                    ctx_len,
                );
                lhs_inhab.into_inner(ctx_len).into_ty().is_prop(prop_ty_vars) &&
                rhs_inhab.into_inner(ctx_len).into_ty().is_prop(prop_ty_vars)
            },

            | NeutralKind::ProjHead { .. }
            | NeutralKind::ProjTail { .. }
            | NeutralKind::App { .. }
            | NeutralKind::Cast { .. }
            => false,
        }
    }

    fn is_discrete_assuming_stuck_ty(&self) -> bool {
        match self {
            NeutralKind::Bind { .. } => unreachable!(),

            | NeutralKind::Explode { motive: _ }
            | NeutralKind::ObsEqual { .. }
            => true,

            NeutralKind::Fold { elim: _, motive: _, zero_inhab, succ_inhab } => {
                // TODO: track discrete-ness of type variables
                zero_inhab.clone().into_ty().is_discrete() &&
                succ_inhab.inner_ref().inner_ref().clone().into_ty().is_discrete()
            },

            NeutralKind::Case { lhs_name: _, elim: _, motive: _, lhs_inhab, rhs_inhab } => {
                lhs_inhab.inner_ref().clone().into_ty().is_discrete() &&
                rhs_inhab.inner_ref().clone().into_ty().is_discrete()
            },

            | NeutralKind::Var { .. }
            | NeutralKind::ProjHead { .. }
            | NeutralKind::ProjTail { .. }
            | NeutralKind::App { .. }
            | NeutralKind::Cast { .. }
            => false,
        }
    }

    fn is_functorial_assuming_stuck_ty(self, ty_var_index: usize, negative: bool) -> bool {
        match self {
            NeutralKind::Var { index } => {
                !negative && index == ty_var_index
            },

            NeutralKind::Bind { .. } => unreachable!(),

            NeutralKind::Fold { .. } => {
                // TODO
                false
            },

            NeutralKind::Explode { .. } => true,

            NeutralKind::Case { lhs_name: _, elim, motive: _, lhs_inhab, rhs_inhab } => {
                !elim.usages().get(ty_var_index) &&
                lhs_inhab
                .map_without_capture(|tm| tm.into_ty())
                .is_functorial(ty_var_index, negative) &&
                rhs_inhab
                .map_without_capture(|tm| tm.into_ty())
                .is_functorial(ty_var_index, negative)
            },

            NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 } => {
                !eq_tm_0.usages().get(ty_var_index) &&
                !eq_tm_1.usages().get(ty_var_index) &&
                eq_ty.is_functorial(ty_var_index, negative)
            },

            | NeutralKind::ProjHead { .. }
            | NeutralKind::ProjTail { .. }
            | NeutralKind::App { .. }
            | NeutralKind::Cast { .. }
            => false,
        }
    }

    fn deep_nf_assuming_stuck(self) -> Weaken<NeutralKind> {
        match self {
            NeutralKind::Var { index } => Weaken::new(NeutralKind::Var { index }),

            NeutralKind::Bind { .. } => unreachable!(),

            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                let elim = elim.as_stuck().unwrap().deep_nf().into_tm();
                let motive = motive.deep_nf().map_without_capture(|motive| motive.into_ty());
                let zero_inhab = zero_inhab.deep_nf().into_tm();
                let succ_inhab = {
                    succ_inhab
                    .deep_nf()
                    .map_without_capture(|succ_inhab| {
                        succ_inhab.map_without_capture(|succ_inhab| succ_inhab.into_tm())
                    })
                };
                Weaken::new(NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab })
            },

            NeutralKind::Explode { motive } => {
                let motive = {
                    motive
                    .deep_nf()
                    .lift_weaken()
                    .into_inner()
                    .map_without_capture(OrLazy::Reduced)
                };

                Weaken::new(NeutralKind::Explode { motive })
            },

            NeutralKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab } => {
                let lhs_name = lhs_name.deep_nf().into_name();
                let elim = elim.as_stuck().unwrap().deep_nf().into_tm();
                let motive = motive.deep_nf().map_without_capture(|motive| motive.into_ty());
                let lhs_inhab = {
                    lhs_inhab.deep_nf().map_without_capture(|lhs_inhab| lhs_inhab.into_tm())
                };
                let rhs_inhab = {
                    rhs_inhab.deep_nf().map_without_capture(|rhs_inhab| rhs_inhab.into_tm())
                };
                Weaken::new(NeutralKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab })
            },

            NeutralKind::ProjHead { elim } => {
                elim.reduced().as_stuck().unwrap().deep_nf().map(|stuck| {
                    let elim = OrLazy::Reduced(TmKind::Stuck { stuck });
                    NeutralKind::ProjHead { elim }
                })
            },

            NeutralKind::ProjTail { elim } => {
                elim.reduced().as_stuck().unwrap().deep_nf().map(|stuck| {
                    let elim = OrLazy::Reduced(TmKind::Stuck { stuck });
                    NeutralKind::ProjTail { elim }
                })
            },

            NeutralKind::App { elim, arg_tm } => {
                let elim = elim.as_stuck().unwrap().deep_nf().into_tm();
                let arg_tm = arg_tm.deep_nf().into_tm();
                Weaken::new(NeutralKind::App { elim, arg_tm })
            },

            NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 } => {
                let eq_ty = eq_ty.deep_nf().into_ty();
                let eq_tm_0 = eq_tm_0.deep_nf().into_tm();
                let eq_tm_1 = eq_tm_1.deep_nf().into_tm();
                Weaken::new(NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 })
            },

            NeutralKind::Cast { ty_0, ty_1, tm_0 } => {
                let ty_0 = ty_0.deep_nf().into_ty();
                let ty_1 = ty_1.deep_nf().into_ty();
                let tm_0 = tm_0.deep_nf().into_tm();
                Weaken::new(NeutralKind::Cast { ty_0, ty_1, tm_0 })
            },
        }
    }

    fn try_commuting_conversions_assuming_stuck(self) -> Option<NeutralKind> {
        match self {
            NeutralKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab } => {
                let elim = elim.as_stuck().unwrap().into_inner().into_neutral();

                match Arc::unwrap_or_clone(elim) {
                    NeutralKind::Explode { motive: inner_motive } => {
                        if let Some(inner_motive) = inner_motive.try_strengthen().ok() {
                            let motive = Scope::constant(
                                motive
                                .bind(
                                    Tm::explode(Scope::constant(Weaken::new(inner_motive))),
                                )
                                .into_inner(),
                            );
                            return Some(NeutralKind::Explode { motive });
                        }
                    },
                    NeutralKind::Case {
                        lhs_name: inner_lhs_name,
                        elim,
                        motive: inner_motive,
                        lhs_inhab: inner_lhs_inhab,
                        rhs_inhab: inner_rhs_inhab,
                    } => {
                        if let Some(inner_motive) = inner_motive.try_strengthen().ok() {
                            let ctx_len = max_all([
                                motive.ctx_len(),
                                inner_motive.ctx_len(),
                                lhs_inhab.ctx_len(),
                                rhs_inhab.ctx_len(),
                                inner_lhs_inhab.ctx_len(),
                                inner_rhs_inhab.ctx_len(),
                            ]);
                            return Some(NeutralKind::Case {
                                lhs_name: inner_lhs_name.clone(),
                                motive: Scope::make(ctx_len, |elim| {
                                    motive
                                    .clone()
                                    .bind(
                                        elim
                                        .case(
                                            inner_lhs_name,
                                            Scope::constant(inner_motive),
                                            inner_lhs_inhab.clone(),
                                            inner_rhs_inhab.clone(),
                                        ),
                                    )
                                }),
                                lhs_inhab: Scope::make(ctx_len, |lhs| {
                                    inner_lhs_inhab
                                    .bind(lhs)
                                    .case(
                                        lhs_name.clone(),
                                        motive.clone(),
                                        lhs_inhab.clone(),
                                        rhs_inhab.clone()
                                    )
                                }),
                                rhs_inhab: Scope::make(ctx_len, |rhs| {
                                    inner_rhs_inhab
                                    .bind(rhs)
                                    .case(
                                        lhs_name.clone(),
                                        motive,
                                        lhs_inhab,
                                        rhs_inhab,
                                    )
                                }),
                                elim,
                            });
                        }
                    },
                    _ => (),
                }
            },
            NeutralKind::App { elim, arg_tm } => {
                let elim = elim.as_stuck().unwrap().into_inner().into_neutral();
                match Arc::unwrap_or_clone(elim) {
                    NeutralKind::Explode { motive } => {
                        if let Some(motive) = motive.try_strengthen().ok() {
                            let (_, _, res_ty) = Weaken::new(motive).as_pi().unwrap();
                            return Some(NeutralKind::Explode {
                                motive: Scope::constant(res_ty.bind(arg_tm).into_inner()),
                            });
                        }
                    },
                    NeutralKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab } => {
                        if let Some(motive) = motive.try_strengthen().ok() {
                            let (_, _, res_ty) = motive.as_pi().unwrap();
                            return Some(NeutralKind::Case {
                                lhs_name,
                                elim,
                                motive: Scope::constant(res_ty.bind(arg_tm.clone())),
                                lhs_inhab: Scope::make(
                                    max_all([lhs_inhab.ctx_len(), arg_tm.ctx_len()]),
                                    |lhs| lhs_inhab.bind(lhs).app(arg_tm.clone()),
                                ), 
                                rhs_inhab: Scope::make(
                                    max_all([rhs_inhab.ctx_len(), arg_tm.ctx_len()]),
                                    |rhs| rhs_inhab.bind(rhs).app(arg_tm),
                                ), 
                            });
                        }
                    },
                    _ => (),
                }
            },
            _ => (),
        }
        None
    }
}

impl TryUnswapVars for StuckKind {
    fn try_unswap_vars(
        self,
        var_index: usize,
    ) -> Option<StuckKind> {
        let StuckKind { kind } = self;
        let kind = kind.try_unswap_vars(var_index)?;
        Some(StuckKind { kind })
    }
}

