use crate::priv_prelude::*;

/*
pub struct Constraint {
    unique_tm: Tm,
    #[expect(unused)]
    proof_opt: Option<Scope<Tm>>,
}
*/

pub struct Simplification {
    //pub constraints: BTreeMap<usize, Constraint>,
    pub unlifted_subst_index: usize,
    pub subst: Subst,
    pub eliminated_vars: Usages,
    pub output_ty: Ty,
    pub iso: Iso,
}

impl Simplification {
    pub fn id(ty: Ty) -> Simplification {
        let ctx_len = ty.ctx_len();

        Simplification {
            unlifted_subst_index: ctx_len,
            subst: Subst::id(ctx_len),
            eliminated_vars: Usages::empty(),
            output_ty: ty,
            iso: Iso::refl(),
        }
    }

    pub fn impossible(from_ty: Ty, scope: Scope<Tm>) -> Simplification {
        Simplification::from_iso(Ty::never(), Iso::scope_never_to_iso_never(from_ty, scope))
    }

    pub fn from_iso(output_ty: Ty, iso: Iso) -> Simplification {
        let ctx_len = max_all([output_ty.ctx_len(), iso.ctx_len()]);
        Simplification {
            //constraints: BTreeMap::new(),
            unlifted_subst_index: ctx_len,
            subst: Subst::id(ctx_len),
            eliminated_vars: Usages::empty(),
            output_ty,
            iso,
        }
    }

    pub fn simplify_more(self, from_ty: Ty) -> Simplification {
        let Some(next_simplification) = self.output_ty.clone().simplify() else {
            return self;
        };

        let Simplification {
            unlifted_subst_index: unlifted_subst_index_0,
            subst: subst_0,
            eliminated_vars: eliminated_vars_0,
            output_ty: _,
            iso: iso_0,
        } = self;
        let Simplification {
            unlifted_subst_index: unlifted_subst_index_1,
            subst: mut subst_1,
            eliminated_vars: eliminated_vars_1,
            output_ty: output_ty_1,
            iso: iso_1,
        } = next_simplification;

        let weakening = {
            let mut weakening = Usages::ones(unlifted_subst_index_1);
            weakening.set_run_to_one(subst_1.subst_index(), subst_1.len());
            weakening
        };
        let subst_0 = subst_0.unfiltered(&weakening);
        let iso_0 = iso_0.unfiltered(&weakening);

        let eliminated_vars = {
            let mut next_var_index = unlifted_subst_index_1;
            let mut eliminated_vars = eliminated_vars_0.clone_truncate(next_var_index);
            for (offset, var_tm) in subst_1.iter_tms().enumerate() {
                if let Some(index) = var_tm.as_var()
                && index == next_var_index
                {
                    if eliminated_vars_0.get(unlifted_subst_index_1.strict_add(offset)) {
                        eliminated_vars.set_to_one(next_var_index);
                    }
                    next_var_index += 1;
                }
            }
            eliminated_vars.or_assign(&eliminated_vars_1);
            eliminated_vars
        };
        let unlifted_subst_index = cmp::min(unlifted_subst_index_0, unlifted_subst_index_1);
        let iso = Iso::transitivity(
            iso_0.subst(&mut subst_1),
            iso_1,
            from_ty,
            output_ty_1.clone(),
        );
        let output_ty = output_ty_1;
        let subst = subst_0.compose(subst_1);

        Simplification {
            unlifted_subst_index,
            subst,
            output_ty,
            iso,
            eliminated_vars,
        }
    }
}

impl Ty {
    pub fn simplify(self) -> Option<Simplification> {
        let form = self.try_reduce_to_form()?;
        form.simplify()
    }
}

impl Form {
    fn simplify(self) -> Option<Simplification> {
        match Arc::unwrap_or_clone(self.into_inner()) {
            | FormKind::Name
            | FormKind::Universe
            | FormKind::Nat
            | FormKind::Never
            | FormKind::Unit
            => None,

            FormKind::Equal { eq_ty, eq_tm_0, eq_tm_1 } => {
                simplify_equal(eq_ty, eq_tm_0, eq_tm_1)
            },
            FormKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                simplify_sum(lhs_name, lhs_ty, rhs_ty)
            },
            FormKind::Sigma { head_name, head_ty, tail_ty } => {
                simplify_sigma(head_name, head_ty, tail_ty)
            },
            FormKind::Pi { arg_name, arg_ty, res_ty } => {
                simplify_pi(arg_name, arg_ty, res_ty)
            },
        }
    }
}

fn simplify_equal(
    eq_ty: Ty,
    eq_tm_0: Tm,
    eq_tm_1: Tm,
) -> Option<Simplification> {
    if let Some(eq_tm) = Unify::unify(eq_tm_0.clone(), eq_tm_1.clone()) {
        return Some(Simplification::from_iso(
            Ty::unit(),
            Iso::reflexive_equality_to_unit(eq_tm)),
        );
    }

    let ctx_len = max_all([eq_ty.ctx_len(), eq_tm_0.ctx_len(), eq_tm_1.ctx_len()]);

    if let Some(var_index) = eq_tm_0.as_var() && eq_tm_1.ctx_len() <= var_index {
        /*
        let mut constraints = BTreeMap::new();
        constraints.insert(var_index, Constraint {
            unique_tm: eq_tm_1.clone(),
            proof_opt: Some(Scope::id()),
        });
        */
        let unlifted_subst_index = var_index;
        let subst = Subst::single_var(var_index, eq_tm_1.clone());
        let eliminated_vars = Usages::empty();
        let output_ty = Ty::unit();
        let iso = Iso::reflexive_equality_to_unit(eq_tm_1);
        //return Some(Simplification { constraints, eliminated_vars, output_ty, iso });
        return Some(Simplification { unlifted_subst_index, subst, eliminated_vars, output_ty, iso });
    }

    if let Some(var_index) = eq_tm_1.as_var() && eq_tm_0.ctx_len() <= var_index {
        /*
        let mut constraints = BTreeMap::new();
        constraints.insert(var_index, Constraint {
            unique_tm: eq_tm_0.clone(),
            proof_opt: Some(Scope::make(ctx_len, |tm| tm.symmetry(eq_ty, eq_tm_0.clone()))),
        });
        */
        let unlifted_subst_index = var_index;
        let subst = Subst::single_var(var_index, eq_tm_0.clone());
        let eliminated_vars = Usages::empty();
        let output_ty = Ty::unit();
        let iso = Iso::reflexive_equality_to_unit(eq_tm_0);
        //return Some(Simplification { constraints, eliminated_vars, output_ty, iso });
        return Some(Simplification { unlifted_subst_index, subst, eliminated_vars, output_ty, iso });
    }

    if let Some((eq_ty_eq_ty, eq_ty_eq_tm_0, eq_ty_eq_tm_1)) = eq_ty.clone().as_equal() {
        return Some(Simplification::from_iso(
            Ty::unit(),
            Iso::equality_of_equalities_to_unit(
                eq_ty_eq_ty,
                eq_ty_eq_tm_0,
                eq_ty_eq_tm_1,
                eq_tm_0,
                eq_tm_1,
            ),
        ));
    }

    let intro_0 = Arc::unwrap_or_clone(eq_tm_0.clone().try_reduce_to_intro()?.into_inner());
    let intro_1 = Arc::unwrap_or_clone(eq_tm_1.clone().try_reduce_to_intro()?.into_inner());
    match (intro_0, intro_1) {
        (IntroKind::Tag { .. }, IntroKind::Tag { .. }) => {
            Some(Simplification::impossible(
                Ty::equal(eq_ty, eq_tm_0, eq_tm_1),
                Scope::make(0, |tm| tm.tags_apart()),
            ))
        },

        (IntroKind::Constant { ubig: ubig_0 }, IntroKind::Constant { ubig: ubig_1 }) => {
            Some(Simplification::impossible(
                Ty::equal(eq_ty, eq_tm_0, eq_tm_1),
                Scope::make(0, |tm| tm.constants_apart(ubig_0, ubig_1)),
            ))
        },
        (IntroKind::Constant { ubig }, IntroKind::Succs { succ_count_m1, pred_tm }) => {
            if ubig <= succ_count_m1 {
                Some(Simplification::impossible(
                    Ty::equal(eq_ty, eq_tm_0, eq_tm_1),
                    Scope::make(0, |tm| {
                        tm.succs_injective(Tm::zero(), ubig).zero_isnt_succ()
                    }),
                ))
            } else {
                let succ_count = succ_count_m1 + 1usize;
                let ubig = ubig.strict_sub(&succ_count);
                let new_eq_tm_0 = Tm::constant(ubig);
                let new_eq_tm_1 = Weaken::new(pred_tm).into_tm();
                let simplification = Simplification::from_iso(
                    Ty::equal(eq_ty.clone(), new_eq_tm_0.clone(), new_eq_tm_1),
                    Iso::succs_injective_bijective(
                        new_eq_tm_0,
                        succ_count,
                    )
                    .symmetry(),
                );
                Some(simplification.simplify_more(Ty::equal(eq_ty, eq_tm_0, eq_tm_1)))
            }
        },
        (IntroKind::Succs { succ_count_m1, pred_tm }, IntroKind::Constant { ubig }) => {
            if ubig <= succ_count_m1 {
                let pred_tm = Weaken::new(pred_tm).into_tm();
                Some(Simplification::impossible(
                    Ty::equal(eq_ty, eq_tm_0, eq_tm_1),
                    Scope::make(0, |tm| {
                        tm
                        .succs_injective(
                            pred_tm.succs(succ_count_m1.strict_sub(&ubig) + 1usize),
                            ubig,
                        )
                        .succ_isnt_zero()
                    }),
                ))
            } else {
                let succ_count = succ_count_m1 + 1usize;
                let ubig = ubig.strict_sub(&succ_count);
                let new_eq_tm_0 = Weaken::new(pred_tm).into_tm();
                let new_eq_tm_1 = Tm::constant(ubig);
                let simplification = Simplification::from_iso(
                    Ty::equal(eq_ty.clone(), new_eq_tm_0.clone(), new_eq_tm_1),
                    Iso::succs_injective_bijective(
                        new_eq_tm_0,
                        succ_count,
                    )
                    .symmetry(),
                );
                Some(simplification.simplify_more(Ty::equal(eq_ty, eq_tm_0, eq_tm_1)))
            }
        },
        (
            IntroKind::Succs { succ_count_m1: succ_count_m1_0, pred_tm: pred_tm_0 },
            IntroKind::Succs { succ_count_m1: succ_count_m1_1, pred_tm: pred_tm_1 },
        ) => {
            let simplification = if succ_count_m1_0 <= succ_count_m1_1 {
                let new_eq_tm_0 = Weaken::new(pred_tm_0).into_tm();
                let new_eq_tm_1 = {
                    Weaken::new(pred_tm_1)
                    .into_tm()
                    .succs(succ_count_m1_1.strict_sub(&succ_count_m1_0))
                };
                Simplification::from_iso(
                    Ty::equal(eq_ty.clone(), new_eq_tm_0.clone(), new_eq_tm_1),
                    Iso::succs_injective_bijective(
                        new_eq_tm_0,
                        succ_count_m1_0,
                    )
                )
            } else {
                let new_eq_tm_0 = {
                    Weaken::new(pred_tm_0)
                    .into_tm()
                    .succs(succ_count_m1_0.strict_sub(&succ_count_m1_1))
                };
                let new_eq_tm_1 = Weaken::new(pred_tm_1).into_tm();
                Simplification::from_iso(
                    Ty::equal(eq_ty.clone(), new_eq_tm_0.clone(), new_eq_tm_1),
                    Iso::succs_injective_bijective(
                        new_eq_tm_0,
                        succ_count_m1_1,
                    )
                )
            };
            Some(simplification.simplify_more(Ty::equal(eq_ty, eq_tm_0, eq_tm_1)))
        },



        (IntroKind::InjLhs { lhs_tm: lhs_tm_0 }, IntroKind::InjLhs { lhs_tm: lhs_tm_1 }) => {
            let lhs_tm_0 = Weaken::new(lhs_tm_0);
            let lhs_tm_1 = Weaken::new(lhs_tm_1);
            let (lhs_name, lhs_ty, rhs_ty) = eq_ty.clone().as_sum().unwrap();
            let simplification = Simplification::from_iso(
                Ty::equal(lhs_ty.clone(), lhs_tm_0.clone(), lhs_tm_1),
                Iso::inj_lhs_injective_bijective(
                    lhs_name, lhs_ty, rhs_ty, lhs_tm_0,
                ),
            );
            Some(simplification.simplify_more(Ty::equal(eq_ty, eq_tm_0, eq_tm_1)))
        },

        (IntroKind::InjRhs { rhs_tm: rhs_tm_0 }, IntroKind::InjRhs { rhs_tm: rhs_tm_1 }) => {
            let rhs_tm_0 = Weaken::new(rhs_tm_0);
            let rhs_tm_1 = Weaken::new(rhs_tm_1);
            let (lhs_name, lhs_ty, rhs_ty) = eq_ty.clone().as_sum().unwrap();
            let simplification = Simplification::from_iso(
                Ty::equal(rhs_ty.clone(), rhs_tm_0.clone(), rhs_tm_1),
                Iso::inj_rhs_injective_bijective(
                    lhs_name, lhs_ty, rhs_ty, rhs_tm_0,
                ),
            );
            Some(simplification.simplify_more(Ty::equal(eq_ty, eq_tm_0, eq_tm_1)))
        },

        (IntroKind::InjLhs { lhs_tm: lhs_tm_0 }, IntroKind::InjRhs { rhs_tm: _ }) => {
            let lhs_tm_0 = Weaken::new(lhs_tm_0);
            let (_lhs_name, lhs_ty, _rhs_ty) = eq_ty.clone().as_sum().unwrap();
            Some(Simplification::impossible(
                Ty::equal(eq_ty, eq_tm_0, eq_tm_1),
                Scope::make(ctx_len, |sum_eq| sum_eq.inj_lhs_injective(lhs_ty, lhs_tm_0)),
            ))
        },

        (IntroKind::InjRhs { rhs_tm: rhs_tm_0 }, IntroKind::InjLhs { lhs_tm: _ }) => {
            let rhs_tm_0 = Weaken::new(rhs_tm_0);
            let (_lhs_name, _lhs_ty, rhs_ty) = eq_ty.clone().as_sum().unwrap();
            Some(Simplification::impossible(
                Ty::equal(eq_ty, eq_tm_0, eq_tm_1),
                Scope::make(ctx_len, |sum_eq| sum_eq.inj_rhs_injective(rhs_ty, rhs_tm_0)),
            ))
        },

        (
            IntroKind::Pair { head_tm: head_tm_0, tail_tm: tail_tm_0 },
            IntroKind::Pair { head_tm: head_tm_1, tail_tm: tail_tm_1 },
        ) => {
            let (head_name, head_ty, tail_ty) = eq_ty.clone().as_sigma().unwrap();
            let simplification = match tail_ty.try_strengthen() {
                Ok(tail_ty) => {
                    Simplification::from_iso(
                        Ty::sigma(
                            head_name.clone(),
                            Ty::equal(head_ty.clone(), head_tm_0.clone(), head_tm_1.clone()),
                            Scope::constant(
                                Ty::equal(tail_ty.clone(), tail_tm_0.clone(), tail_tm_1.clone()),
                            ),
                        ),
                        Iso::equality_of_non_dependent_pairs_to_non_dependent_pair_of_equalities(
                            head_name,
                            head_ty,
                            tail_ty,
                            head_tm_0,
                            head_tm_1,
                            tail_tm_0,
                            tail_tm_1,
                        ),
                    )
                },
                Err(tail_ty) => {
                    Simplification::from_iso(
                        Ty::sigma(
                            head_name.clone(),
                            Ty::equal(head_ty.clone(), head_tm_0.clone(), head_tm_1.clone()),
                            Scope::make(ctx_len, |head_eq| {
                                Ty::heterogeneous_equal(
                                    tail_ty.clone().bind(head_tm_0.clone()),
                                    tail_ty.clone().bind_eq(head_tm_0.clone(), head_eq),
                                    tail_tm_0.clone(),
                                    tail_tm_1.clone(),
                                )
                            }),
                        ),
                        Iso::equality_of_dependent_pairs_to_dependent_pair_of_equalities(
                            head_name,
                            head_ty,
                            tail_ty,
                            head_tm_0,
                            head_tm_1,
                            tail_tm_0,
                            tail_tm_1,
                        ),
                    )
                },
            };
            Some(simplification.simplify_more(Ty::equal(eq_ty, eq_tm_0, eq_tm_1)))
        },

        _ => None,
    }
}

fn simplify_sum(
    lhs_name: Name,
    lhs_ty: Ty,
    rhs_ty: Ty,
) -> Option<Simplification> {
    let lhs_simple_opt = lhs_ty.clone().simplify();
    let rhs_simple_opt = rhs_ty.clone().simplify();

    let (lhs_simple, rhs_simple, any_simplified) = match (lhs_simple_opt, rhs_simple_opt) {
        (None, None) => {
            let lhs_simple = Simplification::id(lhs_ty);
            let rhs_simple = Simplification::id(rhs_ty);
            (lhs_simple, rhs_simple, false)
        },
        (Some(lhs_simple), None) => {
            let rhs_simple = Simplification::id(rhs_ty);
            (lhs_simple, rhs_simple, true)
        },
        (None, Some(rhs_simple)) => {
            let lhs_simple = Simplification::id(lhs_ty);
            (lhs_simple, rhs_simple, true)
        },
        (Some(lhs_simple), Some(rhs_simple)) => {
            (lhs_simple, rhs_simple, true)
        },
    };

    /*
    match lhs_simple.output_ty.clone().try_reduce_to_form().map(|form| form.into_inner()) {
        Some(FormKind::Never) => {
            let Simplification {
                unlifted_subst_index, subst, eliminated_vars, output_ty: _, iso: lhs_iso,
            } = lhs_simple;
            debug_assert_eq!(unlifted_subst_index, subst.subst_index());
            debug_assert_eq!(subst.len(), 0);
            debug_assert_eq!(eliminated_vars.ctx_len(), 0);

            let Simplification {
                unlifted_subst_index, subst, eliminated_vars, output_ty, iso: rhs_iso,
            } = rhs_simple;




        },
    }
    */

    /*

    simplify lhs and rhs in parallel

    check if lhs is Never
    check if lhs is #(name: Never)

    same for rhs
    prefer lhs over rhs if both are named nevers

    */

    todo!()
}

fn simplify_sigma(
    _head_name: Name,
    _head_ty: Ty,
    _tail_ty: Scope<Ty>,
) -> Option<Simplification> {
    /*
    simplify head
    if it's never, then delete tail and become
        #(head_name: Never)
    if it's #(foo: Never) become #(foo: Never)
    substitute tail with the head substitution.
    if head is unit then become SimpleTail[unit()].simplified()
    simplify tail underscope
    if tail is never become never
    if tail is #(foo: Never) become #(foo: Never)
    check if head is affected.
        if it's constrained, become SimpleTail[head_tm]
        if it's eliminated then expand nat/sum/sigma head_tys and recurse.
    merged affected vars and become #(head_name: SimpleHead, .. SimpleTail)
    */
    todo!()
}

fn simplify_pi(
    _arg_name: Name,
    _arg_ty: Ty,
    _res_ty: Scope<Ty>,
) -> Option<Simplification> {
    /*
    */
    todo!()
}

