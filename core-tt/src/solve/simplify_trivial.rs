use crate::priv_prelude::*;

impl Ty {
    pub fn simplify_trivial(&self) -> (Ty, Iso) {
        match self.clone().reduced().into_inner() {
            TyKind::Form { form } => {
                form.simplify_trivial()
            },
            TyKind::Stuck { stuck } => {
                if let NeutralKind::ObsEqual {
                    eq_ty: _, eq_tm_0, eq_tm_1,
                } = &*stuck.into_neutral()
                && let Some(_) = Unify::unify(eq_tm_0.clone(), eq_tm_1.clone())
                {
                    let ty = Ty::unit();
                    let iso = Iso::between_props();
                    return (ty, iso);
                }

                let ty = self.clone();
                let iso = Iso::refl();
                (ty, iso)
            },
        }
    }
}

impl FormKind {
    pub fn simplify_trivial(self: &Arc<FormKind>) -> (Ty, Iso) {
        match &**self {
            | FormKind::Name
            | FormKind::Universe
            | FormKind::Nat
            | FormKind::Never
            | FormKind::Unit
            => {
                let ty = Weaken::new(OrLazy::Reduced(TyKind::Form { form: self.clone() }));
                let iso = Iso::refl();
                (ty, iso)
            },

            FormKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                let (new_lhs_ty, lhs_iso) = lhs_ty.simplify_trivial();
                let (new_rhs_ty, rhs_iso) = rhs_ty.simplify_trivial();
                let ty = Ty::sum(lhs_name.clone(), new_lhs_ty.clone(), new_rhs_ty.clone());
                let iso = Iso::sum_congruence(
                    lhs_name.clone(),
                    lhs_name.clone(),
                    lhs_ty.clone(),
                    new_lhs_ty.clone(),
                    rhs_ty.clone(),
                    new_rhs_ty.clone(),
                    lhs_iso,
                    rhs_iso,
                );
                (ty, iso)
            },

            FormKind::Sigma { head_name, head_ty, tail_ty } => {
                let ctx_len = cmp::max(head_ty.ctx_len(), tail_ty.ctx_len());

                let (new_head_ty, head_iso) = head_ty.simplify_trivial();
                let rebound_tail_ty = Scope::make(ctx_len, |head| {
                    let head = head_iso.rev.clone().bind(head);
                    tail_ty.clone().bind(head)
                });
                let (new_tail_ty, tail_iso) = {
                    let tail_ty_inner = rebound_tail_ty.into_inner(ctx_len);
                    let (new_tail_ty_inner, tail_iso_inner) = tail_ty_inner.simplify_trivial();
                    let new_tail_ty = Scope::new(ctx_len, new_tail_ty_inner);
                    let tail_iso = Scope::new(ctx_len, tail_iso_inner);
                    (new_tail_ty, tail_iso)
                };

                let iso = Iso::transitivity(
                    Iso::dependent_sigma_head_congruence(tail_ty.clone(), head_iso),
                    Iso::dependent_sigma_tail_congruence(tail_iso),
                );

                if let Some(()) = new_head_ty.clone().as_unit() {
                    let new_ty = new_tail_ty.bind(Tm::proof());
                    let iso = Iso::transitivity(
                        iso, Iso::sigma_unit_head(),
                    );
                    return (new_ty, iso);
                }

                if let Some((_, head_head_ty, head_tail_ty)) = new_head_ty.clone().as_sigma()
                && let Some(head_tail_ty) = head_tail_ty.try_strengthen().ok()
                && let Some(()) = head_tail_ty.as_unit()
                {
                    let iso = Iso::transitivity(
                        iso,
                        Iso::dependent_sigma_head_congruence(
                            new_tail_ty.clone(),
                            Iso::sigma_unit_tail(),
                        ),
                    );
                    let new_ty = Ty::sigma(
                        head_name.clone(),
                        head_head_ty,
                        Scope::make(ctx_len, |head| {
                            new_tail_ty.bind(head.pair(Tm::proof()))
                        }),
                    );
                    return (new_ty, iso);
                }

                /*
                if let Some(new_tail_ty) = new_tail_ty.clone().try_strengthen().ok()
                && let Some(()) = new_tail_ty.as_unit()
                && let Some(_) = new_head_ty.clone().as_sigma()
                {
                    let new_ty = new_head_ty;
                    let iso = Iso::transitivity(
                        iso,
                        Iso::sigma_unit_tail(),
                    );
                    return (new_ty, iso);
                }
                */

                let new_ty = Ty::sigma(head_name.clone(), new_head_ty, new_tail_ty);
                (new_ty, iso)
            },

            FormKind::Pi { arg_name, arg_ty, res_ty } => {
                let ctx_len = cmp::max(arg_ty.ctx_len(), res_ty.ctx_len());

                let (new_arg_ty, arg_iso) = arg_ty.simplify_trivial();
                let rebound_res_ty = Scope::make(ctx_len, |arg| {
                    let arg = arg_iso.rev.clone().bind(arg);
                    res_ty.clone().bind(arg)
                });
                let (new_res_ty, res_iso) = {
                    let res_ty_inner = rebound_res_ty.into_inner(ctx_len);
                    let (new_res_ty_inner, res_iso_inner) = res_ty_inner.simplify_trivial();
                    let new_res_ty = Scope::new(ctx_len, new_res_ty_inner);
                    let res_iso = Scope::new(ctx_len, res_iso_inner);
                    (new_res_ty, res_iso)
                };

                let iso = Iso::transitivity(
                    Iso::dependent_pi_arg_congruence(res_ty.clone(), arg_iso),
                    Iso::dependent_pi_res_congruence(res_iso),
                );

                if let Some(()) = new_arg_ty.clone().as_unit() {
                    let new_ty = new_res_ty.bind(Tm::proof());
                    let iso = Iso::transitivity(
                        iso, Iso::pi_unit_arg(),
                    );
                    return (new_ty, iso);
                }

                if let Some(new_res_ty) = new_res_ty.clone().try_strengthen().ok()
                && let Some(()) = new_res_ty.as_unit()
                {
                    let new_ty = Ty::unit();
                    let iso = Iso::transitivity(
                        iso,
                        Iso::between_props(),
                    );
                    return (new_ty, iso);
                }

                if let Some((
                    res_head_name, res_head_ty, res_tail_ty,
                )) = new_res_ty.clone().into_inner(ctx_len).as_sigma()
                && let Some(()) = res_tail_ty.into_inner(ctx_len + 1).as_unit()
                && let Some(head_name) = Scope::new(ctx_len, res_head_name).try_strengthen().ok()
                {
                    let iso = Iso::transitivity(
                        iso,
                        Iso::transitivity(
                            Iso::dependent_pi_res_congruence(
                                Scope::constant(Iso::sigma_unit_tail()),
                            ),
                            Iso::sigma_unit_tail().symmetry(),
                        ),
                    );
                    let new_ty = Ty::sigma(
                        head_name,
                        Ty::pi(
                            arg_name.clone(),
                            new_arg_ty,
                            Scope::new(ctx_len, res_head_ty),
                        ),
                        Scope::constant(Ty::unit()),
                    );
                    return (new_ty, iso);
                }

                let new_ty = Ty::pi(arg_name.clone(), new_arg_ty, new_res_ty);
                (new_ty, iso)
            },
        }
    }
}

