use crate::priv_prelude::*;

pub fn metas(
    inj_span: Span,
) -> [MetaTag; 4] {
    [
        MetaTag::InjLhsImplicitRhsInjections {
            inj_span: inj_span.clone(),
        },
        MetaTag::InjLhsImplicitRhsInjection {
            inj_span: inj_span.clone(),
        },
        MetaTag::InjLhsImplicitRhsInjectionLhsName {
            inj_span: inj_span.clone(),
        },
        MetaTag::InjLhsImplicitRhsInjectionLhsTy {
            inj_span: inj_span.clone(),
        },
    ]
}

pub fn ty(
    ctx_len: usize,
    injections_metas: [&MetaTag; 4],
    inj_count: Tm,
) -> Ty {
    let [_, injection_meta, lhs_name_meta, lhs_ty_meta] = injections_metas;
    inj_count
    .fold(
        Scope::constant(Ty::universe()),
        Ty::unit().into_tm(),
        Scope::constant(Scope::make(ctx_len + 2, |state| {
            Ty::sigma(
                injection_meta.clone().into(),
                Ty::sigma(
                    lhs_name_meta.clone().into(),
                    Ty::name(),
                    Scope::constant(Ty::sigma(
                        lhs_ty_meta.clone().into(),
                        Ty::universe(),
                        Scope::constant(Ty::unit()),
                    )),
                ),
                Scope::constant(state.into_ty()),
            )
            .into_tm()
        })),
    )
    .into_ty()
}

pub fn apply_to_ty(
    ctx_len: usize,
    injections_metas: [&MetaTag; 4],
    inj_count: Tm,
    injections: Tm,
    base_ty: Ty,
) -> Ty {
    let [injections_meta, _, _, _] = injections_metas;
    inj_count
    .fold(
        Scope::make(ctx_len, |inj_count| {
            Ty::pi(
                injections_meta.clone().into(),
                ty(ctx_len + 1, injections_metas, inj_count),
                Scope::constant(Ty::universe()),
            )
        }),
        Tm::func(Scope::constant(base_ty.into_tm())),
        Scope::constant(Scope::make(ctx_len + 2, |apply_rhs_injections| {
            Tm::func(Scope::make(ctx_len + 3, |rhs_injections| {
                let rhs_injection = rhs_injections.clone().proj_head();
                let rhs_injections = rhs_injections.proj_tail();

                let lhs_name = rhs_injection.clone().proj_head();
                let rhs_injection = rhs_injection.proj_tail();
                let lhs_ty = rhs_injection.proj_head();

                Ty::sum(
                    lhs_name.into_name(),
                    lhs_ty.into_ty(),
                    apply_rhs_injections.app(rhs_injections).into_ty(),
                )
                .into_tm()
            }))
        })),
    )
    .app(injections)
    .into_ty()
}

pub fn apply_to_tm(
    ctx_len: usize,
    injections_metas: [&MetaTag; 4],
    inj_count: Tm,
    injections: Tm,
    base_ty: Ty,
    base_tm: Tm,
) -> Tm {
    let [injections_meta, _, _, _] = injections_metas;
    inj_count
    .fold(
        Scope::make(
            ctx_len,
            |inj_count| {
                Ty::pi(
                    injections_meta.clone().into(),
                    ty(ctx_len + 1, injections_metas, inj_count.clone()),
                    Scope::make(ctx_len + 1, |injections| {
                        apply_to_ty(
                            ctx_len + 2,
                            injections_metas,
                            inj_count,
                            injections,
                            base_ty,
                        )
                    }),
                )
            },
        ),
        Tm::func(Scope::constant(base_tm)),
        Scope::constant(Scope::make(ctx_len + 2, |apply_rhs_injections| {
            Tm::func(Scope::make(ctx_len + 3, |rhs_injections| {
                apply_rhs_injections.app(rhs_injections.proj_tail()).inj_rhs()
            }))
        })),
    )
    .app(injections)
}

