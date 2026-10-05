use crate::priv_prelude::*;

pub fn metas(
    proj_span: Span,
) -> [MetaTag; 8] {
    [
        MetaTag::ProjHeadImplicitTailProjections {
            proj_span: proj_span.clone(),
        },
        MetaTag::ProjHeadBaseTy {
            proj_span: proj_span.clone(),
        },
        MetaTag::ProjHeadBaseTm {
            proj_span: proj_span.clone(),
        },
        MetaTag::ProjHeadImplicitTailProjection {
            proj_span: proj_span.clone(),
        },
        MetaTag::ProjHeadImplicitTailProjectionInferredHeadName {
            proj_span: proj_span.clone(),
        },
        MetaTag::ProjHeadImplicitTailProjectionHeadTy {
            proj_span: proj_span.clone(),
        },
        MetaTag::ProjHeadImplicitTailProjectionTailTy {
            proj_span: proj_span.clone(),
        },
        MetaTag::ProjHeadImplicitTailProjectionBaseTyEqualsExpectedType {
            proj_span: proj_span.clone(),
        },
    ]
}

pub fn ty(
    ctx_len: usize,
    projections_metas: [&MetaTag; 8],
    proj_count: Tm,
    base_ty: Ty,
    base_tm: Tm,
) -> Ty {
    let [
        _,
        base_ty_meta,
        base_tm_meta,
        projection_meta,
        inferred_head_name_meta,
        head_ty_meta,
        tail_ty_meta,
        base_ty_eq_meta,
    ] = projections_metas;
    proj_count
    .fold(
        Scope::constant(Ty::pi(
            base_ty_meta.clone().into(),
            Ty::universe(),
            Scope::make(ctx_len + 1, |base_ty| Ty::pi(
                base_tm_meta.clone().into(),
                base_ty.into_ty(),
                Scope::constant(Ty::universe()),
            )),
        )),
        Tm::func(Scope::constant(Tm::func(Scope::constant(Ty::unit().into_tm())))),
        Scope::constant(Scope::make(ctx_len + 1, |projections_ty| {
            Tm::func(Scope::make(ctx_len + 2, |base_ty| {
                Tm::func(Scope::make(ctx_len + 3, |base_tm| {
                    Ty::sigma(
                        projection_meta.clone().into(),
                        Ty::sigma(
                            inferred_head_name_meta.clone().into(),
                            Ty::name(),
                            Scope::make(ctx_len + 4, |inferred_head_name| {
                                let inferred_head_name = inferred_head_name.into_name();
                                Ty::sigma(
                                    head_ty_meta.clone().into(),
                                    Ty::universe(),
                                    Scope::make(ctx_len + 5, |head_ty| {
                                        let head_ty = head_ty.into_ty();
                                        Ty::sigma(
                                            tail_ty_meta.clone().into(),
                                            Ty::pi(
                                                inferred_head_name.clone(),
                                                head_ty.clone(),
                                                Scope::constant(Ty::universe()),
                                            ),
                                            Scope::make(ctx_len + 6, |tail_ty| {
                                                Ty::sigma(
                                                    base_ty_eq_meta.clone().into(),
                                                    Ty::obs_equal(
                                                        Ty::universe(),
                                                        base_ty.clone(),
                                                        Ty::sigma(
                                                            inferred_head_name,
                                                            head_ty,
                                                            Scope::make(ctx_len + 7, |head_tm| {
                                                                tail_ty.app(head_tm).into_ty()
                                                            }),
                                                        )
                                                        .into_tm(),
                                                    ),
                                                    Scope::constant(Ty::unit()),
                                                )
                                            }),
                                        )
                                    }),
                                )
                            }),
                        ),
                        Scope::make(ctx_len + 4, |projection| {
                            let head_name = projection.clone().proj_head();
                            let projection = projection.proj_tail();
                            let head_ty = projection.clone().proj_head();
                            let projection = projection.proj_tail();
                            let tail_ty = projection.proj_head();
                            let pair = Tm::cast(
                                base_ty.into_ty(),
                                Ty::sigma(
                                    head_name.into_name(),
                                    head_ty.into_ty(),
                                    Scope::make(ctx_len + 5, |head| {
                                        tail_ty.clone().app(head).into_ty()
                                    }),
                                ),
                                base_tm,
                            );
                            let head = pair.clone().proj_head();

                            let base_ty = tail_ty.app(head);
                            let base_tm = pair.proj_tail();
                            projections_ty
                            .app(base_ty)
                            .app(base_tm)
                            .into_ty()
                        }),
                    )
                    .into_tm()
                }))
            }))
        })),
    )
    .app(base_ty.into_tm())
    .app(base_tm)
    .into_ty()
}

pub fn apply_to_ty(
    ctx_len: usize,
    projections_metas: [&MetaTag; 8],
    proj_count: Tm,
    base_ty: Ty,
    base_tm: Tm,
    projections: Tm,
) -> Ty {
    let [
        projections_meta,
        base_ty_meta,
        base_tm_meta,
        _,
        _,
        _,
        _,
        _,
    ] = projections_metas;

    proj_count
    .fold(
        Scope::make(ctx_len, |proj_count| Ty::pi(
            base_ty_meta.clone().into(),
            Ty::universe(),
            Scope::make(ctx_len + 1, |base_ty| Ty::pi(
                base_tm_meta.clone().into(),
                base_ty.clone().into_ty(),
                Scope::make(ctx_len + 2, |base_tm| Ty::pi(
                    projections_meta.clone().into(),
                    ty(
                        ctx_len + 3,
                        projections_metas,
                        proj_count,
                        base_ty.into_ty(),
                        base_tm,
                    ),
                    Scope::constant(Ty::universe()),
                )),
            )),
        )),
        Tm::func(Scope::make(ctx_len, |base_ty| {
            Tm::func(Scope::constant(Tm::func(Scope::constant(base_ty))))
        })),
        Scope::constant(Scope::make(ctx_len + 1, |apply_projections| {
            Tm::func(Scope::make(ctx_len + 2, |base_ty| {
                Tm::func(Scope::make(ctx_len + 3, |base_tm| {
                    Tm::func(Scope::make(ctx_len + 4, |projections| {
                        let projection = projections.clone().proj_head();
                        let projections = projections.proj_tail();

                        let head_name = projection.clone().proj_head();
                        let projection = projection.proj_tail();
                        let head_ty = projection.clone().proj_head();
                        let projection = projection.proj_tail();
                        let tail_ty = projection.proj_head();

                        let pair = Tm::cast(
                            base_ty.into_ty(),
                            Ty::sigma(
                                head_name.into_name(),
                                head_ty.into_ty(),
                                Scope::make(ctx_len + 5, |head| {
                                    tail_ty.clone().app(head).into_ty()
                                }),
                            ),
                            base_tm,
                        );
                        let head = pair.clone().proj_head();

                        let base_ty = tail_ty.app(head);
                        let base_tm = pair.proj_tail();
                        apply_projections
                        .app(base_ty)
                        .app(base_tm)
                        .app(projections)
                    }))
                }))
            }))
        })),
    )
    .app(base_ty.into_tm())
    .app(base_tm)
    .app(projections)
    .into_ty()
}

pub fn apply_to_tm(
    ctx_len: usize,
    projections_metas: [&MetaTag; 8],
    proj_count: Tm,
    base_ty: Ty,
    base_tm: Tm,
    projections: Tm,
) -> Tm {
    let [
        projections_meta,
        base_ty_meta,
        base_tm_meta,
        _,
        _,
        _,
        _,
        _,
    ] = projections_metas;

    proj_count
    .fold(
        Scope::make(ctx_len, |proj_count| Ty::pi(
            base_ty_meta.clone().into(),
            Ty::universe(),
            Scope::make(ctx_len + 1, |base_ty| Ty::pi(
                base_tm_meta.clone().into(),
                base_ty.clone().into_ty(),
                Scope::make(ctx_len + 2, |base_tm| Ty::pi(
                    projections_meta.clone().into(),
                    ty(
                        ctx_len + 3,
                        projections_metas,
                        proj_count.clone(),
                        base_ty.clone().into_ty(),
                        base_tm.clone(),
                    ),
                    Scope::make(ctx_len + 3, |projections| {
                        apply_to_ty(
                            ctx_len + 4,
                            projections_metas,
                            proj_count,
                            base_ty.into_ty(),
                            base_tm,
                            projections,
                        )
                    }),
                )),
            )),
        )),
        Tm::func(Scope::constant(Tm::func(Scope::make(ctx_len + 1, |base_tm| {
            Tm::func(Scope::constant(base_tm))
        })))),
        Scope::constant(Scope::make(ctx_len + 1, |apply_projections| {
            Tm::func(Scope::make(ctx_len + 2, |base_ty| {
                Tm::func(Scope::make(ctx_len + 3, |base_tm| {
                    Tm::func(Scope::make(ctx_len + 4, |projections| {
                        let projection = projections.clone().proj_head();
                        let projections = projections.proj_tail();

                        let head_name = projection.clone().proj_head();
                        let projection = projection.proj_tail();
                        let head_ty = projection.clone().proj_head();
                        let projection = projection.proj_tail();
                        let tail_ty = projection.proj_head();

                        let pair = Tm::cast(
                            base_ty.into_ty(),
                            Ty::sigma(
                                head_name.into_name(),
                                head_ty.into_ty(),
                                Scope::make(ctx_len + 5, |head| {
                                    tail_ty.clone().app(head).into_ty()
                                }),
                            ),
                            base_tm,
                        );
                        let head = pair.clone().proj_head();

                        let base_ty = tail_ty.app(head);
                        let base_tm = pair.proj_tail();
                        apply_projections
                        .app(base_ty)
                        .app(base_tm)
                        .app(projections)
                    }))
                }))
            }))
        })),
    )
    .app(base_ty.into_tm())
    .app(base_tm)
    .app(projections)
}

