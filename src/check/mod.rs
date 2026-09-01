pub mod check_ctx;
pub mod checked;
pub mod typecheck;

/*
impl Check for UntypedTm {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        let UntypedTm { span, kind } = self;
        match &**kind {
            UntypedTmKind::Hole => {
                Checked::assume_ty(MetaTag::TypeOfHole { span: span.clone() }.into())
                .and_then(ch, |ch, _, hole_ty| {
                    Checked::assume(
                        MetaTag::Hole { span: span.clone() }.into(),
                        hole_ty.clone(),
                    )
                    .map(ch, |_, _, hole| (hole_ty, hole))
                })
            },

            UntypedTmKind::Var { name } => {
                name
                .check(ch)
                .group(MetaTag::CheckVarName { span: span.clone() })
                .and_then(ch, |ch, _, name| {
                    let name_ctx_len = name.ctx_len();
                    let mut iter = ch.var_names_tys.iter().rev();
                    let ty_index_opt = loop {
                        let Some((var_name, var_ty, index)) = iter.next() else {
                            break None;
                        };
                        if *index < name_ctx_len {
                            break None;
                        }
                        if Unify::unify(
                            name.clone(),
                            var_name.clone(),
                        ).is_some() {
                            break Some((var_ty.clone(), *index));
                        }
                    };
                    match ty_index_opt {
                        None => {
                            Checked::assume_ty(
                                MetaTag::TypeOfUnresolvedVariable { span: span.clone() },
                            )
                            .and_then(ch, |ch, _, var_ty| {
                                Checked::assume(
                                    MetaTag::UnresolvedVariable { span: span.clone() },
                                    Ty::never(),
                                )
                                .map(ch, |_, _, never| {
                                    let tm = never.explode(Scope::constant(var_ty.clone()));
                                    (var_ty, tm)
                                })
                            })
                        },
                        Some((var_ty, index)) => {
                            Checked::pure((var_ty, Tm::var(index)))
                        },
                    }
                })
            },

            UntypedTmKind::Bind { var_name, var_tm, body } => {
                var_name
                .check(ch)
                .group(MetaTag::CheckBindVarName { span: span.clone() })
                .and_then(ch, |ch, _, var_name| {
                    var_tm
                    .check(ch)
                    .group(MetaTag::CheckBindVarTm { span: span.clone() })
                    .and_then(ch, |ch, _, (var_ty, var_tm)| {
                        ch
                        .with_var(var_name, var_ty, |ch, _| {
                            body
                            .body
                            .check(ch)
                            .group(MetaTag::CheckBindBody { span: span.clone() })
                        })
                        .bind(var_tm)
                    })
                })
            },

            UntypedTmKind::Name => {
                let ty = Ty::universe();
                let tm = Ty::name().into_tm();
                Checked::pure((ty, tm))
            },

            UntypedTmKind::Tag { tag } => {
                let ty = Ty::name();
                let tm = Tm::tag(tag.clone());
                Checked::pure((ty, tm))
            },

            UntypedTmKind::TagsApart { tag_0, tag_1, elim } => {
                if tag_0 == tag_1 {
                    Checked::assume(
                        MetaTag::EqualTagsAreApart { tag: tag_0.clone(), span: span.clone() },
                        Ty::never(),
                    )
                    .map(ch, |_, _, never| (Ty::never(), never))
                } else {
                    elim
                    .check(ch)
                    .group(MetaTag::CheckTagsApartElim { span: span.clone() })
                    .cast(
                        ch,
                        MetaTag::TagsApartElim { span: span.clone() }.into(),
                        MetaTag::TagsApartElimHasCorrectType { span: span.clone() },
                        Ty::equal(Ty::name(), Tm::tag(tag_0.clone()), Tm::tag(tag_1.clone())),
                    )
                    .map(ch, |_, _, elim| {
                        let ty = Ty::never();
                        let tm = elim.tags_apart();
                        (ty, tm)
                    })
                }
            },

            UntypedTmKind::Universe => {
                let ty = Ty::universe();
                let tm = Ty::universe().into_tm();
                Checked::pure((ty, tm))
            },

            UntypedTmKind::NatTy => {
                let ty = Ty::universe();
                let tm = Ty::nat().into_tm();
                Checked::pure((ty, tm))
            },

            UntypedTmKind::Constant { ubig } => {
                let ty = Ty::nat();
                let tm = Tm::constant(ubig.clone());
                Checked::pure((ty, tm))
            },

            UntypedTmKind::Succs { succ_count_m1, pred_tm } => {
                pred_tm
                .check(ch)
                .group(MetaTag::CheckSuccsPredTm { span: span.clone() })
                .cast(
                    ch,
                    MetaTag::SuccsPredTm { span: span.clone() }.into(),
                    MetaTag::SuccsPredTmHasCorrectType { span: span.clone() },
                    Ty::nat(),
                )
                .map(ch, |_, _, pred_tm| {
                    let ty = Ty::nat();
                    let tm = pred_tm.succs(succ_count_m1.clone() + 1usize);
                    (ty, tm)
                })
            },

            /*
            UntypedTmKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                elim
                .check(ch)
                .group(MetaTag::CheckFoldElim { span: span.clone() })
                .and_then(ch, |ch, _, elim| {

                })
            },
            */

            _ => todo!(),
        }
    }
}

impl Check for UntypedName {
    type Output = Name;

    fn check(&self, _ch: &mut CheckCtx) -> Checked<Name> {
        todo!()
    }
}

impl Check for UntypedTy {
    type Output = Ty;

    fn check(&self, _ch: &mut CheckCtx) -> Checked<Ty> {
        todo!()
    }
}

/*
impl<T: Check> Check for UntypedScope<T> {
    type Output = (Ty, Scope<T::Output>);

    fn check(&self, _ch: &mut CheckCtx) -> Checked<(Ty, Scope<T::Output>)> {
        todo!()
    }
}
*/
*/

