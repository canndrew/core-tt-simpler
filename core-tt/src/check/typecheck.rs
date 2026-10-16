use crate::priv_prelude::*;
use {
    parser::ast,
    crate::check::{injections, projections},
};

pub trait Check {
    type Output;
    fn check(&self, ch: &mut CheckCtx) -> Checked<Self::Output>;
}

impl Check for Spanned<Span, ast::Name<Span>> {
    type Output = Name;

    fn check(&self, ch: &mut CheckCtx) -> Checked<Name> {
        match &self.inner {
            ast::Name::Ident(ident) => {
                let s = Arc::from(ident.as_str());
                let name = Name::from(s);
                Checked::pure(name)
            },
            ast::Name::Quoted(expr) => {
                expr
                .check(ch)
                .group(MetaTag::QuotedNameConstraint { span: self.span() })
                .and_then(ch, |ch, _, (name_ty, name)| {
                    Checked::cast(
                        ch,
                        MetaTag::QuotedNameHasTypeName { span: self.span() },
                        name_ty,
                        Ty::name(),
                        name,
                    )
                })
                .map(ch, |_, _, name| name.into_name())
            },
        }
    }
}

impl Check for ast::PrecStmt<Span> {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        match self {
            ast::PrecStmt::Let(let_stmt) => {
                let_stmt.check(ch)
            },
            ast::PrecStmt::Blank(_) => {
                Checked::pure((Ty::unit(), Tm::proof()))
            },
            ast::PrecStmt::Other(prec_func) => {
                prec_func.check(ch)
            },
        }
    }
}

impl Check for ast::PrecFunc<Span> {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        match self {
            ast::PrecFunc::FuncType(func_type) => {
                func_type.check(ch).into_ty_tm()
            },
            ast::PrecFunc::FuncTerm(func_term) => {
                func_term.check(ch)
            },
            ast::PrecFunc::Other(prec_equal) => {
                prec_equal.check(ch)
            },
        }
    }
}

impl Check for ast::PrecEqual<Span> {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        match self {
            ast::PrecEqual::Equal(expr_equal) => {
                expr_equal.check(ch).into_ty_tm()
            },
            ast::PrecEqual::Other(prec_add) => {
                prec_add.check(ch)
            },
        }
    }
}

impl Check for ast::PrecAdd<Span> {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        match self {
            ast::PrecAdd::Add(expr_add) => {
                expr_add.check(ch)
            },
            ast::PrecAdd::Other(prec_mul) => {
                prec_mul.check(ch)
            },
        }
    }
}

impl Check for ast::PrecMul<Span> {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        match self {
            ast::PrecMul::Mul(expr_mul) => {
                expr_mul.check(ch)
            },
            ast::PrecMul::Other(prec_inj) => {
                prec_inj.check(ch)
            },
        }
    }
}

impl Check for ast::PrecInj<Span> {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        match self {
            ast::PrecInj::InjLhs(expr_inj_lhs) => {
                expr_inj_lhs.check(ch)
            },
            ast::PrecInj::InjRhs(expr_inj_rhs) => {
                expr_inj_rhs.check(ch)
            },
            ast::PrecInj::Refl(expr_refl) => {
                expr_refl.check(ch)
            },
            ast::PrecInj::Other(prec_proj) => {
                prec_proj.check(ch)
            },
        }
    }
}

impl Check for ast::PrecProj<Span> {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        match self {
            ast::PrecProj::Proj(expr_proj) => {
                expr_proj.check(ch)
            },
            ast::PrecProj::Other(prec_app) => {
                prec_app.check(ch)
            },
        }
    }
}

impl Check for ast::PrecApp<Span> {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        match self {
            ast::PrecApp::App(expr_app) => {
                expr_app.check(ch)
            },
            ast::PrecApp::Other(prec_atom) => {
                prec_atom.check(ch)
            },
        }
    }
}

impl Check for ast::PrecAtom<Span> {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        match self {
            ast::PrecAtom::Var(var_name) => {
                var_name
                .check(ch)
                .group(MetaTag::VarNameConstraint { span: self.span() })
                .and_then(ch, |ch, _, var_name| {
                    lookup_var(ch, self.span(), var_name)
                })
            },
            ast::PrecAtom::NameLiteral(s) => {
                let s = Arc::from(s.inner.as_str());
                let ty = Ty::name();
                let tm = Tm::tag(Tag::from(s));
                Checked::pure((ty, tm))
            },
            ast::PrecAtom::Nat(constant) => {
                // FIXME: convert properly
                let ubig: Ubig = {
                    let printed = format!("{}", constant.inner);
                    std::str::FromStr::from_str(&printed).unwrap()
                };

                let ty = Ty::nat();
                let tm = Tm::constant(ubig);
                Checked::pure((ty, tm))
            },
            ast::PrecAtom::Match(expr_match) => {
                expr_match.check(ch)
            },
            ast::PrecAtom::StructType(expr_struct_type) => {
                expr_struct_type.check(ch).into_ty_tm()
            },
            ast::PrecAtom::StructTerm(expr_struct_term) => {
                expr_struct_term.check(ch)
            },
            ast::PrecAtom::EnumType(expr_enum_type) => {
                expr_enum_type.check(ch).into_ty_tm()
            },
            ast::PrecAtom::Braced(prec_stmt) => {
                prec_stmt.inner.check(ch)
            },
        }
    }
}

impl Check for Spanned<Span, ast::LetStmt<Span>> {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        let ast::LetStmt { var_pat, var_args_opt, var_ty_opt, var_expr, body } = &self.inner;

        let var_args = {
            var_args_opt
            .as_ref()
            .map_or(&[][..], |var_args| var_args.inner.as_slice())
        };
        check_func_term(
            ch,
            var_args,
            var_expr.span(),
            |ch| {
                let var_tm = {
                    var_expr
                    .check(ch)
                    .group(MetaTag::LetStmtVarTmConstraint {
                        var_tm_span: var_expr.span(),
                    })
                };
                match var_ty_opt {
                    None => var_tm,
                    Some(var_ty) => {
                        let var_ty_span = var_ty.span();
                        var_ty
                        .check(ch)
                        .group(MetaTag::LetStmtVarTyConstraint {
                            var_ty_span: var_ty_span.clone(),
                        })
                        .and_then(ch, |ch, _, (var_ty_ty, var_ty)| {
                            Checked::cast_to_ty(
                                ch,
                                MetaTag::LetStmtVarTyIsAType { var_ty_span: var_ty_span.clone() },
                                var_ty_ty,
                                var_ty,
                            )
                        })
                        .and_then(ch, |ch, _, var_ty| {
                            var_tm
                            .and_then(ch, |ch, _, (var_tm_ty, var_tm)| {
                                Checked::cast(
                                    ch,
                                    MetaTag::LetStmtVarTmTypeMatchesAnnotatedType {
                                        var_tm_span: var_expr.span(),
                                        var_ty_span,
                                    },
                                    var_tm_ty,
                                    var_ty.clone(),
                                    var_tm,
                                )
                            })
                            .map(ch, |_, _, var_tm| {
                                (var_ty, var_tm)
                            })
                        })

                    },
                }
            },
        )
        .and_then(ch, |ch, _, (var_ty, var_tm)| {
            check_pat_prec_inj(ch, var_pat, var_ty.clone(), |ch| {
                body
                .check(ch)
                .group(MetaTag::LetStmtBody { body_span: body.span() })
            })
            .and_then(ch, |_, _, scope| scope.bind(var_tm))
        })
    }
}

impl Check for Spanned<Span, ast::ExprFuncType<Span>> {
    type Output = Ty;

    fn check(&self, ch: &mut CheckCtx) -> Checked<Ty> {
        let ast::ExprFuncType { args, return_ty } = &self.inner;
        check_func_type(
            ch,
            args.inner.as_slice(),
            return_ty.span(),
            |ch| {
                return_ty
                .check(ch)
                .and_then(ch, |ch, _, (res_ty_ty, res_ty)| {
                    Checked::cast_to_ty(
                        ch,
                        MetaTag::FuncResTyIsAType { res_ty_span: return_ty.span() },
                        res_ty_ty,
                        res_ty
                    )
                })
            },
        )
    }
}

impl Check for Spanned<Span, ast::ExprFuncTerm<Span>> {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        let ast::ExprFuncTerm { args, body } = &self.inner;
        check_func_term(
            ch,
            args.inner.as_slice(),
            body.span(),
            |ch| body.check(ch),
        )
    }
}

impl Check for Spanned<Span, ast::ExprEqual<Span>> {
    type Output = Ty;

    fn check(&self, ch: &mut CheckCtx) -> Checked<Ty> {
        let ast::ExprEqual { eq_expr_0, eq_expr_1 } = &self.inner;
        eq_expr_0
        .check(ch)
        .group(MetaTag::EqualEqTm0Constraint {
            equal_span: self.span(),
            eq_tm_0_span: eq_expr_0.span(),
        })
        .and_then(ch, |ch, _, (eq_ty_0, eq_tm_0)| {
            eq_expr_1
            .check(ch)
            .group(MetaTag::EqualEqTm1Constraint {
                equal_span: self.span(),
                eq_tm_1_span: eq_expr_1.span(),
            })
            .and_then(ch, |ch, _, (eq_ty_1, eq_tm_1)| {
                Checked::cast(
                    ch,
                    MetaTag::EqualEndpointTypesAreTheSame {
                        equal_span: self.span(),
                        eq_tm_0_span: eq_expr_0.span(),
                        eq_tm_1_span: eq_expr_1.span(),
                    },
                    eq_ty_0,
                    eq_ty_1.clone(),
                    eq_tm_0,
                )
                .map(ch, |_, _, eq_tm_0| {
                    Ty::obs_equal(eq_ty_1, eq_tm_0, eq_tm_1)
                })
            })
        })
    }
}

impl Check for Spanned<Span, ast::ExprAdd<Span>> {
    type Output = (Ty, Tm);

    fn check(&self, _ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        unimplemented!()
    }
}

impl Check for Spanned<Span, ast::ExprMul<Span>> {
    type Output = (Ty, Tm);

    fn check(&self, _ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        unimplemented!()
    }
}

impl Check for Spanned<Span, ast::ExprInjLhs<Span>> {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        let ast::ExprInjLhs { variant_name, payload } = &self.inner;
        
        variant_name
        .check(ch)
        .group(MetaTag::InjLhsLhsNameConstraint {
            inj_span: self.span(),
            lhs_name_span: variant_name.span(),
        })
        .and_then(ch, |ch, _, lhs_name| {
            payload
            .check(ch)
            .group(MetaTag::InjLhsLhsTmConstraint {
                inj_span: self.span(),
                lhs_tm_span: payload.span(),
            })
            .and_then(ch, |ch, _, (lhs_ty, lhs_tm)| {
                Checked::assume_ty(
                    MetaTag::InjLhsRhsType {
                        inj_span: self.span(),
                        lhs_name_span: variant_name.span(),
                        lhs_tm_span: payload.span(),
                    },
                )
                .and_then(ch, |ch, _, rhs_ty| {
                    let base_ty = Ty::sum(lhs_name, lhs_ty, rhs_ty);
                    let base_tm = lhs_tm.inj_lhs();
                    Checked::assume(
                        MetaTag::InjLhsImplicitRhsInjectionCount {
                            inj_span: self.span(),
                        },
                        Ty::nat(),
                    )
                    .and_then(ch, |ch, _, inj_count| {
                        let injections_metas = injections::metas(self.span());
                        let injections_metas = injections_metas.each_ref();
                        Checked::assume(
                            injections_metas[0].clone(),
                            injections::ty(ch.ctx_len(), injections_metas, inj_count.clone())
                        )
                        .map(ch, |ch, _, injections| {
                            let ty = injections::apply_to_ty(
                                ch.ctx_len(),
                                injections_metas,
                                inj_count.clone(),
                                injections.clone(),
                                base_ty.clone(),
                            );
                            let tm = injections::apply_to_tm(
                                ch.ctx_len(),
                                injections_metas,
                                inj_count,
                                injections,
                                base_ty,
                                base_tm,
                            );
                            (ty, tm)
                        })
                    })
                })
            })
        })
    }
}

impl Check for Spanned<Span, ast::ExprInjRhs<Span>> {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        let ast::ExprInjRhs { payload } = &self.inner;

        payload
        .check(ch)
        .group(MetaTag::InjRhsRhsTmConstraint {
            inj_span: self.span(),
            rhs_tm_span: payload.span(),
        })
        .and_then(ch, |ch, _, (rhs_ty, rhs_tm)| {
            Checked::assume(
                MetaTag::InjRhsLhsName {
                    inj_span: self.span(),
                    rhs_tm_span: payload.span(),
                },
                Ty::name(),
            )
            .and_then(ch, |ch, _, lhs_name| {
                let lhs_name = lhs_name.into_name();
                Checked::assume_ty(
                    MetaTag::InjRhsLhsType {
                        inj_span: self.span(),
                        rhs_tm_span: payload.span(),
                    },
                )
                .map(ch, |_, _, lhs_ty| {
                    let ty = Ty::sum(lhs_name, lhs_ty, rhs_ty);
                    let tm = rhs_tm.inj_rhs();
                    (ty, tm)
                })
            })
        })
    }
}

impl Check for Spanned<Span, ast::ExprRefl<Span>> {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        let ast::ExprRefl { eq_expr } = &self.inner;
        eq_expr
        .check(ch)
        .group(MetaTag::ReflEqTmConstraint {
            refl_tm_span: self.span(),
            eq_tm_span: eq_expr.span(),
        })
        .map(ch, |_, _, (eq_ty, eq_tm)| {
            let ty = Ty::obs_equal(eq_ty, eq_tm.clone(), eq_tm.clone());
            (ty, Tm::proof())
        })
    }
}

impl Check for Spanned<Span, ast::ExprProj<Span>> {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        let ast::ExprProj { base, field_name } = &self.inner;
        
        base
        .check(ch)
        .group(MetaTag::ProjHeadBaseConstraint {
            proj_span: self.span(),
            base_tm_span: base.span(),
        })
        .and_then(ch, |ch, _, (base_ty, base_tm)| {
            field_name
            .check(ch)
            .group(MetaTag::ProjHeadHeadNameConstraint {
                proj_span: self.span(),
                head_name_span: field_name.span(),
            })
            .and_then(ch, |ch, _, head_name| {
                Checked::assume(
                    MetaTag::ProjHeadImplicitTailProjectionCount {
                        proj_span: self.span(),
                    },
                    Ty::nat(),
                )
                .and_then(ch, |ch, _, proj_count| {
                    let projections_metas = projections::metas(self.span());
                    let projections_metas = projections_metas.each_ref();
                    Checked::assume(
                        projections_metas[0].clone(),
                        projections::ty(
                            ch.ctx_len(),
                            projections_metas,
                            proj_count.clone(),
                            base_ty.clone(),
                            base_tm.clone(),
                        ),
                    )
                    .and_then(ch, |ch, _, projections| {
                        let ty = projections::apply_to_ty(
                            ch.ctx_len(),
                            projections_metas,
                            proj_count.clone(),
                            base_ty.clone(),
                            base_tm.clone(),
                            projections.clone(),
                        );
                        let tm = projections::apply_to_tm(
                            ch.ctx_len(),
                            projections_metas,
                            proj_count,
                            base_ty,
                            base_tm,
                            projections,
                        );
                        Checked::assume_ty(
                            MetaTag::ProjHeadHeadTy {
                                proj_span: self.span(),
                            },
                        )
                        .and_then(ch, |ch, _, head_ty| {
                            Checked::assume(
                                MetaTag::ProjHeadTailTy {
                                    proj_span: self.span(),
                                },
                                Ty::pi(
                                    head_name.clone(),
                                    head_ty.clone(),
                                    Scope::constant(Ty::universe()),
                                ),
                            )
                            .and_then(ch, |ch, _, tail_ty| {
                                let expected_ty = Ty::sigma(
                                    head_name,
                                    head_ty.clone(),
                                    Scope::make(ch.ctx_len(), |head_tm| {
                                        tail_ty.app(head_tm).into_ty()
                                    }),
                                );
                                Checked::cast(
                                    ch,
                                    MetaTag::ProjHeadHasExpectedType {
                                        proj_span: self.span(),
                                    },
                                    ty,
                                    expected_ty,
                                    tm,
                                )
                                .map(ch, |_, _, tm| {
                                    (head_ty, tm.proj_head())
                                })
                            })
                        })
                    })
                })
            })
        })
    }
}

impl Check for Spanned<Span, ast::ExprApp<Span>> {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        let ast::ExprApp { func, args } = &self.inner;

        let mut checked = {
            func
            .check(ch)
            .group(MetaTag::AppElimConstraint {
                app_span: self.span(),
                elim_span: func.span(),
            })
        };
        for arg in &args.inner {
            checked = checked.and_then(ch, |ch, _, (elim_ty, elim)| {
                arg
                .check(ch)
                .and_then(ch, |ch, _, (arg_name, arg_ty, arg_tm)| {
                    Checked::assume(
                        MetaTag::AppResTy {
                            app_span: self.span(),
                            arg_span: arg.span(),
                        },
                        Ty::pi(
                            arg_name.clone(),
                            arg_ty.clone(),
                            Scope::constant(Ty::universe()),
                        ),
                    )
                    .and_then(ch, |ch, _, res_ty| {
                        let res_ty = Scope::make(ch.ctx_len(), |arg_tm| {
                            res_ty.app(arg_tm).into_ty()
                        });
                        let expected_elim_ty = Ty::pi(arg_name, arg_ty, res_ty.clone());
                        Checked::cast(
                            ch,
                            MetaTag::AppElimHasExpectedType {
                                elim_span: func.span(),
                                arg_tm_span: arg.span(),
                            },
                            elim_ty,
                            expected_elim_ty,
                            elim,
                        )
                        .map(ch, |_, _, elim| {
                            let ty = res_ty.bind(arg_tm.clone());
                            let tm = elim.app(arg_tm);
                            (ty, tm)
                        })
                    })
                })
            });
        }
        checked
    }
}

impl Check for Spanned<Span, ast::FuncAppArg<Span>> {
    type Output = (Name, Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Name, Ty, Tm)> {
        let ast::FuncAppArg { arg_name, arg_expr_opt } = &self.inner;
        arg_name
        .check(ch)
        .group(MetaTag::AppArgNameConstraint {
            arg_name_span: arg_name.span(),
        })
        .and_then(ch, |ch, _, name| {
            match arg_expr_opt {
                None => lookup_var(ch, arg_name.span(), name.clone()),
                Some(arg_expr) => {
                    arg_expr
                    .check(ch)
                    .group(MetaTag::AppArgTmConstraint {
                        arg_span: self.span(),
                    })
                },
            }
            .map(ch, |_, _, (ty, tm)| (name, ty, tm))
        })
    }
}

impl Check for &ast::FuncAppArgExpr<Span> {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        let ast::FuncAppArgExpr { args_opt, expr } = self;
        let args = args_opt.as_ref().map_or(&[][..], |args| &args.inner);
        check_func_term(
            ch,
            args,
            expr.span(),
            |ch| expr.check(ch),
        )
    }
}

impl Check for Spanned<Span, ast::ExprMatch<Span>> {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        let ast::ExprMatch { elim, branches } = &self.inner;

        elim
        .check(ch)
        .group(MetaTag::MatchElimConstraint {
            elim_span: elim.span(),
        })
        .and_then(ch, |ch, _, (elim_ty, elim)| {
            check_match_branches(ch, branches.span(), &branches.inner, elim_ty)
            .and_then(ch, |_, _, scope| {
                scope.bind(elim)
            })
        })
    }
}

impl Check for Spanned<Span, ast::ExprStructType<Span>> {
    type Output = Ty;

    fn check(&self, ch: &mut CheckCtx) -> Checked<Ty> {
        fn recurse(
            ch: &mut CheckCtx,
            fields: &[Spanned<Span, ast::TypeField<Span>>],
            tail_ty_opt: Option<&ast::PrecFunc<Span>>,
        ) -> Checked<Ty> {
            match fields.split_first() {
                None => {
                    match tail_ty_opt {
                        None => Checked::pure(Ty::unit()),
                        Some(tail_ty) => {
                            let tail_ty_span = tail_ty.span();
                            tail_ty
                            .check(ch)
                            .group(MetaTag::SigmaTailTyConstraint {
                                tail_ty_span: tail_ty_span.clone(),
                            })
                            .and_then(ch, |ch, _, (tail_ty_ty, tail_ty)| {
                                Checked::cast_to_ty(
                                    ch,
                                    MetaTag::SigmaTailTyIsAType {
                                        tail_ty_span: tail_ty_span.clone(),
                                    },
                                    tail_ty_ty,
                                    tail_ty,
                                )
                            })
                        },
                    }
                },
                Some((field, fields)) => {
                    field
                    .check(ch)
                    .and_then(ch, |ch, _, (head_name, head_ty)| {
                        ch
                        .with_var(head_name.clone(), head_ty.clone(), |ch, _| {
                            recurse(ch, fields, tail_ty_opt)
                        })
                        .group_and_lift_checked(
                            head_name.clone(),
                            head_ty.clone(),
                            MetaTag::SigmaRemainingTailTyConstraint {
                                head_span: field.span(),
                            },
                        )
                        .map(ch, |_, _, tail_ty| {
                            Ty::sigma(head_name, head_ty, tail_ty)
                        })
                    })
                },
            }
        }

        let ast::ExprStructType { fields, tail_ty_opt } = &self.inner;
        recurse(ch, fields, tail_ty_opt.as_deref())
    }
}

impl Check for Spanned<Span, ast::ExprStructTerm<Span>> {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        fn check_struct_term_fields(
            ch: &mut CheckCtx,
            fields: &[Spanned<Span, ast::ExprStructTermField<Span>>],
            tail_opt: Option<&ast::PrecFunc<Span>>,
        ) -> Checked<(Ty, Tm)> {
            match fields.split_first() {
                None => {
                    match tail_opt {
                        None => Checked::pure((Ty::unit(), Tm::proof())),
                        Some(tail) => {
                            tail.check(ch)
                        },
                    }
                },
                Some((field, fields)) => {
                    field
                    .check(ch)
                    .and_then(ch, |ch, _, (head_name, head_ty, head_tm)| {
                        Checked::assume(
                            MetaTag::PairTailTy {
                                head_span: field.span(),
                            },
                            Ty::pi(
                                head_name.clone(),
                                head_ty.clone(),
                                Scope::constant(Ty::universe()),
                            )
                        )
                        .and_then(ch, |ch, _, tail_ty| {
                            let tail_ty = Scope::make(ch.ctx_len(), |head| {
                                tail_ty.app(head).into_ty()
                            });
                            check_struct_term_fields(ch, fields, tail_opt)
                            .and_then(ch, |ch, _, (bound_tail_ty, tail_tm)| {
                                Checked::assume(
                                    MetaTag::PairTailTyIsExpectedTy {
                                        head_span: field.span(),
                                    },
                                    Ty::obs_equal(
                                        Ty::universe(),
                                        bound_tail_ty.clone().into_tm(),
                                        tail_ty.clone().bind(head_tm.clone()).into_tm(),
                                    ),
                                )
                                .map(ch, |_, _, _| {
                                    let tail_tm = {
                                        Tm::cast(
                                            bound_tail_ty.clone(),
                                            tail_ty.clone().bind(head_tm.clone()),
                                            tail_tm,
                                        )
                                    };
                                    let ty = Ty::sigma(
                                        head_name.clone(),
                                        head_ty.clone(),
                                        tail_ty.clone(),
                                    );
                                    let tm = head_tm.pair(tail_tm);
                                    (ty, tm)
                                })
                            })
                        })
                    })
                },
            }
        }

        let ast::ExprStructTerm { fields, tail_opt } = &self.inner;
        check_struct_term_fields(ch, fields, tail_opt.as_deref())
    }
}

impl Check for Spanned<Span, ast::ExprStructTermField<Span>> {
    type Output = (Name, Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Name, Ty, Tm)> {
        let ast::ExprStructTermField { name, expr_opt } = &self.inner;
        
        name
        .check(ch)
        .group(MetaTag::PairHeadNameConstraint {
            head_name_span: name.span(),
        })
        .and_then(ch, |ch, _, head_name| {
            match expr_opt {
                None => lookup_var(ch, name.span(), head_name.clone()),
                Some(expr) => {
                    expr
                    .check(ch)
                    .group(MetaTag::PairHeadTmConstraint {
                        head_span: expr.span(),
                    })
                },
            }
            .map(ch, |_, _, (head_ty, head_tm)| {
                (head_name, head_ty, head_tm)
            })
        })
    }
}

impl Check for Spanned<Span, ast::ExprEnumType<Span>> {
    type Output = Ty;

    fn check(&self, ch: &mut CheckCtx) -> Checked<Ty> {
        let ast::ExprEnumType { variants, rhs_ty_opt } = &self.inner;

        let mut checked = match rhs_ty_opt {
            None => Checked::pure(Ty::never()),
            Some(rhs_ty) => {
                let rhs_ty_span = rhs_ty.span();
                rhs_ty
                .check(ch)
                .group(MetaTag::SumRhsTyConstraint {
                    rhs_ty_span: rhs_ty_span.clone(),
                })
                .and_then(ch, |ch, _, (rhs_ty_ty, rhs_ty)| {
                    Checked::cast_to_ty(
                        ch,
                        MetaTag::SumRhsTyIsAType {
                            rhs_ty_span: rhs_ty_span.clone(),
                        },
                        rhs_ty_ty,
                        rhs_ty,
                    )
                })
            },
        };
        for variant in variants.iter().rev() {
            checked = checked.and_then(ch, |ch, _, rhs_ty| {
                variant
                .check(ch)
                .group(MetaTag::SumLhsTyConstraint {
                    lhs_ty_span: variant.span(),
                })
                .map(ch, |_, _, (lhs_name, lhs_ty)| {
                    Ty::sum(lhs_name, lhs_ty, rhs_ty)
                })
            });
        }
        checked
    }
}

impl Check for Spanned<Span, ast::TypeField<Span>> {
    type Output = (Name, Ty);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Name, Ty)> {
        let ast::TypeField { name, ty } = &self.inner;

        name
        .check(ch)
        .group(MetaTag::TypeFieldNameConstraint {
            field_span: self.span(),
            name_span: name.span(),
        })
        .and_then(ch, |ch, _, name| {
            let ty_span = ty.span();
            ty
            .check(ch)
            .group(MetaTag::TypeFieldTyConstraint {
                field_span: self.span(),
                ty_span: ty_span.clone(),
            })
            .and_then(ch, |ch, _, (ty_ty, ty)| {
                Checked::cast_to_ty(
                    ch,
                    MetaTag::TypeFieldTyIsAType {
                        ty_span,
                    },
                    ty_ty,
                    ty,
                )
            })
            .map(ch, |_, _, ty| (name, ty))
        })
    }
}

impl Check for Spanned<Span, ast::FuncTermArg<Span>> {
    type Output = (Name, Ty);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Name, Ty)> {
        let ast::FuncTermArg { arg_name, arg_ty_opt } = &self.inner;
        let arg_name_span = arg_name.span();

        arg_name
        .check(ch)
        .group(MetaTag::FuncArgNameConstraint { arg_name_span: arg_name_span.clone() })
        .and_then(ch, |ch, _, arg_name| {
            let arg_ty_checked = match arg_ty_opt {
                None => {
                    Checked::assume_ty(
                        MetaTag::FuncArgTy { arg_name_span: arg_name_span.clone() },
                    )
                },
                Some(arg_ty) => {
                    arg_ty
                    .check(ch)
                    .group(MetaTag::FuncArgTyConstraint { span: self.span() })
                },
            };
            arg_ty_checked.map(ch, |_, _, arg_ty| (arg_name, arg_ty))
        })
    }
}

impl Check for ast::FuncTermArgTy<Span> {
    type Output = Ty;

    fn check(&self, ch: &mut CheckCtx) -> Checked<Ty> {
        let ast::FuncTermArgTy { args_opt, ty } = self;
        let args = args_opt.as_ref().map_or(&[][..], |args| args.inner.as_slice());
        let ty_span = ty.span();

        check_func_type(
            ch,
            args,
            ty_span.clone(),
            |ch| {
                ty
                .check(ch)
                .and_then(ch, |ch, _, (ty_ty, ty)| {
                    Checked::cast_to_ty(
                        ch,
                        MetaTag::FuncResTyIsAType { res_ty_span: ty_span },
                        ty_ty,
                        ty,
                    )
                })
            },
        )
    }
}

fn check_func_term(
    ch: &mut CheckCtx,
    func_term_args: &[Spanned<Span, ast::FuncTermArg<Span>>],
    res_tm_span: Span,
    check_res_tm: impl FnOnce(&mut CheckCtx) -> Checked<(Ty, Tm)>,
) -> Checked<(Ty, Tm)> {
    match func_term_args.split_first() {
        None => check_res_tm(ch),
        Some((func_term_arg, func_term_args)) => {
            func_term_arg
            .check(ch)
            .group(MetaTag::FuncArgConstraint { func_arg_span: func_term_arg.span() })
            .and_then(ch, |ch, _, (arg_name, arg_ty)| {
                ch
                .with_var(arg_name.clone(), arg_ty.clone(), |ch, _| {
                    check_func_term(
                        ch,
                        func_term_args,
                        res_tm_span.clone(),
                        check_res_tm,
                    )
                })
                .group_and_lift_checked(
                    arg_name.clone(),
                    arg_ty.clone(),
                    MetaTag::FuncResTmConstraint {
                        remaining_args_span_opt: {
                            func_term_args
                            .first()
                            .map(|first| {
                                let last = func_term_args.last().unwrap();
                                Span::combine(&first.span(), &last.span())
                            })
                        },
                        res_tm_span: res_tm_span.clone(),
                    },
                )
                .map(ch, |_, _, res_tm| {
                    let (res_ty, res_tm) = res_tm.lift_tuple();
                    let ty = Ty::pi(arg_name, arg_ty, res_ty);
                    let tm = Tm::func(res_tm);
                    (ty, tm)
                })
            })
        },
    }
}

fn check_func_type(
    ch: &mut CheckCtx,
    func_term_args: &[Spanned<Span, ast::FuncTermArg<Span>>],
    res_ty_span: Span,
    check_res_ty: impl FnOnce(&mut CheckCtx) -> Checked<Ty>,
) -> Checked<Ty> {
    match func_term_args.split_first() {
        None => check_res_ty(ch),
        Some((func_term_arg, func_term_args)) => {
            func_term_arg
            .check(ch)
            .group(MetaTag::FuncArgConstraint { func_arg_span: func_term_arg.span() })
            .and_then(ch, |ch, _, (arg_name, arg_ty)| {
                ch
                .with_var(arg_name.clone(), arg_ty.clone(), |ch, _| {
                    check_func_type(
                        ch,
                        func_term_args,
                        res_ty_span.clone(),
                        check_res_ty,
                    )
                })
                .group_and_lift_checked(
                    arg_name.clone(),
                    arg_ty.clone(),
                    MetaTag::FuncResTyConstraint {
                        remaining_args_span_opt: {
                            func_term_args
                            .first()
                            .map(|first| {
                                let last = func_term_args.last().unwrap();
                                Span::combine(&first.span(), &last.span())
                            })
                        },
                        res_ty_span: res_ty_span.clone(),
                    },
                )
                .map(ch, |_, _, res_ty| {
                    Ty::pi(arg_name, arg_ty, res_ty)
                })
            })
        },
    }
}

fn check_pat_prec_inj(
    ch: &mut CheckCtx,
    pat_prec_inj: &ast::PatPrecInj<Span>,
    var_ty: Ty,
    func: impl FnOnce(&mut CheckCtx) -> Checked<(Ty, Tm)>,
) -> Checked<Scope<Checked<(Ty, Tm)>>> {
    match pat_prec_inj {
        ast::PatPrecInj::Refl(pat_refl) => {
            check_pat_refl(ch, pat_refl, var_ty, func)
        },
        ast::PatPrecInj::Other(pat_prec_atom) => {
            check_pat_prec_atom(ch, pat_prec_atom, var_ty, func)
        },
    }
}

fn check_pat_prec_atom(
    ch: &mut CheckCtx,
    pat_prec_atom: &ast::PatPrecAtom<Span>,
    var_ty: Ty,
    func: impl FnOnce(&mut CheckCtx) -> Checked<(Ty, Tm)>,
) -> Checked<Scope<Checked<(Ty, Tm)>>> {
    match pat_prec_atom {
        ast::PatPrecAtom::Var(name) => {
            check_pat_var(ch, name, var_ty, func)
        },
        ast::PatPrecAtom::Struct(pat_struct_term) => {
            check_pat_struct_term(ch, pat_struct_term, var_ty, func)
        },
    }
}

fn check_pat_var(
    ch: &mut CheckCtx,
    name: &Spanned<Span, ast::Name<Span>>,
    var_ty: Ty,
    func: impl FnOnce(&mut CheckCtx) -> Checked<(Ty, Tm)>,
) -> Checked<Scope<Checked<(Ty, Tm)>>> {
    name
    .check(ch)
    .group(MetaTag::PatternVarNameConstraint { name_span: name.span() })
    .map(ch, |ch, _, name| {
        ch
        .with_var(name, var_ty.clone(), |ch, _| func(ch))
    })
}

fn check_pat_refl(
    ch: &mut CheckCtx,
    pat_refl: &Spanned<Span, ast::PatRefl<Span>>,
    var_ty: Ty,
    func: impl FnOnce(&mut CheckCtx) -> Checked<(Ty, Tm)>,
) -> Checked<Scope<Checked<(Ty, Tm)>>> {
    let refl_pat_span = pat_refl.span();
    let ast::PatRefl { eq_pat } = &pat_refl.inner;

    Checked::assume_ty(
        MetaTag::ReflPatEqTy {
            refl_pat_span: refl_pat_span.clone(),
        },
    )
    .and_then(ch, |ch, _, eq_ty| {
        Checked::assume(
            MetaTag::ReflPatEqTm0 {
                refl_pat_span: refl_pat_span.clone(),
            },
            eq_ty.clone(),
        )
        .and_then(ch, |ch, _, eq_tm_0| {
            Checked::assume(
                MetaTag::ReflPatEqTm1 {
                    refl_pat_span: refl_pat_span.clone(),
                },
                eq_ty.clone(),
            )
            .and_then(ch, |ch, _, eq_tm_1| {
                Checked::assume(
                    MetaTag::ReflPatVarTyIsExpectedTy {
                        refl_pat_span: refl_pat_span.clone(),
                    },
                    Ty::obs_equal(
                        Ty::universe(),
                        var_ty.clone().into_tm(),
                        Ty::obs_equal(eq_ty.clone(), eq_tm_0.clone(), eq_tm_1.clone()).into_tm(),
                    ),
                )
                .and_then(ch, |ch, _, _var_tys_eq| {
                    Checked::assume(
                        MetaTag::ReflPatMotive {
                            refl_pat_span: refl_pat_span.clone(),
                        },
                        Ty::pi(
                            MetaTag::ReflPatMotiveEqTm1 {
                                refl_pat_span: refl_pat_span.clone(),
                                eq_pat_span: eq_pat.span(),
                            }.into(),
                            eq_ty.clone(),
                            Scope::make(ch.ctx_len(), |eq_tm_1| {
                                Ty::pi(
                                    MetaTag::ReflPatMotiveElim {
                                        refl_pat_span: refl_pat_span.clone(),
                                        eq_pat_span: eq_pat.span(),
                                    }.into(),
                                    Ty::obs_equal(eq_ty.clone(), eq_tm_0.clone(), eq_tm_1),
                                    Scope::constant(Ty::universe()),
                                )
                            })
                        ),
                    )
                    .and_then(ch, |ch, _, motive| {
                        check_pat_prec_inj(ch, eq_pat, eq_ty.clone(), func)
                        .group(MetaTag::ReflPatInhabOuterConstraint {
                            refl_pat_span: refl_pat_span.clone(),
                        })
                        .and_then(ch, |ch, _, inhab| {
                            inhab
                            .bind(eq_tm_0.clone())
                            .group(MetaTag::ReflPatInhabInnerConstraint {
                                refl_pat_span: refl_pat_span.clone(),
                            })
                            .and_then(ch, |ch, _, (inhab_ty, inhab)| {
                                let expected_inhab_ty = {
                                    motive
                                    .clone()
                                    .app(eq_tm_0.clone())
                                    .app(Tm::proof())
                                    .into_ty()
                                };

                                Checked::cast(
                                    ch,
                                    MetaTag::ReflPatInhabHasCorrectType {
                                        refl_pat_span: refl_pat_span.clone(),
                                    },
                                    inhab_ty,
                                    expected_inhab_ty.clone(),
                                    inhab,
                                )
                                .map(ch, |ch, _, inhab| {
                                    Scope::make(ch.ctx_len(), |var_tm| {
                                        let elim = Tm::cast(
                                            var_ty.clone(),
                                            Ty::obs_equal(
                                                eq_ty.clone(),
                                                eq_tm_0.clone(),
                                                eq_tm_1.clone(),
                                            ),
                                            var_tm,
                                        );
                                        let ty = {
                                            motive
                                            .clone()
                                            .app(eq_tm_1)
                                            .app(elim.clone())
                                            .into_ty()
                                        };
                                        let tm = Tm::cast(
                                            expected_inhab_ty,
                                            ty.clone(),
                                            inhab,
                                        );
                                        Checked::pure((ty, tm))
                                    })
                                })
                            })
                        })
                    })
                })
            })
        })
    })
}

fn check_pat_struct_term(
    ch: &mut CheckCtx,
    pat_struct_term: &Spanned<Span, ast::PatStructTerm<Span>>,
    var_ty: Ty,
    func: impl FnOnce(&mut CheckCtx) -> Checked<(Ty, Tm)>,
) -> Checked<Scope<Checked<(Ty, Tm)>>> {

    fn check_pat_struct_term_fields(
        ch: &mut CheckCtx,
        pat_span: Span,
        fields: &[Spanned<Span, ast::PatStructTermField<Span>>],
        tail_opt: Option<&ast::PatPrecInj<Span>>,
        var_ty: Ty,
        func: Box<dyn FnOnce(&mut CheckCtx) -> Checked<(Ty, Tm)> + '_>,
    ) -> Checked<Scope<Checked<(Ty, Tm)>>> {
        match fields.split_first() {
            None => {
                match tail_opt {
                    None => {
                        Checked::assume(
                            MetaTag::UnitPatVarTyIsUnit {
                                pat_span: pat_span.clone(),
                            },
                            Ty::obs_equal(
                                Ty::universe(),
                                var_ty.clone().into_tm(),
                                Ty::unit().into_tm(),
                            ),
                        )
                        .map(ch, |ch, _, _| {
                            let body = func(ch);
                            Scope::constant(body)
                        })
                    },
                    Some(tail) => {
                        check_pat_prec_inj(ch, tail, var_ty, func)
                    },
                }
            },
            Some((field, fields)) => {
                let ast::PatStructTermField { name, pat_opt } = &field.inner;
                
                name
                .check(ch)
                .group(MetaTag::PairPatHeadNameConstraint {
                    head_name_span: name.span(),
                })
                .and_then(ch, |ch, _, head_name| {
                    Checked::assume_ty(
                        MetaTag::PairPatHeadTy {
                            field_span: field.span(),
                        },
                    )
                    .and_then(ch, |ch, _, head_ty| {
                        Checked::assume(
                            MetaTag::PairPatTailTy {
                                field_span: field.span(),
                            },
                            Ty::pi(
                                head_name.clone(),
                                head_ty.clone(),
                                Scope::constant(Ty::universe()),
                            )
                        )
                        .and_then(ch, |ch, _, tail_ty| {
                            let tail_ty = Scope::make(ch.ctx_len(), |head| {
                                tail_ty.app(head).into_ty()
                            });
                            let sigma_ty = Ty::sigma(
                                head_name.clone(),
                                head_ty.clone(),
                                tail_ty.clone(),
                            );

                            Checked::assume(
                                MetaTag::PairPatVarTyIsExpectedTy {
                                    field_span: field.span(),
                                },
                                Ty::obs_equal(
                                    Ty::universe(),
                                    var_ty.clone().into_tm(),
                                    sigma_ty.clone().into_tm(),
                                ),
                            )
                            .map(ch, |ch, _, _| {
                                ch.with_anon_var(var_ty.clone(), |ch, tm| {
                                    let pair = Tm::cast(var_ty.clone(), sigma_ty.clone(), tm);
                                    let head_tm = pair.clone().proj_head();
                                    let tail_tm = pair.proj_tail();

                                    let tail_func: Box<
                                        dyn FnOnce(&mut CheckCtx) -> Checked<(Ty, Tm)> + '_,
                                    > = {
                                        let head_tm = head_tm.clone();
                                        Box::new(move |ch: &mut CheckCtx| {
                                            let bound_tail_ty = {
                                                tail_ty
                                                .clone()
                                                .bind(head_tm.clone())
                                            };
                                            check_pat_struct_term_fields(
                                                ch,
                                                pat_span.clone(),
                                                fields,
                                                tail_opt,
                                                bound_tail_ty,
                                                func,
                                            )
                                            .and_then(ch, |_, _, tail_scope| {
                                                tail_scope.bind(tail_tm)
                                            })
                                        })
                                    };

                                    match pat_opt {
                                        None => {
                                            Checked::pure(ch.with_var(
                                                head_name.clone(),
                                                head_ty.clone(),
                                                move |ch, _| tail_func(ch),
                                            ))
                                        },
                                        Some(pat) => {
                                            check_pat_prec_inj(ch, pat, head_ty.clone(), tail_func)
                                        },
                                    }
                                    .and_then(ch, |_, _, head_scope| {
                                        head_scope.bind(head_tm)
                                    })
                                })
                            })
                        })
                    })
                })
            },
        }
    }

    let ast::PatStructTerm { fields, tail_opt } = &pat_struct_term.inner;
    check_pat_struct_term_fields(
        ch, pat_struct_term.span(), fields, tail_opt.as_deref(), var_ty, Box::new(func),
    )
}

fn check_match_branches(
    ch: &mut CheckCtx,
    branches_span: Span,
    branches: &[Spanned<Span, ast::MatchBranch<Span>>],
    var_ty: Ty,
) -> Checked<Scope<Checked<(Ty, Tm)>>> {
    match branches.split_first() {
        None => {
            Checked::assume(
                MetaTag::MatchElimTypeIsNever {
                    branches_span: branches_span.clone(),
                },
                Ty::obs_equal(
                    Ty::universe(),
                    var_ty.clone().into_tm(),
                    Ty::never().into_tm(),
                ),
            )
            .and_then(ch, |ch, _, _| {
                Checked::assume(
                    MetaTag::MatchRhsBranchMotive {
                        branches_span: branches_span.clone(),
                    },
                    Ty::pi(
                        Name::from("never"),
                        Ty::never(),
                        Scope::constant(Ty::universe()),
                    ),
                )
                .map(ch, |ch, _, motive| {
                    Scope::make(ch.ctx_len(), |tm| {
                        let never = Tm::cast(
                            var_ty,
                            Ty::never(),
                            tm,
                        );
                        let tm = Tm::explode(
                            Scope::make(ch.ctx_len() + 1, |never| {
                                motive.clone().app(never).into_ty()
                            }),
                        );
                        let ty = motive.app(never).into_ty();
                        Checked::pure((ty, tm))
                    })
                })
            })
        },
        Some((branch, branches)) => {
            let ast::MatchBranch { variant_name, payload_pat, body } = &branch.inner;

            variant_name
            .check(ch)
            .group(MetaTag::MatchLhsNameConstraint {
                branch_span: branch.span(),
                branches_span: branches_span.clone(),
            })
            .and_then(ch, |ch, _, lhs_name| {
                Checked::assume_ty(
                    MetaTag::MatchLhsTy {
                        branch_span: branch.span(),
                        branches_span: branches_span.clone(),
                    },
                )
                .and_then(ch, |ch, _, lhs_ty| {
                    Checked::assume_ty(
                        MetaTag::MatchRhsTy {
                            branch_span: branch.span(),
                            branches_span: branches_span.clone(),
                        },
                    )
                    .and_then(ch, |ch, _, rhs_ty| {
                        let sum_ty = Ty::sum(lhs_name.clone(), lhs_ty.clone(), rhs_ty.clone());
                        Checked::assume(
                            MetaTag::MatchElimTypeIsSum {
                                branch_span: branch.span(),
                                branches_span: branches_span.clone(),
                            },
                            Ty::obs_equal(
                                Ty::universe(),
                                var_ty.clone().into_tm(),
                                sum_ty.clone().into_tm(),
                            ),
                        )
                        .and_then(ch, |ch, _, _| {
                            Checked::assume(
                                MetaTag::MatchLhsBranchMotive {
                                    branch_span: branch.span(),
                                    branches_span: branches_span.clone(),
                                },
                                Ty::pi(
                                    Name::from("sum"),
                                    sum_ty.clone(),
                                    Scope::constant(Ty::universe()),
                                ),
                            )
                            .and_then(ch, |ch, _, motive| {
                                check_pat_prec_inj(
                                    ch,
                                    payload_pat,
                                    lhs_ty.clone(),
                                    |ch| body.check(ch),
                                )
                                .and_then(ch, |_, _, lhs_inhab| {
                                    lhs_inhab
                                    .group_and_lift_checked(
                                        lhs_name.clone(),
                                        lhs_ty.clone(),
                                        MetaTag::MatchLhsInhabConstraint {
                                            branch_span: branch.span(),
                                            branches_span: branches_span.clone(),
                                        },
                                    )
                                })
                                .and_then(ch, |ch, _, lhs_inhab| {
                                    check_match_branches(
                                        ch,
                                        branches_span.clone(),
                                        branches,
                                        rhs_ty.clone(),
                                    )
                                    .and_then(ch, |_, _, rhs_inhab| {
                                        rhs_inhab
                                        .group_and_lift_checked(
                                            Name::from("sum"),
                                            rhs_ty.clone(),
                                            MetaTag::MatchRhsInhabConstraint {
                                                branches_span: branches_span.clone(),
                                            },
                                        )
                                    })
                                    .and_then(ch, |ch, _, rhs_inhab| {
                                        let (lhs_inhab_ty, lhs_inhab_tm) = lhs_inhab.map_multi(
                                            ch.ctx_len(),
                                            |_, (ty, tm)| (ty, tm)
                                        );
                                        let (rhs_inhab_ty, rhs_inhab_tm) = rhs_inhab.map_multi(
                                            ch.ctx_len(),
                                            |_, (ty, tm)| (ty, tm)
                                        );

                                        Checked::assume(
                                            MetaTag::MatchLhsInhabTyIsExpectedTy {
                                                branch_span: branch.span(),
                                                branches_span: branches_span.clone(),
                                            },
                                            Ty::pi(
                                                lhs_name.clone(),
                                                lhs_ty.clone(),
                                                Scope::make(ch.ctx_len(), |lhs| {
                                                    Ty::obs_equal(
                                                        Ty::universe(),
                                                        lhs_inhab_ty
                                                        .clone()
                                                        .bind(lhs.clone())
                                                        .into_tm(),
                                                        motive.clone().app(lhs.inj_lhs()),
                                                    )
                                                })
                                            )
                                        )
                                        .and_then(ch, |ch, _, _| {
                                            let lhs_inhab = Scope::make(
                                                ch.ctx_len(),
                                                |lhs| {
                                                    Tm::cast(
                                                        lhs_inhab_ty.clone().bind(lhs.clone()),
                                                        motive
                                                        .clone()
                                                        .app(lhs.clone().inj_lhs())
                                                        .into_ty(),
                                                        lhs_inhab_tm.bind(lhs),
                                                    )
                                                },
                                            );
                                            Checked::assume(
                                                MetaTag::MatchRhsInhabTyIsExpectedTy {
                                                    branches_span: branches_span.clone(),
                                                },
                                                Ty::pi(
                                                    Name::from("sum"),
                                                    rhs_ty.clone(),
                                                    Scope::make(ch.ctx_len(), |rhs| {
                                                        Ty::obs_equal(
                                                            Ty::universe(),
                                                            rhs_inhab_ty
                                                            .clone()
                                                            .bind(rhs.clone())
                                                            .into_tm(),
                                                            motive.clone().app(rhs.inj_rhs()),
                                                        )
                                                    })
                                                )
                                            )
                                            .map(ch, |ch, _, _| {
                                                let rhs_inhab = Scope::make(
                                                    ch.ctx_len(),
                                                    |rhs| {
                                                        Tm::cast(
                                                            rhs_inhab_ty.clone().bind(rhs.clone()),
                                                            motive
                                                            .clone()
                                                            .app(rhs.clone().inj_rhs())
                                                            .into_ty(),
                                                            rhs_inhab_tm.bind(rhs),
                                                        )
                                                    },
                                                );
                                                Scope::make(ch.ctx_len(), |tm| {
                                                    let sum = Tm::cast(var_ty, sum_ty, tm);

                                                    let ty = {
                                                        motive
                                                        .clone()
                                                        .app(sum.clone())
                                                        .into_ty()
                                                    };
                                                    let tm = {
                                                        sum
                                                        .case(
                                                            lhs_name,
                                                            Scope::make(ch.ctx_len() + 1, |sum| {
                                                                motive.app(sum).into_ty()
                                                            }),
                                                            lhs_inhab,
                                                            rhs_inhab,
                                                        )
                                                    };
                                                    Checked::pure((ty, tm))
                                                })
                                            })
                                        })
                                    })
                                })
                            })
                        })
                    })
                })
            })
        },
    }
}

fn lookup_var(ch: &mut CheckCtx, span: Span, var_name: Name) -> Checked<(Ty, Tm)> {
    match ch.lookup_var(&var_name) {
        None => {
            Checked::assume_ty(
                MetaTag::TypeOfUnresolvedVariable { span: span.clone() },
            )
            .and_then(ch, |ch, _, var_ty| {
                Checked::assume(
                    MetaTag::UnresolvedVariable { span: span.clone() },
                    Ty::never(),
                )
                .map(ch, |_, _, _| {
                    let tm = Tm::explode(Scope::constant(var_ty.clone()));
                    (var_ty, tm)
                })
            })
        },
        Some((var_ty, index)) => {
            Checked::pure((var_ty, Tm::var(index)))
        },
    }
}

