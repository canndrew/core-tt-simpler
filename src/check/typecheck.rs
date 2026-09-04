use crate::priv_prelude::*;
use parser::ast;

pub trait Check {
    type Output;
    fn check(&self, ch: &mut CheckCtx) -> Checked<Self::Output>;
}

impl Check for Spanned<ast::Name> {
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
                        MetaTag::QuotedName { span: expr.span() }.into(),
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

impl Check for ast::PrecStmt {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        match self {
            ast::PrecStmt::Let(let_stmt) => {
                let_stmt.check(ch)
            },
            ast::PrecStmt::Blank(_) => {
                Checked::pure((Ty::unit(), Tm::unit()))
            },
            ast::PrecStmt::Other(prec_func) => {
                prec_func.check(ch)
            },
        }
    }
}

impl Check for ast::PrecFunc {
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

impl Check for ast::PrecEqual {
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

impl Check for ast::PrecAdd {
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

impl Check for ast::PrecMul {
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

impl Check for ast::PrecInj {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        match self {
            ast::PrecInj::Inj(expr_inj) => {
                expr_inj.check(ch)
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

impl Check for ast::PrecProj {
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

impl Check for ast::PrecApp {
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

impl Check for ast::PrecAtom {
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

impl Check for Spanned<ast::LetStmt> {
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
                                MetaTag::LetStmtVarTy { var_ty_span: var_ty_span.clone() }.into(),
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
                                    MetaTag::LetStmtVarTm { var_tm_span: var_expr.span() }.into(),
                                    MetaTag::LetStmtVarTmTypeMatchesAnnotatedType {
                                        var_tm_span: var_expr.span(),
                                        var_ty_span: var_ty_span,
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

impl Check for Spanned<ast::ExprFuncType> {
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
                        MetaTag::FuncResTy { res_ty_span: return_ty.span() }.into(),
                        MetaTag::FuncResTyIsAType { res_ty_span: return_ty.span() },
                        res_ty_ty,
                        res_ty
                    )
                })
            },
        )
    }
}

impl Check for Spanned<ast::ExprFuncTerm> {
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

impl Check for Spanned<ast::ExprEqual> {
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
                    MetaTag::EqualEqTm0 { eq_tm_0_span: eq_expr_0.span() }.into(),
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
                    Ty::equal(eq_ty_1, eq_tm_0, eq_tm_1)
                })
            })
        })
    }
}

impl Check for Spanned<ast::ExprAdd> {
    type Output = (Ty, Tm);

    fn check(&self, _ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        unimplemented!()
    }
}

impl Check for Spanned<ast::ExprMul> {
    type Output = (Ty, Tm);

    fn check(&self, _ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        unimplemented!()
    }
}

impl Check for Spanned<ast::ExprInj> {
    type Output = (Ty, Tm);

    fn check(&self, ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        let ast::ExprInj { variant_name, payload } = &self.inner;
        
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
                        }.into(),
                        Ty::nat(),
                    )
                    .and_then(ch, |ch, _, inj_count| {
                        let injections_metas = implicit_rhs_injections_metas(self.span());
                        let injections_metas = injections_metas.each_ref();
                        Checked::assume(
                            injections_metas[0].clone(),
                            implicit_rhs_injections_ty(ch.ctx_len(), injections_metas, inj_count.clone())
                        )
                        .map(ch, |ch, _, injections| {
                            let ty = apply_implicit_rhs_injections_to_ty(
                                ch.ctx_len(),
                                injections_metas,
                                inj_count.clone(),
                                injections.clone(),
                                base_ty.clone(),
                            );
                            let tm = apply_implicit_rhs_injections_to_tm(
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

impl Check for Spanned<ast::ExprRefl> {
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
            let ty = Ty::equal(eq_ty, eq_tm.clone(), eq_tm.clone());
            (ty, eq_tm.refl())
        })
    }
}

impl Check for Spanned<ast::ExprProj> {
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
                    let projections_metas = implicit_tail_projections_metas(self.span());
                    let projections_metas = projections_metas.each_ref();
                    Checked::assume(
                        projections_metas[0].clone(),
                        implicit_tail_projections_ty(
                            ch.ctx_len(),
                            projections_metas,
                            proj_count.clone(),
                            base_ty.clone(),
                            base_tm.clone(),
                        ),
                    )
                    .and_then(ch, |ch, _, projections| {
                        let ty = apply_implicit_tail_projections_to_ty(
                            ch.ctx_len(),
                            projections_metas,
                            proj_count.clone(),
                            base_ty.clone(),
                            base_tm.clone(),
                            projections.clone(),
                        );
                        let tm = apply_implicit_tail_projections_to_tm(
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
                                    projections_metas[2].clone().into(),
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

impl Check for Spanned<ast::ExprApp> {
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
                            MetaTag::AppElim {
                                elim_span: func.span(),
                                arg_tm_span: arg.span(),
                            }.into(),
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

impl Check for Spanned<ast::FuncAppArg> {
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

impl Check for &ast::FuncAppArgExpr {
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

impl Check for Spanned<ast::ExprMatch> {
    type Output = (Ty, Tm);

    fn check(&self, _ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        todo!()
    }
}

impl Check for Spanned<ast::ExprStructType> {
    type Output = Ty;

    fn check(&self, ch: &mut CheckCtx) -> Checked<Ty> {
        fn recurse(
            ch: &mut CheckCtx,
            fields: &[Spanned<ast::TypeField>],
            tail_ty_opt: Option<&ast::PrecFunc>,
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
                                    MetaTag::SigmaTailTy {
                                        tail_ty_span: tail_ty_span.clone(),
                                    }.into(),
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
        recurse(ch, &fields, tail_ty_opt.as_deref())
    }
}

impl Check for Spanned<ast::ExprStructTerm> {
    type Output = (Ty, Tm);

    fn check(&self, _ch: &mut CheckCtx) -> Checked<(Ty, Tm)> {
        todo!()
        //let ast::ExprStructTerm { fields, tail_opt } = &self.inner;
    }
}

impl Check for Spanned<ast::ExprEnumType> {
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
                        MetaTag::SumRhsTy {
                            rhs_ty_span: rhs_ty_span.clone(),
                        }.into(),
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

impl Check for Spanned<ast::TypeField> {
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
                    MetaTag::TypeFieldTy {
                        ty_span: ty_span.clone(),
                    }.into(),
                    MetaTag::TypeFieldTyIsAType {
                        ty_span: ty_span,
                    },
                    ty_ty,
                    ty,
                )
            })
            .map(ch, |_, _, ty| (name, ty))
        })
    }
}

impl Check for Spanned<ast::FuncTermArg> {
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

impl Check for ast::FuncTermArgTy {
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
                        MetaTag::FuncResTy { res_ty_span: ty_span.clone() }.into(),
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
    func_term_args: &[Spanned<ast::FuncTermArg>],
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
    func_term_args: &[Spanned<ast::FuncTermArg>],
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
    pat_prec_inj: &ast::PatPrecInj,
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
    pat_prec_atom: &ast::PatPrecAtom,
    var_ty: Ty,
    func: impl FnOnce(&mut CheckCtx) -> Checked<(Ty, Tm)>,
) -> Checked<Scope<Checked<(Ty, Tm)>>> {
    match pat_prec_atom {
        ast::PatPrecAtom::Var(name) => {
            name
            .check(ch)
            .group(MetaTag::PatternVarNameConstraint { name_span: name.span() })
            .map(ch, |ch, _, name| {
                ch
                .with_var(name, var_ty.clone(), |ch, _| func(ch))
            })
        },
        ast::PatPrecAtom::Struct(pat_struct_term) => {
            check_pat_struct_term(ch, pat_struct_term, var_ty, func)
        },
    }
}

fn check_pat_refl(
    ch: &mut CheckCtx,
    pat_refl: &Spanned<ast::PatRefl>,
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
                    Ty::equal(
                        Ty::universe(),
                        var_ty.clone().into_tm(),
                        Ty::equal(eq_ty.clone(), eq_tm_0.clone(), eq_tm_1.clone()).into_tm(),
                    ),
                )
                .and_then(ch, |ch, _, var_tys_eq| {
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
                                    Ty::equal(eq_ty.clone(), eq_tm_0.clone(), eq_tm_1),
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
                                    .app(eq_tm_0.clone().refl())
                                    .into_ty()
                                };

                                Checked::cast(
                                    ch,
                                    MetaTag::ReflPatInhab {
                                        refl_pat_span: refl_pat_span.clone(),
                                    }.into(),
                                    MetaTag::ReflPatInhabHasCorrectType {
                                        refl_pat_span: refl_pat_span.clone(),
                                    },
                                    inhab_ty,
                                    expected_inhab_ty,
                                    inhab,
                                )
                                .map(ch, |ch, _, inhab| {
                                    Scope::make(ch.ctx_len(), |var_tm| {
                                        let elim = {
                                            var_tys_eq
                                            .transport(
                                                var_ty.clone(),
                                                var_tm,
                                                MetaTag::ReflPatVarTm {
                                                    refl_pat_span: refl_pat_span.clone(),
                                                }.into(),
                                            )
                                        };
                                        let ty = {
                                            motive
                                            .clone()
                                            .app(eq_tm_1)
                                            .app(elim.clone())
                                            .into_ty()
                                        };
                                        let tm = {
                                            elim
                                            .cong(
                                                Scope::make(ch.ctx_len() + 1, |eq_tm_1| {
                                                    Scope::make(ch.ctx_len() + 2, |elim| {
                                                        motive.app(eq_tm_1).app(elim).into_ty()
                                                    })
                                                }),
                                                inhab,
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
}

fn check_pat_struct_term(
    _ch: &mut CheckCtx,
    _pat_struct_term: &Spanned<ast::PatStructTerm>,
    _var_ty: Ty,
    _func: impl FnOnce(&mut CheckCtx) -> Checked<(Ty, Tm)>,
) -> Checked<Scope<Checked<(Ty, Tm)>>> {
    todo!()
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
}

fn implicit_rhs_injections_metas(
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

fn implicit_rhs_injections_ty(
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

fn apply_implicit_rhs_injections_to_ty(
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
                implicit_rhs_injections_ty(ctx_len + 1, injections_metas, inj_count),
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

fn apply_implicit_rhs_injections_to_tm(
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
                    implicit_rhs_injections_ty(ctx_len + 1, injections_metas, inj_count.clone()),
                    Scope::make(ctx_len + 1, |injections| {
                        apply_implicit_rhs_injections_to_ty(
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

fn implicit_tail_projections_metas(
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

fn implicit_tail_projections_ty(
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
                                                    Ty::equal(
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
                            let projection = projection.proj_tail();
                            let projection = projection.proj_tail();
                            let tail_ty = projection.clone().proj_head();
                            let projection = projection.proj_tail();
                            let base_ty_eq = projection.proj_head();
                            let pair = base_ty_eq.transport(
                                base_ty.into_ty(),
                                base_tm,
                                base_tm_meta.clone().into(),
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

fn apply_implicit_tail_projections_to_ty(
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
                    implicit_tail_projections_ty(
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

                        let projection = projection.proj_tail();
                        let projection = projection.proj_tail();
                        let tail_ty = projection.clone().proj_head();
                        let projection = projection.proj_tail();
                        let base_ty_eq = projection.proj_head();

                        let pair = base_ty_eq.transport(
                            base_ty.into_ty(),
                            base_tm,
                            base_tm_meta.clone().into(),
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

fn apply_implicit_tail_projections_to_tm(
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
                    implicit_tail_projections_ty(
                        ctx_len + 3,
                        projections_metas,
                        proj_count.clone(),
                        base_ty.clone().into_ty(),
                        base_tm.clone(),
                    ),
                    Scope::make(ctx_len + 3, |projections| {
                        apply_implicit_tail_projections_to_ty(
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

                        let projection = projection.proj_tail();
                        let projection = projection.proj_tail();
                        let tail_ty = projection.clone().proj_head();
                        let projection = projection.proj_tail();
                        let base_ty_eq = projection.proj_head();

                        let pair = base_ty_eq.transport(
                            base_ty.into_ty(),
                            base_tm,
                            base_tm_meta.clone().into(),
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

