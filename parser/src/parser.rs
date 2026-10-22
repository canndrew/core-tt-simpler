use crate::priv_prelude::*;

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("unexpected token at {}", token.span())]
    UnexpectedToken {
        token: Token<Span>,
    },
    #[error("{0}")]
    Tokenize(TokenizeError),
    #[error("error parsing let pattern at {}", let_span)]
    ParseLetPattern {
        let_span: Span,
    },
    #[error("error parsing let statement ty starting at {}", colon_span)]
    ParseLetTy {
        colon_span: Span,
    },
    #[error("expected '=' after pattern for let statement at {}", let_span)]
    ParseLetEq {
        let_span: Span,
    },
    #[error("error parsing let rhs at {}", let_span)]
    ParseLetRhs {
        let_span: Span,
    },
    #[error("error parsing let body at {}", let_span)]
    ParseLetBody {
        let_span: Span,
    },
    #[error("error parsing block at {}", block_span)]
    ParseBlock {
        block_span: Span,
    },
    #[error("expected fn arguments at {}", fn_span)]
    MissingFnTermArgs {
        fn_span: Span,
    },
    #[error("error parsing field type starting at {}", colon_span)]
    ParseTypeFieldTy {
        colon_span: Span,
    },
    #[error("error parsing function arg type starting at {}", colon_span)]
    ParseFuncTermArgTy {
        colon_span: Span,
    },
}

impl From<UnexpectedTokenError> for ParseError {
    fn from(err: UnexpectedTokenError) -> ParseError {
        ParseError::UnexpectedToken { token: err.token }
    }
}

impl From<TokenizeError> for ParseError {
    fn from(err: TokenizeError) -> ParseError {
        ParseError::Tokenize(err)
    }
}

#[derive(Clone, Copy)]
enum Keyword {
    Def,
    FnLower,
    FnUpper,
    Let,
    Refl,
    Match,
    For,
    In,
    With,
    Struct,
    Enum,
    /*
    Type,
    Nat,
    Funds,
    Commit,
    */
}

impl Keyword {
    fn all() -> &'static [Keyword] {
        &[
            Keyword::Def,
            Keyword::FnLower,
            Keyword::FnUpper,
            Keyword::Let,
            Keyword::Refl,
            Keyword::Match,
            Keyword::For,
            Keyword::In,
            Keyword::With,
            Keyword::Struct,
            Keyword::Enum,
            /*
            Keyword::Type,
            Keyword::Nat,
            Keyword::Funds,
            Keyword::Commit,
            */
        ]
    }

    fn as_str(&self) -> &'static str {
        match self {
            Keyword::Def => "def",
            Keyword::FnLower => "fn",
            Keyword::FnUpper => "Fn",
            Keyword::Let => "let",
            Keyword::Refl => "refl",
            Keyword::Match => "match",
            Keyword::For => "for",
            Keyword::In => "in",
            Keyword::With => "with",
            Keyword::Struct => "struct",
            Keyword::Enum => "enum",
            /*
            Keyword::Type => "Type",
            Keyword::Nat => "Nat",
            Keyword::Funds => "Funds",
            Keyword::Commit => "commit",
            */
        }
    }
}

fn keyword<E>(keyword: Keyword) -> impl Parser<Output = (), Error = E> {
    ident()
    .filter_map(move |ident| {
        (ident.as_str() == keyword.as_str()).then_some(())
    })
}

fn name_ident<E>() -> impl Parser<Output = Ident, Error = E> {
    ident().filter_map(move |ident| {
        if Keyword::all().iter().all(|keyword| ident.as_str() != keyword.as_str()) {
            Some(ident)
        } else {
            None
        }
    })
}


pub type DynParser<T> = Box<dyn Parser<Output = T, Error = ParseError>>;

fn name() -> DynParser<ast::Name<Span>> {
    lazy(|| {
        any_of((
            name_ident().map(ast::Name::Ident),
            punct(PunctKind::Dollar).unit_then(prec_atom().boxed()).map(ast::Name::Quoted),
        ))
    })
    .box_dyn()
}

/*
pub fn program() -> Box<dyn Parser<Output = ast::Program, Error = ParseError>> {
    item().many().map(|items| ast::Program { items }).box_dyn()
}

fn item() -> Box<dyn Parser<Output = ast::Item, Error = ParseError>> {
    item_def().spanned().map(|item| ast::Item::ItemDef(item)).box_dyn()
}

fn item_def() -> Box<dyn Parser<Output = ast::ItemDef, Error = ParseError>> {
    all_of((
        keyword(Keyword::Def).unit_then(name_ident()),
        parens(|_| type_field().spanned().box_dyn().comma_separated()),
        punct(PunctKind::Arrow).unit_then(prec_equal().boxed()),
        curly_braced(|_| prec_stmt().boxed()),
    ))
    .map(|(name, args, return_ty, body)| ast::ItemDef { name, args, return_ty, body })
    .box_dyn()
}
*/

fn let_stmt() -> DynParser<ast::LetStmt<Span>> {
    keyword(Keyword::Let)
    .spanned()
    .spanned_unit_then(|let_span| {
        all_of((
            {
                let let_span = let_span.clone();
                pat_prec_inj()
                .boxed()
                .required(move || ParseError::ParseLetPattern { let_span: let_span.clone() })
            },
            {
                parens(|_| {
                    func_term_arg()
                    .spanned()
                    .box_dyn()
                    .comma_separated()
                })
                .optional()
            },
            {
                punct(PunctKind::Colon)
                .spanned()
                .spanned_unit_then(|colon_span| {
                    let colon_span = colon_span.clone();
                    prec_func()
                    .required(move || ParseError::ParseLetTy { colon_span: colon_span.clone() })
                })
                .boxed()
                .optional()
            },
            {
                let let_span_0 = let_span.clone();
                let let_span_1 = let_span.clone();
                punct(PunctKind::Equal)
                .required(move || ParseError::ParseLetEq { let_span: let_span_0.clone() })
                .unit_then(prec_func())
                .boxed()
                .required(move || ParseError::ParseLetRhs { let_span: let_span_1.clone() })
            },
            {
                let let_span = let_span.clone();
                punct(PunctKind::Semicolon)
                .unit_then(prec_stmt())
                .boxed()
                .required(move || ParseError::ParseLetBody { let_span: let_span.clone() })
            },
        ))
        .map(|(var_pat, var_args_opt, var_ty_opt, var_expr, body)| {
            ast::LetStmt { var_pat, var_args_opt, var_ty_opt, var_expr, body }
        })
    })
    .box_dyn()
}

fn expr_func_type() -> DynParser<ast::ExprFuncType<Span>> {
    all_of((
        keyword(Keyword::FnUpper).unit_then(parens(|_| func_term_arg().spanned().box_dyn().comma_separated())),
        punct(PunctKind::Arrow).unit_then(prec_func().boxed()),
    ))
    .map(|(args, return_ty)| ast::ExprFuncType { args, return_ty })
    .box_dyn()
}

fn func_term_arg() -> DynParser<ast::FuncTermArg<Span>> {
    name()
    .spanned()
    .then(func_term_arg_ty().optional())
    .map(|(arg_name, arg_ty_opt)| ast::FuncTermArg { arg_name, arg_ty_opt })
    .box_dyn()
}

fn func_term_arg_ty() -> DynParser<ast::FuncTermArgTy<Span>> {
    all_of((
        parens(|_| {
            func_term_arg()
            .spanned()
            .box_dyn()
            .comma_separated()
        })
        .optional(),
        punct(PunctKind::Colon)
        .spanned()
        .spanned_unit_then(|colon_span| {
            prec_func()
            .required(move || ParseError::ParseFuncTermArgTy { colon_span: colon_span.clone() })
            .boxed()
        })
    ))
    .map(|(args_opt, ty)| ast::FuncTermArgTy { args_opt, ty })
    .box_dyn()
}

fn expr_func_term() -> DynParser<ast::ExprFuncTerm<Span>> {
    all_of((
        keyword(Keyword::FnLower)
        .spanned()
        .spanned_unit_then(|fn_span| {
            let fn_span = fn_span.clone();
            parens(|_| {
                func_term_arg()
                .spanned()
                .box_dyn()
                .comma_separated()
            })
            .required(move || ParseError::MissingFnTermArgs { fn_span: fn_span.clone() })
        }),
        punct(PunctKind::FatArrow).unit_then(prec_func().boxed()),
    ))
    .map(|(args, body)| ast::ExprFuncTerm { args, body })
    .box_dyn()
}

fn expr_inj_lhs() -> DynParser<ast::ExprInjLhs<Span>> {
    all_of((
        //punct(PunctKind::Dot).unit_then(name_ident()),
        punct(PunctKind::Dot).unit_then(name().spanned()),
        prec_inj().boxed(),
    ))
    .map(|(variant_name, payload)| ast::ExprInjLhs { variant_name, payload })
    .box_dyn()
}

fn expr_inj_rhs() -> DynParser<ast::ExprInjRhs<Span>> {
    punct(PunctKind::TripleDot)
    .unit_then(prec_inj().boxed())
    .map(|payload| ast::ExprInjRhs { payload })
    .box_dyn()
}

fn expr_refl() -> DynParser<ast::ExprRefl<Span>> {
    keyword(Keyword::Refl)
    .unit_then(prec_inj().boxed())
    .map(|eq_expr| ast::ExprRefl { eq_expr })
    .box_dyn()
}

fn func_app_arg() -> DynParser<ast::FuncAppArg<Span>> {
    all_of((
        name().spanned(),
        func_app_arg_expr().optional(),
    ))
    .map(|(arg_name, arg_expr_opt)| ast::FuncAppArg { arg_name, arg_expr_opt })
    .box_dyn()
}

fn func_app_arg_expr() -> DynParser<ast::FuncAppArgExpr<Span>> {
    all_of((
        parens(|_| {
            func_term_arg()
            .spanned()
            .box_dyn()
            .comma_separated()
        })
        .optional(),
        punct(PunctKind::Equal).unit_then(prec_func().boxed()),
    ))
    .map(|(args_opt, expr)| ast::FuncAppArgExpr { args_opt, expr })
    .box_dyn()
}

fn expr_match() -> DynParser<ast::ExprMatch<Span>> {
    all_of((
        keyword(Keyword::Match).unit_then(prec_equal().boxed()),
        curly_braced(|_| match_branch().spanned().box_dyn().comma_separated()),
    ))
    .map(|(elim, branches)| ast::ExprMatch { elim, branches })
    .box_dyn()
}

fn match_branch() -> DynParser<ast::MatchBranch<Span>> {
    all_of((
        punct(PunctKind::Dot).unit_then(name().spanned()),
        pat_prec_inj().boxed(),
        punct(PunctKind::FatArrow).unit_then(prec_equal().boxed()),
    ))
    .map(|(variant_name, payload_pat, body)| {
        ast::MatchBranch { variant_name, payload_pat, body }
    })
    .box_dyn()
}

/*
fn expr_for_loop() -> Box<dyn Parser<Output = ast::ExprForLoop<Span>, Error = ParseError>> {
    all_of((
        keyword(Keyword::For).unit_then(name_ident()),
        keyword(Keyword::In).unit_then(prec_equal().boxed()),
        keyword(Keyword::With).unit_then(name_ident()),
        punct(PunctKind::Colon).unit_then(prec_func().boxed()),
        punct(PunctKind::Equal).unit_then(prec_func().boxed()),
        curly_braced(|_| prec_stmt().boxed()),
    ))
    .map(|(counter_name, elim, state_name, state_ty, init, body)| {
        ast::ExprForLoop { counter_name, elim, state_name, state_ty, init, body }
    })
    .box_dyn()
}
*/

fn expr_struct_type() -> DynParser<ast::ExprStructType<Span>> {
    keyword(Keyword::Struct)
    .unit_then(curly_braced(|_| {
        type_field()
        .spanned()
        .box_dyn()
        .comma_separated_trailing(
            punct(PunctKind::DoubleDot)
            .unit_then(prec_func().boxed())
        )
    }))
    .map(|fields_and_tail_ty_opt| {
        let (fields, tail_ty_opt) = fields_and_tail_ty_opt.inner;
        ast::ExprStructType { fields, tail_ty_opt }
    })
    .box_dyn()
}

fn expr_enum_type() -> DynParser<ast::ExprEnumType<Span>> {
    keyword(Keyword::Enum)
    .unit_then(curly_braced(|_| {
        type_field()
        .spanned()
        .box_dyn()
        .comma_separated_trailing(
            punct(PunctKind::DoubleDot)
            .unit_then(prec_func().boxed())
        )
    }))
    .map(|variants_and_rhs_ty_opt| {
        let (variants, rhs_ty_opt) = variants_and_rhs_ty_opt.inner;
        ast::ExprEnumType { variants, rhs_ty_opt }
    })
    .box_dyn()
}

fn type_field() -> DynParser<ast::TypeField<Span>> {
    name()
    .spanned()
    .then(
        punct(PunctKind::Colon)
        .spanned()
        .spanned_unit_then(|colon_span| {
            prec_equal()
            .required(move || ParseError::ParseTypeFieldTy { colon_span: colon_span.clone() })
            .boxed()
        })
    )
    .map(|(name, ty)| ast::TypeField { name, ty })
    .box_dyn()
}

fn expr_struct_term() -> DynParser<ast::ExprStructTerm<Span>> {
    parens(|_| {
        expr_struct_term_field()
        .spanned()
        .box_dyn()
        .comma_separated_trailing(
            punct(PunctKind::DoubleDot)
            .unit_then(prec_func().boxed())
        )
    })
    .map(|fields_and_tail_opt| {
        let (fields, tail_opt) = fields_and_tail_opt.inner;
        ast::ExprStructTerm { fields, tail_opt }
    })
    .box_dyn()
}

fn expr_struct_term_field() -> DynParser<ast::ExprStructTermField<Span>> {
    name()
    .spanned()
    .then(
        punct(PunctKind::Equal)
        .unit_then(prec_equal())
        .optional()
    )
    .map(|(name, expr_opt)| ast::ExprStructTermField { name, expr_opt })
    .box_dyn()
}

pub fn prec_stmt() -> DynParser<ast::PrecStmt<Span>> {
    lazy(|| {
        any_of((
            let_stmt().spanned().map(ast::PrecStmt::Let),
            prec_func().map(ast::PrecStmt::Other),
            pure(()).spanned().map(|spanned| ast::PrecStmt::Blank(spanned.span)),
        ))
    })
    .box_dyn()
}

fn prec_func() -> DynParser<ast::PrecFunc<Span>> {
    lazy(|| {
        any_of((
            expr_func_type().spanned().map(ast::PrecFunc::FuncType),
            expr_func_term().spanned().map(ast::PrecFunc::FuncTerm),
            prec_equal().map(ast::PrecFunc::Other),
        ))
    })
    .box_dyn()
}

fn prec_equal() -> DynParser<ast::PrecEqual<Span>> {
    lazy(|| {
        prec_add()
        .then(
            punct(PunctKind::DoubleEqual)
            .unit_then(prec_add().boxed())
            .optional()
        )
        .map(|(eq_expr_0, eq_expr_1_opt)| {
            match eq_expr_1_opt {
                None => ast::PrecEqual::Other(eq_expr_0),
                Some(eq_expr_1) => {
                    let eq_expr_0 = Box::new(eq_expr_0);
                    let span = Span::combine(&eq_expr_0.span(), &eq_expr_1.span());
                    ast::PrecEqual::Equal(
                        Spanned::new(span, ast::ExprEqual { eq_expr_0, eq_expr_1 }),
                    )
                },
            }
        })
    })
    .box_dyn()
}

fn prec_add() -> DynParser<ast::PrecAdd<Span>> {
    lazy(|| {
        prec_mul()
        .map(ast::PrecAdd::Other)
        .then(punct(PunctKind::Plus).unit_then(prec_mul().boxed()).many())
        .map(|(lhs, rhss)| rhss.into_iter().fold(lhs, |lhs, rhs| {
            let span = Span::combine(&lhs.span(), &rhs.span());
            ast::PrecAdd::Add(Spanned::new(span, ast::ExprAdd { lhs: Box::new(lhs), rhs }))
        }))
    })
    .box_dyn()
}

fn prec_mul() -> DynParser<ast::PrecMul<Span>> {
    lazy(|| {
        prec_inj()
        .map(ast::PrecMul::Other)
        .then(punct(PunctKind::Star).unit_then(prec_inj().boxed()).many())
        .map(|(lhs, rhss)| rhss.into_iter().fold(lhs, |lhs, rhs| {
            let span = Span::combine(&lhs.span(), &rhs.span());
            ast::PrecMul::Mul(Spanned::new(span, ast::ExprMul { lhs: Box::new(lhs), rhs }))
        }))
    })
    .box_dyn()
}

fn prec_inj() -> DynParser<ast::PrecInj<Span>> {
    lazy(|| {
        any_of((
            expr_inj_lhs().spanned().map(ast::PrecInj::InjLhs),
            expr_inj_rhs().spanned().map(ast::PrecInj::InjRhs),
            expr_refl().spanned().map(ast::PrecInj::Refl),
            prec_proj().map(ast::PrecInj::Other),
        ))
    })
    .box_dyn()
}

fn prec_proj() -> DynParser<ast::PrecProj<Span>> {
    lazy(|| {
        prec_app()
        .map(ast::PrecProj::Other)
        .then(punct(PunctKind::Dot).unit_then(name().spanned()).many())
        .map(|(base, field_names)| field_names.into_iter().fold(base, |base, field_name| {
            let span = Span::combine(&base.span(), &field_name.span());
            ast::PrecProj::Proj(Spanned::new(span, ast::ExprProj { base: Box::new(base), field_name }))
        }))
    })
    .box_dyn()
}

fn prec_app() -> DynParser<ast::PrecApp<Span>> {
    lazy(|| {
        prec_atom()
        .map(ast::PrecApp::Other)
        .then(parens(|_| func_app_arg().spanned().box_dyn().comma_separated()).many())
        .map(|(func, argss)| argss.into_iter().fold(func, |func, args| {
            let span = Span::combine(&func.span(), &args.span);
            ast::PrecApp::App(Spanned::new(span, ast::ExprApp { func: Box::new(func), args }))
        }))
    })
    .box_dyn()
}

fn prec_atom() -> DynParser<ast::PrecAtom<Span>> {
    lazy(|| {
        any_of((
            name().spanned().map(ast::PrecAtom::Var),
            string().map(ast::PrecAtom::NameLiteral),
            number().spanned().map(ast::PrecAtom::Nat),
            expr_match().spanned().map(ast::PrecAtom::Match),
            //expr_for_loop().spanned().map(ast::PrecAtom::ForLoop),
            expr_struct_type().spanned().map(ast::PrecAtom::StructType),
            expr_enum_type().spanned().map(ast::PrecAtom::EnumType),
            expr_struct_term().spanned().map(ast::PrecAtom::StructTerm),
            curly_braced(|block_span| {
                prec_stmt()
                .boxed()
                .required(move || ParseError::ParseBlock { block_span: block_span.clone() })
            }).map(ast::PrecAtom::Braced),
        ))
    })
    .box_dyn()
}

fn pat_refl() -> DynParser<ast::PatRefl<Span>> {
    keyword(Keyword::Refl)
    .unit_then(pat_prec_inj().boxed())
    .map(|eq_pat| ast::PatRefl { eq_pat })
    .box_dyn()
}

fn pat_struct_term() -> DynParser<ast::PatStructTerm<Span>> {
    parens(|_| {
        pat_struct_term_field()
        .spanned()
        .box_dyn()
        .comma_separated_trailing(
            punct(PunctKind::DoubleDot)
            .unit_then(pat_prec_inj().boxed())
        )
    })
    .map(|fields_and_tail_opt| {
        let (fields, tail_opt) = fields_and_tail_opt.inner;
        ast::PatStructTerm { fields, tail_opt }
    })
    .box_dyn()
}

fn pat_struct_term_field() -> DynParser<ast::PatStructTermField<Span>> {
    name()
    .spanned()
    .then(
        punct(PunctKind::Equal).unit_then(pat_prec_inj())
        .optional()
    )
    .map(|(name, pat_opt)| ast::PatStructTermField { name, pat_opt })
    .box_dyn()
}

fn pat_prec_inj() -> DynParser<ast::PatPrecInj<Span>> {
    lazy(|| {
        any_of((
            pat_refl().spanned().map(ast::PatPrecInj::Refl),
            pat_prec_atom().map(ast::PatPrecInj::Other)
        ))
    })
    .box_dyn()
}

fn pat_prec_atom() -> DynParser<ast::PatPrecAtom<Span>> {
    lazy(||
        any_of((
            name().spanned().map(ast::PatPrecAtom::Var),
            pat_struct_term().spanned().map(ast::PatPrecAtom::Struct),
        ))
    )
    .box_dyn()
}

