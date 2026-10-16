use crate::priv_prelude::*;

#[derive(Debug)]
pub enum Name<S: Spans> {
    Ident(S::Ident),
    Quoted(Box<PrecAtom<S>>),
}

#[derive(Debug)]
pub enum PrecStmt<S: Spans> {
    Let(Spanned<S, LetStmt<S>>),
    Blank(S),
    Other(PrecFunc<S>),
}

#[derive(Debug)]
pub enum PrecFunc<S: Spans> {
    FuncType(Spanned<S, ExprFuncType<S>>),
    FuncTerm(Spanned<S, ExprFuncTerm<S>>),
    Other(PrecEqual<S>),
}

#[derive(Debug)]
pub enum PrecEqual<S: Spans> {
    Equal(Spanned<S, ExprEqual<S>>),
    Other(PrecAdd<S>),
}

#[derive(Debug)]
pub enum PrecAdd<S: Spans> {
    Add(Spanned<S, ExprAdd<S>>),
    Other(PrecMul<S>),
}

#[derive(Debug)]
pub enum PrecMul<S: Spans> {
    Mul(Spanned<S, ExprMul<S>>),
    Other(PrecInj<S>),
}

#[derive(Debug)]
pub enum PrecInj<S: Spans> {
    InjLhs(Spanned<S, ExprInjLhs<S>>),
    InjRhs(Spanned<S, ExprInjRhs<S>>),
    Refl(Spanned<S, ExprRefl<S>>),
    Other(PrecProj<S>),
}

#[derive(Debug)]
pub enum PrecProj<S: Spans> {
    Proj(Spanned<S, ExprProj<S>>),
    Other(PrecApp<S>),
}

#[derive(Debug)]
pub enum PrecApp<S: Spans> {
    App(Spanned<S, ExprApp<S>>),
    Other(PrecAtom<S>),
}

#[derive(Debug)]
pub enum PrecAtom<S: Spans> {
    Var(Spanned<S, Name<S>>),
    NameLiteral(Spanned<S, String>),
    Nat(Spanned<S, BigUint>),
    Match(Spanned<S, ExprMatch<S>>),
    StructType(Spanned<S, ExprStructType<S>>),
    StructTerm(Spanned<S, ExprStructTerm<S>>),
    EnumType(Spanned<S, ExprEnumType<S>>),
    Braced(Spanned<S, Box<PrecStmt<S>>>),
}

#[derive(Debug)]
pub struct LetStmt<S: Spans> {
    pub var_pat: Box<PatPrecInj<S>>,
    pub var_args_opt: Option<Spanned<S, Vec<Spanned<S, FuncTermArg<S>>>>>,
    pub var_ty_opt: Option<Box<PrecFunc<S>>>,
    pub var_expr: Box<PrecFunc<S>>,
    pub body: Box<PrecStmt<S>>,
}

#[derive(Debug)]
pub struct ExprFuncType<S: Spans> {
    pub args: Spanned<S, Vec<Spanned<S, FuncTermArg<S>>>>,
    pub return_ty: Box<PrecFunc<S>>,
}

#[derive(Debug)]
pub struct ExprFuncTerm<S: Spans> {
    pub args: Spanned<S, Vec<Spanned<S, FuncTermArg<S>>>>,
    pub body: Box<PrecFunc<S>>,
}

#[derive(Debug)]
pub struct ExprEqual<S: Spans> {
    pub eq_expr_0: Box<PrecAdd<S>>,
    pub eq_expr_1: Box<PrecAdd<S>>,
}

#[derive(Debug)]
pub struct ExprAdd<S: Spans> {
    pub lhs: Box<PrecAdd<S>>,
    pub rhs: Box<PrecMul<S>>,
}

#[derive(Debug)]
pub struct ExprMul<S: Spans> {
    pub lhs: Box<PrecMul<S>>,
    pub rhs: Box<PrecInj<S>>,
}

#[derive(Debug)]
pub struct ExprInjLhs<S: Spans> {
    pub variant_name: Spanned<S, Name<S>>,
    pub payload: Box<PrecInj<S>>,
}

#[derive(Debug)]
pub struct ExprInjRhs<S: Spans> {
    pub payload: Box<PrecInj<S>>,
}

#[derive(Debug)]
pub struct ExprRefl<S: Spans> {
    pub eq_expr: Box<PrecInj<S>>,
}

#[derive(Debug)]
pub struct ExprProj<S: Spans> {
    pub base: Box<PrecProj<S>>,
    pub field_name: Spanned<S, Name<S>>,
}

#[derive(Debug)]
pub struct ExprApp<S: Spans> {
    pub func: Box<PrecApp<S>>,
    pub args: Spanned<S, Vec<Spanned<S, FuncAppArg<S>>>>,
}

#[derive(Debug)]
pub struct FuncAppArg<S: Spans> {
    pub arg_name: Spanned<S, Name<S>>,
    pub arg_expr_opt: Option<FuncAppArgExpr<S>>,
}

#[derive(Debug)]
pub struct FuncAppArgExpr<S: Spans> {
    pub args_opt: Option<Spanned<S, Vec<Spanned<S, FuncTermArg<S>>>>>,
    pub expr: Box<PrecFunc<S>>,
}

#[derive(Debug)]
pub struct ExprMatch<S: Spans> {
    pub elim: Box<PrecEqual<S>>,
    pub branches: Spanned<S, Vec<Spanned<S, MatchBranch<S>>>>,
}

#[derive(Debug)]
pub struct MatchBranch<S: Spans> {
    pub variant_name: Spanned<S, Name<S>>,
    pub payload_pat: Box<PatPrecInj<S>>,
    pub body: Box<PrecEqual<S>>,
}

#[derive(Debug)]
pub struct ExprStructType<S: Spans> {
    pub fields: Vec<Spanned<S, TypeField<S>>>,
    pub tail_ty_opt: Option<Box<PrecFunc<S>>>,
}

#[derive(Debug)]
pub struct ExprStructTerm<S: Spans> {
    pub fields: Vec<Spanned<S, ExprStructTermField<S>>>,
    pub tail_opt: Option<Box<PrecFunc<S>>>,
}

#[derive(Debug)]
pub struct ExprStructTermField<S: Spans> {
    pub name: Spanned<S, Name<S>>,
    pub expr_opt: Option<PrecEqual<S>>,
}

#[derive(Debug)]
pub struct ExprEnumType<S: Spans> {
    pub variants: Vec<Spanned<S, TypeField<S>>>,
    pub rhs_ty_opt: Option<Box<PrecFunc<S>>>,
}

#[derive(Debug)]
pub struct FuncTermArg<S: Spans> {
    pub arg_name: Spanned<S, Name<S>>,
    pub arg_ty_opt: Option<FuncTermArgTy<S>>,
}

#[derive(Debug)]
pub struct FuncTermArgTy<S: Spans> {
    pub args_opt: Option<Spanned<S, Vec<Spanned<S, FuncTermArg<S>>>>>,
    pub ty: Box<PrecFunc<S>>,
}

#[derive(Debug)]
pub struct TypeField<S: Spans> {
    pub name: Spanned<S, Name<S>>,
    pub ty: Box<PrecEqual<S>>,
}

#[derive(Debug)]
pub enum PatPrecInj<S: Spans> {
    Refl(Spanned<S, PatRefl<S>>),
    Other(PatPrecAtom<S>),
}

#[derive(Debug)]
pub enum PatPrecAtom<S: Spans> {
    Var(Spanned<S, Name<S>>),
    Struct(Spanned<S, PatStructTerm<S>>),
}

#[derive(Debug)]
pub struct PatRefl<S: Spans> {
    pub eq_pat: Box<PatPrecInj<S>>,
}

#[derive(Debug)]
pub struct PatStructTerm<S: Spans> {
    pub fields: Vec<Spanned<S, PatStructTermField<S>>>,
    pub tail_opt: Option<Box<PatPrecInj<S>>>,
}

#[derive(Debug)]
pub struct PatStructTermField<S: Spans> {
    pub name: Spanned<S, Name<S>>,
    pub pat_opt: Option<PatPrecInj<S>>,
}

impl<S: Spans> HasSpan<S> for Name<S> {
    fn span(&self) -> S {
        match self {
            Name::Ident(ident) => ident.span(),
            Name::Quoted(prec_atom) => prec_atom.span(),
        }
    }
}

impl<S: Spans> HasSpan<S> for PrecStmt<S> {
    fn span(&self) -> S {
        match self {
            PrecStmt::Let(x) => x.span(),
            PrecStmt::Blank(span) => span.clone(),
            PrecStmt::Other(x) => x.span(),
        }
    }
}

impl<S: Spans> HasSpan<S> for PrecFunc<S> {
    fn span(&self) -> S {
        match self {
            PrecFunc::FuncType(x) => x.span(),
            PrecFunc::FuncTerm(x) => x.span(),
            PrecFunc::Other(x) => x.span(),
        }
    }
}

impl<S: Spans> HasSpan<S> for PrecEqual<S> {
    fn span(&self) -> S {
        match self {
            PrecEqual::Equal(expr_equal) => expr_equal.span(),
            PrecEqual::Other(prec_add) => prec_add.span(),
        }
    }
}

impl<S: Spans> HasSpan<S> for PrecAdd<S> {
    fn span(&self) -> S {
        match self {
            PrecAdd::Add(expr_add) => expr_add.span(),
            PrecAdd::Other(prec_mul) => prec_mul.span(),
        }
    }
}

impl<S: Spans> HasSpan<S> for PrecMul<S> {
    fn span(&self) -> S {
        match self {
            PrecMul::Mul(expr_mul) => expr_mul.span(),
            PrecMul::Other(prec_inj) => prec_inj.span(),
        }
    }
}

impl<S: Spans> HasSpan<S> for PrecInj<S> {
    fn span(&self) -> S {
        match self {
            PrecInj::InjLhs(expr_inj_lhs) => expr_inj_lhs.span(),
            PrecInj::InjRhs(expr_inj_rhs) => expr_inj_rhs.span(),
            PrecInj::Refl(expr_refl) => expr_refl.span(),
            PrecInj::Other(prec_proj) => prec_proj.span(),
        }
    }
}

impl<S: Spans> HasSpan<S> for PrecProj<S> {
    fn span(&self) -> S {
        match self {
            PrecProj::Proj(expr_proj) => expr_proj.span(),
            PrecProj::Other(prec_app) => prec_app.span(),
        }
    }
}

impl<S: Spans> HasSpan<S> for PrecApp<S> {
    fn span(&self) -> S {
        match self {
            PrecApp::App(expr_app) => expr_app.span(),
            PrecApp::Other(prec_atom) => prec_atom.span(),
        }
    }
}

impl<S: Spans> HasSpan<S> for PrecAtom<S> {
    fn span(&self) -> S {
        match self {
            PrecAtom::Var(s) => s.span(),
            PrecAtom::NameLiteral(s) => s.span(),
            PrecAtom::Nat(x) => x.span(),
            PrecAtom::Match(x) => x.span(),
            PrecAtom::StructType(x) => x.span(),
            PrecAtom::EnumType(x) => x.span(),
            PrecAtom::StructTerm(x) => x.span(),
            PrecAtom::Braced(x) => x.span(),
        }
    }
}

impl<S: Spans> HasSpan<S> for PatPrecInj<S> {
    fn span(&self) -> S {
        match self {
            PatPrecInj::Refl(x) => x.span(),
            PatPrecInj::Other(x) => x.span(),
        }
    }
}

impl<S: Spans> HasSpan<S> for PatPrecAtom<S> {
    fn span(&self) -> S {
        match self {
            PatPrecAtom::Var(s) => s.span(),
            PatPrecAtom::Struct(x) => x.span(),
        }
    }
}

