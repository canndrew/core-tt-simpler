use crate::priv_prelude::*;

#[derive(Debug)]
pub enum Name {
    Ident(Ident),
    Quoted(Box<PrecAtom>),
}

#[derive(Debug)]
pub enum PrecStmt {
    Let(Spanned<LetStmt>),
    Blank(Span),
    Other(PrecFunc),
}

#[derive(Debug)]
pub enum PrecFunc {
    FuncType(Spanned<ExprFuncType>),
    FuncTerm(Spanned<ExprFuncTerm>),
    Other(PrecEqual),
}

#[derive(Debug)]
pub enum PrecEqual {
    Equal(Spanned<ExprEqual>),
    Other(PrecAdd),
}

#[derive(Debug)]
pub enum PrecAdd {
    Add(Spanned<ExprAdd>),
    Other(PrecMul),
}

#[derive(Debug)]
pub enum PrecMul {
    Mul(Spanned<ExprMul>),
    Other(PrecInj),
}

#[derive(Debug)]
pub enum PrecInj {
    InjLhs(Spanned<ExprInjLhs>),
    InjRhs(Spanned<ExprInjRhs>),
    Refl(Spanned<ExprRefl>),
    Other(PrecProj),
}

#[derive(Debug)]
pub enum PrecProj {
    Proj(Spanned<ExprProj>),
    Other(PrecApp),
}

#[derive(Debug)]
pub enum PrecApp {
    App(Spanned<ExprApp>),
    Other(PrecAtom),
}

#[derive(Debug)]
pub enum PrecAtom {
    Var(Spanned<Name>),
    NameLiteral(Spanned<String>),
    Nat(Spanned<BigUint>),
    Match(Spanned<ExprMatch>),
    StructType(Spanned<ExprStructType>),
    StructTerm(Spanned<ExprStructTerm>),
    EnumType(Spanned<ExprEnumType>),
    Braced(Spanned<Box<PrecStmt>>),
}

#[derive(Debug)]
pub struct LetStmt {
    pub var_pat: Box<PatPrecInj>,
    pub var_args_opt: Option<Spanned<Vec<Spanned<FuncTermArg>>>>,
    pub var_ty_opt: Option<Box<PrecFunc>>,
    pub var_expr: Box<PrecFunc>,
    pub body: Box<PrecStmt>,
}

#[derive(Debug)]
pub struct ExprFuncType {
    pub args: Spanned<Vec<Spanned<FuncTermArg>>>,
    pub return_ty: Box<PrecFunc>,
}

#[derive(Debug)]
pub struct ExprFuncTerm {
    pub args: Spanned<Vec<Spanned<FuncTermArg>>>,
    pub body: Box<PrecFunc>,
}

#[derive(Debug)]
pub struct ExprEqual {
    pub eq_expr_0: Box<PrecAdd>,
    pub eq_expr_1: Box<PrecAdd>,
}

#[derive(Debug)]
pub struct ExprAdd {
    pub lhs: Box<PrecAdd>,
    pub rhs: Box<PrecMul>,
}

#[derive(Debug)]
pub struct ExprMul {
    pub lhs: Box<PrecMul>,
    pub rhs: Box<PrecInj>,
}

#[derive(Debug)]
pub struct ExprInjLhs {
    pub variant_name: Spanned<Name>,
    pub payload: Box<PrecInj>,
}

#[derive(Debug)]
pub struct ExprInjRhs {
    pub payload: Box<PrecInj>,
}

#[derive(Debug)]
pub struct ExprRefl {
    pub eq_expr: Box<PrecInj>,
}

#[derive(Debug)]
pub struct ExprProj {
    pub base: Box<PrecProj>,
    pub field_name: Spanned<Name>,
}

#[derive(Debug)]
pub struct ExprApp {
    pub func: Box<PrecApp>,
    pub args: Spanned<Vec<Spanned<FuncAppArg>>>,
}

#[derive(Debug)]
pub struct FuncAppArg {
    pub arg_name: Spanned<Name>,
    pub arg_expr_opt: Option<FuncAppArgExpr>,
}

#[derive(Debug)]
pub struct FuncAppArgExpr {
    pub args_opt: Option<Spanned<Vec<Spanned<FuncTermArg>>>>,
    pub expr: Box<PrecFunc>,
}

#[derive(Debug)]
pub struct ExprMatch {
    pub elim: Box<PrecEqual>,
    pub branches: Spanned<Vec<Spanned<MatchBranch>>>,
}

#[derive(Debug)]
pub struct MatchBranch {
    pub variant_name: Spanned<Name>,
    pub payload_pat: Box<PatPrecInj>,
    pub body: Box<PrecEqual>,
}

#[derive(Debug)]
pub struct ExprStructType {
    pub fields: Vec<Spanned<TypeField>>,
    pub tail_ty_opt: Option<Box<PrecFunc>>,
}

#[derive(Debug)]
pub struct ExprStructTerm {
    pub fields: Vec<Spanned<ExprStructTermField>>,
    pub tail_opt: Option<Box<PrecFunc>>,
}

#[derive(Debug)]
pub struct ExprStructTermField {
    pub name: Spanned<Name>,
    pub expr_opt: Option<PrecEqual>,
}

#[derive(Debug)]
pub struct ExprEnumType {
    pub variants: Vec<Spanned<TypeField>>,
    pub rhs_ty_opt: Option<Box<PrecFunc>>,
}

#[derive(Debug)]
pub struct FuncTermArg {
    pub arg_name: Spanned<Name>,
    pub arg_ty_opt: Option<FuncTermArgTy>,
}

#[derive(Debug)]
pub struct FuncTermArgTy {
    pub args_opt: Option<Spanned<Vec<Spanned<FuncTermArg>>>>,
    pub ty: Box<PrecFunc>,
}

#[derive(Debug)]
pub struct TypeField {
    pub name: Spanned<Name>,
    pub ty: Box<PrecEqual>,
}

#[derive(Debug)]
pub enum PatPrecInj {
    Refl(Spanned<PatRefl>),
    Other(PatPrecAtom),
}

#[derive(Debug)]
pub enum PatPrecAtom {
    Var(Spanned<Name>),
    Struct(Spanned<PatStructTerm>),
}

#[derive(Debug)]
pub struct PatRefl {
    pub eq_pat: Box<PatPrecInj>,
}

#[derive(Debug)]
pub struct PatStructTerm {
    pub fields: Vec<Spanned<PatStructTermField>>,
    pub tail_opt: Option<Box<PatPrecInj>>,
}

#[derive(Debug)]
pub struct PatStructTermField {
    pub name: Spanned<Name>,
    pub pat_opt: Option<PatPrecInj>,
}

impl Name {
    pub fn span(&self) -> Span {
        match self {
            Name::Ident(ident) => ident.span(),
            Name::Quoted(prec_atom) => prec_atom.span(),
        }
    }
}

impl PrecStmt {
    pub fn span(&self) -> Span {
        match self {
            PrecStmt::Let(x) => x.span(),
            PrecStmt::Blank(span) => span.clone(),
            PrecStmt::Other(x) => x.span(),
        }
    }
}

impl PrecFunc {
    pub fn span(&self) -> Span {
        match self {
            PrecFunc::FuncType(x) => x.span(),
            PrecFunc::FuncTerm(x) => x.span(),
            PrecFunc::Other(x) => x.span(),
        }
    }
}

impl PrecEqual {
    pub fn span(&self) -> Span {
        match self {
            PrecEqual::Equal(expr_equal) => expr_equal.span(),
            PrecEqual::Other(prec_add) => prec_add.span(),
        }
    }
}

impl PrecAdd {
    pub fn span(&self) -> Span {
        match self {
            PrecAdd::Add(expr_add) => expr_add.span(),
            PrecAdd::Other(prec_mul) => prec_mul.span(),
        }
    }
}

impl PrecMul {
    pub fn span(&self) -> Span {
        match self {
            PrecMul::Mul(expr_mul) => expr_mul.span(),
            PrecMul::Other(prec_inj) => prec_inj.span(),
        }
    }
}

impl PrecInj {
    pub fn span(&self) -> Span {
        match self {
            PrecInj::InjLhs(expr_inj_lhs) => expr_inj_lhs.span(),
            PrecInj::InjRhs(expr_inj_rhs) => expr_inj_rhs.span(),
            PrecInj::Refl(expr_refl) => expr_refl.span(),
            PrecInj::Other(prec_proj) => prec_proj.span(),
        }
    }
}

impl PrecProj {
    pub fn span(&self) -> Span {
        match self {
            PrecProj::Proj(expr_proj) => expr_proj.span(),
            PrecProj::Other(prec_app) => prec_app.span(),
        }
    }
}

impl PrecApp {
    pub fn span(&self) -> Span {
        match self {
            PrecApp::App(expr_app) => expr_app.span(),
            PrecApp::Other(prec_atom) => prec_atom.span(),
        }
    }
}

impl PrecAtom {
    pub fn span(&self) -> Span {
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

impl PatPrecInj {
    pub fn span(&self) -> Span {
        match self {
            PatPrecInj::Refl(x) => x.span(),
            PatPrecInj::Other(x) => x.span(),
        }
    }
}

impl PatPrecAtom {
    pub fn span(&self) -> Span {
        match self {
            PatPrecAtom::Var(s) => s.span(),
            PatPrecAtom::Struct(x) => x.span(),
        }
    }
}

