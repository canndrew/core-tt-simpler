use crate::priv_prelude::*;

#[derive(Clone, Debug, PartialEq)]
pub struct Span {
}

pub struct UntypedScope<T> {
    #[expect(unused)]
    pub(crate) body: T,
}

pub struct UntypedTm {
    pub(crate) span: Span,
    pub(crate) kind: Box<UntypedTmKind>,
}

pub struct UntypedTy {
    #[expect(unused)]
    pub(crate) span: Span,
    #[expect(unused)]
    pub(crate) kind: Box<UntypedTmKind>,
}

pub struct UntypedName {
    #[expect(unused)]
    pub(crate) span: Span,
    #[expect(unused)]
    pub(crate) kind: Box<UntypedTmKind>,
}

pub enum UntypedTmKind {
    Hole,
    Var {
        name: UntypedName,
    },
    Bind {
        var_name: UntypedName,
        var_tm: UntypedTm,
        body: UntypedScope<UntypedTm>,
    },

    Name,
    Tag {
        tag: Tag,
    },
    TagsApart {
        tag_0: Tag,
        tag_1: Tag,
        elim: UntypedTm,
    },

    Universe,

    NatTy,
    Constant {
        ubig: Ubig,
    },
    Succs {
        succ_count_m1: Ubig,
        pred_tm: UntypedTm,
    },
    Fold {
        elim: UntypedTm,
        motive: UntypedScope<UntypedTy>,
        zero_inhab: UntypedTm,
        succ_inhab: UntypedScope<UntypedScope<UntypedTm>>,
    },

    Equal {
        eq_tm_0: UntypedTm,
        eq_tm_1: UntypedTm,
    },
    Refl {
        eq_tm: UntypedTm,
    },
    Cong {
        elim: UntypedTm,
        motive: UntypedScope<UntypedScope<UntypedTy>>,
        inhab: UntypedTm,
    },

    Never,
    Explode {
        elim: UntypedTm,
        motive: UntypedScope<UntypedTy>,
    },

    UnitTy,
    UnitTm,

    Sum {
        lhs_name: UntypedName,
        lhs_ty: UntypedTy,
        rhs_ty: UntypedTy,
    },
    InjLhs {
        lhs_name: UntypedName,
        rhs_ty: UntypedTy,
        lhs_tm: UntypedTm,
    },
    InjRhs {
        lhs_name: UntypedName,
        lhs_ty: UntypedTy,
        rhs_tm: UntypedTm,
    },
    Case {
        elim: UntypedTm,
        motive: UntypedScope<UntypedTy>,
        lhs_inhab: UntypedScope<UntypedTm>,
        rhs_inhab: UntypedScope<UntypedTm>,
    },

    Sigma {
        head_name: UntypedName,
        head_ty: UntypedTy,
        tail_ty: UntypedScope<UntypedTy>,
    },
    Pair {
        head_name: UntypedName,
        tail_ty: UntypedScope<UntypedTy>,
        head_tm: UntypedTm,
        tail_tm: UntypedTm,
    },
    ProjHead {
        elim: UntypedTm,
    },
    ProjTail {
        elim: UntypedTm,
    },

    Pi {
        arg_name: UntypedName,
        arg_ty: UntypedTy,
        res_ty: UntypedScope<UntypedTy>,
    },
    Func {
        arg_name: UntypedName,
        res_tm: UntypedScope<UntypedTm>,
    },
    App {
        elim: UntypedTm,
        arg_tm: UntypedTm,
    },
}

