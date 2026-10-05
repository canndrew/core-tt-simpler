use crate::priv_prelude::*;

#[derive(Clone, PartialEq, Debug)]
pub struct Tag {
    pub kind: TagKind,
}

#[derive(Clone, PartialEq, Debug)]
pub enum TagKind {
    Literal {
        s: Arc<str>,
    },
    Meta {
        meta: Arc<MetaTag>,
    },
}

#[derive(Clone, PartialEq, Debug, Hash)]
pub enum MetaTag {
    QuotedNameConstraint {
        span: Span,
    },
    QuotedName {
        span: Span,
    },
    QuotedNameHasTypeName {
        span: Span,
    },

    VarNameConstraint {
        span: Span,
    },
    TypeOfUnresolvedVariable {
        span: Span,
    },
    UnresolvedVariable {
        span: Span,
    },

    LetStmtVarTmConstraint {
        var_tm_span: Span,
    },
    LetStmtVarTyConstraint {
        var_ty_span: Span,
    },
    LetStmtVarTy {
        var_ty_span: Span,
    },
    LetStmtVarTyIsAType {
        var_ty_span: Span,
    },
    LetStmtVarTm {
        var_tm_span: Span,
    },
    LetStmtVarTmTypeMatchesAnnotatedType {
        var_tm_span: Span,
        var_ty_span: Span,
    },
    LetStmtBody {
        body_span: Span,
    },

    FuncArgNameConstraint {
        arg_name_span: Span,
    },
    FuncArgTy {
        arg_name_span: Span,
    },
    FuncArgTyConstraint {
        span: Span,
    },
    FuncArgConstraint {
        func_arg_span: Span,
    },
    FuncResTmConstraint {
        remaining_args_span_opt: Option<Span>,
        res_tm_span: Span,
    },
    FuncResTyConstraint {
        remaining_args_span_opt: Option<Span>,
        res_ty_span: Span,
    },
    FuncResTy {
        res_ty_span: Span,
    },
    FuncResTyIsAType {
        res_ty_span: Span,
    },

    EqualEqTm0Constraint {
        equal_span: Span,
        eq_tm_0_span: Span,
    },
    EqualEqTm1Constraint {
        equal_span: Span,
        eq_tm_1_span: Span,
    },
    EqualEqTm0 {
        eq_tm_0_span: Span,
    },
    EqualEndpointTypesAreTheSame {
        equal_span: Span,
        eq_tm_0_span: Span,
        eq_tm_1_span: Span,
    },

    ReflEqTmConstraint {
        refl_tm_span: Span,
        eq_tm_span: Span,
    },

    InjLhsLhsNameConstraint {
        inj_span: Span,
        lhs_name_span: Span,
    },
    InjLhsLhsTmConstraint {
        inj_span: Span,
        lhs_tm_span: Span,
    },
    InjLhsRhsType {
        inj_span: Span,
        lhs_name_span: Span,
        lhs_tm_span: Span,
    },
    InjLhsImplicitRhsInjectionCount {
        inj_span: Span,
    },
    InjLhsImplicitRhsInjections {
        inj_span: Span,
    },
    InjLhsImplicitRhsInjection {
        inj_span: Span,
    },
    InjLhsImplicitRhsInjectionLhsName {
        inj_span: Span,
    },
    InjLhsImplicitRhsInjectionLhsTy {
        inj_span: Span,
    },

    InjRhsRhsTmConstraint {
        inj_span: Span,
        rhs_tm_span: Span,
    },
    InjRhsLhsName {
        inj_span: Span,
        rhs_tm_span: Span,
    },
    InjRhsLhsType {
        inj_span: Span,
        rhs_tm_span: Span,
    },

    MatchElimConstraint {
        elim_span: Span,
    },
    MatchElimTypeIsNever {
        branches_span: Span,
    },
    MatchRhsBranchMotive {
        branches_span: Span,
    },
    MatchLhsNameConstraint {
        branch_span: Span,
        branches_span: Span,
    },
    MatchLhsTy {
        branch_span: Span,
        branches_span: Span,
    },
    MatchRhsTy {
        branch_span: Span,
        branches_span: Span,
    },
    MatchElimTypeIsSum {
        branch_span: Span,
        branches_span: Span,
    },
    MatchLhsBranchMotive {
        branch_span: Span,
        branches_span: Span,
    },
    MatchLhsInhabConstraint {
        branch_span: Span,
        branches_span: Span,
    },
    MatchRhsInhabConstraint {
        branches_span: Span,
    },
    MatchLhsInhabTyIsExpectedTy {
        branch_span: Span,
        branches_span: Span,
    },
    MatchRhsInhabTyIsExpectedTy {
        branches_span: Span,
    },

    PairHeadTmConstraint {
        head_span: Span,
    },
    PairTailTy {
        head_span: Span,
    },
    PairTailTyIsExpectedTy {
        head_span: Span,
    },
    PairHeadNameConstraint {
        head_name_span: Span,
    },

    AppElimConstraint {
        app_span: Span,
        elim_span: Span,
    },
    AppResTy {
        app_span: Span,
        arg_span: Span,
    },
    AppElim {
        elim_span: Span,
        arg_tm_span: Span,
    },
    AppElimHasExpectedType {
        elim_span: Span,
        arg_tm_span: Span,
    },
    AppArgNameConstraint {
        arg_name_span: Span,
    },
    AppArgTmConstraint {
        arg_span: Span,
    },

    SigmaTailTyConstraint {
        tail_ty_span: Span,
    },
    SigmaTailTyIsAType {
        tail_ty_span: Span,
    },
    SigmaTailTy {
        tail_ty_span: Span,
    },
    SigmaRemainingTailTyConstraint {
        head_span: Span,
    },

    SumLhsTyConstraint {
        lhs_ty_span: Span,
    },
    SumRhsTyConstraint {
        rhs_ty_span: Span,
    },
    SumRhsTy {
        rhs_ty_span: Span,
    },
    SumRhsTyIsAType {
        rhs_ty_span: Span,
    },

    TypeFieldNameConstraint {
        field_span: Span,
        name_span: Span,
    },
    TypeFieldTyConstraint {
        field_span: Span,
        ty_span: Span,
    },
    TypeFieldTy {
        ty_span: Span,
    },
    TypeFieldTyIsAType {
        ty_span: Span,
    },

    PatternVarNameConstraint {
        name_span: Span,
    },

    ProjHeadBaseConstraint {
        proj_span: Span,
        base_tm_span: Span,
    },
    ProjHeadHeadNameConstraint {
        proj_span: Span,
        head_name_span: Span,
    },
    ProjHeadBaseTy {
        proj_span: Span,
    },
    ProjHeadBaseTm {
        proj_span: Span,
    },
    ProjHeadImplicitTailProjections {
        proj_span: Span,
    },
    ProjHeadImplicitTailProjectionCount {
        proj_span: Span,
    },
    ProjHeadImplicitTailProjection {
        proj_span: Span,
    },
    ProjHeadImplicitTailProjectionInferredHeadName {
        proj_span: Span,
    },
    ProjHeadImplicitTailProjectionHeadTy {
        proj_span: Span,
    },
    ProjHeadImplicitTailProjectionTailTy {
        proj_span: Span,
    },
    ProjHeadImplicitTailProjectionBaseTyEqualsExpectedType {
        proj_span: Span,
    },
    ProjHeadHeadTy {
        proj_span: Span,
    },
    ProjHeadTailTy {
        proj_span: Span,
    },
    ProjHeadHasExpectedType {
        proj_span: Span,
    },

    ReflPatEqTy {
        refl_pat_span: Span,
    },
    ReflPatEqTm0 {
        refl_pat_span: Span,
    },
    ReflPatEqTm1 {
        refl_pat_span: Span,
    },
    ReflPatVarTyIsExpectedTy {
        refl_pat_span: Span,
    },
    ReflPatMotive {
        refl_pat_span: Span,
    },
    ReflPatMotiveEqTm1 {
        refl_pat_span: Span,
        eq_pat_span: Span,
    },
    ReflPatMotiveElim {
        refl_pat_span: Span,
        eq_pat_span: Span,
    },
    ReflPatInhabOuterConstraint {
        refl_pat_span: Span,
    },
    ReflPatInhabInnerConstraint {
        refl_pat_span: Span,
    },
    ReflPatInhab {
        refl_pat_span: Span,
    },
    ReflPatInhabHasCorrectType {
        refl_pat_span: Span,
    },
    ReflPatVarTm {
        refl_pat_span: Span,
    },

    UnitPatVarTyIsUnit {
        pat_span: Span,
    },
    PairPatHeadNameConstraint {
        head_name_span: Span,
    },
    PairPatHeadTy {
        field_span: Span,
    },
    PairPatTailTy {
        field_span: Span,
    },
    PairPatVarTyIsExpectedTy {
        field_span: Span,
    },
}

impl From<&str> for Tag {
    fn from(s: &str) -> Tag {
        lazy_static! {
            static ref TAG_LITERAL_INTERNER: RwLock<HashMap<Arc<str>, ()>> = {
                RwLock::new(HashMap::new())
            };
        }

        let s: Arc<str> = {
            let interner = TAG_LITERAL_INTERNER.read().unwrap();
            match interner.get_key_value(s) {
                Some((s, ())) => s.clone(),
                None => {
                    drop(interner);
                    let mut interner = TAG_LITERAL_INTERNER.write().unwrap();
                    let entry = match interner.entry(Arc::from(s)) {
                        hash_map::Entry::Occupied(entry) => entry,
                        hash_map::Entry::Vacant(entry) => entry.insert_entry(()),
                    };
                    entry.key().clone()
                },
            }
        };

        Tag::from(s)
    }
}

impl From<Arc<str>> for Tag {
    fn from(s: Arc<str>) -> Tag {
        Tag {
            kind: TagKind::Literal { s },
        }
    }
}

impl From<MetaTag> for Tag {
    fn from(meta: MetaTag) -> Tag {
        Tag {
            kind: TagKind::Meta { meta: Arc::new(meta) }
        }
    }
}

impl From<&str> for Name {
    fn from(s: &str) -> Name {
        Name::from(Tag::from(s))
    }
}

impl From<Arc<str>> for Name {
    fn from(s: Arc<str>) -> Name {
        Name::tag(Tag::from(s))
    }
}

impl From<MetaTag> for Name {
    fn from(meta: MetaTag) -> Name {
        Name::tag(Tag::from(meta))
    }
}

impl From<Tag> for Name {
    fn from(tag: Tag) -> Name {
        Name::tag(tag)
    }
}

