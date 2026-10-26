use crate::priv_prelude::*;

#[derive(Clone, PartialEq, Hash, Debug)]
pub struct Tag {
    pub kind: TagKind,
}

#[derive(Clone, PartialEq, Hash, Debug)]
pub enum TagKind {
    Literal {
        s: Arc<str>,
    },
    Meta {
        meta: Arc<MetaTag>,
    },
}

#[derive(Clone, PartialEq, Hash, Debug)]
pub enum MetaTag {
    Concat {
        tags: Vec<Tag>,
    },

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

    AddRhsConstraint {
        add_span: Span,
        rhs_span: Span,
    },
    AddLhsTypeIsNat {
        add_span: Span,
        lhs_span: Span,
    },
    AddRhsTypeIsNat {
        add_span: Span,
        rhs_span: Span,
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

/*
impl PartialEq for MetaTag {
    fn eq(&self, other: &MetaTag) -> bool {
        PartialEq::eq(
            &mem::discriminant(self),
            &mem::discriminant(other),
        )
    }
}

impl std::hash::Hash for MetaTag {
    fn hash<H: std::hash::Hasher>(&self, hasher: &mut H) {
        std::hash::Hash::hash(&mem::discriminant(self), hasher)
    }
}
*/

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

impl Tag {
    pub(crate) fn concat(iter: impl IntoIterator<Item = Tag>) -> Tag {
        Tag {
            kind: TagKind::Meta { meta: MetaTag::concat(iter) },
        }
    }
}

impl MetaTag {
    pub(crate) fn concat(iter: impl IntoIterator<Item = Tag>) -> Arc<MetaTag> {
        let mut tags: Vec<Tag> = Vec::new();
        for tag in iter {
            if let TagKind::Meta { meta } = &tag.kind
            && let MetaTag::Concat { tags: tags_1 } = &**meta
            {
                tags.extend(tags_1.iter().cloned());
            } else {
                tags.push(tag);
            }
        }
        Arc::new(MetaTag::Concat { tags })
    }

    pub(crate) fn used_for_universe(&self) -> bool {
        match self {
            MetaTag::Concat { .. } => false,
            MetaTag::QuotedNameConstraint { .. } => false,
            MetaTag::QuotedName { .. } => false,
            MetaTag::QuotedNameHasTypeName { .. } => false,
            MetaTag::VarNameConstraint { .. } => false,
            MetaTag::TypeOfUnresolvedVariable { .. } => true,
            MetaTag::UnresolvedVariable { .. } => false,
            MetaTag::LetStmtVarTmConstraint { .. } => false,
            MetaTag::LetStmtVarTyConstraint { .. } => false,
            MetaTag::LetStmtVarTy { .. } => true,
            MetaTag::LetStmtVarTyIsAType { .. } => false,
            MetaTag::LetStmtVarTm { .. } => false,
            MetaTag::LetStmtVarTmTypeMatchesAnnotatedType { .. } => false,
            MetaTag::LetStmtBody { .. } => false,
            MetaTag::FuncArgNameConstraint { .. } => false,
            MetaTag::FuncArgTy { .. } => true,
            MetaTag::FuncArgTyConstraint { .. } => false,
            MetaTag::FuncArgConstraint { .. } => false,
            MetaTag::FuncResTmConstraint { .. } => false,
            MetaTag::FuncResTyConstraint { .. } => false,
            MetaTag::FuncResTy { .. } => true,
            MetaTag::FuncResTyIsAType { .. } => false,
            MetaTag::EqualEqTm0Constraint { .. } => false,
            MetaTag::EqualEqTm1Constraint { .. } => false,
            MetaTag::EqualEqTm0 { .. } => false,
            MetaTag::EqualEndpointTypesAreTheSame { .. } => false,
            MetaTag::AddRhsConstraint { .. } => false,
            MetaTag::AddLhsTypeIsNat { .. } => false,
            MetaTag::AddRhsTypeIsNat { .. } => false,
            MetaTag::ReflEqTmConstraint { .. } => false,
            MetaTag::InjLhsLhsNameConstraint { .. } => false,
            MetaTag::InjLhsLhsTmConstraint { .. } => false,
            MetaTag::InjLhsRhsType { .. } => true,
            MetaTag::InjLhsImplicitRhsInjectionCount { .. } => false,
            MetaTag::InjLhsImplicitRhsInjections { .. } => false,
            MetaTag::InjLhsImplicitRhsInjection { .. } => false,
            MetaTag::InjLhsImplicitRhsInjectionLhsName { .. } => false,
            MetaTag::InjLhsImplicitRhsInjectionLhsTy { .. } => true,
            MetaTag::InjRhsRhsTmConstraint { .. } => false,
            MetaTag::InjRhsLhsName { .. } => false,
            MetaTag::InjRhsLhsType { .. } => true,
            MetaTag::MatchElimConstraint { .. } => false,
            MetaTag::MatchElimTypeIsNever { .. } => false,
            MetaTag::MatchRhsBranchMotive { .. } => true,
            MetaTag::MatchLhsNameConstraint { .. } => false,
            MetaTag::MatchLhsTy { .. } => true,
            MetaTag::MatchRhsTy { .. } => true,
            MetaTag::MatchElimTypeIsSum { .. } => false,
            MetaTag::MatchLhsBranchMotive { .. } => true,
            MetaTag::MatchLhsInhabConstraint { .. } => false,
            MetaTag::MatchRhsInhabConstraint { .. } => false,
            MetaTag::MatchLhsInhabTyIsExpectedTy { .. } => false,
            MetaTag::MatchRhsInhabTyIsExpectedTy { .. } => false,
            MetaTag::PairHeadTmConstraint { .. } => false,
            MetaTag::PairTailTy { .. } => true,
            MetaTag::PairTailTyIsExpectedTy { .. } => false,
            MetaTag::PairHeadNameConstraint { .. } => false,
            MetaTag::AppElimConstraint { .. } => false,
            MetaTag::AppResTy { .. } => true,
            MetaTag::AppElim { .. } => false,
            MetaTag::AppElimHasExpectedType { .. } => false,
            MetaTag::AppArgNameConstraint { .. } => false,
            MetaTag::AppArgTmConstraint { .. } => false,
            MetaTag::SigmaTailTyConstraint { .. } => false,
            MetaTag::SigmaTailTyIsAType { .. } => false,
            MetaTag::SigmaTailTy { .. } => true,
            MetaTag::SigmaRemainingTailTyConstraint { .. } => false,
            MetaTag::SumLhsTyConstraint { .. } => false,
            MetaTag::SumRhsTyConstraint { .. } => false,
            MetaTag::SumRhsTy { .. } => true,
            MetaTag::SumRhsTyIsAType { .. } => false,
            MetaTag::TypeFieldNameConstraint { .. } => false,
            MetaTag::TypeFieldTyConstraint { .. } => false,
            MetaTag::TypeFieldTy { .. } => true,
            MetaTag::TypeFieldTyIsAType { .. } => false,
            MetaTag::PatternVarNameConstraint { .. } => false,
            MetaTag::ProjHeadBaseConstraint { .. } => false,
            MetaTag::ProjHeadHeadNameConstraint { .. } => false,
            MetaTag::ProjHeadBaseTy { .. } => true,
            MetaTag::ProjHeadBaseTm { .. } => false,
            MetaTag::ProjHeadImplicitTailProjections { .. } => false,
            MetaTag::ProjHeadImplicitTailProjectionCount { .. } => false,
            MetaTag::ProjHeadImplicitTailProjection { .. } => false,
            MetaTag::ProjHeadImplicitTailProjectionInferredHeadName { .. } => false,
            MetaTag::ProjHeadImplicitTailProjectionHeadTy { .. } => true,
            MetaTag::ProjHeadImplicitTailProjectionTailTy { .. } => true,
            MetaTag::ProjHeadImplicitTailProjectionBaseTyEqualsExpectedType { .. } => false,
            MetaTag::ProjHeadHeadTy { .. } => true,
            MetaTag::ProjHeadTailTy { .. } => true,
            MetaTag::ProjHeadHasExpectedType { .. } => false,
            MetaTag::ReflPatEqTy { .. } => true,
            MetaTag::ReflPatEqTm0 { .. } => false,
            MetaTag::ReflPatEqTm1 { .. } => false,
            MetaTag::ReflPatVarTyIsExpectedTy { .. } => false,
            MetaTag::ReflPatMotive { .. } => true,
            MetaTag::ReflPatMotiveEqTm1 { .. } => false,
            MetaTag::ReflPatMotiveElim { .. } => false,
            MetaTag::ReflPatInhabOuterConstraint { .. } => false,
            MetaTag::ReflPatInhabInnerConstraint { .. } => false,
            MetaTag::ReflPatInhab { .. } => false,
            MetaTag::ReflPatInhabHasCorrectType { .. } => false,
            MetaTag::ReflPatVarTm { .. } => false,
            MetaTag::UnitPatVarTyIsUnit { .. } => false,
            MetaTag::PairPatHeadNameConstraint { .. } => false,
            MetaTag::PairPatHeadTy { .. } => true,
            MetaTag::PairPatTailTy { .. } => true,
            MetaTag::PairPatVarTyIsExpectedTy { .. } => false,
        }
    }
}

