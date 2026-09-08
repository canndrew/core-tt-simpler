use crate::priv_prelude::*;

pub type Name = Weaken<NameKind>;

#[derive(Clone, Debug, Contextual)]
pub enum NameKind {
    Tag {
        #[contextual(ignore)]
        tag: Tag,
    },
    Neutral {
        neutral: Arc<NeutralData>,
    },
}

impl Name {
    pub fn into_tm(self) -> Tm {
        self.map(NameKind::into_tm_kind)
    }

    pub fn tag(tag: Tag) -> Name {
        Weaken::new(NameKind::Tag { tag })
    }

    pub fn as_tag(&self) -> Option<&Tag> {
        match self.weak() {
            NameKind::Tag { tag } => Some(tag),
            NameKind::Neutral { .. } => None,
        }
    }

    pub fn deep_nf(self) -> Name {
        self.map_out_unfiltered(|name_kind| {
            name_kind.deep_nf()
        })
    }
}

impl NameKind {
    pub fn into_tm_kind(self) -> TmKind {
        match self {
            NameKind::Tag { tag } => {
                let intro = Arc::new(IntroKind::Tag { tag });
                TmKind::Intro { intro }
            },
            NameKind::Neutral { neutral } => {
                TmKind::Neutral { neutral }
            },
        }
    }

    pub fn deep_nf(self) -> Name {
        match self {
            NameKind::Tag { tag } => {
                Weaken::new(NameKind::Tag { tag })
            },
            NameKind::Neutral { neutral } => {
                Arc::unwrap_or_clone(neutral).deep_nf().into_name()
            },
        }
    }
}

impl Bindable for Name {
    fn capture_subst(self, subst: Subst) -> Name {
        let tm = self.into_tm();
        let tm = tm.capture_subst(subst);
        tm.into_name()
    }
}

impl Unify for NameKind {
    type Meta = ();

    fn unify(
        ctx_tys: &mut Vec<Ty>,
        (): (),
        name_kind_0: NameKind,
        name_kind_1: NameKind,
    ) -> Option<NameKind> {
        match (name_kind_0, name_kind_1) {
            (NameKind::Tag { tag: tag_0 }, NameKind::Tag { tag: tag_1 }) => {
                let tag = as_equal(tag_0, &tag_1)?;
                Some(NameKind::Tag { tag })
            },

            (NameKind::Tag { tag: tag_0 }, NameKind::Neutral { neutral }) => {
                let intro_1 = neutral.try_reduce_to_intro()?.into_inner();
                let intro_1 = Arc::unwrap_or_clone(intro_1);
                let IntroKind::Tag { tag: tag_1 } = intro_1 else {
                    unreachable!();
                };
                let tag = as_equal(tag_0, &tag_1)?;
                Some(NameKind::Tag { tag })
            },

            (NameKind::Neutral { neutral }, NameKind::Tag { tag: tag_1 }) => {
                let intro_0 = neutral.try_reduce_to_intro()?.into_inner();
                let intro_0 = Arc::unwrap_or_clone(intro_0);
                let IntroKind::Tag { tag: tag_0 } = intro_0 else {
                    unreachable!();
                };
                let tag = as_equal(tag_0, &tag_1)?;
                Some(NameKind::Tag { tag })
            },
            
            (NameKind::Neutral { neutral: neutral_0 }, NameKind::Neutral { neutral: neutral_1 }) => {
                if Arc::ptr_eq(&neutral_0, &neutral_1) {
                    return Some(NameKind::Neutral { neutral: neutral_0 });
                }
                match (neutral_0.try_reduce(), neutral_1.try_reduce()) {
                    (None, None) => {
                        let neutral_0 = Arc::unwrap_or_clone(neutral_0);
                        let neutral_1 = Arc::unwrap_or_clone(neutral_1);
                        let kind = Unify::unify(ctx_tys, (), neutral_0.kind, neutral_1.kind)?;
                        let neutral = NeutralData::new_arc(kind);
                        Some(NameKind::Neutral { neutral })
                    },
                    (None, Some(tm_1)) => {
                        match tm_1.into_inner() {
                            TmKind::Intro { .. } => None,
                            TmKind::Neutral { neutral: neutral_1 } => {
                                let neutral = NeutralData::unify_without_cached_reduction(
                                    ctx_tys,
                                    neutral_0,
                                    neutral_1,
                                )?;
                                Some(NameKind::Neutral { neutral })
                            },
                        }
                    },
                    (Some(tm_0), None) => {
                        match tm_0.into_inner() {
                            TmKind::Intro { .. } => None,
                            TmKind::Neutral { neutral: neutral_0 } => {
                                let neutral = NeutralData::unify_without_cached_reduction(
                                    ctx_tys,
                                    neutral_0,
                                    neutral_1,
                                )?;
                                Some(NameKind::Neutral { neutral })
                            },
                        }
                    },
                    (Some(tm_0), Some(tm_1)) => {
                        let tm = Unify::unify(ctx_tys, Ty::name(), tm_0.clone(), tm_1.clone())?;
                        Some(tm.into_inner().into_name_kind())
                    },
                }
            },
        }
    }
}

impl Substitutable for Name {
    type Output = Name;

    fn subst(self, subst: &mut Subst) -> Name {
        if self.ctx_len() <= subst.subst_index() {
            return self;
        }
        self.into_inner().subst(subst)
    }

    fn into_output(self) -> Name {
        self
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<Name> {
        Some(self.do_try_strengthen_index(var_index)?.flatten())
    }
}

impl Substitutable for NameKind {
    type Output = Name;

    fn subst(self, subst: &mut Subst) -> Name {
        match self {
            NameKind::Tag { .. } => Weaken::new(self),
            NameKind::Neutral { neutral } => {
                neutral.subst(subst).into_name()
            },
        }
    }

    fn into_output(self) -> Name {
        Weaken::new(self)
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<Name> {
        match self { 
            NameKind::Tag { .. } => Some(Weaken::new(self)),
            NameKind::Neutral { neutral } => {
                Some(neutral.try_strengthen_index(var_index)?.into_name())
            },
        }
    }
}

