use crate::priv_prelude::*;

pub type Name = Weaken<OrLazy<NameKind>>;
pub type ValName = Weaken<NameKind>;

#[derive(Clone, Debug, Contextual)]
pub enum NameKind {
    Tag {
        #[contextual(ignore)]
        tag: Tag,
    },
    Stuck {
        stuck: StuckKind,
    },
    /*
    Lazy {
        lazy: Arc<LazyData>,
    },
    */
}

impl Name {
    pub fn into_tm(self) -> Tm {
        self.map(|lazy| lazy.map(NameKind::into_tm_kind))
    }

    pub fn tag(tag: Tag) -> Name {
        Weaken::new(OrLazy::Reduced(NameKind::Tag { tag }))
    }

    pub fn as_tag(self) -> Option<Tag> {
        match self.reduced().weak() {
            NameKind::Tag { tag } => Some(tag.clone()),
            NameKind::Stuck { .. } => None,
        }
    }
}

impl NameKind {
    pub fn into_tm_kind(self) -> TmKind {
        match self {
            NameKind::Tag { tag } => {
                let intro = Arc::new(IntroKind::Tag { tag });
                TmKind::Intro { intro }
            },
            NameKind::Stuck { stuck } => {
                TmKind::Stuck { stuck }
            },
        }
    }
}

impl ValName {
    pub fn into_name(self) -> Name {
        self.map(|name_kind| OrLazy::Reduced(name_kind))
    }
}

impl DeepNf for NameKind {
    type Output = ValName;

    fn deep_nf(self) -> ValName {
        match self {
            NameKind::Tag { tag } => {
                Weaken::new(NameKind::Tag { tag })
            },
            NameKind::Stuck { stuck } => {
                stuck.deep_nf().map(|stuck| NameKind::Stuck { stuck })
            },
        }
    }
}

impl Unify for NameKind {
    fn unify(
        name_kind_0: NameKind,
        name_kind_1: NameKind,
    ) -> Option<NameKind> {
        match (name_kind_0, name_kind_1) {
            (NameKind::Tag { tag: tag_0 }, NameKind::Tag { tag: tag_1 }) => {
                let tag = as_equal(tag_0, &tag_1)?;
                Some(NameKind::Tag { tag })
            },

            (
                NameKind::Stuck { stuck: stuck_0 },
                NameKind::Stuck { stuck: stuck_1 },
            ) => {
                let stuck = Unify::unify(stuck_0, stuck_1)?;
                Some(NameKind::Stuck { stuck })
            },

            _ => None,
        }
    }
}

impl Substitutable for NameKind {
    type Output = ValName;

    fn subst(self, subst: &mut Subst) -> ValName {
        match self {
            NameKind::Tag { .. } => Weaken::new(self),
            NameKind::Stuck { stuck } => {
                stuck.subst(subst).map(|kind| kind.into_name_kind())
            },
        }
    }

    fn into_output(self) -> ValName {
        Weaken::new(self)
    }

    fn try_strengthen_index(self, var_index: usize) -> Option<NameKind> {
        match self {
            NameKind::Tag { .. } => Some(self),
            NameKind::Stuck { stuck } => {
                let stuck = stuck.try_strengthen_index(var_index)?;
                Some(NameKind::Stuck { stuck })
            },
        }
    }
}

