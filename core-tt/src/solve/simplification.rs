use crate::priv_prelude::*;

pub struct Uninhabited {
    pub tag: Tag,
}

#[derive(Clone, Contextual)]
pub struct Progress {
    pub new_ty: Ty,
    pub iso: Iso,
}

#[derive(Clone)]
pub struct Undecided {
    pub progress_opt: Option<Progress>,
    pub constraints: Constraints,
    pub eliminated: Usages,
    pub hit_case_split_limit: bool,
}

pub struct UnscopedUndecided {
    pub progress_opt: Option<Scope<Progress>>,
    pub constraints: Constraints,
    pub eliminated: Usages,
    pub hit_case_split_limit: bool,
    pub var_constraint_opt: Option<Tm>,
    pub var_eliminated: bool,
}

#[derive(Clone)]
pub enum Simplification {
    Unique {
        unique_tm: Tm,
    },
    Undecided(Undecided),
}

impl Uninhabited {
    pub fn new() -> Uninhabited {
        Uninhabited {
            tag: Tag {
                kind: TagKind::Meta {
                    meta: MetaTag::concat([]),
                },
            },
        }
    }
}

impl Progress {
    pub fn id(orig_ty: Ty) -> Progress {
        Progress {
            new_ty: orig_ty,
            iso: Iso::refl(),
        }
    }

    pub fn simplify_more(
        self,
        ctx_names_opt: Option<&mut Vec<Name>>,
        ctx: &mut Vec<Ty>,
        preserved_constraint_depth: usize,
        cache: &mut SimplifyCache,
        remaining_case_splits: u32,
    ) -> Result<Simplification, Uninhabited> {
        let simplification = self.new_ty.clone().simplify(
            ctx_names_opt, ctx, preserved_constraint_depth, cache, remaining_case_splits,
        )?;
        Ok(simplification.precompose_progress(self))
    }
}

impl Bindable for Progress {
    fn capture_subst(self, subst: Subst) -> Progress {
        let Progress { new_ty, iso } = self;
        let new_ty = new_ty.capture_subst(subst.clone());
        let iso = iso.capture_subst(subst);
        Progress { new_ty, iso }
    }
}

impl Undecided {
    pub fn id() -> Undecided {
        Undecided {
            progress_opt: None,
            constraints: Constraints::new(),
            eliminated: Usages::empty(),
            hit_case_split_limit: false,
        }
    }

    pub fn from_progress(progress: Progress) -> Undecided {
        Undecided {
            progress_opt: Some(progress),
            constraints: Constraints::new(),
            eliminated: Usages::empty(),
            hit_case_split_limit: false,
        }
    }

    pub fn from_constraint(var_index: usize, unique_tm: Tm) -> Undecided {
        Undecided {
            progress_opt: None,
            constraints: Constraints::single(var_index, unique_tm),
            eliminated: Usages::empty(),
            hit_case_split_limit: false,
        }
    }

    pub fn stuck(stuck: StuckKind) -> Undecided {
        let mut eliminated = Usages::empty();
        stuck.collect_stuck_vars(&mut eliminated);
        Undecided {
            progress_opt: None,
            constraints: Constraints::new(),
            eliminated,
            hit_case_split_limit: false,
        }
    }

    pub fn hit_case_split_limit() -> Undecided {
        Undecided {
            progress_opt: None,
            constraints: Constraints::new(),
            eliminated: Usages::empty(),
            hit_case_split_limit: true,
        }
    }

    pub fn new_ty<'a>(&'a self, orig_ty: &'a Ty) -> &'a Ty {
        self.progress_opt.as_ref().map(|progress| &progress.new_ty).unwrap_or(orig_ty)
    }

    pub fn with_additional_constraints(
        mut self,
        constraints: Constraints,
    ) -> Result<Undecided, Uninhabited> {
        self.constraints = Constraints::union(self.constraints, constraints)?;
        Ok(self)
    }

    pub fn consider_equality(self, orig_ty: &Ty) -> Result<Undecided, Uninhabited> {
        let ty = self.new_ty(orig_ty);
        if let Some((_, eq_tm_0, eq_tm_1)) = ty.clone().as_equal() {
            return self.with_additional_constraints(
                Constraints::from_equality(eq_tm_0, eq_tm_1),
            );
        }
        Ok(self)
    }
}

impl Simplification {
    pub fn id() -> Simplification {
        Simplification::Undecided(Undecided::id())
    }

    pub fn hit_case_split_limit() -> Simplification {
        Simplification::Undecided(Undecided::hit_case_split_limit())
    }

    pub fn precompose_progress(self, progress: Progress) -> Simplification {
        let Progress { new_ty, iso } = progress;
        match self {
            Simplification::Unique { unique_tm } => {
                let unique_tm = iso.rev.bind(unique_tm);
                Simplification::Unique { unique_tm }
            },
            Simplification::Undecided(Undecided {
                progress_opt, constraints, eliminated, hit_case_split_limit,
            }) => {
                let progress_opt = Some(match progress_opt {
                    None => Progress { new_ty, iso },
                    Some(Progress { new_ty, iso: next_iso }) => {
                        let iso = Iso::transitivity(iso, next_iso);
                        Progress { new_ty, iso }
                    },
                });
                Simplification::Undecided(Undecided {
                    progress_opt, constraints, eliminated, hit_case_split_limit,
                })
            },
        }
    }

    pub fn into_undecided(self, orig_ty: Ty) -> Undecided {
        match self {
            Simplification::Undecided(undecided) => undecided,
            Simplification::Unique { unique_tm } => {
                let progress_opt = match orig_ty.as_unit() {
                    Some(()) => None,
                    None => Some(Progress {
                        new_ty: Ty::unit(),
                        iso: Iso::uniquely_inhabited_to_unit(unique_tm),
                    }),
                };
                let constraints = Constraints::new();
                let eliminated = Usages::empty();
                let hit_case_split_limit = false;
                Undecided { progress_opt, constraints, eliminated, hit_case_split_limit }
            },
        }
    }

    pub fn solved(unique_tm: Tm) -> Simplification {
        Simplification::Unique { unique_tm }
    }

    pub fn from_progress(progress: Progress) -> Simplification {
        Simplification::Undecided(Undecided::from_progress(progress))
    }

    pub fn from_constraint(var_index: usize, unique_tm: Tm) -> Simplification {
        Simplification::Undecided(Undecided::from_constraint(var_index, unique_tm))
    }

    pub fn stuck(stuck: StuckKind) -> Simplification {
        Simplification::Undecided(Undecided::stuck(stuck))
    }

    pub fn consider_equality(self, orig_ty: &Ty) -> Result<Simplification, Uninhabited> {
        match self {
            Simplification::Unique { unique_tm } => {
                Ok(Simplification::Unique { unique_tm })
            },
            Simplification::Undecided(undecided) => {
                let undecided = undecided.consider_equality(orig_ty)?;
                Ok(Simplification::Undecided(undecided))
            },
        }
    }
}

impl Scope<Progress> {
    pub fn lift_progress(self) -> (Scope<Ty>, Scope<Iso>) {
        let ctx_len = self.ctx_len();
        self.map_multi(ctx_len, |_, progress| {
            let Progress { new_ty, iso } = progress;
            (new_ty, iso)
        })
    }
}

