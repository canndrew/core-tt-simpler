use crate::priv_prelude::*;

#[derive(Debug)]
pub struct SolveError {
    ctx_names: Vec<Name>,
    ctx: Vec<Ty>,
    kind: SolveErrorKind,
}

#[derive(Debug)]
pub enum SolveErrorKind {
    Uninhabited {
        tag: Tag,
    },
    Ambiguous {
        ty: Ty,
    },
    ConstrainsCtx {
        constraints: Constraints,
    },
}

impl fmt::Display for SolveError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let SolveError { ctx_names, ctx, kind } = self;
        match kind {
            SolveErrorKind::Uninhabited { tag } => {
                writeln!(f, "uninhabited at: {:#?}", tag)?;
                Ok(())
            },
            SolveErrorKind::Ambiguous { ty } => {
                let mut ctx_names = ctx_names.clone();
                let mut ctx = ctx.clone();
                writeln!(
                    f, "failed to solve constraint: {}",
                    ty.clone().pprint(&mut ctx_names, &mut ctx, ()),
                )
            },
            SolveErrorKind::ConstrainsCtx { constraints } => {
                let (index, tm) = constraints.clone().into_iter().next().unwrap();
                let var_name = ctx_names[index].clone();
                let var_ty = ctx[index].clone();
                let mut ctx_names = ctx_names.clone();
                let mut ctx = ctx.clone();
                writeln!(
                    f, "inhabitation requires var {} equals {}",
                    var_name.pprint(&mut ctx_names, &mut ctx, ()),
                    tm.pprint(&mut ctx_names, &mut ctx, var_ty),
                )
            },
        }
    }
}

impl<T> Checked<T> {
    pub fn solve(
        self,
        ctx_names: Vec<Name>,
        ctx: Vec<Ty>,
    ) -> Result<T, SolveError>
    where
        T: Contextual,
        T: Bindable,
    {
        assert_eq!(ctx_names.len(), ctx.len());
        let mut ctx_names = ctx_names;
        let mut ctx = ctx;
        let ctx_len = ctx.len();
        let (constraint_ty, scope) = self.into_constraint_ty_and_scope();
        let result = {
            /*
            let ctx_names_opt = if cfg!(debug_assertions) {
                Some(&mut ctx_names)
            } else {
                None
            };
            let mut cache = SimplifyCache::new();
            constraint_ty.simplify(ctx_names_opt, &mut ctx, ctx_len, &mut cache)
            */


            // debugging, but might just want to keep this anyway...
            let (constraint_ty, first_iso) = constraint_ty.simplify_trivial();
            let result = {
                let ctx_names_opt = if cfg!(debug_assertions) {
                    Some(&mut ctx_names)
                } else {
                    None
                };
                let mut cache = SimplifyCache::new();
                let case_splits = 2 + constraint_ty.count_case_splits();
                constraint_ty.simplify(ctx_names_opt, &mut ctx, ctx_len, &mut cache, case_splits)
            };
            result
            .map(|simplification| {
                match simplification {
                    Simplification::Unique { unique_tm } => {
                        let unique_tm = first_iso.rev.bind(unique_tm);
                        Simplification::Unique { unique_tm }
                    },
                    Simplification::Undecided(Undecided {
                        progress_opt, constraints, eliminated, hit_case_split_limit,
                    }) => {
                        let progress_opt = Some(match progress_opt {
                            None => Progress { new_ty: constraint_ty, iso: first_iso },
                            Some(Progress { new_ty, iso }) => {
                                let iso = Iso::transitivity(first_iso, iso);
                                Progress { new_ty, iso }
                            },
                        });
                        Simplification::Undecided(Undecided {
                            progress_opt, constraints, eliminated, hit_case_split_limit,
                        })
                    },
                }
            })
        };
        debug_assert_eq!(ctx.len(), ctx_len);

        match result {
            Err(Uninhabited { tag }) => {
                let kind = SolveErrorKind::Uninhabited { tag };
                Err(SolveError { ctx_names, ctx, kind })
            },
            Ok(Simplification::Undecided(Undecided {
                progress_opt, constraints, eliminated: _, hit_case_split_limit: _,
            })) => {
                if !constraints.is_empty() {
                    let kind = SolveErrorKind::ConstrainsCtx { constraints };
                    return Err(SolveError { ctx_names, ctx, kind });
                }
                let ty = match progress_opt {
                    Some(Progress { new_ty, .. }) => new_ty,
                    None => constraint_ty,
                };
                let ty = ty.deep_nf().into_ty();
                let kind = SolveErrorKind::Ambiguous { ty };
                Err(SolveError { ctx_names, ctx, kind })
            },
            Ok(Simplification::Unique { unique_tm }) => {
                let body = scope.bind(unique_tm);
                Ok(body)
            },
        }
    }
}

trait CountCaseSplits {
    fn count_case_splits(&self) -> u32;
}

impl<T> CountCaseSplits for Weaken<T>
where
    T: CountCaseSplits,
{
    fn count_case_splits(&self) -> u32 {
        self.weak().count_case_splits()
    }
}

impl<T> CountCaseSplits for Arc<T>
where
    T: CountCaseSplits,
{
    fn count_case_splits(&self) -> u32 {
        (**self).count_case_splits()
    }
}

impl<T> CountCaseSplits for Scope<T>
where
    T: CountCaseSplits,
{
    fn count_case_splits(&self) -> u32 {
        self.inner_ref().count_case_splits()
    }
}

impl<T> CountCaseSplits for OrLazy<T>
where
    T: CountCaseSplits + AsTmKind + Clone,
{
    fn count_case_splits(&self) -> u32 {
        self.clone().reduced().count_case_splits()
    }
}

impl CountCaseSplits for TyKind {
    fn count_case_splits(&self) -> u32 {
        match self {
            TyKind::Form { form } => form.count_case_splits(),
            TyKind::Stuck { stuck } => stuck.count_case_splits(),
        }
    }
}

impl CountCaseSplits for TmKind {
    fn count_case_splits(&self) -> u32 {
        match self {
            TmKind::Intro { intro } => intro.count_case_splits(),
            //TmKind::Proof => 0,
            TmKind::Proof => unreachable!(),
            TmKind::Stuck { stuck } => stuck.count_case_splits(),
        }
    }
}

impl CountCaseSplits for FormKind {
    fn count_case_splits(&self) -> u32 {
        match self {
            FormKind::Never => 0,

            | FormKind::Name
            | FormKind::Universe
            | FormKind::Nat
            | FormKind::Unit
            => 1,

            FormKind::Sum { lhs_name: _, lhs_ty, rhs_ty } => {
                lhs_ty.count_case_splits() + rhs_ty.count_case_splits()
            },

            FormKind::Sigma { head_name: _, head_ty, tail_ty } => {
                cmp::max(head_ty.count_case_splits(), tail_ty.count_case_splits())
            },

            FormKind::Pi { arg_name: _, arg_ty, res_ty } => {
                cmp::max(arg_ty.count_case_splits(), res_ty.count_case_splits())
            },
        }
    }
}

impl CountCaseSplits for IntroKind {
    fn count_case_splits(&self) -> u32 {
        match self {
            IntroKind::Form { form } => form.count_case_splits(),
            _ => unreachable!(),
        }
    }
}

impl CountCaseSplits for StuckKind {
    fn count_case_splits(&self) -> u32 {
        match &**self.neutral_ref() {
            | NeutralKind::Var { .. }
            | NeutralKind::Explode { .. }
            | NeutralKind::ProjHead { .. }
            | NeutralKind::ProjTail { .. }
            | NeutralKind::App { .. }
            | NeutralKind::ObsEqual { .. }
            | NeutralKind::Cast { .. }
            => 1,

            | NeutralKind::Bind { .. }
            | NeutralKind::Add { .. }
            => unreachable!(),

            NeutralKind::Fold { elim: _, motive: _, zero_inhab, succ_inhab } => {
                cmp::max(
                    zero_inhab.count_case_splits(),
                    succ_inhab.count_case_splits(),
                )
            },

            NeutralKind::Case { lhs_name: _, elim: _, motive: _, lhs_inhab, rhs_inhab } => {
                cmp::max(
                    lhs_inhab.count_case_splits(),
                    rhs_inhab.count_case_splits(),
                )
            },
        }
    }
}
