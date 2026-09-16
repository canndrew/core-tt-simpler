use crate::priv_prelude::*;

#[derive(Debug)]
pub struct SolveError {
    ctx: Vec<(Option<Name>, Option<Ty>)>,
    kind: SolveErrorKind,
}

#[derive(Debug)]
pub enum SolveErrorKind {
    Uninhabited {
        tags: Vec<Tag>,
    },
    Ambiguous {
        ty: Ty,
    },
}

impl fmt::Display for SolveError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let SolveError { ctx, kind } = self;
        match kind {
            SolveErrorKind::Uninhabited { tags } => {
                writeln!(f, "uninhabited at:")?;
                for tag in tags {
                    write!(f, "    {:?}", tag)?;
                }
                Ok(())
            },
            SolveErrorKind::Ambiguous { ty } => {
                let mut ctx = ctx.clone();
                let mut s = String::new();
                crate::pprint::Pretty::pretty(ty.clone(), &mut ctx, 0, &mut s, ());
                writeln!(f, "failed to solve constraint: {}", s)
            },
        }
    }
}

impl<T> Checked<T> {
    pub fn solve(self, ctx: Vec<(Name, Ty)>) -> Result<T, SolveError>
    where
        T: Contextual,
        T: Bindable,
    {
        let (constraint_ty, scope) = self.into_constraint_ty_and_scope();
        let result = {
            let mut ctx = ctx.iter().map(|(_name, ty)| ty.clone()).collect();
            constraint_ty.simplify(&mut ctx, 0)
        };

        let simplification = match result {
            Ok(simplification) => simplification,
            Err(Uninhabited { tags }) => {
                let ctx = ctx.into_iter().map(|(name, ty)| (Some(name), Some(ty))).collect();
                let kind = SolveErrorKind::Uninhabited { tags };
                return Err(SolveError { ctx, kind });
            },
        };
        let Simplification { new_ty, iso, constraints, eliminated } = simplification;
        debug_assert!(constraints.is_empty());
        debug_assert!(eliminated.is_empty());

        let Some(()) = new_ty.clone().as_unit() else {
            let ty = new_ty.deep_nf();
            let ctx = ctx.into_iter().map(|(name, ty)| (Some(name), Some(ty))).collect();
            let kind = SolveErrorKind::Ambiguous { ty };
            return Err(SolveError { ctx, kind });
        };

        let body = scope.bind(iso.rev.bind(Tm::proof()));
        Ok(body)
    }
}

