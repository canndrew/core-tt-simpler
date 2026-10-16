use crate::priv_prelude::*;

#[derive(Debug)]
pub struct SolveError {
    ctx: Vec<(Name, Ty)>,
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
    ConstrainsCtx {
        constraints: Constraints,
    },
}

impl fmt::Display for SolveError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let SolveError { ctx, kind } = self;
        match kind {
            SolveErrorKind::Uninhabited { tags } => {
                writeln!(f, "uninhabited at:")?;
                for tag in tags {
                    writeln!(f, "    {:?}", tag)?;
                }
                Ok(())
            },
            SolveErrorKind::Ambiguous { ty } => {
                let mut ctx = {
                    ctx
                    .iter()
                    .map(|(name, ty)| (Some(name.clone()), Some(ty.clone())))
                    .collect()
                };
                let mut s = String::new();
                crate::pprint::Pretty::pretty(ty.clone(), &mut ctx, 0, &mut s, ());
                writeln!(f, "failed to solve constraint: {}", s)
            },
            SolveErrorKind::ConstrainsCtx { constraints } => {
                let (index, tm) = constraints.clone().into_iter().next().unwrap();
                let (var_name, _) = &ctx[index];
                let mut ctx = {
                    ctx
                    .iter()
                    .map(|(name, ty)| (Some(name.clone()), Some(ty.clone())))
                    .collect()
                };
                let name_s = {
                    let mut name_s = String::new();
                    crate::pprint::Pretty::pretty(var_name.clone(), &mut ctx, 0, &mut name_s, ());
                    name_s
                };
                let tm_s = {
                    let mut tm_s = String::new();
                    crate::pprint::Pretty::pretty(tm, &mut ctx, 0, &mut tm_s, ());
                    tm_s
                };
                writeln!(f, "inhabitation requires var {} equals {}", name_s, tm_s)
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
        let ctx_len = ctx.len();
        let (constraint_ty, scope) = self.into_constraint_ty_and_scope();
        let result = {
            let mut cache = SimplifyCache::new();
            let mut ctx = ctx.iter().map(|(_name, ty)| ty.clone()).collect();
            constraint_ty.simplify(&mut ctx, ctx_len, &mut cache)
        };

        let simplification = match result {
            Ok(simplification) => simplification,
            Err(Uninhabited { tags }) => {
                let kind = SolveErrorKind::Uninhabited { tags };
                return Err(SolveError { ctx, kind });
            },
        };
        let Simplification {
            is_changed: _, new_ty, iso, constraints, eliminated,
        } = simplification;
        if !constraints.is_empty() {
            let kind = SolveErrorKind::ConstrainsCtx { constraints };
            return Err(SolveError { ctx, kind });
        }

        let Some(()) = new_ty.clone().as_unit() else {
            let ty = new_ty.deep_nf().into_ty();


            /*
            // debugging
            {
                debug!("starting debugging re-pass");
                let mut cache = SimplifyCache::new();
                let mut ctx = ctx.iter().map(|(_name, ty)| ty.clone()).collect();
                let simplification_res = ty.clone().simplify(&mut ctx, ctx_len, &mut cache);
                let simplification = simplification_res.ok().unwrap();
                let Simplification {
                    is_changed, new_ty, iso, constraints, eliminated: _,
                } = simplification;
                assert_eq!(ctx_len, ctx.len());
                let actually_changed = Unify::unify(ty.clone(), new_ty.clone()).is_none();
                if is_changed {
                    println!("simplified type == {}", debug_print(&ctx, &ty));
                    println!("re-simplified type == {}", debug_print(&ctx, &new_ty));
                    println!("actually changed == {}", actually_changed);
                }
                assert!(!is_changed);
                assert!(!actually_changed);
                let (fwd, rev) = iso.into_scopes();
                Unify::unify(fwd.into_inner(ctx_len), Tm::var(ctx_len)).unwrap();
                Unify::unify(rev.into_inner(ctx_len), Tm::var(ctx_len)).unwrap();
                assert!(constraints.is_empty());
            }
            */



            let kind = SolveErrorKind::Ambiguous { ty };
            return Err(SolveError { ctx, kind });
        };

        debug_assert!(eliminated.is_empty());
        let body = scope.bind(iso.rev.bind(Tm::proof()));
        Ok(body)
    }
}

