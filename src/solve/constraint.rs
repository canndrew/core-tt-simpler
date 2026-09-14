use crate::priv_prelude::*;

#[derive(Clone)]
pub struct Constraint {
    pub unique_tm: Tm,
    pub proof: Scope<Tm>,
}

pub struct Constraints {
    map: BTreeMap<usize, Constraint>,
}

impl Constraints {
    pub fn new() -> Constraints {
        Constraints {
            map: BTreeMap::new(),
        }
    }

    pub fn single(index: usize, constraint: Constraint) -> Constraints {
        let mut map = BTreeMap::new();
        map.insert(index, constraint);
        Constraints { map }
    }

    pub fn from_map(map: BTreeMap<usize, Constraint>) -> Constraints {
        Constraints { map }
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn has_preserved_constraints(&self, preserved_constraint_depth: usize) -> bool {
        match self.map.last_key_value() {
            None => false,
            Some((index, _)) => *index >= preserved_constraint_depth,
        }
    }

    pub fn pop_at_index(&mut self, index: usize) -> Option<Constraint> {
        let entry = self.map.last_entry()?;
        debug_assert!(*entry.key() <= index);
        if *entry.key() == index {
            Some(entry.remove())
        } else {
            None
        }
    }

    pub fn map_in_place(
        &mut self,
        ctx_len: usize,
        mut func: impl FnMut(usize, &Tm, Scope<Tm>, Tm) -> Tm,
    ) {
        for (index, Constraint { unique_tm, proof }) in self.map.iter_mut() {
            *proof = Scope::make(ctx_len, |tm| {
                func(*index, unique_tm, proof.clone(), tm)
            });
        }
    }

    pub fn union(
        ctx: &mut Vec<Ty>,
        fwd: &Scope<Tm>,
        constraints_0: Constraints,
        constraints_1: Constraints,
        eliminated: &mut Usages,
    ) -> Result<Constraints, Uninhabited> {
        let mut map = constraints_0.map;
        let mut unprocessed = constraints_1.map.into_iter().collect::<Vec<_>>();
        while let Some((index, constraint_1)) = unprocessed.pop() {
            let entry = match map.entry(index) {
                btree_map::Entry::Vacant(entry) => {
                    entry.insert(constraint_1);
                    continue;
                },
                btree_map::Entry::Occupied(entry) => entry,
            };

            let Constraint { unique_tm: unique_tm_0, proof: proof_0 } = entry.get().clone();
            let Constraint { unique_tm: unique_tm_1, proof: proof_1 } = constraint_1;
            
            let var_ty = ctx[index].clone();
            if let Some(unique_tm) = Unify::unify(
                ctx, var_ty.clone(), unique_tm_0.clone(), unique_tm_1.clone(),
            ) {
                *entry.into_mut() = Constraint { unique_tm, proof: proof_0 };
                continue;
            }

            let equal_ty = Ty::obs_equal(
                var_ty.clone(),
                unique_tm_0.clone(),
                unique_tm_1.clone(),
            );
            let transitively_eq = Scope::make(ctx.len(), |tm| {
                proof_0
                .bind(tm.clone())
                .transitivity(
                    proof_1.bind(tm),
                    var_ty.clone(),
                    unique_tm_0.clone(),
                    unique_tm_1.clone(),
                )
            });

            match equal_ty.simplify(ctx, index) {
                Err(Uninhabited { tags, proof }) => {
                    let proof = Scope::make(ctx.len(), |tm| {
                        proof.bind(transitively_eq.bind(fwd.clone().bind(tm)))
                    });
                    return Err(Uninhabited { tags, proof });
                },
                Ok(Simplification {
                    new_ty: _,
                    iso: equals_iso,
                    constraints: equals_constraints,
                    eliminated: equals_eliminated,
                }) => {
                    let equals_fwd = equals_iso.fwd;
                    unprocessed.extend(
                        equals_constraints
                        .into_iter()
                        .map(|(index, Constraint { unique_tm, proof })| {
                            let proof = Scope::make(ctx.len(), |tm| {
                                let eq = transitively_eq.clone().bind(tm);
                                proof.bind(equals_fwd.clone().bind(eq))
                            });
                            (index, Constraint { unique_tm, proof })
                        })
                    );
                    eliminated.or_assign(&equals_eliminated);
                },
            }
        }

        Ok(Constraints { map })
    }

    pub fn intersection(
        ctx: &mut Vec<Ty>,
        constraints_0: Constraints,
        constraints_1: Constraints,
        mut combine: impl FnMut(&mut Vec<Ty>, usize, &Tm, Scope<Tm>, Scope<Tm>, Tm) -> Tm,
    ) -> Constraints {
        let mut constraints = BTreeMap::new();
        for (index, which) in merge_enumerated(constraints_0, constraints_1) {
            let (constraint_0, constraint_1) = match which {
                Which::Left(_) | Which::Right(_) => continue,
                Which::Both(constraint_0, constraint_1) => {
                    (constraint_0, constraint_1)
                },
            };
            let Constraint {
                unique_tm: unique_tm_0, proof: proof_0,
            } = constraint_0;
            let Constraint {
                unique_tm: unique_tm_1, proof: proof_1,
            } = constraint_1;

            let Some(unique_tm) = Unify::unify(
                ctx, ctx[index].clone(), unique_tm_0, unique_tm_1,
            ) else {
                continue;
            };

            let proof = Scope::make(ctx.len(), |tm| {
                combine(ctx, index, &unique_tm, proof_0, proof_1, tm)
            });

            constraints.insert(
                index,
                Constraint { unique_tm, proof },
            );
        }
        Constraints::from_map(constraints)
    }
}

impl IntoIterator for Constraints {
    type Item = (usize, Constraint);
    type IntoIter = btree_map::IntoIter<usize, Constraint>;

    fn into_iter(self) -> btree_map::IntoIter<usize, Constraint> {
        self.map.into_iter()
    }
}

