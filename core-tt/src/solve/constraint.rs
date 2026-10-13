use crate::priv_prelude::*;

#[derive(Clone, Debug)]
pub struct Constraints {
    unique_tms: BTreeMap<usize, Tm>,
}

impl Constraints {
    pub fn new() -> Constraints {
        Constraints {
            unique_tms: BTreeMap::new(),
        }
    }

    pub fn single(index: usize, unique_tm: Tm) -> Constraints {
        let mut unique_tms = BTreeMap::new();
        unique_tms.insert(index, unique_tm);
        Constraints { unique_tms }
    }

    pub fn from_map(unique_tms: BTreeMap<usize, Tm>) -> Constraints {
        Constraints { unique_tms }
    }

    pub fn is_empty(&self) -> bool {
        self.unique_tms.is_empty()
    }

    pub fn has_preserved_constraints(&self, preserved_constraint_depth: usize) -> bool {
        match self.unique_tms.last_key_value() {
            None => false,
            Some((index, _)) => *index >= preserved_constraint_depth,
        }
    }

    pub fn pop_at_index(&mut self, index: usize) -> Option<Tm> {
        let entry = self.unique_tms.last_entry()?;
        debug_assert!(*entry.key() <= index);
        if *entry.key() == index {
            Some(entry.remove())
        } else {
            None
        }
    }

    pub fn union(
        ctx: &mut Vec<Ty>,
        constraints_0: Constraints,
        constraints_1: Constraints,
        eliminated: &mut Usages,
    ) -> Result<Constraints, Uninhabited> {
        let mut unique_tms = constraints_0.unique_tms;
        let mut unprocessed = constraints_1.unique_tms.into_iter().collect::<Vec<_>>();
        while let Some((index, unique_tm_1)) = unprocessed.pop() {
            let entry = match unique_tms.entry(index) {
                btree_map::Entry::Vacant(entry) => {
                    entry.insert(unique_tm_1);
                    continue;
                },
                btree_map::Entry::Occupied(entry) => entry,
            };

            let unique_tm_0 = entry.get().clone();

            // note: this is what prevents this loop from being infinite.
            debug_assert!(unique_tm_0.ctx_len() < index);
            debug_assert!(unique_tm_1.ctx_len() < index);

            if let Some(unique_tm) = Unify::unify(unique_tm_0.clone(), unique_tm_1.clone()) {
                *entry.into_mut() = unique_tm;
                continue;
            }

            let equal_ty = Ty::obs_equal(
                ctx[index].clone(),
                unique_tm_0.clone(),
                unique_tm_1.clone(),
            );
            let Simplification {
                new_ty: _,
                iso: _,
                constraints: equals_constraints,
                eliminated: equals_eliminated,
            } = solve::simplify::simplify_equal(ctx, &equal_ty, &unique_tm_0, &unique_tm_1)?;

            unprocessed.extend(equals_constraints);
            eliminated.or_assign(&equals_eliminated);
        }

        Ok(Constraints { unique_tms })
    }

    pub fn intersection(
        constraints_0: Constraints,
        constraints_1: Constraints,
    ) -> Constraints {
        let mut constraints = BTreeMap::new();
        for (index, which) in merge_enumerated(constraints_0, constraints_1) {
            let (unique_tm_0, unique_tm_1) = match which {
                Which::Left(_) | Which::Right(_) => continue,
                Which::Both(unique_tm_0, unique_tm_1) => {
                    (unique_tm_0, unique_tm_1)
                },
            };

            if let Some(unique_tm) = Unify::unify(unique_tm_0, unique_tm_1) {
                constraints.insert(index, unique_tm);
            }
        }
        Constraints::from_map(constraints)
    }
}

impl IntoIterator for Constraints {
    type Item = (usize, Tm);
    type IntoIter = btree_map::IntoIter<usize, Tm>;

    fn into_iter(self) -> btree_map::IntoIter<usize, Tm> {
        self.unique_tms.into_iter()
    }
}

