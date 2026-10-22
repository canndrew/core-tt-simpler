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
        constraints_0: Constraints,
        constraints_1: Constraints,
    ) -> Result<Constraints, Uninhabited> {
        if constraints_0.is_empty() {
            return Ok(constraints_1);
        }
        if constraints_1.is_empty() {
            return Ok(constraints_0);
        }

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
            debug_assert!(unique_tm_0.ctx_len() <= index);
            debug_assert!(unique_tm_1.ctx_len() <= index);

            if let Some(unique_tm) = Unify::unify(unique_tm_0.clone(), unique_tm_1.clone()) {
                *entry.into_mut() = unique_tm;
                continue;
            }

            if let Some((var_index, unique_tm)) = Constraints::single_from_equality(
                unique_tm_0,
                unique_tm_1,
            ) {
                unprocessed.push((var_index, unique_tm));
            }
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

    pub fn from_equality(
        eq_tm_0: Tm,
        eq_tm_1: Tm,
    ) -> Constraints {
        match Constraints::single_from_equality(eq_tm_0, eq_tm_1) {
            Some((var_index, unique_tm)) => Constraints::single(var_index, unique_tm),
            None => Constraints::new(),
        }
    }

    pub fn single_from_equality(
        eq_tm_0: Tm,
        eq_tm_1: Tm,
    ) -> Option<(usize, Tm)> {
        let eq_tm_0 = eq_tm_0.deep_nf();
        let eq_tm_1 = eq_tm_1.deep_nf();

        if let Some(var_index) = eq_tm_0.ctx_len().checked_sub(1)
        && eq_tm_1.ctx_len() <= var_index
        && let Some(_) = Unify::unify(Tm::var(var_index), eq_tm_0.clone().into_tm())
        {
            return Some((var_index, eq_tm_1.into_tm()));
        }

        if let Some(var_index) = eq_tm_1.ctx_len().checked_sub(1)
        && eq_tm_0.ctx_len() <= var_index
        && let Some(_) = Unify::unify(Tm::var(var_index), eq_tm_1.clone().into_tm())
        {
            return Some((var_index, eq_tm_0.into_tm()));
        }

        debug!("no constraint generated from equality");

        None
    }
}

impl IntoIterator for Constraints {
    type Item = (usize, Tm);
    type IntoIter = btree_map::IntoIter<usize, Tm>;

    fn into_iter(self) -> btree_map::IntoIter<usize, Tm> {
        self.unique_tms.into_iter()
    }
}

