use crate::priv_prelude::*;

pub struct Simplification {
    pub new_ty: Ty,

    // between orig_ty and new_ty
    pub iso: Iso,

    // scoped over new_ty
    pub constraints: Constraints,
    pub eliminated: Usages,
}

impl Simplification {
    pub fn id(ty: Ty) -> Simplification {
        Simplification {
            new_ty: ty,
            iso: Iso::refl(),
            constraints: Constraints::new(),
            eliminated: Usages::empty(),
        }
    }

    pub fn from_iso(
        new_ty: Ty,
        iso: Iso,
    ) -> Simplification {
        let constraints = Constraints::new();
        let eliminated = Usages::empty();
        Simplification { new_ty, iso, constraints, eliminated }
    }

    pub fn from_constraint(
        orig_ty: &Ty,
        index: usize,
        constraint: Constraint,
    ) -> Simplification {
        let new_ty = orig_ty.clone();
        let iso = Iso::refl();
        let constraints = Constraints::single(index, constraint);
        let eliminated = Usages::empty();
        Simplification { new_ty, iso, constraints, eliminated }
    }

    pub fn from_eliminated(
        orig_ty: &Ty,
        eliminated: Usages,
    ) -> Simplification {
        let new_ty = orig_ty.clone();
        let iso = Iso::refl();
        let constraints = Constraints::new();
        Simplification { new_ty, iso, constraints, eliminated }
    }

    pub fn simplify_more(
        self,
        ctx: &mut Vec<Ty>,
        preserved_constraint_depth: usize,
    ) -> Result<Simplification, Uninhabited> {
        let Simplification {
            new_ty: new_ty_0,
            iso: iso_0,
            constraints: constraints_0,
            eliminated: eliminated_0,
        } = self;
        let Simplification {
            new_ty: new_ty_1,
            iso: iso_1,
            constraints: constraints_1,
            eliminated: eliminated_1,
        } = new_ty_0.simplify(ctx, preserved_constraint_depth)?;

        let mut eliminated = eliminated_0.or(eliminated_1);

        let iso = Iso::transitivity(
            iso_0,
            iso_1,
        );

        let constraints = Constraints::union(
            ctx,
            constraints_0,
            constraints_1,
            &mut eliminated,
        )?;

        Ok(Simplification { new_ty: new_ty_1, iso, constraints, eliminated })
    }
}

pub struct Uninhabited {
    pub tags: Vec<Tag>,
}

impl Uninhabited {
    pub fn new() -> Uninhabited {
        Uninhabited {
            tags: Vec::new(),
        }
    }
}

