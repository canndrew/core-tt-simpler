use crate::priv_prelude::*;

pub struct Simplification {
    pub new_ty: Ty,
    pub iso: Iso,
    pub constraints: Vec<(usize, Constraint)>,
    pub eliminated: Usages,
}

impl Simplification {
    pub fn id(ty: Ty) -> Simplification {
        Simplification {
            new_ty: ty,
            iso: Iso::refl(),
            constraints: Vec::new(),
            eliminated: Usages::empty(),
        }
    }

    pub fn from_iso(
        new_ty: Ty,
        iso: Iso,
    ) -> Simplification {
        let constraints = Vec::new();
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
        let constraints = vec![(index, constraint)];
        let eliminated = Usages::empty();
        Simplification { new_ty, iso, constraints, eliminated }
    }

    pub fn from_eliminated(
        orig_ty: &Ty,
        eliminated: Usages,
    ) -> Simplification {
        let new_ty = orig_ty.clone();
        let iso = Iso::refl();
        let constraints = Vec::new();
        Simplification { new_ty, iso, constraints, eliminated }
    }

    pub fn simplify_more(
        self,
        ctx: &mut Vec<Ty>,
        preserved_constraint_depth: usize,
        orig_ty: &Ty,
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

        let constraints_0 = {
            constraints_0
            .into_iter()
            .map(|(index, Constraint { unique_tm, proof })| {
                let proof = Scope::make(ctx.len(), |tm| {
                    proof.bind(iso_1.rev.clone().bind(tm))
                });
                (index, Constraint { unique_tm, proof })
            })
            .collect::<Vec<_>>()
        };

        let constraints = Constraint::merge(ctx, constraints_0, constraints_1, &mut eliminated)?;

        let iso = Iso::transitivity(
            iso_0,
            iso_1,
            orig_ty.clone(),
            new_ty_1.clone(),
        );

        Ok(Simplification { new_ty: new_ty_1, iso, constraints, eliminated })
    }
}

pub struct Uninhabited {
    pub tags: Vec<Tag>,
    pub proof: Scope<Tm>,
}

impl Uninhabited {
    pub fn from_proof(proof: Scope<Tm>) -> Uninhabited {
        Uninhabited {
            tags: Vec::new(),
            proof,
        }
    }
}

