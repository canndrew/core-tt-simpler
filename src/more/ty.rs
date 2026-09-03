use crate::priv_prelude::*;

/*
pub enum Decision {
    Inhabited(Tm),
    Uninhabited(Scope<Tm>),
}
*/

impl Ty {
    /*
    pub fn try_decide(
        &self,
        ctx: &mut Vec<Ty>,
    ) -> Option<Decision> {
        match self.into_inner() {
            TyKind::Form { form } => {
                Arc::unwrap_or_clone(form).try_decide(ctx)
            },
            TyKind::Neutral { neutral: _ } => {
                // TODO
                None
            },
        }
    }
    */

    pub fn try_prove_uninhabited(&self) -> Option<Scope<Tm>> {
        todo!()
    }

    pub fn try_find_arbitrary_tm(
        self,
        ctx: &mut Vec<Ty>,
    ) -> Option<Tm> {
        match self.clone().into_inner() {
            TyKind::Form { form } => {
                match Arc::unwrap_or_clone(form).try_find_arbitrary_tm_excluding_ctx(ctx) {
                    Some(tm) => return Some(tm),
                    None => (),
                }
            },
            TyKind::Neutral { neutral: _ } => {
                // TODO
            },
        };

        for var_index in self.ctx_len()..ctx.len() {
            let var_ty = ctx[var_index].clone();
            if let Some(_) = Unify::unify(ctx, (), var_ty, self.clone()) {
                return Some(Tm::var(var_index));
            }
        }

        None
    }

    /*
    pub fn try_find_alternate_tm(
        &self,
        ctx: &mut Vec<Ty>,
        intro: Intro,
    ) -> Option<(Tm, Scope<Tm>)> {
        match self.clone().into_inner() {
            TyKind::Form { form } => {
                match Arc::unwrap_or_clone(form).try_find_alternate_tm(ctx, intro) {
                    Some((tm, proof)) => Some((tm, proof)),
                    None => None,
                }
            },
            TyKind::Neutral { neutral: _ } => {
                // TODO
                None
            },
        }
    }
    */
}

impl FormKind {
    pub fn try_find_arbitrary_tm_excluding_ctx(
        self,
        ctx: &mut Vec<Ty>,
    ) -> Option<Tm> {
        match self {
            FormKind::Name => {
                lazy_static! {
                    static ref X: Tag = Tag::from("x");
                }
                Some(Tm::tag(X.clone()))
            },

            FormKind::Universe => {
                Some(Ty::never().into_tm())
            },

            FormKind::Nat => {
                Some(Tm::zero())
            },

            FormKind::Equal { eq_ty, eq_tm_0, eq_tm_1 } => {
                let eq_tm = Unify::unify(ctx, eq_ty, eq_tm_0, eq_tm_1)?;
                Some(eq_tm.refl())
            },

            FormKind::Never => None,

            FormKind::Unit => Some(Tm::unit()),

            FormKind::Sum { lhs_name: _, lhs_ty, rhs_ty } => {
                match lhs_ty.try_find_arbitrary_tm(ctx) {
                    Some(lhs_tm) => Some(lhs_tm.inj_lhs()),
                    None => {
                        match rhs_ty.try_find_arbitrary_tm(ctx) {
                            Some(rhs_tm) => Some(rhs_tm.inj_rhs()),
                            None => None,
                        }
                    },
                }
            },

            FormKind::Sigma { head_name: _, head_ty, tail_ty } => {
                match head_ty.try_find_arbitrary_tm(ctx) {
                    None => None,
                    Some(head_tm) => {
                        let tail_ty = tail_ty.bind(head_tm.clone());
                        match tail_ty.try_find_arbitrary_tm(ctx) {
                            None => None,
                            Some(tail_tm) => Some(head_tm.pair(tail_tm)),
                        }
                    },
                }
            },

            FormKind::Pi { arg_name: _, arg_ty, res_ty } => {
                match {
                    res_ty
                    .clone()
                    .try_map(ctx.len(), |_, res_ty| {
                        ctx.push(arg_ty.clone());
                        let ret = res_ty.try_find_arbitrary_tm(ctx);
                        ctx.pop();
                        ret
                    })
                } {
                    Some(res_tm) => Some(Tm::func(res_tm)),
                    None => {
                        match arg_ty.try_prove_uninhabited() {
                            Some(proof) => {
                                Some(Tm::func(Scope::make(ctx.len(), |arg| {
                                    proof
                                    .bind(arg.clone())
                                    .explode(Scope::constant(res_ty.bind(arg)))
                                })))
                            },
                            None => None,
                        }
                    },
                }
            },
        }
    }

    /*
    pub fn try_find_alternate_tm(
        &self,
        ctx: &mut Vec<Ty>,
        intro: Intro,
    ) -> Option<(Tm, Scope<Tm>)> {
        match self {
            FormKind::Name => {
                let tag = intro.as_tag().unwrap();
                let tm_1 = match tag.kind {
                    TagKind::Literal { s } => Tm::tag(Tag::from(format!("other_{}", s).as_str())),
                    TagKind::Meta { .. } => Tm::tag(Tag::from("x")),
                };
                let proof = Scope::make(0, |eq| eq.tags_apart());
                Some((tm_1, proof))
            },

            FormKind::Universe => {
                let form_0 = intro.as_form().unwrap();
                match form_0.as_never() {
                    Some(()) => {
                        let tm_1 = Ty::unit().into_tm();
                        let proof = Scope::make(0, |eq| {
                            eq
                            .cong(
                                Scope::make(1, |ty_1| Scope::constant(
                                    Ty::pi(
                                        Name::from("tm_1"),
                                        ty_1.into_ty(),
                                        Scope::constant(Ty::never()),
                                    )
                                )),
                                Tm::func(Scope::id()),
                            )
                            .app(Tm::unit())
                        });
                        Some((tm_1, proof))
                    },
                    None => {
                        let ty_0 = intro.into_ty();
                        match ty_0.try_find_arbitrary_tm(ctx) {
                            None => None,
                            Some(tm) => {
                                /*
                                let tm_1 = Ty::never().into_tm();
                                let proof = Scope::make(0, |eq| {
                                    eq
                                    .cong(
                                        Scope::make(1, |_| Scope::constant(
                                            Ty::pi(
                                                Name::from("tm_0"),
                                                ty_0,
                                                Scope::constant(Ty::never()),
                                            )
                                        )),
                                        Tm::func(Scope::id()),
                                    )
                                    .app(tm)
                                });
                                Some((tm_1, proof))
                                */
                                todo!()
                            },
                        }
                    },
                }
            },

            FormKind::Nat => {
                todo!()
            },
        }
    }
    */
}
