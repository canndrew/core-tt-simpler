use crate::priv_prelude::*;

/*
pub enum Decision {
    Inhabited(Tm),
    Uninhabited(Scope<Tm>),
}
*/

impl Ty {
    pub fn try_prove_uninhabited(
        self,
        ctx: &mut Vec<Ty>,
    ) -> Option<Scope<Tm>> {
        match self.into_inner() {
            TyKind::Form { form } => {
                Arc::unwrap_or_clone(form).try_prove_uninhabited(ctx)
            },
            TyKind::Neutral { .. } => None,
        }
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

    pub fn try_find_alternate_tm(
        &self,
        ctx: &mut Vec<Ty>,
        tm_0: Tm,
    ) -> Option<(Tm, Scope<Tm>)> {
        match self.clone().into_inner() {
            TyKind::Form { form } => {
                match Arc::unwrap_or_clone(form).try_find_alternate_tm(ctx, tm_0) {
                    Some((tm_1, proof)) => Some((tm_1, proof)),
                    None => None,
                }
            },
            TyKind::Neutral { neutral: _ } => {
                // TODO
                None
            },
        }
    }
}

impl FormKind {
    pub fn try_prove_uninhabited(
        self,
        ctx: &mut Vec<Ty>,
    ) -> Option<Scope<Tm>> {
        let ctx_len = self.ctx_len();
        match self {
            | FormKind::Name
            | FormKind::Universe
            | FormKind::Nat
            | FormKind::Unit
            => None,

            FormKind::Never => Some(Scope::id()),

            FormKind::Sum { lhs_name: _, lhs_ty, rhs_ty } => {
                let lhs_proof = lhs_ty.try_prove_uninhabited(ctx)?;
                let rhs_proof = rhs_ty.try_prove_uninhabited(ctx)?;
                let proof = Scope::make(ctx_len, |sum| {
                    sum
                    .case(
                        Scope::constant(Ty::never()),
                        lhs_proof,
                        rhs_proof,
                    )
                });
                Some(proof)
            },

            FormKind::Sigma { head_name: _, head_ty, tail_ty } => {
                match head_ty.clone().try_prove_uninhabited(ctx) {
                    Some(proof) => {
                        let proof = Scope::make(ctx_len, |pair| {
                            proof.bind(pair.proj_head())
                        });
                        Some(proof)
                    },
                    None => {
                        let proof = {
                            let tail_ty = tail_ty.clone().into_inner(ctx_len);
                            ctx.push(head_ty.clone());
                            let proof = tail_ty.try_prove_uninhabited(ctx)?;
                            ctx.pop();
                            Scope::new(ctx_len, proof)
                        };
                        let proof = Scope::make(ctx_len, |pair| {
                            proof.bind(pair.clone().proj_head()).bind(pair.proj_tail())
                        });
                        Some(proof)
                    },
                }
            },

            FormKind::Pi { arg_name: _, arg_ty, res_ty } => {
                let arg_tm = arg_ty.try_find_arbitrary_tm(ctx)?;
                let res_ty = res_ty.bind(arg_tm.clone());
                let proof = res_ty.try_prove_uninhabited(ctx)?;
                let proof = Scope::make(ctx_len, |func| {
                    proof.bind(func.app(arg_tm))
                });
                Some(proof)
            },
        }
    }

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
                        match arg_ty.try_prove_uninhabited(ctx) {
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

    // Given a term tm_0 of type `self`, tries to find
    // * another term tm_1 and
    // * a proof that (tm_0 == tm_1) -> Never
    pub fn try_find_alternate_tm(
        &self,
        ctx: &mut Vec<Ty>,
        tm_0: Tm,
    ) -> Option<(Tm, Scope<Tm>)> {
        let (tm_1, proof) = match self {
            FormKind::Name => {
                let tag = tm_0.as_tag().unwrap();
                let tm_1 = match tag.kind {
                    TagKind::Literal { s } => Tm::tag(Tag::from(format!("other_{}", s).as_str())),
                    TagKind::Meta { .. } => Tm::tag(Tag::from("x")),
                };
                let proof = Scope::make(0, |eq| eq);
                (tm_1, proof)
            },

            FormKind::Universe => {
                let ty_0 = tm_0.into_ty();
                match ty_0.clone().try_prove_uninhabited(ctx) {
                    None => {
                        let tm_0 = ty_0.clone().try_find_arbitrary_tm(ctx)?;
                        let tm_1 = Ty::never().into_tm();
                        let proof = Scope::make(tm_0.ctx_len(), |eq| {
                            eq.cast(ty_0, Ty::never(), tm_0)
                        });
                        (tm_1, proof)
                    },
                    Some(proof_0) => {
                        let tm_1 = Ty::unit().into_tm();
                        let proof = Scope::make(proof_0.ctx_len(), |eq| {
                            proof_0.bind(eq.cast(Ty::unit(), ty_0, Tm::unit()))
                        });
                        (tm_1, proof)
                    },
                }
            },

            FormKind::Nat => {
                let tm_1 = tm_0.succs(Ubig::ONE);
                let proof = Scope::make(0, |eq| eq);
                (tm_1, proof)
            },

            FormKind::Never => {
                let tm_1 = tm_0.clone();
                let proof = Scope::constant(tm_0);
                (tm_1, proof)
            },

            FormKind::Unit => return None,

            FormKind::Sum { lhs_name: _, lhs_ty, rhs_ty } => {
                match tm_0.clone().as_intro()?.into_inner_arc() {
                    IntroKind::InjLhs { lhs_tm: lhs_tm_0 } => {
                        match rhs_ty.clone().try_find_arbitrary_tm(ctx) {
                            None => {
                                let lhs_tm_0 = Weaken::new(lhs_tm_0);
                                let (lhs_tm_1, proof) = {
                                    lhs_ty.try_find_alternate_tm(ctx, lhs_tm_0)?
                                };
                                let tm_1 = lhs_tm_1.inj_lhs();
                                (tm_1, proof)
                            },
                            Some(rhs_tm_1) => {
                                let tm_1 = rhs_tm_1.inj_rhs();
                                let proof = Scope::make(0, |eq| eq);
                                (tm_1, proof)
                            },
                        }
                    },

                    IntroKind::InjRhs { rhs_tm: rhs_tm_0 } => {
                        match lhs_ty.clone().try_find_arbitrary_tm(ctx) {
                            None => {
                                let rhs_tm_0 = Weaken::new(rhs_tm_0);
                                let (rhs_tm_1, proof) = {
                                    rhs_ty.try_find_alternate_tm(ctx, rhs_tm_0)?
                                };
                                let tm_1 = rhs_tm_1.inj_rhs();
                                (tm_1, proof)
                            },
                            Some(lhs_tm_1) => {
                                let tm_1 = lhs_tm_1.inj_lhs();
                                let proof = Scope::make(0, |eq| eq);
                                (tm_1, proof)
                            },
                        }
                    },

                    _ => unreachable!(),
                }
            },

            FormKind::Sigma { head_name: _, head_ty, tail_ty } => {
                let (head_tm_0, tail_tm_0) = {
                    tm_0
                    .clone()
                    .as_intro()?
                    .into_inner_arc()
                    .as_pair()?
                };

                let bound_tail_ty_0 = tail_ty.clone().bind(head_tm_0.clone());
                match bound_tail_ty_0.try_find_alternate_tm(ctx, tail_tm_0.clone()) {
                    Some((tail_tm_1, proof)) => {
                        let proof = Scope::make(proof.ctx_len(), |eq| {
                            proof.bind(eq.proj_tail())
                        });
                        let tm_1 = head_tm_0.pair(tail_tm_1);
                        (tm_1, proof)
                    },
                    None => {
                        let (head_tm_1, proof) = head_ty.try_find_alternate_tm(ctx, head_tm_0)?;
                        let proof = Scope::make(proof.ctx_len(), |eq| {
                            proof.bind(eq.proj_head())
                        });
                        let tail_tm_1 = match tail_ty.clone().try_strengthen() {
                            Ok(_) => tail_tm_0,
                            Err(tail_ty) => {
                                let bound_tail_ty_1 = tail_ty.bind(head_tm_1.clone());
                                bound_tail_ty_1.try_find_arbitrary_tm(ctx)?
                            },
                        };
                        let tm_1 = head_tm_1.pair(tail_tm_1);
                        (tm_1, proof)
                    },
                }
            },

            FormKind::Pi { arg_name: _, arg_ty, res_ty } => {
                let arg_tm = arg_ty.clone().try_find_arbitrary_tm(ctx)?;

                let res_tm_0 = {
                    tm_0
                    .clone()
                    .as_intro()?
                    .into_inner_arc()
                    .as_func()?
                };

                let res_ty_inner = res_ty.clone().into_inner(ctx.len());
                let res_tm_inner_0 = {
                    res_tm_0
                    .map_without_capture(Weaken::new)
                    .into_inner(ctx.len())
                };
                let (res_tm_inner_1, proof_inner) = {
                    ctx.push(arg_ty.clone());
                    let result = res_ty_inner.try_find_alternate_tm(ctx, res_tm_inner_0);
                    ctx.pop();
                    result?
                };
                let res_tm_1 = Scope::new(ctx.len(), res_tm_inner_1);
                let proof = Scope::new(ctx.len(), proof_inner);
                let tm_1 = Tm::func(res_tm_1);

                let proof = Scope::make(ctx.len(), |eq| {
                    proof.bind(arg_tm.clone()).bind(eq.app(arg_tm))
                });
                (tm_1, proof)
            },
        };
        Some((tm_1, proof))
    }
}
