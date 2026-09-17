use crate::priv_prelude::*;

impl Ty {
    pub fn try_prove_uninhabited(
        self,
        ctx: &mut Vec<Ty>,
    ) -> Option<()> {
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
            if let Some(_) = Unify::unify(var_ty, self.clone()) {
                return Some(Tm::var(var_index));
            }
        }

        None
    }

    pub fn try_find_alternate_tm(
        &self,
        ctx: &mut Vec<Ty>,
        tm_0: Tm,
    ) -> Option<Tm> {
        match self.clone().into_inner() {
            TyKind::Form { form } => {
                match Arc::unwrap_or_clone(form).try_find_alternate_tm(ctx, tm_0) {
                    Some(tm_1) => Some(tm_1),
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
    ) -> Option<()> {
        let ctx_len = self.ctx_len();
        match self {
            | FormKind::Name
            | FormKind::Universe
            | FormKind::Nat
            | FormKind::Unit
            => None,

            FormKind::Never => Some(()),

            FormKind::Sum { lhs_name: _, lhs_ty, rhs_ty } => {
                let () = lhs_ty.try_prove_uninhabited(ctx)?;
                let () = rhs_ty.try_prove_uninhabited(ctx)?;
                Some(())
            },

            FormKind::Sigma { head_name: _, head_ty, tail_ty } => {
                match head_ty.clone().try_prove_uninhabited(ctx) {
                    Some(()) => {
                        Some(())
                    },
                    None => {
                        let tail_ty = tail_ty.clone().into_inner(ctx_len);
                        ctx.push(head_ty.clone());
                        let res = tail_ty.try_prove_uninhabited(ctx);
                        ctx.pop();
                        res
                    },
                }
            },

            FormKind::Pi { arg_name: _, arg_ty, res_ty } => {
                let arg_tm = arg_ty.try_find_arbitrary_tm(ctx)?;
                let res_ty = res_ty.bind(arg_tm.clone());
                let () = res_ty.try_prove_uninhabited(ctx)?;
                Some(())
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

            FormKind::Unit => Some(Tm::proof()),

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
                            Some(_) => {
                                Some(Tm::func(Scope::make(ctx.len(), |arg| {
                                    Tm::explode(Scope::constant(res_ty.bind(arg)))
                                })))
                            },
                            None => None,
                        }
                    },
                }
            },
        }
    }

    // Given a term `tm_0` of type `self`, tries to find another term `tm_1` which is provably apart
    // from `tm_0`
    pub fn try_find_alternate_tm(
        &self,
        ctx: &mut Vec<Ty>,
        tm_0: Tm,
    ) -> Option<Tm> {
        let tm_1 = match self {
            FormKind::Name => {
                let tag = tm_0.as_tag().unwrap();
                match tag.kind {
                    TagKind::Literal { s } => Tm::tag(Tag::from(format!("other_{}", s).as_str())),
                    TagKind::Meta { .. } => Tm::tag(Tag::from("x")),
                }
            },

            FormKind::Universe => {
                let ty_0 = tm_0.into_ty();
                match ty_0.clone().try_prove_uninhabited(ctx) {
                    None => {
                        let _inhabitant = ty_0.clone().try_find_arbitrary_tm(ctx)?;
                        let tm_1 = Ty::never().into_tm();
                        tm_1
                    },
                    Some(_) => {
                        Ty::unit().into_tm()
                    },
                }
            },

            FormKind::Nat => {
                tm_0.clone().succs(Ubig::ONE)
            },

            FormKind::Never => {
                tm_0.clone()
            },

            FormKind::Unit => return None,

            FormKind::Sum { lhs_name: _, lhs_ty, rhs_ty } => {
                match tm_0.clone().as_intro()?.into_inner_arc() {
                    IntroKind::InjLhs { lhs_tm: lhs_tm_0 } => {
                        match rhs_ty.clone().try_find_arbitrary_tm(ctx) {
                            None => {
                                let lhs_tm_0 = Weaken::new(lhs_tm_0);
                                let lhs_tm_1 = {
                                    lhs_ty.try_find_alternate_tm(ctx, lhs_tm_0)?
                                };
                                lhs_tm_1.inj_lhs()
                            },
                            Some(rhs_tm_1) => {
                                rhs_tm_1.inj_rhs()
                            },
                        }
                    },

                    IntroKind::InjRhs { rhs_tm: rhs_tm_0 } => {
                        match lhs_ty.clone().try_find_arbitrary_tm(ctx) {
                            None => {
                                let rhs_tm_0 = Weaken::new(rhs_tm_0);
                                let rhs_tm_1 = {
                                    rhs_ty.try_find_alternate_tm(ctx, rhs_tm_0)?
                                };
                                rhs_tm_1.inj_rhs()
                            },
                            Some(lhs_tm_1) => {
                                lhs_tm_1.inj_lhs()
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
                    Some(tail_tm_1) => {
                        head_tm_0.pair(tail_tm_1)
                    },
                    None => {
                        let head_tm_1 = head_ty.try_find_alternate_tm(ctx, head_tm_0)?;
                        let tail_tm_1 = match tail_ty.clone().try_strengthen() {
                            Ok(_) => tail_tm_0,
                            Err(tail_ty) => {
                                let bound_tail_ty_1 = tail_ty.bind(head_tm_1.clone());
                                bound_tail_ty_1.try_find_arbitrary_tm(ctx)?
                            },
                        };
                        head_tm_1.pair(tail_tm_1)
                    },
                }
            },

            FormKind::Pi { arg_name: _, arg_ty, res_ty } => {
                let _arg_tm = arg_ty.clone().try_find_arbitrary_tm(ctx)?;

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
                let res_tm_inner_1 = {
                    ctx.push(arg_ty.clone());
                    let result = res_ty_inner.try_find_alternate_tm(ctx, res_tm_inner_0);
                    ctx.pop();
                    result?
                };
                let res_tm_1 = Scope::new(ctx.len(), res_tm_inner_1);
                Tm::func(res_tm_1)
            },
        };
        Some(tm_1)
    }
}

