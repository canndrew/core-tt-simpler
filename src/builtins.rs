use crate::priv_prelude::*;

pub struct Builtin {
    pub name: &'static str,
    pub ty: Ty,
    pub tm: Tm,
}

lazy_static! {
    pub static ref BUILTINS: Vec<Builtin> = {
        let mut builtins = Vec::new();
        builtins.push(Builtin {
            name: "Type",
            ty: Ty::universe(),
            tm: Ty::universe().into_tm(),
        });
        builtins.push(Builtin {
            name: "Nat",
            ty: Ty::universe(),
            tm: Ty::nat().into_tm(),
        });
        builtins.push(Builtin {
            name: "String",
            ty: Ty::universe(),
            tm: Ty::name().into_tm(),
        });

        /*
        builtins.push(Builtin {
            name: "cong",
            ty: Ty::pi(
                Name::from("Ty"),
                Ty::universe(),
                Scope::make(0, |eq_ty| {
                    let eq_ty = eq_ty.into_ty();
                    Ty::pi(
                        Name::from("val_0"),
                        eq_ty.clone(),
                        Scope::make(1, |eq_tm_0| {
                            Ty::pi(
                                Name::from("Motive"),
                                Ty::pi(
                                    Name::from("val_1"),
                                    eq_ty.clone(),
                                    Scope::make(2, |eq_tm_1| {
                                        Ty::pi(
                                            Name::from("elim"),
                                            Ty::equal(
                                                eq_ty.clone(),
                                                eq_tm_0.clone(),
                                                eq_tm_1,
                                            ),
                                            Scope::constant(Ty::universe()),
                                        )
                                    }),
                                ),
                                Scope::make(2, |motive| {
                                    Ty::pi(
                                        Name::from("inhab"),
                                        motive
                                        .clone()
                                        .app(eq_tm_0.clone())
                                        .app(eq_tm_0.clone().refl())
                                        .into_ty(),
                                        Scope::make(3, |_inhab| {
                                            Ty::pi(
                                                Name::from("val_1"),
                                                eq_ty.clone(),
                                                Scope::make(4, |eq_tm_1| {
                                                    Ty::pi(
                                                        Name::from("elim"),
                                                        Ty::equal(
                                                            eq_ty,
                                                            eq_tm_0,
                                                            eq_tm_1.clone(),
                                                        ),
                                                        Scope::make(5, |elim| {
                                                            motive
                                                            .app(eq_tm_1)
                                                            .app(elim)
                                                            .into_ty()
                                                        }),
                                                    )
                                                }),
                                            )
                                        }),
                                    )
                                }),
                            )
                        }),
                    )
                }),
            ),
            tm: Tm::func(Scope::make(0, |_eq_ty| {
                Tm::func(Scope::make(1, |_eq_tm_0| {
                    Tm::func(Scope::make(2, |motive| {
                        Tm::func(Scope::make(3, |inhab| {
                            Tm::func(Scope::make(4, |_eq_tm_1| {
                                Tm::func(Scope::make(5, |elim| {
                                    elim
                                    .cong(
                                        Scope::make(6, |eq_tm_1| {
                                            Scope::make(7, |elim| {
                                                motive
                                                .app(eq_tm_1)
                                                .app(elim)
                                                .into_ty()
                                            })
                                        }),
                                        inhab,
                                    )
                                }))
                            }))
                        }))
                    }))
                }))
            })),
        });
        */

        builtins.push(Builtin {
            name: "fold",
            ty: Ty::pi(
                Name::from("Motive"),
                Ty::pi(
                    Name::from("elim"),
                    Ty::nat(),
                    Scope::constant(Ty::universe()),
                ),
                Scope::make(0, |motive| {
                    Ty::pi(
                        Name::from("on_zero"),
                        motive.clone().app(Tm::zero()).into_ty(),
                        Scope::make(1, |_zero_inhab| {
                            Ty::pi(
                                Name::from("on_succ"),
                                Ty::pi(
                                    Name::from("elim"),
                                    Ty::nat(),
                                    Scope::make(2, |elim| {
                                        Ty::pi(
                                            Name::from("state"),
                                            motive.clone().app(elim.clone()).into_ty(),
                                            Scope::make(3, |_state| {
                                                motive.clone().app(elim.succs(1usize)).into_ty()
                                            }),
                                        )
                                    }),
                                ),
                                Scope::make(2, |_succ_inhab| {
                                    Ty::pi(
                                        Name::from("elim"),
                                        Ty::nat(),
                                        Scope::make(3, |elim| {
                                            motive.app(elim).into_ty()
                                        }),
                                    )
                                }),
                            )
                        }),
                    )
                }),
            ),
            tm: Tm::func(Scope::make(0, |motive| {
                Tm::func(Scope::make(1, |zero_inhab| {
                    Tm::func(Scope::make(2, |succ_inhab| {
                        Tm::func(Scope::make(3, |elim| {
                            elim
                            .fold(
                                Scope::make(4, |elim| {
                                    motive.clone().app(elim).into_ty()
                                }),
                                zero_inhab,
                                Scope::make(4, |elim| {
                                    Scope::make(5, |state| {
                                        succ_inhab.app(elim).app(state)
                                    })
                                }),
                            )
                        }))
                    }))
                }))
            })),
        });

        builtins.push(Builtin {
            name: "explode",
            ty: Ty::pi(
                Name::from("Motive"),
                Ty::pi(
                    Name::from("elim"),
                    Ty::never(),
                    Scope::constant(Ty::universe()),
                ),
                Scope::make(0, |motive| {
                    Ty::pi(
                        Name::from("elim"),
                        Ty::never(),
                        Scope::make(1, |elim| {
                            motive.app(elim).into_ty()
                        }),
                    )
                }),
            ),
            tm: Tm::func(Scope::make(0, |motive| {
                Tm::func(Scope::make(1, |elim| {
                    elim
                    .explode(
                        Scope::make(2, |elim| {
                            motive.app(elim).into_ty()
                        })
                    )
                }))
            })),
        });

        builtins.push(Builtin {
            name: "case",
            ty: Ty::pi(
                Name::from("lhs_name"),
                Ty::name(),
                Scope::make(0, |lhs_name| {
                    let lhs_name = lhs_name.into_name();
                    Ty::pi(
                        Name::from("Lhs"),
                        Ty::universe(),
                        Scope::make(1, |lhs_ty| {
                            let lhs_ty = lhs_ty.into_ty();
                            Ty::pi(
                                Name::from("Rhs"),
                                Ty::universe(),
                                Scope::make(2, |rhs_ty| {
                                    let rhs_ty = rhs_ty.into_ty();
                                    let sum_ty = Ty::sum(lhs_name, lhs_ty.clone(), rhs_ty.clone());
                                    Ty::pi(
                                        Name::from("Motive"),
                                        Ty::pi(
                                            Name::from("elim"),
                                            sum_ty.clone(),
                                            Scope::constant(Ty::universe()),
                                        ),
                                        Scope::make(3, |motive| {
                                            Ty::pi(
                                                Name::from("on_lhs"),
                                                Ty::pi(
                                                    Name::from("lhs"),
                                                    lhs_ty,
                                                    Scope::make(4, |lhs| {
                                                        motive
                                                        .clone()
                                                        .app(lhs.inj_lhs())
                                                        .into_ty()
                                                    }),
                                                ),
                                                Scope::make(4, |_lhs_inhab| {
                                                    Ty::pi(
                                                        Name::from("on_rhs"),
                                                        Ty::pi(
                                                            Name::from("rhs"),
                                                            rhs_ty,
                                                            Scope::make(5, |rhs| {
                                                                motive
                                                                .clone()
                                                                .app(rhs.inj_rhs())
                                                                .into_ty()
                                                            }),
                                                        ),
                                                        Scope::make(5, |_rhs_inhab| {
                                                            Ty::pi(
                                                                Name::from("elim"),
                                                                sum_ty,
                                                                Scope::make(6, |elim| {
                                                                    motive.app(elim).into_ty()
                                                                }),
                                                            )
                                                        }),
                                                    )
                                                }),
                                            )
                                        }),
                                    )
                                }),
                            )
                        }),
                    )
                }),
            ),
            tm: Tm::func(Scope::make(0, |_lhs_name| {
                Tm::func(Scope::make(1, |_lhs_ty| {
                    Tm::func(Scope::make(2, |_rhs_ty| {
                        Tm::func(Scope::make(3, |motive| {
                            Tm::func(Scope::make(4, |lhs_inhab| {
                                Tm::func(Scope::make(5, |rhs_inhab| {
                                    Tm::func(Scope::make(6, |elim| {
                                        elim
                                        .case(
                                            Scope::make(7, |elim| {
                                                motive.app(elim).into_ty()
                                            }),
                                            Scope::make(7, |lhs| {
                                                lhs_inhab.app(lhs)
                                            }),
                                            Scope::make(7, |rhs| {
                                                rhs_inhab.app(rhs)
                                            }),
                                        )
                                    }))
                                }))
                            }))
                        }))
                    }))
                }))
            })),
        });

        /*
        let ctx_len = 0;
        builtins.push(Builtin {
            name: "transitivity",
            ty: pi!(ctx_len @
                (
                    Ty: Ty::universe(),
                    val_0: Ty.clone(),
                    val_1: Ty.clone(),
                    val_2: Ty.clone(),
                    eq_0: Ty::obs_equal(Ty.clone(), val_0.clone(), val_1.clone()),
                    eq_1: Ty::obs_equal(Ty.clone(), val_1, val_2.clone()),
                ) -> Ty::obs_equal(
                    Ty, val_0, val_2,
                )
            ),
        });
        */

        builtins.push(Builtin {
            name: "transitivity",
            ty: Ty::pi(
                Name::from("Ty"),
                Ty::universe(),
                Scope::make(0, |ty| {
                    let ty = ty.into_ty();
                    Ty::pi(
                        Name::from("val_0"),
                        ty.clone(),
                        Scope::make(1, |tm_0| {
                            Ty::pi(
                                Name::from("val_1"),
                                ty.clone(),
                                Scope::make(2, |tm_1| {
                                    Ty::pi(
                                        Name::from("val_2"),
                                        ty.clone(),
                                        Scope::make(3, |tm_2| {
                                            Ty::pi(
                                                Name::from("eq_0"),
                                                Ty::obs_equal(
                                                    ty.clone(),
                                                    tm_0.clone(),
                                                    tm_1.clone(),
                                                ),
                                                Scope::constant(
                                                    Ty::pi(
                                                        Name::from("eq_1"),
                                                        Ty::obs_equal(
                                                            ty.clone(),
                                                            tm_1,
                                                            tm_2.clone(),
                                                        ),
                                                        Scope::constant(
                                                            Ty::obs_equal(
                                                                ty,
                                                                tm_0,
                                                                tm_2,
                                                            )
                                                        ),
                                                    )
                                                ),
                                            )
                                        }),
                                    )
                                }),
                            )
                        }),
                    )
                }),
            ),
            tm: Tm::func(Scope::make(0, |ty| {
                let ty = ty.into_ty();
                Tm::func(Scope::make(1, |tm_0| {
                    Tm::func(Scope::make(2, |_tm_1| {
                        Tm::func(Scope::make(3, |tm_2| {
                            Tm::func(Scope::make(4, |eq_0| {
                                eq_0
                                .obs_cong(
                                    Scope::make(5, |tm_1| {
                                        Scope::make(6, |_eq_0| {
                                            Ty::pi(
                                                Name::from("eq_1"),
                                                Ty::obs_equal(
                                                    ty.clone(),
                                                    tm_1,
                                                    tm_2.clone(),
                                                ),
                                                Scope::make(7, |_eq_1| {
                                                    Ty::obs_equal(
                                                        ty,
                                                        tm_0,
                                                        tm_2,
                                                    )
                                                }),
                                            )
                                        })
                                    }),
                                    Tm::func(Scope::make(5, |eq_1| eq_1)),
                                )
                            }))
                        }))
                    }))
                }))
            })),
        });

        builtins
    };
}

