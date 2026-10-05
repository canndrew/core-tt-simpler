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
                                            Ty::obs_equal(
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
                                        .app(Tm::proof())
                                        .into_ty(),
                                        Scope::make(3, |_inhab| {
                                            Ty::pi(
                                                Name::from("val_1"),
                                                eq_ty.clone(),
                                                Scope::make(4, |eq_tm_1| {
                                                    Ty::pi(
                                                        Name::from("elim"),
                                                        Ty::obs_equal(
                                                            eq_ty,
                                                            eq_tm_0,
                                                            eq_tm_1.clone(),
                                                        ),
                                                        Scope::make(5, |_elim| {
                                                            motive
                                                            .app(eq_tm_1)
                                                            .app(Tm::proof())
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
                Tm::func(Scope::make(1, |eq_tm_0| {
                    Tm::func(Scope::make(2, |motive| {
                        Tm::func(Scope::make(3, |inhab| {
                            Tm::func(Scope::make(4, |eq_tm_1| {
                                Tm::func(Scope::make(5, |elim| {
                                    Tm::cast(
                                        motive.clone().app(eq_tm_0).app(Tm::proof()).into_ty(),
                                        motive.app(eq_tm_1).app(elim).into_ty(),
                                        inhab,
                                    )
                                }))
                            }))
                        }))
                    }))
                }))
            })),
        });

        builtins.push(Builtin {
            name: "cast",
            ty: Ty::pi(
                Name::from("From"),
                Ty::universe(),
                Scope::make(0, |from_ty| {
                    let from_ty = from_ty.into_ty();
                    Ty::pi(
                        Name::from("Into"),
                        Ty::universe(),
                        Scope::make(1, |into_ty| {
                            let into_ty = into_ty.into_ty();
                            Ty::pi(
                                Name::from("elim"),
                                Ty::obs_equal(
                                    Ty::universe(),
                                    from_ty.clone().into_tm(),
                                    into_ty.clone().into_tm(),
                                ),
                                Scope::constant(
                                    Ty::pi(
                                        Name::from("val"),
                                        from_ty,
                                        Scope::constant(into_ty),
                                    )
                                ),
                            )
                        }),
                    )
                }),
            ),
            tm: Tm::func(Scope::make(0, |from_ty| {
                Tm::func(Scope::make(1, |into_ty| {
                    Tm::func(Scope::constant(
                        Tm::func(Scope::make(3, |tm| {
                            Tm::cast(from_ty.into_ty(), into_ty.into_ty(), tm)
                        }))
                    ))
                }))
            }))
        });

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
                Tm::func(Scope::constant(
                    Tm::explode(
                        Scope::make(2, |elim| {
                            motive.app(elim).into_ty()
                        })
                    )
                ))
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
            tm: Tm::func(Scope::make(0, |lhs_name| {
                Tm::func(Scope::make(1, |_lhs_ty| {
                    Tm::func(Scope::make(2, |_rhs_ty| {
                        Tm::func(Scope::make(3, |motive| {
                            Tm::func(Scope::make(4, |lhs_inhab| {
                                Tm::func(Scope::make(5, |rhs_inhab| {
                                    Tm::func(Scope::make(6, |elim| {
                                        elim
                                        .case(
                                            lhs_name.into_name(),
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

        builtins
    };
}

// TODO: use an IndexMap
pub fn get_index(name: &'static str) -> usize {
    for (index, builtin) in BUILTINS.iter().enumerate() {
        if name == builtin.name {
            return index;
        }
    }
    panic!("no such builtin")
}

