use crate::priv_prelude::*;

pub type Ty = Wrapper<core_tt::Ty>;

impl Ty {
    pub fn into_tm(self) -> Tm {
        let (ty, ctx_params) = self.unwrap_parts();
        let ctx_params = ctx_params.map(|_, (ctx, ())| {
            let ty = core_tt::Ty::universe();
            (ctx, ty)
        });
        let tm = ty.into_tm();
        Wrapper::new(tm, ctx_params)
    }

    pub fn name() -> Ty {
        Wrapper::new(core_tt::Ty::name(), DebugOnly::new(|_| (Ctx::root(), ())))
    }

    pub fn universe() -> Ty {
        Wrapper::new(core_tt::Ty::universe(), DebugOnly::new(|_| (Ctx::root(), ())))
    }

    pub fn nat() -> Ty {
        Wrapper::new(core_tt::Ty::nat(), DebugOnly::new(|_| (Ctx::root(), ())))
    }

    pub fn never() -> Ty {
        Wrapper::new(core_tt::Ty::never(), DebugOnly::new(|_| (Ctx::root(), ())))
    }

    pub fn unit() -> Ty {
        Wrapper::new(core_tt::Ty::unit(), DebugOnly::new(|_| (Ctx::root(), ())))
    }

    pub fn sum(
        lhs_name: Name,
        lhs_ty: Ty,
        rhs_ty: Ty,
    ) -> Ty {
        let ((lhs_name, lhs_ty, rhs_ty), ctx_params) = {
            (lhs_name, lhs_ty, rhs_ty)
            .merge(|_, _, ctx, _| (ctx, ()))
        };
        let ty = core_tt::Ty::sum(lhs_name, lhs_ty, rhs_ty);
        Wrapper::new(ty, ctx_params)
    }

    pub fn sigma(
        head_name: Name,
        head_ty: Ty,
        tail_ty: Scope<Ty>,
    ) -> Ty {
        let ((head_name, head_ty, tail_ty), ctx_params) = {
            (head_name, head_ty, tail_ty)
            .merge(|_, (_, head_ty, _), ctx, (_, _, (tail_head_ty, _))| {
                Unify::unify(head_ty.clone(), tail_head_ty).unwrap();
                (ctx, ())
            })
        };
        let ty = core_tt::Ty::sigma(head_name, head_ty, tail_ty);
        Wrapper::new(ty, ctx_params)
    }

    pub fn equal(
        eq_ty: Ty,
        eq_tm_0: Tm,
        eq_tm_1: Tm,
    ) -> Ty {
        let ((eq_ty, eq_tm_0, eq_tm_1), ctx_params) = {
            (eq_ty, eq_tm_0, eq_tm_1)
            .merge(|_, (eq_ty, _, _), ctx, ((), eq_ty_0, eq_ty_1)| {
                Unify::unify(
                    eq_ty.clone(),
                    Unify::unify(eq_ty_0, eq_ty_1).unwrap(),
                ).unwrap();
                (ctx, ())
            })
        };
        let ty = core_tt::Ty::obs_equal(eq_ty, eq_tm_0, eq_tm_1);
        Wrapper::new(ty, ctx_params)
    }

    pub fn as_name(self) -> Option<()> {
        self.into_wrapped().as_name()
    }

    pub fn as_universe(self) -> Option<()> {
        self.into_wrapped().as_universe()
    }

    pub fn as_nat(self) -> Option<()> {
        self.into_wrapped().as_nat()
    }

    pub fn as_never(self) -> Option<()> {
        self.into_wrapped().as_never()
    }

    pub fn as_unit(self) -> Option<()> {
        self.into_wrapped().as_unit()
    }

    pub fn as_sum(self) -> Option<(Name, Ty, Ty)> {
        let (ty, ctx_params) = self.unwrap_parts();
        let (lhs_name, lhs_ty, rhs_ty) = ty.as_sum()?;
        let lhs_name = Wrapper::new(lhs_name, ctx_params.clone());
        let lhs_ty = Wrapper::new(lhs_ty, ctx_params.clone());
        let rhs_ty = Wrapper::new(rhs_ty, ctx_params);
        Some((lhs_name, lhs_ty, rhs_ty))
    }

    pub fn as_sigma(self) -> Option<(Name, Ty, Scope<Ty>)> {
        let (ty, ctx_params) = self.unwrap_parts();
        let (head_name, head_ty, tail_ty) = ty.as_sigma()?;
        let head_name = Wrapper::new(head_name, ctx_params.clone());
        let tail_ty = {
            let ctx_params = ctx_params.as_ref().map(|_, (ctx, ())| {
                (ctx.clone(), (head_ty.clone(), core_tt::Scope::constant(())))
            });
            Wrapper::new(tail_ty, ctx_params)
        };
        let head_ty = Wrapper::new(head_ty, ctx_params);
        Some((head_name, head_ty, tail_ty))
    }

    pub fn as_pi(self) -> Option<(Name, Ty, Scope<Ty>)> {
        let (ty, ctx_params) = self.unwrap_parts();
        let (arg_name, arg_ty, res_ty) = ty.as_pi()?;
        let arg_name = Wrapper::new(arg_name, ctx_params.clone());
        let res_ty = {
            let ctx_params = ctx_params.as_ref().map(|_, (ctx, ())| {
                (ctx.clone(), (arg_ty.clone(), core_tt::Scope::constant(())))
            });
            Wrapper::new(res_ty, ctx_params)
        };
        let arg_ty = Wrapper::new(arg_ty, ctx_params);
        Some((arg_name, arg_ty, res_ty))
    }

    pub fn as_equal(self) -> Option<(Ty, Tm, Tm)> {
        let (ty, ctx_params) = self.unwrap_parts();
        let (eq_ty, eq_tm_0, eq_tm_1) = ty.as_equal()?;
        let eq_tm_0 = Wrapper::new(
            eq_tm_0,
            ctx_params.as_ref().map(|_, (ctx, ())| (ctx.clone(), eq_ty.clone())),
        );
        let eq_tm_1 = Wrapper::new(
            eq_tm_1,
            ctx_params.as_ref().map(|_, (ctx, ())| (ctx.clone(), eq_ty.clone())),
        );
        let eq_ty = Wrapper::new(eq_ty, ctx_params);
        Some((eq_ty, eq_tm_0, eq_tm_1))
    }
}

