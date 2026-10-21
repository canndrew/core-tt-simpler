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
}

