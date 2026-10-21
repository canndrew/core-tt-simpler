use crate::priv_prelude::*;

#[derive(Clone)]
pub struct CtxCons {
    ctx: Ctx,
    ty: core_tt::Ty,
}

#[derive(Clone)]
pub struct Ctx {
    len: usize,
    cons_opt: Option<Arc<CtxCons>>,
}

#[derive(Clone)]
pub struct PartialCtx {
    len: usize,
    cons_opt: DebugOnly<Option<Arc<CtxCons>>>,
}

impl Ctx {
    const ROOT: Ctx = Ctx { len: 0, cons_opt: None };

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_root(&self) -> bool {
        self.len == 0
    }

    pub fn root() -> Ctx {
        Ctx::ROOT.clone()
    }

    pub fn arc_eq(
        ctx_0: &Ctx,
        ctx_1: &Ctx,
    ) -> bool {
        let Ctx { len: len_0, cons_opt: cons_opt_0 } = ctx_0;
        let Ctx { len: len_1, cons_opt: cons_opt_1 } = ctx_1;
        len_0 == len_1 && {
            match (cons_opt_0, cons_opt_1) {
                (None, Some(_)) | (Some(_), None) => unreachable!(),
                (None, None) => {
                    debug_assert_eq!(*len_0, 0);
                    true
                },
                (Some(cons_0), Some(cons_1)) => {
                    Arc::ptr_eq(cons_0, cons_1)
                },
            }
        }
    }

    pub fn nth_parent(&self, n: usize) -> &Ctx {
        let mut ret = self;
        for _ in 0..n {
            ret = &ret.cons_opt.as_ref().unwrap().ctx;
        }
        ret
    }

    pub fn is_subctx_of(&self, super_ctx: &Ctx) -> bool {
        if self.len == 0 {
            return true;
        }

        let Some(diff) = super_ctx.len.checked_sub(self.len) else {
            return false;
        };
        Ctx::arc_eq(super_ctx.nth_parent(diff), self)
    }

    pub fn push(self, var_ty: Ty) -> Ctx {
        let ctx_len = self.len();
        let (var_ty, ctx_params) = var_ty.unwrap_parts();
        ctx_params.map(|_, (var_ctx, ())| {
            assert!(var_ctx.is_subctx_of(&self));
        });
        let len = ctx_len + 1;
        let cons_opt = Some(Arc::new(CtxCons {
            ctx: self,
            ty: var_ty,
        }));
        Ctx { len, cons_opt }
    }

    pub fn pop(self) -> Option<(Ctx, Ty)> {
        let Ctx { len: _, cons_opt } = self;
        let cons = cons_opt?;
        let CtxCons { ctx, ty } = Arc::unwrap_or_clone(cons);
        let ty = Wrapper::new(ty, DebugOnly::new(|_| (ctx.clone(), ())));
        Some((ctx, ty))
    }

    pub fn parent(&self) -> Option<Ctx> {
        let Ctx { len: _, cons_opt } = self;
        let cons = cons_opt.as_ref()?;
        Some(cons.ctx.clone())
    }

    pub fn as_var_ty_vec(&self) -> Vec<core_tt::Ty> {
        fn recurse(
            ctx: &Ctx,
            acc: &mut Vec<core_tt::Ty>,
        ) {
            if let Some(cons) = &ctx.cons_opt {
                recurse(&cons.ctx, acc);
                acc.push(cons.ty.clone());
            }
        }

        let mut acc = Vec::with_capacity(self.len());
        recurse(self, &mut acc);
        acc
    }

    pub fn common_super_ctx_2_ref<'c>(
        ctx_0: &'c Ctx,
        ctx_1: &'c Ctx,
    ) -> &'c Ctx {
        match ctx_0.len.cmp(&ctx_1.len) {
            cmp::Ordering::Less => {
                let diff = ctx_1.len.strict_sub(ctx_0.len);
                assert!(Ctx::arc_eq(&ctx_0, ctx_1.nth_parent(diff)));
                ctx_1
            },
            cmp::Ordering::Equal => {
                assert!(Ctx::arc_eq(&ctx_0, &ctx_1));
                ctx_0
            },
            cmp::Ordering::Greater => {
                let diff = ctx_0.len.strict_sub(ctx_1.len);
                assert!(Ctx::arc_eq(ctx_0.nth_parent(diff), &ctx_1));
                ctx_1
            },
        }
    }

    pub fn common_super_ctx_ref<'c>(ctxs: impl IntoIterator<Item = &'c Ctx>) -> &'c Ctx {
        let mut common_ctx = &Ctx::ROOT;
        for ctx in ctxs {
            common_ctx = Ctx::common_super_ctx_2_ref(common_ctx, ctx);
        }
        common_ctx
    }

    pub fn common_super_ctx_2(
        ctx_0: Ctx,
        ctx_1: Ctx,
    ) -> Ctx {
        match ctx_0.len.cmp(&ctx_1.len) {
            cmp::Ordering::Less => {
                let diff = ctx_1.len.strict_sub(ctx_0.len);
                assert!(Ctx::arc_eq(&ctx_0, ctx_1.nth_parent(diff)));
                ctx_1
            },
            cmp::Ordering::Equal => {
                assert!(Ctx::arc_eq(&ctx_0, &ctx_1));
                ctx_0
            },
            cmp::Ordering::Greater => {
                let diff = ctx_0.len.strict_sub(ctx_1.len);
                assert!(Ctx::arc_eq(ctx_0.nth_parent(diff), &ctx_1));
                ctx_1
            },
        }
    }

    pub fn common_super_ctx(ctxs: impl IntoIterator<Item = Ctx>) -> Ctx {
        let mut common_ctx = Ctx::ROOT;
        for ctx in ctxs {
            common_ctx = Ctx::common_super_ctx_2(common_ctx, ctx);
        }
        common_ctx
    }

    /*
    pub fn get_ty(&self, index: usize) -> Ty {
        let diff = self.len.strict_sub(index.strict_add(1));
        let ctx = self.nth_parent(diff);
        let cons = ctx.cons_opt.as_ref().unwrap();
        let ty = cons.ty.clone();
        let ctx_params = DebugOnly::new(|_| (cons.ctx.clone(), ()));
        Wrapper::new(ty, ctx_params)
    }
    */
}

impl PartialCtx {
    pub fn root() -> PartialCtx {
        PartialCtx {
            len: 0,
            cons_opt: DebugOnly::new(|_| None),
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn unlock(self, lock: DebugLock) -> Ctx {
        let PartialCtx { len, cons_opt } = self;
        let cons_opt = cons_opt.unlock(lock);
        Ctx { len, cons_opt }
    }

    pub fn var(&self, index: usize) -> Tm {
        let ctx_params = DebugOnly::new(|lock| {
            let diff = self.len.strict_sub(index.strict_add(1));
            let ctx = self.clone().unlock(lock);
            let ctx = ctx.nth_parent(diff).clone();
            let ty = ctx.cons_opt.as_ref().unwrap().ty.clone();
            (ctx, ty)
        });
        let tm = core_tt::Tm::var(index);
        Wrapper::new(tm, ctx_params)
    }

    /*
    pub fn new_scope<T>(
        &self,
        var_ty: DebugOnly<Ty>,
        inner: Wrapper<T>,
    ) -> Scope<T> {
        let (inner, ctx_params) = inner.unwrap_parts();
        let ctx_params = ctx_params.map(|lock, (ctx, params)| {
            let var_ty = var_ty.unlock(lock);
            let (var_ty, var_ty_ctx_params) = var_ty.unwrap_parts();
            let (var_ty_ctx, ()) = var_ty_ctx_params.unlock(lock);
            assert!(var_ty_ctx.is_subctx_of(&ctx));
            let params = core_tt::Scope::new(ctx.len(), params);
            (ctx, (var_ty, params))
        });
        let scope = core_tt::Scope::new(self.len(), 
    }
    */

    pub fn make_scope<T>(
        &self,
        var_ty: DebugOnly<Ty>,
        func: impl FnOnce(Tm) -> Wrapper<T>,
    ) -> Scope<Wrapper<T>>
    where
        T: WellFormed<Params: Contextual>,
        T: Contextual,
    {
        let sub_ctx = var_ty.map(|lock, var_ty| {
            let ctx = self.clone().unlock(lock);
            ctx.push(var_ty)
        });
        let scope = core_tt::Scope::make(
            self.len(),
            |tm| {
                let ctx_params = sub_ctx.as_ref().map(|_, sub_ctx| {
                    let ty = sub_ctx.cons_opt.as_ref().unwrap().ty.clone();
                    (sub_ctx.clone(), ty)
                });
                let tm = Wrapper::new(tm, ctx_params);
                let inner = func(tm);
                let (inner, inner_ctx_params) = inner.unwrap_parts();
                let inner_params = inner_ctx_params.map(|lock, (inner_ctx, params)| {
                    let sub_ctx = sub_ctx.as_ref().unlock(lock);
                    assert!(inner_ctx.is_subctx_of(&sub_ctx));
                    params
                });
                (inner, inner_params)
            },
        );
        let (scope, params) = scope.lift_tuple();
        let ctx_params = sub_ctx.map(|lock, sub_ctx| {
            let CtxCons { ctx, ty } = Arc::unwrap_or_clone(sub_ctx.cons_opt.unwrap());
            let params = params.map_without_capture(|params| params.unlock(lock));
            (ctx, (ty, params))
        });
        Wrapper::new(scope, ctx_params)
    }
}

