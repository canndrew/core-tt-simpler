use crate::priv_prelude::*;

#[derive(Contextual)]
pub struct Checked<T> {
    constraint_ty: Ty,
    scope: Scope<T>,
}

impl<T: Contextual + Bindable> Bindable for Checked<T> {
    fn capture_subst(
        self,
        subst: Subst,
    ) -> Checked<T> {
        let Checked { constraint_ty, scope } = self;
        let constraint_ty = constraint_ty.capture_subst(subst.clone());
        let scope = scope.capture_subst(subst);
        Checked { constraint_ty, scope }
    }
}

impl<T> Checked<T> {
    pub fn pure(val: T) -> Checked<T>
    where
        T: Contextual,
    {
        let constraint_ty = Ty::unit();
        let scope = Scope::constant(val);
        Checked { constraint_ty, scope }
    }

    pub fn map<U>(
        self,
        ch: &mut CheckCtx,
        func: impl FnOnce(&mut CheckCtx, Tm, T) -> U,
    ) -> Checked<U>
    where
        T: Contextual + Bindable,
        U: Contextual,
    {
        let Checked { constraint_ty, scope } = self;
        let scope = ch.with_anon_var(|ch, constraint| {
            func(ch, constraint.clone(), scope.bind(constraint))
        });
        Checked { constraint_ty, scope }
    }

    pub fn and_then<U>(
        self,
        ch: &mut CheckCtx,
        func: impl FnOnce(&mut CheckCtx, Tm, T) -> Checked<U>,
    ) -> Checked<U>
    where
        T: Contextual + Bindable,
        U: Contextual + Bindable,
    {
        let Checked { constraint_ty: outer_constraint_ty, scope } = self;
        let (inner_constraint_ty, scope) = {
            ch
            .with_anon_var(|ch, outer_constraint| {
                let Checked {
                    constraint_ty: inner_constraint_ty, scope,
                } = func(ch, outer_constraint.clone(), scope.bind(outer_constraint));
                (inner_constraint_ty, scope)
            })
            .lift_tuple()
        };

        let ctx_len = ch.ctx_len();
        let mut outer_parts = Vec::new();
        let mut outer = outer_constraint_ty;
        loop {
            match Arc::unwrap_or_clone(outer.try_reduce_to_form().unwrap().into_inner()) {
                FormKind::Unit => break,
                FormKind::Sigma { head_name, head_ty, tail_ty } => {
                    outer = tail_ty.into_inner(ctx_len + outer_parts.len());
                    outer_parts.push((head_name, head_ty));
                },
                _ => unreachable!(),
            }
        }
        let num_outer_parts = outer_parts.len();

        let constraint_ty = {
            let mut outer_constraint = Tm::unit();
            for offset in (0..num_outer_parts).rev() {
                outer_constraint = Tm::pair(Tm::var(ctx_len + offset), outer_constraint);
            }

            let mut constraint_ty = inner_constraint_ty.bind(outer_constraint);
            for (offset, (head_name, head_ty)) in outer_parts.into_iter().enumerate().rev() {
                let tail_ty = Scope::new(ctx_len + offset, constraint_ty);
                constraint_ty = Ty::sigma(head_name, head_ty, tail_ty);
            }
            constraint_ty
        };

        let scope = {
            let mut outer_constraint = Tm::unit();
            for offset in (0..num_outer_parts).rev() {
                let head_tm = {
                    let mut head_tm = Tm::var(ctx_len);
                    for _ in 0..offset {
                        head_tm = head_tm.proj_tail();
                    }
                    head_tm.proj_head()
                };
                outer_constraint = Tm::pair(head_tm, outer_constraint);
            }
            let mut inner_constraint = Tm::var(ctx_len);
            for _ in 0..num_outer_parts {
                inner_constraint = inner_constraint.proj_tail();
            }
            Scope::new(ctx_len, scope.bind(outer_constraint).bind(inner_constraint))
        };

        Checked { constraint_ty, scope }
    }

    pub fn group(self, meta: MetaTag) -> Checked<T>
    where
        T: Contextual + Bindable,
    {
        let ctx_len = self.ctx_len();
        let Checked { constraint_ty, scope } = self;
        let constraint_ty = Ty::sigma(
            meta.into(),
            constraint_ty,
            Scope::constant(Ty::unit()),
        );
        let scope = Scope::make(ctx_len, |constraint| {
            scope.bind(constraint.proj_head())
        });
        Checked { constraint_ty, scope }
    }
}

impl Checked<Tm> {
    pub fn assume(
        meta: MetaTag,
        ty: Ty,
    ) -> Checked<Tm> {
        let constraint_ty = Ty::sigma(
            meta.into(),
            ty,
            Scope::constant(Ty::unit()),
        );
        let scope = Scope::new(0, Tm::var(0).proj_head());
        Checked { constraint_ty, scope }
    }
}

impl Checked<Ty> {
    pub fn assume_ty(
        meta: MetaTag,
    ) -> Checked<Ty> {
        let constraint_ty = Ty::sigma(
            meta.into(),
            Ty::universe(),
            Scope::constant(Ty::unit()),
        );
        let scope = Scope::new(0, Tm::var(0).proj_head().into_ty());
        Checked { constraint_ty, scope }
    }

    pub fn into_ty_tm(self) -> Checked<(Ty, Tm)> {
        let Checked { constraint_ty, scope } = self;
        let scope = scope.map_without_capture(|ty| (Ty::universe(), ty.into_tm()));
        Checked { constraint_ty, scope }
    }
}

impl Checked<(Ty, Tm)> {
    pub fn cast(
        ch: &mut CheckCtx,
        tm_name: Name,
        meta: MetaTag,
        from_ty: Ty,
        into_ty: Ty,
        tm: Tm,
    ) -> Checked<Tm> {
        Checked::assume(
            meta,
            Ty::equal(Ty::universe(), from_ty.clone().into_tm(), into_ty.into_tm()),
        )
        .map(ch, |ch, _, tys_eq| {
            tys_eq
            .cong(
                Scope::make(ch.ctx_len(), |into_ty| {
                    Scope::constant(
                        Ty::pi(tm_name, from_ty, Scope::constant(into_ty.into_ty()))
                    )
                }),
                Tm::func(Scope::id()),
            )
            .app(tm)
        })
    }

    pub fn cast_to_ty(
        ch: &mut CheckCtx,
        tm_name: Name,
        meta: MetaTag,
        from_ty: Ty,
        tm: Tm,
    ) -> Checked<Ty> {
        Checked::cast(ch, tm_name, meta, from_ty, Ty::universe(), tm)
        .map(ch, |_, _, ty| ty.into_ty())
    }
}

impl<T: Contextual + Bindable> Scope<Checked<T>> {
    pub fn group_and_lift_checked(
        self,
        var_name: Name,
        var_ty: Ty,
        meta: MetaTag,
    ) -> Checked<Scope<T>> {
        let ctx_len = self.ctx_len();
        let (constraint_ty, scope) = self.map_multi(ctx_len, |_, checked| {
            let Checked { constraint_ty, scope } = checked;
            (constraint_ty, scope)
        });
        let constraint_ty = Ty::sigma(
            meta.into(),
            Ty::pi(
                var_name,
                var_ty,
                constraint_ty,
            ),
            Scope::constant(Ty::unit()),
        );
        let scope = Scope::make(ctx_len, |grouped_func| {
            scope.map(ctx_len + 1, |var_tm, inner_scope| {
                inner_scope.bind(grouped_func.proj_head().app(var_tm))
            })
        });
        Checked { constraint_ty, scope }
    }
}

