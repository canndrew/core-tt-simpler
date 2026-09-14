use crate::priv_prelude::*;

pub struct CheckCtx {
    var_tys: Vec<Ty>,
    var_names: Vec<(Name, usize)>,
}

impl CheckCtx {
    pub fn new() -> CheckCtx {
        CheckCtx {
            var_tys: Vec::new(),
            var_names: Vec::new(),
        }
    }

    pub fn ctx_len(&self) -> usize {
        self.var_tys.len()
    }

    pub fn with_var<T>(
        &mut self,
        var_name: Name,
        var_ty: Ty,
        func: impl FnOnce(&mut CheckCtx, Tm) -> T,
    ) -> Scope<T>
    where
        T: Contextual,
    {
        let ctx_len = self.var_tys.len();
        let var_names_len = self.var_names.len();
        let scope = Scope::make(ctx_len, |var_tm| {
            self.var_tys.push(var_ty);
            self.var_names.push((var_name, ctx_len));
            func(self, var_tm)
        });
        self.var_tys.truncate(ctx_len);
        self.var_names.truncate(var_names_len);
        scope
    }

    pub fn with_anon_var<T>(
        &mut self,
        var_ty: Ty,
        func: impl FnOnce(&mut CheckCtx, Tm) -> T,
    ) -> Scope<T>
    where
        T: Contextual,
    {
        let ctx_len = self.var_tys.len();
        let scope = Scope::make(ctx_len, |var_tm| {
            self.var_tys.push(var_ty);
            func(self, var_tm)
        });
        self.var_tys.truncate(ctx_len);
        scope
    }

    pub fn lookup_var(&mut self, name: &Name) -> Option<(Ty, usize)> {
        let name_ctx_len = name.ctx_len();
        let mut name_iter = self.var_names.iter().rev();
        loop {
            let Some((var_name, index)) = name_iter.next() else {
                break None;
            };
            if *index < name_ctx_len {
                break None;
            }

            let var_tys_len = self.var_tys.len();
            let resolved = Unify::unify(&mut self.var_tys, (), name.clone(), var_name.clone()).is_some();
            debug_assert_eq!(self.var_tys.len(), var_tys_len);

            if resolved {
                break Some((self.var_tys[*index].clone(), *index));
            }
        }
    }

    pub fn with_builtins<T: Contextual + Substitutable>(
        func: impl FnOnce(&mut CheckCtx) -> T,
    ) -> (Vec<(Name, Ty)>, <T as Substitutable>::Output) {
        let builtins = crate::builtins::BUILTINS.as_slice();
        let mut var_tys = Vec::new();
        let mut var_names = Vec::new();
        let mut var_tms = Vec::new();
        for (index, Builtin { name, ty, tm }) in builtins.iter().enumerate() {
            let name = Name::from(*name);
            var_tys.push(ty.clone());
            var_names.push((Name::from(name), index));
            var_tms.push(tm.clone());
        }

        let mut ch = CheckCtx { var_tys, var_names };
        let ret = func(&mut ch);
        let CheckCtx { var_tys, var_names } = ch;
        debug_assert_eq!(var_tys.len(), builtins.len());
        debug_assert_eq!(var_names.len(), builtins.len());
        debug_assert!(ret.ctx_len() <= builtins.len());

        let mut subst = Subst::from_var_tms(0, var_tms);
        let ret = ret.subst(&mut subst);
        let ctx = var_names.into_iter().map(|(name, _)| name).zip(var_tys).collect();
        (ctx, ret)
    }
}

