use crate::priv_prelude::*;

pub struct CheckCtx {
    ctx_len: usize,
    var_names_tys: Vec<(Name, Ty, usize)>,
}

impl CheckCtx {
    pub fn ctx_len(&self) -> usize {
        self.ctx_len
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
        let var_names_tys_len = self.var_names_tys.len();
        let ctx_len = self.ctx_len;

        self.var_names_tys.push((var_name, var_ty, ctx_len));
        let var_tm = Tm::var(ctx_len);
        self.ctx_len += 1;
        let ret = func(self, var_tm);
        self.var_names_tys.truncate(var_names_tys_len);
        self.ctx_len = ctx_len;
        Scope::new(ctx_len, ret)
    }

    pub fn with_anon_var<T>(
        &mut self,
        func: impl FnOnce(&mut CheckCtx, Tm) -> T,
    ) -> Scope<T>
    where
        T: Contextual,
    {
        let ctx_len = self.ctx_len;
        let scope = Scope::make(self.ctx_len, |var_tm| {
            self.ctx_len += 1;
            func(self, var_tm)
        });
        self.ctx_len = ctx_len;
        scope
    }

    pub fn lookup_var(&self, name: &Name) -> Option<(Ty, usize)> {
        let name_ctx_len = name.ctx_len();
        let mut iter = self.var_names_tys.iter().rev();
        loop {
            let Some((var_name, var_ty, index)) = iter.next() else {
                break None;
            };
            if *index < name_ctx_len {
                break None;
            }
            if Unify::unify(
                name.clone(),
                var_name.clone(),
            ).is_some() {
                break Some((var_ty.clone(), *index));
            }
        }
    }
}

