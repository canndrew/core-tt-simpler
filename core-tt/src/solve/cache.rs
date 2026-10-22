use crate::priv_prelude::*;

pub struct SimplifyCache {
    simple_forms: HashMap<*const FormKind, Usages>,
    simple_neutrals: HashMap<*const NeutralKind, Usages>,
}

impl SimplifyCache {
    pub fn new() -> SimplifyCache {
        SimplifyCache {
            simple_forms: HashMap::new(),
            simple_neutrals: HashMap::new(),
        }
    }

    pub fn insert(&mut self, ty: &ValTy, eliminated: Usages) {
        match ty.weak() {
            TyKind::Form { form } => {
                let form = Arc::downgrade(form);
                let form = std::sync::Weak::into_raw(form);
                self.simple_forms.insert(form, eliminated);
            },
            TyKind::Stuck { stuck } => {
                let neutral = stuck.neutral_ref();
                let neutral = Arc::downgrade(neutral);
                let neutral = std::sync::Weak::into_raw(neutral);
                self.simple_neutrals.insert(neutral, eliminated);
            },
        }
    }

    pub fn get(&self, ty: &ValTy) -> Option<Usages> {
        match ty.weak() {
            TyKind::Form { form } => {
                let form = Arc::as_ptr(form);
                self.simple_forms.get(&form).cloned()
            },
            TyKind::Stuck { stuck } => {
                let neutral = stuck.neutral_ref();
                let neutral = Arc::as_ptr(neutral);
                self.simple_neutrals.get(&neutral).cloned()
            },
        }
    }
}

impl Drop for SimplifyCache {
    fn drop(&mut self) {
        for form in mem::take(&mut self.simple_forms).into_keys() {
            let form = unsafe { std::sync::Weak::from_raw(form) };
            drop(form);
        }
        for neutral in mem::take(&mut self.simple_neutrals).into_keys() {
            let neutral = unsafe { std::sync::Weak::from_raw(neutral) };
            drop(neutral);
        }
    }
}

/*
impl Usages {
    fn filter_ctx(
        &self,
        ctx: &[Ty],
    ) -> Vec<Ty> {
        let mut usages = self.clone();
        let mut var_tys = Vec::new();
        for (index, var_ty) in ctx[..self.ctx_len()].iter().enumerate().rev() {
            if usages.get(index) {
                usages.or_assign(var_ty.usages());
                var_tys.push(var_ty.clone());
            }
        }

        var_tys.reverse();
        for var_ty in &mut var_tys {
            var_ty.filter_usages(&usages);
        }
        var_tys
    }
}
*/

