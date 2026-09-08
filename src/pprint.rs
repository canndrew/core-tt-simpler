use crate::priv_prelude::*;
use std::fmt::Write;

pub fn pprint<T: Pretty<()> + Contextual>(thing: T) -> String {
    let mut ctx = Vec::new();
    for _ in 0..thing.ctx_len() {
        ctx.push((None, None));
    }
    let mut s = String::new();
    thing.pretty(&mut ctx, 0, &mut s, ());
    s
}

pub trait Pretty<V> {
    fn pretty(
        self,
        ctx: &mut Vec<(Option<Name>, Option<Ty>)>,
        indent: usize,
        s: &mut String,
        vars: V,
    );

    fn is_shallow(&self) -> bool;
}

struct Fmt<T>(T);

impl<T: fmt::Debug> Pretty<()> for Fmt<T> {
    fn pretty(
        self,
        _ctx: &mut Vec<(Option<Name>, Option<Ty>)>,
        indent: usize,
        s: &mut String,
        (): (),
    ) {
        let Fmt(inner) = self;
        let mut buffer = String::new();
        write!(&mut buffer, "{:#?}", inner).unwrap();
        let mut written = false;
        for line in buffer.split('\n') {
            if written {
                s.push('\n');
                for _ in 0..indent {
                    s.push_str("    ");
                }
            }
            s.push_str(line);
            written = true;
        }
    }

    fn is_shallow(&self) -> bool {
        true
    }
}

struct Scoped<V, T>(V, T);

impl<V, T: Pretty<V>> Pretty<()> for Scoped<V, T> {
    fn pretty(
        self,
        ctx: &mut Vec<(Option<Name>, Option<Ty>)>,
        indent: usize,
        s: &mut String,
        (): (),
    ) {
        let Scoped(vars, thing) = self;
        thing.pretty(ctx, indent, s, vars)
    }

    fn is_shallow(&self) -> bool {
        let Scoped(_, thing) = self;
        thing.is_shallow()
    }
}

macro_rules! voom {
    (
        $ctx:ident,
        $indent:ident,
        $s:ident,
        $name:ident ($($($v:expr),+ $(,)?)?)
        $(,)?
    ) => {{
        #[allow(unused)]
        $s.push_str(concat!(stringify!($name), "("));
        if true $($(&& $v.is_shallow())+)? {
            #[allow(unused)]
            let printed = false;
            $($(
                if printed {
                    $s.push_str(", ");
                }
                $v.pretty($ctx, $indent, $s, ());
                #[allow(unused)]
                let printed = true;
            )+)?
        } else {
            $($(
                $s.push('\n');
                for _ in 0..($indent + 1) {
                    $s.push_str("    ");
                }
                $v.pretty($ctx, $indent + 1, $s, ());
                $s.push(',');
            )+)?
            $s.push('\n');
            for _ in 0..$indent {
                $s.push_str("    ");
            }
        }
        $s.push(')');
    }};
}

impl<V, T: Pretty<V> + Contextual + Clone> Pretty<V> for Weaken<T>
where
    // TODO: remove
    T: fmt::Debug,
{
    fn pretty(
        self,
        ctx: &mut Vec<(Option<Name>, Option<Ty>)>,
        indent: usize,
        s: &mut String,
        vars: V,
    ) {
        debug_indent!();
        print_on_panic!("ctx == {:#?}", ctx.clone());
        print_on_panic!("self == {:#?}", self);
        self.clone().into_inner().pretty(ctx, indent, s, vars)
    }

    fn is_shallow(&self) -> bool {
        self.weak().is_shallow()
    }
}

impl<V, T: Pretty<V> + Clone> Pretty<V> for Arc<T> {
    fn pretty(
        self,
        ctx: &mut Vec<(Option<Name>, Option<Ty>)>,
        indent: usize,
        s: &mut String,
        vars: V,
    ) {
        Arc::unwrap_or_clone(self).pretty(ctx, indent, s, vars)
    }

    fn is_shallow(&self) -> bool {
        (&**self).is_shallow()
    }
}

impl Pretty<()> for Tag {
    fn pretty(
        self,
        ctx: &mut Vec<(Option<Name>, Option<Ty>)>,
        indent: usize,
        s: &mut String,
        (): (),
    ) {
        match self.kind {
            TagKind::Literal { s: lit } => {
                write!(s, "{:?}", lit).unwrap()
            },
            TagKind::Meta { meta } => {
                Fmt(&meta).pretty(ctx, indent, s, ())
            },
        }
    }

    fn is_shallow(&self) -> bool {
        match &self.kind {
            TagKind::Literal { .. } => true,
            TagKind::Meta { .. } => false,
        }
    }
}

impl Pretty<()> for FormKind {
    fn pretty(
        self,
        ctx: &mut Vec<(Option<Name>, Option<Ty>)>,
        indent: usize,
        s: &mut String,
        (): (),
    ) {
        match self {
            FormKind::Name => {
                voom!(ctx, indent, s, Name());
            },
            FormKind::Universe => {
                voom!(ctx, indent, s, Universe());
            },
            FormKind::Nat => {
                voom!(ctx, indent, s, Nat());
            },
            FormKind::Equal { eq_ty, eq_tm_0, eq_tm_1 } => {
                voom!(ctx, indent, s, Equal(eq_ty, eq_tm_0, eq_tm_1));
            },
            FormKind::Never => {
                voom!(ctx, indent, s, Never());
            },
            FormKind::Unit => {
                voom!(ctx, indent, s, Unit());
            },
            FormKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                voom!(ctx, indent, s, Sum(lhs_name, lhs_ty, rhs_ty));
            },
            FormKind::Sigma { head_name, head_ty, tail_ty } => {
                voom!(
                    ctx, indent, s,
                    Sigma(
                        head_name.clone(),
                        head_ty.clone(),
                        Scoped(((), Some(head_name.clone()), Some(head_ty.clone())), tail_ty.clone()),
                    ),
                );
            },
            FormKind::Pi { arg_name, arg_ty, res_ty } => {
                voom!(
                    ctx, indent, s,
                    Pi(
                        arg_name.clone(),
                        arg_ty.clone(),
                        Scoped(((), Some(arg_name.clone()), Some(arg_ty.clone())), res_ty.clone()),
                    ),
                )
            },
        }
    }

    fn is_shallow(&self) -> bool {
        match self {
            | FormKind::Name
            | FormKind::Universe
            | FormKind::Nat
            | FormKind::Never
            | FormKind::Unit
            => true,

            | FormKind::Equal { .. }
            | FormKind::Sum { .. }
            | FormKind::Sigma { .. }
            | FormKind::Pi { .. }
            => false,
        }
    }
}

impl Pretty<()> for IntroKind {
    fn pretty(
        self,
        ctx: &mut Vec<(Option<Name>, Option<Ty>)>,
        indent: usize,
        s: &mut String,
        (): (),
    ) {
        match self {
            IntroKind::Tag { tag } => {
                voom!(ctx, indent, s, tag(tag.clone()));
            },
            IntroKind::Form { form } => {
                form.pretty(ctx, indent, s, ());
            },
            IntroKind::Constant { ubig } => {
                voom!(ctx, indent, s, constant(Fmt(&ubig)));
            },
            IntroKind::Succs { succ_count_m1, pred_tm } => {
                voom!(ctx, indent, s, succs(Fmt(&succ_count_m1), pred_tm.clone()));
            },
            IntroKind::Refl { eq_tm } => {
                voom!(ctx, indent, s, refl(eq_tm));
            },
            IntroKind::Unit => {
                voom!(ctx, indent, s, unit());
            },
            IntroKind::InjLhs { lhs_tm } => {
                voom!(ctx, indent, s, inj_lhs(lhs_tm));
            },
            IntroKind::InjRhs { rhs_tm } => {
                voom!(ctx, indent, s, inj_rhs(rhs_tm));
            },
            IntroKind::Pair { head_tm, tail_tm } => {
                voom!(ctx, indent, s, pair(head_tm, tail_tm));
            },
            IntroKind::Func { res_tm } => {
                voom!(ctx, indent, s, func(Scoped(((), None, None), res_tm.clone())));
            },
        }
    }

    fn is_shallow(&self) -> bool {
        match self {
            | IntroKind::Tag { .. }
            | IntroKind::Constant { .. }
            | IntroKind::Unit
            => true,

            IntroKind::Form { form } => {
                form.is_shallow()
            },

            | IntroKind::Succs { .. }
            | IntroKind::Refl { .. }
            | IntroKind::InjLhs { .. }
            | IntroKind::InjRhs { .. }
            | IntroKind::Pair { .. }
            | IntroKind::Func { .. }
            => false,
        }
    }
}

impl Pretty<()> for NeutralKind {
    fn pretty(
        self,
        ctx: &mut Vec<(Option<Name>, Option<Ty>)>,
        indent: usize,
        s: &mut String,
        (): (),
    ) {
        match self {
            NeutralKind::Var { index } => {
                let (name_opt, _) = &ctx[index];
                let index = &fmt::from_fn(|f| write!(f, "#{}", index));
                match name_opt {
                    Some(name) => {
                        let name = name.clone();
                        voom!(ctx, indent, s, var(Fmt(index), name));
                    },
                    None => {
                        voom!(ctx, indent, s, var(Fmt(index)));
                    },
                }
            },
            NeutralKind::Bind { var_tms, truncated_body_usages, body } => {
                let mut usages = truncated_body_usages.clone();
                usages.set_run_to_one(truncated_body_usages.ctx_len(), var_tms.len());
                let body = Weaken::from_usages_and_weak(usages, body.clone());

                s.push_str("bind(\n");
                let sub_indent = indent + 1;

                let num_var_tms = var_tms.len();
                for (index, var_tm) in var_tms.into_iter().enumerate() {
                    for _ in 0..sub_indent {
                        s.push_str("    ");
                    }
                    write!(s, "#{} = ", ctx.len() + index).unwrap();
                    var_tm.pretty(ctx, sub_indent, s, ());
                    s.push_str(",\n");
                }

                let ctx_len = ctx.len();
                for _ in 0..num_var_tms {
                    ctx.push((None, None));
                }
                for _ in 0..sub_indent {
                    s.push_str("    ");
                }
                body.pretty(ctx, sub_indent, s, ());
                s.push_str(",\n");
                ctx.truncate(ctx_len);

                for _ in 0..indent {
                    s.push_str("    ");
                }
                s.push(')');
            },
            NeutralKind::TagsApart { elim } => {
                voom!(ctx, indent, s, tags_apart(elim));
            },
            NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
                voom!(ctx, indent, s, fold(
                    elim,
                    Scoped(((), None, Some(Ty::nat())), motive.clone()),
                    zero_inhab,
                    Scoped((((), None, Some(Ty::nat())), None, None), succ_inhab.clone()),
                ));
            },
            NeutralKind::UniqueIdentity { elim, motive, inhab } => {
                voom!(ctx, indent, s, unique_identity(
                    elim,
                    Scoped(((), None, None), motive.clone()),
                    inhab,
                ));
            },
            NeutralKind::Cong { elim, motive, inhab } => {
                voom!(ctx, indent, s, cong(
                    elim,
                    Scoped((((), None, None), None, None), motive.clone()),
                    inhab,
                ));
            },
            NeutralKind::Explode { elim, motive } => {
                voom!(ctx, indent, s, explode(
                    elim,
                    Scoped(((), None, Some(Ty::never())), motive.clone()),
                ));
            },
            NeutralKind::Case { elim, motive, lhs_inhab, rhs_inhab } => {
                voom!(ctx, indent, s, case(
                    elim,
                    Scoped(((), None, None), motive.clone()),
                    Scoped(((), None, None), lhs_inhab.clone()),
                    Scoped(((), None, None), rhs_inhab.clone()),
                ));
            },
            NeutralKind::ProjHead { elim } => {
                voom!(ctx, indent, s, proj_head(elim));
            },
            NeutralKind::ProjTail { elim } => {
                voom!(ctx, indent, s, proj_tail(elim));
            },
            NeutralKind::App { elim, arg_tm } => {
                voom!(ctx, indent, s, app(elim, arg_tm));
            },
        }
    }

    fn is_shallow(&self) -> bool {
        match self {
            NeutralKind::Var { .. } => true,

            | NeutralKind::Bind { .. }
            | NeutralKind::TagsApart { .. }
            | NeutralKind::Fold { .. }
            | NeutralKind::UniqueIdentity { .. }
            | NeutralKind::Cong { .. }
            | NeutralKind::Explode { .. }
            | NeutralKind::Case { .. }
            | NeutralKind::ProjHead { .. }
            | NeutralKind::ProjTail { .. }
            | NeutralKind::App { .. }
            => false
        }
    }
}

impl Pretty<()> for NeutralData {
    fn pretty(
        self,
        ctx: &mut Vec<(Option<Name>, Option<Ty>)>,
        indent: usize,
        s: &mut String,
        (): (),
    ) {
        if let Some(tm) = self.get_cached_reduction() {
            tm.pretty(ctx, indent, s, ())
        } else {
            self.kind.pretty(ctx, indent, s, ());
        }
    }

    fn is_shallow(&self) -> bool {
        if let Some(tm) = self.get_cached_reduction() {
            tm.is_shallow()
        } else {
            self.kind.is_shallow()
        }
    }
}

impl Pretty<()> for NameKind {
    fn pretty(
        self,
        ctx: &mut Vec<(Option<Name>, Option<Ty>)>,
        indent: usize,
        s: &mut String,
        (): (),
    ) {
        match self {
            NameKind::Tag { tag } => {
                tag.pretty(ctx, indent, s, ())
            },
            NameKind::Neutral { neutral } => {
                neutral.pretty(ctx, indent, s, ());
            },
        }
    }

    fn is_shallow(&self) -> bool {
        match self {
            NameKind::Tag { .. } => true,
            NameKind::Neutral { neutral } => neutral.is_shallow(),
        }
    }
}

impl Pretty<()> for TyKind {
    fn pretty(
        self,
        ctx: &mut Vec<(Option<Name>, Option<Ty>)>,
        indent: usize,
        s: &mut String,
        (): (),
    ) {
        match self {
            TyKind::Form { form } => {
                form.pretty(ctx, indent, s, ());
            },
            TyKind::Neutral { neutral } => {
                neutral.pretty(ctx, indent, s, ());
            },
        }
    }

    fn is_shallow(&self) -> bool {
        match self {
            TyKind::Form { form } => {
                form.is_shallow()
            },
            TyKind::Neutral { neutral } => {
                neutral.is_shallow()
            },
        }
    }
}

impl Pretty<()> for TmKind {
    fn pretty(
        self,
        ctx: &mut Vec<(Option<Name>, Option<Ty>)>,
        indent: usize,
        s: &mut String,
        (): (),
    ) {
        match self {
            TmKind::Intro { intro } => {
                intro.pretty(ctx, indent, s, ());
            },
            TmKind::Neutral { neutral } => {
                neutral.pretty(ctx, indent, s, ());
            },
        }
    }

    fn is_shallow(&self) -> bool {
        match self {
            TmKind::Intro { intro } => {
                intro.is_shallow()
            },
            TmKind::Neutral { neutral } => {
                neutral.is_shallow()
            },
        }
    }
}

impl<V, T: Pretty<V> + Contextual + Clone> Pretty<(V, Option<Name>, Option<Ty>)> for Scope<T>
where
    // TODO: remove
    T: fmt::Debug,
{
    fn pretty(
        self,
        ctx: &mut Vec<(Option<Name>, Option<Ty>)>,
        indent: usize,
        s: &mut String,
        (vars, name_opt, ty_opt): (V, Option<Name>, Option<Ty>),
    ) {
        let ctx_len = ctx.len();
        let inner = self.clone().into_inner(ctx_len);
        write!(s, "#{}", ctx_len).unwrap();
        if let Some(name) = name_opt.clone() {
            s.push(' ');
            name.pretty(ctx, indent, s, ());
        }
        s.push_str(" |- ");
        ctx.push((name_opt, ty_opt));
        inner.pretty(ctx, indent, s, vars);
        ctx.pop();
        debug_assert_eq!(ctx.len(), ctx_len);
    }

    fn is_shallow(&self) -> bool {
        self.inner.is_shallow()
    }
}

