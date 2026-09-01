extern crate self as core_tt_simpler;

mod priv_prelude;
mod util;
mod tag;
mod core;
//mod untyped;
mod check;

mod more;
mod solve;

pub use {
    self::{
        tag::Tag,
        core::{
            usages::Usages,
            weaken::Weaken,
            contextual::{Contextual, TupleOfContextual},
            form::{Form, FormKind},
            intro::{Intro, IntroKind},
            neutral::{Neutral, NeutralData, NeutralKind},
            name::{Name, NameKind},
            ty::{Ty, TyKind},
            tm::{Tm, TmKind},
            scope::Scope,
            unify::Unify,
            subst::{Subst, Substitutable},
        },
        more::iso::Iso,
        check::{check_ctx::CheckCtx, checked::Checked, typecheck::Check},
    },
    ubig::Ubig,
};

