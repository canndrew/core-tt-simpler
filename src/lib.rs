extern crate self as core_tt_simpler;

mod priv_prelude;
mod util;
mod tag;
mod core;
//mod check;

pub mod pprint;
/*
mod more;
mod solve;
mod builtins;
*/
mod sanity_check;

#[cfg(debug_assertions)]
mod debug;

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
        /*
        more::iso::Iso,
        check::{check_ctx::CheckCtx, checked::Checked, typecheck::Check},
        */
        sanity_check::SanityCheck,
    },
    ubig::Ubig,
};

