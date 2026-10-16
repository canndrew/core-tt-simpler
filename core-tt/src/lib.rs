extern crate self as core_tt;

mod priv_prelude;
mod util;
mod tag;
mod core;


pub mod check;

pub mod pprint;
pub mod more;
pub mod solve;
pub mod builtins;
mod sanity_check;

//mod prettier;
mod prettier_2;

#[cfg(debug_assertions)]
mod debug;

pub use {
    self::{
        tag::Tag,
        core::{
            usages::Usages,
            weaken::Weaken,
            contextual::{Contextual, TupleOfContextual, DeepNf},
            form::{Form, FormKind},
            intro::{Intro, IntroKind},
            neutral::NeutralKind,
            stuck::{Stuck, StuckKind},
            lazy::{Lazy, OrLazy, LazyData},
            name::{Name, NameKind},
            ty::{Ty, TyKind},
            tm::{Tm, TmKind},
            scope::Scope,
            unify::Unify,
            subst::{Subst, Substitutable},
        },
        more::iso::Iso,
        check::{check_ctx::CheckCtx, checked::Checked, typecheck::Check},
        sanity_check::SanityCheck,
    },
    ubig::Ubig,
};

