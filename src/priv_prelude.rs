pub(crate) use {
    std::{
        cmp, iter, fmt, mem,
        collections::{btree_map, hash_map, BTreeMap, HashMap},
        sync::{Arc, OnceLock, RwLock},
    },
    lazy_static::lazy_static,
    ubig::Ubig,
    parser::{Span, Spanned},
    //derive_where::derive_where,
    crate::{
        util::{as_equal, max_all, iter::{Which, merge_enumerated}},
        tag::{Tag, TagKind, MetaTag},
        //macros::pi,
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
            scope::{Scope, Bindable},
            subst::{Subst, Substitutable},
            unify::Unify,
        },
        check::{
            check_ctx::CheckCtx,
            checked::Checked,
        },
        more::iso::Iso,
        solve::{
            simplification::{Simplification, Uninhabited},
            constraint::{Constraint, Constraints},
        },
        builtins::Builtin,
    },
    core_tt_simpler_macros::Contextual,
};

#[cfg(debug_assertions)]
#[allow(unused)]
pub(crate) use crate::debug::{debug_indent, debug, print_on_panic};

