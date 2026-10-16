pub(crate) use {
    std::{
        cmp, iter, fmt, mem,
        collections::{btree_map, hash_map, BTreeMap, HashMap},
        sync::{Arc, OnceLock, RwLock},
    },
    lazy_static::lazy_static,
    ubig::Ubig,
    parser::{Span, Spanned, HasSpan},
    crate::{
        solve,
        util::{as_equal, max_all, iter::{Which, merge_enumerated}},
        tag::{Tag, TagKind, MetaTag},
        core::{
            usages::Usages,
            weaken::Weaken,
            contextual::{Contextual, TupleOfContextual, DeepNf},
            form::{Form, FormKind},
            intro::{Intro, IntroKind},
            neutral::NeutralKind,
            stuck::{Stuck, StuckKind},
            lazy::{Lazy, LazyData, OrLazy, AsTmKind},
            name::{Name, NameKind},
            ty::{Ty, TyKind, ValTy},
            tm::{Tm, TmKind, ValTm},
            scope::{Scope, Bindable},
            subst::{Subst, Substitutable},
            unify::Unify,
            well_formed::WellFormed,
        },
        check::{
            check_ctx::CheckCtx,
            checked::Checked,
        },
        more::iso::Iso,
        solve::{
            simplification::{Simplification, Uninhabited},
            cache::SimplifyCache,
            constraint::Constraints,
        },
        builtins::Builtin,
    },
    core_tt_macros::Contextual,
};

#[cfg(debug_assertions)]
#[allow(unused)]
pub(crate) use crate::{
    debug::{debug_indent, debug, print_on_panic},
    pprint::debug_print,
};

