//use crate::priv_prelude::*;

macro_rules! pi {
    ($ctx_len:ident @ ($arg_name:ident: $arg_ty:expr) -> $res_ty:expr) => {
        pi!($ctx_len @ ($arg_name: $arg_ty,) -> $res_ty)
    };
    ($ctx_len:ident @ ($arg_name:ident: $arg_ty:expr,) -> $res_ty:expr) => {
        Ty::pi(
            Name::from(stringify!($arg_name)),
            $arg_ty,
            Scope::make($ctx_len, |$arg_name| {
                let $ctx_len = $ctx_len + 1;
                $res_ty
            }),
        )
    };
    ($ctx_len:ident @ ($arg_name:ident: $arg_ty:expr, $($more:tt)+) -> $res_ty:expr) => {
        Ty::pi(
            Name::from(stringify!($arg_name)),
            $arg_ty,
            Scope::make($ctx_len, |$arg_name| {
                let $ctx_len = $ctx_len + 1;
                pi!($ctx_len @ ($($more)+) -> $res_ty)
            }),
        )
    };
}

pub(crate) use pi;

macro_rules! func {
    ($ctx_len:ident @ ($arg_name:ident) => $res_tm:expr) => {
        func!($ctx_len @ ($arg_name,) => $res_tm)
    };
    ($ctx_len:ident @ ($arg_name:ident,) => $res_tm:expr) => {
        Tm::func(Scope::make($ctx_len, |$arg_name| {
            let $ctx_len = $ctx_len + 1;
            $res_tm
        }))
    };
    ($ctx_len:ident @ ($arg_name:ident, $($more:tt)+) => $res_tm:expr) => {
        Tm::func(Scope::make($ctx_len, |$arg_name| {
            let $ctx_len = $ctx_len + 1;
            func!($ctx_len @ ($($more)+) => $res_tm)
        }))
    };
}

pub(crate) use func;

