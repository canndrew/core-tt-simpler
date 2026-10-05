pub(crate) use {
    std::{
        cmp, fmt, hash,
        num::NonZero,
        ops::Deref,
        str::FromStr,
        sync::Arc,
    },
    thiserror::Error,
    ext_trait::extension,
    num::BigUint,
    crate::{
        ast,
        token::{Token, TokensRef, Ident, GroupKind, PunctKind, TokenizeError},
        span::{Position, Span, Spanned},
        combinators::{
            UnexpectedTokenError,
            Parser, ParserExt, ParserExtStatic, ParserExtUnit, ParserExtSpannedUnit, ParserExtBox,
            ident, string, all_of, parens, punct, curly_braced, lazy, any_of, pure, number,
        },
        parser::ParseError,
    },
};

#[cfg(debug_assertions)]
pub(crate) use {
    std::cell::Cell,
    crate::debug::{indent, get_indent},
};

