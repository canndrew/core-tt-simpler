use crate::priv_prelude::*;

pub fn parse_to_completion<T, E: From<UnexpectedTokenError>>(
    parser: impl Parser<Output = T, Error = E>,
    tokens: &TokensRef<'_>,
) -> Result<Option<T>, E> {
    match must_consume_all(parser).parse(tokens)? {
        Some((_count, val)) => Ok(Some(val)),
        None => Ok(None),
    }
}

pub trait Parser {
    type Output;
    type Error;

    fn parse(&self, tokens: &TokensRef<'_>) -> Result<Option<(usize, Self::Output)>, Self::Error>;
}

impl<P: Parser + ?Sized> Parser for Box<P> {
    type Output = P::Output;
    type Error = P::Error;

    fn parse(&self, tokens: &TokensRef<'_>) -> Result<Option<(usize, P::Output)>, P::Error> {
        (**self).parse(tokens)
    }
}

pub struct AnyOf<Tup> {
    tup: Tup,
}

macro_rules! impl_any_of_inner (
    ($($tys:ident,)*) => (
        impl<T, E, $($tys: Parser<Output = T, Error = E>,)*> Parser for AnyOf<($($tys,)*)> {
            type Output = T;
            type Error = E;

            #[allow(non_snake_case)]
            fn parse(&self, tokens: &TokensRef<'_>) -> Result<Option<(usize, T)>, E> {
                let AnyOf { tup: ($($tys,)*) } = self;
                $(
                    match $tys.parse(tokens)? {
                        Some(stuff) => return Ok(Some(stuff)),
                        None => (),
                    }
                )*
                Ok(None)
            }
        }
    );
);

impl Parser for AnyOf<()> {
    type Output = !;
    type Error = !;

    fn parse(&self, _tokens: &TokensRef<'_>) -> Result<Option<(usize, !)>, !> {
        Ok(None)
    }
}

macro_rules! impl_any_of (
    () => ();
    ($head:ident $(,$tail:ident)*) => (
        impl_any_of_inner!($head, $($tail,)*);
        impl_any_of!($($tail),*);
    );
);

impl_any_of!(P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11);

pub fn any_of<Tup>(tup: Tup) -> AnyOf<Tup> {
    AnyOf { tup }
}

pub struct AllOf<Tup> {
    tup: Tup,
}

macro_rules! impl_all_of_inner (
    ($($tys:ident,)*) => (
        impl<E, $($tys: Parser<Error = E>,)*> Parser for AllOf<($($tys,)*)> {
            type Output = ($($tys::Output,)*);
            type Error = E;

            #[allow(non_snake_case)]
            fn parse(&self, tokens: &TokensRef<'_>) -> Result<Option<(usize, ($($tys::Output,)*))>, E> {
                let AllOf { tup: ($($tys,)*) } = self;
                let mut total_count = 0;
                $(
                    let (count, $tys) = match $tys.parse(&tokens.skip(total_count))? {
                        Some(stuff) => stuff,
                        None => return Ok(None),
                    };
                    total_count += count;
                )*
                Ok(Some((total_count, ($($tys,)*))))
            }
        }
    );
);

impl Parser for AllOf<()> {
    type Output = ();
    type Error = !;

    fn parse(&self, _tokens: &TokensRef<'_>) -> Result<Option<(usize, ())>, !> {
        Ok(Some((0, ())))
    }
}

macro_rules! impl_all_of (
    () => ();
    ($head:ident $(,$tail:ident)*) => (
        impl_all_of_inner!($head, $($tail,)*);
        impl_all_of!($($tail),*);
    );
);

impl_all_of!(P0, P1, P2, P3, P4, P5, P6, P7);

pub fn all_of<Tup>(tup: Tup) -> AllOf<Tup> {
    AllOf { tup }
}

struct FromFn<F> {
    func: F,
}

impl<T, E, F> Parser for FromFn<F>
where
    F: Fn(&TokensRef<'_>) -> Result<Option<(usize, T)>, E>,
{
    type Output = T;
    type Error = E;

    fn parse(&self, tokens: &TokensRef<'_>) -> Result<Option<(usize, T)>, E> {
        (self.func)(tokens)
    }
}

fn from_fn<T, E, F>(func: F) -> impl Parser<Output = T, Error = E>
where
    F: Fn(&TokensRef<'_>) -> Result<Option<(usize, T)>, E>,
{
    FromFn { func }
}

#[allow(unused)]
pub fn todo<T, E>() -> impl Parser<Output = T, Error = E> {
    from_fn(|_| todo!())
}

pub fn pure<T: Clone, E>(val: T) -> impl Parser<Output = T, Error = E> {
    from_fn(move |_| Ok(Some((0, val.clone()))))
}

pub fn lazy<T, E, F, P>(func: F) -> impl Parser<Output = T, Error = E>
where
    F: Fn() -> P,
    P: Parser<Output = T, Error = E>,
{
    from_fn(move |tokens| {
        func().parse(tokens)
    })
}

pub fn token<E>() -> impl Parser<Output = Token, Error = E> {
    from_fn(|tokens| {
        match tokens.first() {
            Some(token) => Ok(Some((1, token.clone()))),
            _ => Ok(None),
        }
    })
}

pub fn ident<E>() -> impl Parser<Output = Ident, Error = E> {
    token().filter_map(move |token| match token {
        Token::Ident(ident) => Some(ident),
        _ => None,
    })
}

pub fn string<E>() -> impl Parser<Output = Spanned<String>, Error = E> {
    token().filter_map(move |token| match token {
        Token::Str(s) => Some(s),
        _ => None,
    })
}

pub fn punct<E>(kind: PunctKind) -> impl Parser<Output = (), Error = E> {
    token().filter_map(move |token| match token {
        Token::Punct(punct) if punct.kind == kind => Some(()),
        _ => None,
    })
}

pub fn number<E>() -> impl Parser<Output = BigUint, Error = E> {
    token().filter_map(move |token| match token {
        Token::Lit(val) => Some(val.inner),
        _ => None,
    })
}

fn must_consume_all<T, E: From<UnexpectedTokenError>>(
    parser: impl Parser<Output = T, Error = E>,
) -> impl Parser<Output = T, Error = E> {
    from_fn(move |tokens| {
        match parser.parse(tokens)? {
            None => Ok(None),
            Some((count, val)) => {
                let remaining = tokens.skip(count);
                match remaining.first() {
                    None => Ok(Some((count, val))),
                    Some(token) => {
                        Err(UnexpectedTokenError { token: token.clone() }.into())
                    },
                }
            },
        }
    })
}

pub fn group<T, E: From<UnexpectedTokenError>, P>(
    kind: GroupKind,
    parser: impl Fn(Span) -> P,
) -> impl Parser<Output = Spanned<T>, Error = E>
where
    P: Parser<Output = T, Error = E>,
{
    from_fn(move |tokens| {
        let Some(token) = tokens.first() else {
            return Ok(None);
        };
        let Token::Group(group) = token else {
            return Ok(None);
        };
        if group.kind != kind {
            return Ok(None);
        }
        let inner_tokens = group.tokens.as_ref();
        match must_consume_all(parser(group.outer_span.clone())).parse(&inner_tokens)? {
            None => Ok(None),
            Some((_count, val)) => Ok(Some((1, Spanned::new(group.span(), val)))),
        }
    })
}

pub fn curly_braced<T, E: From<UnexpectedTokenError>, P: Parser<Output = T, Error = E>>(
    parser: impl Fn(Span) -> P,
) -> impl Parser<Output = Spanned<T>, Error = E>
where
{
    group(GroupKind::CurlyBrace, parser)
}

pub fn parens<T, E: From<UnexpectedTokenError>, P: Parser<Output = T, Error = E>>(
    parser: impl Fn(Span) -> P,
) -> impl Parser<Output = Spanned<T>, Error = E>
where
{
    group(GroupKind::RoundParen, parser)
}

#[extension(pub trait ParserExt)]
impl<T, E, P: Parser<Output = T, Error = E>> P {
    fn filter_map<U>(
        self,
        func: impl Fn(T) -> Option<U>,
    ) -> impl Parser<Output = U, Error = E> {
        from_fn(move |tokens| {
            match self.parse(tokens)? {
                None => Ok(None),
                Some((count, val)) => match func(val) {
                    None => Ok(None),
                    Some(val) => Ok(Some((count, val))),
                },
            }
        })
    }

    fn then<U>(
        self,
        next: impl Parser<Output = U, Error = E>,
    ) -> impl Parser<Output = (T, U), Error = E> {
        from_fn(move |tokens| {
            match self.parse(tokens)? {
                None => Ok(None),
                Some((count_0, val_0)) => match next.parse(&tokens.skip(count_0))? {
                    None => Ok(None),
                    Some((count_1, val_1)) => Ok(Some((count_0 + count_1, (val_0, val_1))))
                },
            }
        })
    }

    fn or(self, other: impl Parser<Output = T, Error = E>) -> impl Parser<Output = T, Error = E> {
        from_fn(move |tokens| {
            match self.parse(tokens)? {
                Some(stuff) => Ok(Some(stuff)),
                None => other.parse(tokens),
            }
        })
    }

    fn required(self, err: impl Fn() -> E) -> impl Parser<Output = T, Error = E> {
        from_fn(move |tokens| {
            match self.parse(tokens)? {
                Some(val) => Ok(Some(val)),
                None => Err(err()),
            }
        })
    }

    fn map<U>(self, func: impl Fn(T) -> U) -> impl Parser<Output = U, Error = E> {
        from_fn(move |tokens| {
            match self.parse(tokens)? {
                Some((count, val)) => Ok(Some((count, func(val)))),
                None => Ok(None),
            }
        })
    }

    fn optional(self) -> impl Parser<Output = Option<T>, Error = E> {
        from_fn(move |tokens| {
            match self.parse(tokens)? {
                None => Ok(Some((0, None))),
                Some((count, val)) => Ok(Some((count, Some(val)))),
            }
        })
    }

    fn spanned(self) -> impl Parser<Output = Spanned<T>, Error = E> {
        from_fn(move |tokens| {
            let start = tokens.span().start;
            match self.parse(tokens)? {
                None => Ok(None),
                Some((count, val)) => {
                    let end = match count.checked_sub(1) {
                        Some(count_m1) => tokens.get(count_m1).unwrap().span().end,
                        None => start,
                    };
                    let span = Span { full_src: tokens.span().full_src, start, end };
                    Ok(Some((count, Spanned::new(span, val))))
                },
            }
        })
    }

    #[cfg(debug_assertions)]
    fn debug(self, name: &'static str) -> impl Parser<Output = T, Error = E> {
        from_fn(move |tokens| {
            println!("{}{} {{", get_indent(), name);
            let ret = indent(|| self.parse(tokens));
            match &ret {
                Ok(Some((count, _))) => {
                    println!("{}}} -> Ok(Some(({}, _)));", get_indent(), count)
                },
                Ok(None) => {
                    println!("{}}} -> Ok(None);", get_indent());
                },
                Err(_) => {
                    println!("{}}} -> Err(_);", get_indent());
                },
            }
            ret
        })
    }
}

#[extension(pub trait ParserExtUnit)]
impl<E, P: Parser<Output = (), Error = E>> P {
    fn unit_then<U>(
        self,
        next: impl Parser<Output = U, Error = E>,
    ) -> impl Parser<Output = U, Error = E>
    where
        P: Parser<Output = ()>,
    {
        from_fn(move |tokens| {
            match self.parse(tokens)? {
                None => Ok(None),
                Some((count_0, ())) => match next.parse(&tokens.skip(count_0))? {
                    None => Ok(None),
                    Some((count_1, val)) => Ok(Some((count_0 + count_1, val)))
                },
            }
        })
    }
}

#[extension(pub trait ParserExtSpannedUnit)]
impl<E, P: Parser<Output = Spanned<()>, Error = E>> P {
    fn spanned_unit_then<U, F, Q>(
        self,
        next: F,
    ) -> impl Parser<Output = U, Error = E>
    where
        P: Parser<Output = Spanned<()>>,
        F: Fn(Span) -> Q,
        Q: Parser<Output = U, Error = E>,
    {
        from_fn(move |tokens| {
            match self.parse(tokens)? {
                None => Ok(None),
                Some((count_0, spanned)) => match next(spanned.span()).parse(&tokens.skip(count_0))? {
                    None => Ok(None),
                    Some((count_1, val)) => Ok(Some((count_0 + count_1, val)))
                },
            }
        })
    }

}

#[extension(pub trait ParserExtStatic)]
impl<T: 'static, E: 'static, P: Parser<Output = T, Error = E> + 'static> P {
    fn boxed(self) -> Box<dyn Parser<Output = Box<T>, Error = E> + 'static> {
        Box::new(self.map(Box::new))
    }

    fn box_dyn(self) -> Box<dyn Parser<Output = T, Error = E> + 'static> {
        Box::new(self)
    }

    fn many(self) -> impl Parser<Output = Vec<T>, Error = E> {
        from_fn(move |tokens| {
            let mut total_count = 0;
            let mut ret = Vec::new();
            loop {
                match self.parse(&tokens.skip(total_count))? {
                    None => break Ok(Some((total_count, ret))),
                    Some((count, val)) => {
                        total_count += count;
                        ret.push(val);
                    },
                }
            }
        })
    }
}

#[extension(pub trait ParserExtBox)]
impl<T: 'static, E: 'static> Box<dyn Parser<Output = T, Error = E>> {
    fn separated(
        self,
        sep: impl Parser<Output = (), Error = E> + 'static,
    ) -> impl Parser<Output = Vec<T>, Error = E> {
        from_fn(move |tokens| {
            let mut total_count = 0;
            let mut ret = Vec::new();
            loop {
                match self.parse(&tokens.skip(total_count))? {
                    None => break Ok(Some((total_count, ret))),
                    Some((count, val)) => {
                        total_count += count;
                        ret.push(val);
                        match sep.parse(&tokens.skip(total_count))? {
                            None => break Ok(Some((total_count, ret))),
                            Some((count, ())) => {
                                total_count += count;
                            },
                        }
                    },
                }
            }
        })
    }

    fn separated_trailing<U>(
        self,
        sep: impl Parser<Output = (), Error = E> + 'static,
        trailing: impl Parser<Output = U, Error = E> + 'static,
    ) -> impl Parser<Output = (Vec<T>, Option<U>), Error = E> {
        from_fn(move |tokens| {
            let mut total_count = 0;
            let mut ret = Vec::new();
            loop {
                match self.parse(&tokens.skip(total_count))? {
                    None => {
                        match trailing.parse(&tokens.skip(total_count))? {
                            None => {
                                break Ok(Some((total_count, (ret, None))))
                            },
                            Some((count, trailing_val)) => {
                                total_count += count;
                                break Ok(Some((total_count, (ret, Some(trailing_val)))))
                            },
                        }
                    },
                    Some((count, val)) => {
                        total_count += count;
                        ret.push(val);
                        match sep.parse(&tokens.skip(total_count))? {
                            None => break Ok(Some((total_count, (ret, None)))),
                            Some((count, ())) => {
                                total_count += count;
                            },
                        }
                    },
                }
            }
        })
    }

    fn comma_separated(
        self,
    ) -> impl Parser<Output = Vec<T>, Error = E> {
        self.separated(punct(PunctKind::Comma))
    }

    fn comma_separated_trailing<U>(
        self,
        trailing: impl Parser<Output = U, Error = E> + 'static,
    ) -> impl Parser<Output = (Vec<T>, Option<U>), Error = E> {
        self.separated_trailing(punct(PunctKind::Comma), trailing)
    }
}

pub struct UnexpectedTokenError {
    pub token: Token,
}

