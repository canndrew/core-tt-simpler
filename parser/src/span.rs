use crate::priv_prelude::*;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Position {
    pub line: NonZero<usize>,
    pub column: NonZero<usize>,
    pub byte: usize,
}

impl Position {
    pub fn start() -> Position {
        Position {
            line: const { NonZero::new(1).unwrap() },
            column: const { NonZero::new(1).unwrap() },
            byte: 0,
        }
    }

    pub fn end(s: &str) -> Position {
        let mut ret = Position::start();
        ret.advance_past_str(s);
        ret
    }

    pub fn advance_past_char(&mut self, c: char) {
        self.byte += c.len_utf8();
        if c == '\n' {
            self.line = self.line.checked_add(1).unwrap();
            self.column = const { NonZero::new(1).unwrap() };
        } else {
            self.column = self.column.checked_add(c.len_utf16()).unwrap();
        }
    }

    pub fn advance_past_str(&mut self, s: &str) {
        for c in s.chars() {
            self.advance_past_char(c);
        }
    }
}


#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    pub full_src: Arc<str>,
    pub start: Position,
    pub end: Position,
}

impl Span {
    pub fn combine(span_0: &Span, span_1: &Span) -> Span {
        assert!(Arc::ptr_eq(&span_0.full_src, &span_1.full_src));
        Span {
            full_src: span_0.full_src.clone(),
            start: cmp::min(span_0.start, span_1.start),
            end: cmp::max(span_0.end, span_1.end),
        }
    }

    pub fn end_as_span(&self) -> Span {
        Span {
            full_src: self.full_src.clone(),
            start: self.end,
            end: self.end,
        }
    }
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}..{} ", self.start, self.end)?;
        let string;

        let start = self.start.byte;
        let end = self.end.byte;
        let chunk = &self.full_src[start..end];
        let mut char_indices = chunk.char_indices();
        let s = loop {
            let Some((i, c)) = char_indices.next() else {
                break chunk;
            };
            if i >= 10 || matches!(c, '(' | ')' | '{' | '}' | '[' | ']' | '"' | '\'') {
                string = format!("{}…", &chunk[..i]);
                break string.as_str();
            }
        };
        write!(f, "{:?}", s)?;
        Ok(())
    }
}

impl fmt::Debug for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl<S, T: fmt::Debug> fmt::Debug for Spanned<S, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.inner, f)
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Spanned<S, T> {
    pub span: S,
    pub inner: T,
}

impl<S: Spans, T> Spanned<S, T> {
    pub fn new(span: S, inner: T) -> Spanned<S, T> {
        Spanned { span, inner }
    }

    pub fn span(&self) -> S {
        self.span.clone()
    }

    pub fn map<R>(self, func: impl FnOnce(T) -> R) -> Spanned<S, R> {
        let Spanned { span, inner } = self;
        Spanned {
            span,
            inner: func(inner),
        }
    }

    pub fn as_ref(&self) -> Spanned<S, &T> {
        Spanned {
            span: self.span.clone(),
            inner: &self.inner,
        }
    }

    pub fn as_deref(&self) -> Spanned<S, &T::Target>
    where
        T: Deref,
    {
        Spanned {
            span: self.span.clone(),
            inner: &self.inner,
        }
    }
}

pub trait Spans: Clone + fmt::Debug {
    type Ident: HasSpan<Self> + Clone + fmt::Debug + AsRef<str>;
}

impl Spans for Span {
    type Ident = Ident;
}

pub trait HasSpan<S> {
    fn span(&self) -> S;
}

