use crate::priv_prelude::*;

#[derive(Clone, Debug)]
pub enum Token<S: Spans> {
    Lit(Spanned<S, BigUint>),
    Str(Spanned<S, String>),
    Group(Group<S>),
    Punct(Punct<S>),
    Ident(S::Ident),
}

impl<S: Spans> Token<S> {
    pub fn span(&self) -> S {
        match self {
            Token::Lit(val) => val.span.clone(),
            Token::Str(s) => s.span.clone(),
            Token::Group(group) => group.span(),
            Token::Punct(punct) => punct.span(),
            Token::Ident(ident) => ident.span(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Tokens<S: Spans> {
    span: S,
    tokens: Vec<Token<S>>,
}

impl<S: Spans> Tokens<S> {
    pub fn as_ref(&self) -> TokensRef<'_, S> {
        TokensRef {
            span: self.span.clone(),
            tokens: &self.tokens,
        }
    }
}

#[derive(Clone, Debug)]
pub struct TokensRef<'a, S: Spans> {
    span: S,
    tokens: &'a [Token<S>],
}

impl<'a, S: Spans> TokensRef<'a, S> {
    pub fn span(&self) -> S {
        self.span.clone()
    }

    pub fn first(&self) -> Option<&Token<S>> {
        self.tokens.first()
    }

    pub fn get(&self, index: usize) -> Option<&'a Token<S>> {
        self.tokens.get(index)
    }
}

impl<'a> TokensRef<'a, Span> {
    pub fn skip(&self, count: usize) -> TokensRef<'a, Span> {
        let tokens = &self.tokens[count..];
        let start = tokens.first().map(|token| token.span().start).unwrap_or(self.span.end);
        let span = Span {
            full_src: self.span.full_src.clone(),
            start,
            end: self.span.end,
        };
        TokensRef { span, tokens }
    }
}

#[derive(Clone, Debug)]
pub struct Ident {
    span: Span,
}

impl HasSpan<Span> for Ident {
    fn span(&self) -> Span {
        self.span.clone()
    }
}

impl PartialEq for Ident {
    fn eq(&self, other: &Ident) -> bool {
        PartialEq::eq(self.as_str(), other.as_str())
    }
}

impl Eq for Ident {}

impl PartialOrd for Ident {
    fn partial_cmp(&self, other: &Ident) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_str(), other.as_str())
    }
}

impl Ord for Ident {
    fn cmp(&self, other: &Ident) -> cmp::Ordering {
        Ord::cmp(self.as_str(), other.as_str())
    }
}

impl hash::Hash for Ident {
    fn hash<H>(&self, state: &mut H)
    where
        H: hash::Hasher,
    {
        hash::Hash::hash(self.as_str(), state)
    }
}

impl AsRef<str> for Ident {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl Ident {
    pub fn new(span: Span) -> Ident {
        Ident { span }
    }

    pub fn as_str(&self) -> &str {
        &self.span.full_src[self.span.start.byte..self.span.end.byte]
    }

    pub fn from_str_fake_span(s: &str) -> Ident {
        let span = Span { full_src: Arc::from(s), start: Position::start(), end: Position::end(s) };
        Ident::new(span)
    }
}

#[derive(Clone, Debug)]
pub struct Group<S: Spans> {
    pub outer_span: S,
    pub kind: GroupKind,
    pub tokens: Tokens<S>,
}

impl<S: Spans> Group<S> {
    pub fn span(&self) -> S {
        self.outer_span.clone()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum GroupKind {
    CurlyBrace,
    RoundParen,
}

#[derive(Clone, Debug)]
pub struct Punct<S: Spans> {
    pub span: S,
    pub kind: PunctKind,
}

impl<S: Spans> Punct<S> {
    pub fn span(&self) -> S {
        self.span.clone()
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum PunctKind {
    Arrow,
    FatArrow,
    Comma,
    Colon,
    Equal,
    DoubleEqual,
    Plus,
    Star,
    Dot,
    DoubleDot,
    TripleDot,
    Semicolon,
    Dollar,
}

#[derive(Error, Debug)]
pub enum TokenizeError {
    #[error("unclosed block comment starting at {}", open_position)]
    UnclosedBlockComment {
        open_position: Position,
    },
    #[error("missing closing delimiter for open delimiter at {}", open_position)]
    UnclosedDelimiter {
        kind: GroupKind,
        open_position: Position,
    },
    #[error("mismatched delimiters at {} and {}", open_position, close_position)]
    MismatchedClosingDelimiter {
        open_kind: GroupKind,
        close_kind: GroupKind,
        open_position: Position,
        close_position: Position,
    },
    #[error("unexpected char at {}", position)]
    UnexpectedChar {
        position: Position,
        c: char,
    },
    #[error("unexpected closing delimiter at {}", position)]
    UnexpectedClosingDelimiter {
        position: Position,
        kind: GroupKind,
    },
    #[error("unclosed string starting at {}", start_position)]
    UnclosedString {
        start_position: Position,
    },
    #[error("invalid escape sequence '{}' at {}", invalid_char, escape_position)]
    InvalidEscapeSequence {
        escape_position: Position,
        invalid_char: char,
    },
}

struct Tokenizer {
    full_src: Arc<str>,
    position: Position,
}

impl Tokenizer {
    pub fn new(full_src: Arc<str>) -> Tokenizer {
        Tokenizer {
            full_src,
            position: Position::start(),
        }
    }

    fn remaining(&self) -> &str {
        &self.full_src[self.position.byte..]
    }

    fn span(&self, start: Position, end: Position) -> Span {
        Span {
            full_src: self.full_src.clone(),
            start,
            end,
        }
    }

    fn pop_char_matching(&mut self, pred: impl FnOnce(char) -> bool) -> Option<char> {
        let c = self.remaining().chars().next()?;
        if !pred(c) {
            return None;
        }
        self.position.advance_past_char(c);
        Some(c)
    }

    fn pop_just(&mut self, pat: char) -> bool {
        self.pop_char_matching(|c| c == pat).is_some()
    }

    fn pop_any_char(&mut self) -> Option<char> {
        self.pop_char_matching(|_| true)
    }

    fn pop_any_of(&mut self, chars: &[char]) -> Option<char> {
        self.pop_char_matching(|c| chars.contains(&c))
    }

    fn pop_prefix(&mut self, prefix: &str) -> bool {
        if !self.remaining().starts_with(prefix) {
            return false;
        }
        self.position.advance_past_str(prefix);
        true
    }

    fn pop_prefix_spanned(&mut self, prefix: &str) -> Option<Span> {
        let start = self.position;
        if self.pop_prefix(prefix) {
            let end = self.position;
            return Some(self.span(start, end));
        }
        None
    }

    fn rest_of_block_comment(&mut self, open_position: Position) -> Result<(), TokenizeError> {
        let mut depth = 0u32;
        loop {
            if self.pop_prefix("/*") {
                depth += 1;
                continue;
            }
            if self.pop_prefix("*/") {
                match depth.checked_sub(1) {
                    None => break Ok(()),
                    Some(new_depth) => depth = new_depth,
                }
                continue;
            }
            if !self.pop_any_char().is_some() {
                return Err(TokenizeError::UnclosedBlockComment {
                    open_position,
                });
            }
        }
    }

    fn rest_of_line_comment(&mut self) {
        loop {
            match self.pop_any_char() {
                None | Some('\n') => break,
                _ => (),
            }
        }
    }

    fn trim_leading_whitespace(&mut self) -> Result<(), TokenizeError> {
        loop {
            let position = self.position;
            if self.pop_any_of(&[' ', '\n', '\r']).is_some() {
                continue;
            }
            if self.pop_prefix("/*") {
                self.rest_of_block_comment(position)?;
                continue;
            }
            if self.pop_prefix("//") {
                self.rest_of_line_comment();
                continue;
            }
            break Ok(());
        }
    }

    fn rest_of_group(&mut self, kind: GroupKind, start: Position) -> Result<Group<Span>, TokenizeError> {
        let (tokens, position_close_kind_opt) = self.pop_tokens()?;
        let Some((close_position, close_kind)) = position_close_kind_opt else {
            return Err(TokenizeError::UnclosedDelimiter {
                kind,
                open_position: start,
            });
        };
        if kind != close_kind {
            return Err(TokenizeError::MismatchedClosingDelimiter {
                open_kind: kind,
                close_kind,
                open_position: start,
                close_position,
            });
        }
        let end = self.position;
        let outer_span = self.span(start, end);
        let group = Group { outer_span, kind, tokens };
        return Ok(group);
    }

    fn pop_string(&mut self) -> Result<Option<Spanned<Span, String>>, TokenizeError> {
        let start_position = self.position;
        if !self.pop_just('"') {
            return Ok(None);
        }

        let mut ret = String::new();
        loop {
            let Some(c) = self.pop_any_char() else {
                return Err(TokenizeError::UnclosedString { start_position });
            };
            let c = match c {
                '"' => break,
                '\\' => {
                    let escape_position = self.position;
                    let Some(c) = self.pop_any_char() else {
                        return Err(TokenizeError::UnclosedString { start_position });
                    };
                    match c {
                        '\"' => '"',
                        '\\' => '\\',
                        // TODO: more escape sequences
                        invalid_char => {
                            return Err(TokenizeError::InvalidEscapeSequence {
                                escape_position, invalid_char,
                            });
                        },
                    }
                },
                c => c,
            };
            ret.push(c);
        }
        let span = self.span(start_position, self.position);
        let spanned = Spanned { span, inner: ret };

        Ok(Some(spanned))
    }

    fn pop_punct(&mut self) -> Option<Punct<Span>> {
        if let Some(span) = self.pop_prefix_spanned("->") {
            return Some(Punct { span, kind: PunctKind::Arrow });
        }
        if let Some(span) = self.pop_prefix_spanned("=>") {
            return Some(Punct { span, kind: PunctKind::FatArrow });
        }
        if let Some(span) = self.pop_prefix_spanned(",") {
            return Some(Punct { span, kind: PunctKind::Comma });
        }
        if let Some(span) = self.pop_prefix_spanned(":") {
            return Some(Punct { span, kind: PunctKind::Colon });
        }
        if let Some(span) = self.pop_prefix_spanned("==") {
            return Some(Punct { span, kind: PunctKind::DoubleEqual });
        }
        if let Some(span) = self.pop_prefix_spanned("=") {
            return Some(Punct { span, kind: PunctKind::Equal });
        }
        if let Some(span) = self.pop_prefix_spanned("+") {
            return Some(Punct { span, kind: PunctKind::Plus });
        }
        if let Some(span) = self.pop_prefix_spanned("*") {
            return Some(Punct { span, kind: PunctKind::Star });
        }
        if let Some(span) = self.pop_prefix_spanned("...") {
            return Some(Punct { span, kind: PunctKind::TripleDot });
        }
        if let Some(span) = self.pop_prefix_spanned("..") {
            return Some(Punct { span, kind: PunctKind::DoubleDot });
        }
        if let Some(span) = self.pop_prefix_spanned(".") {
            return Some(Punct { span, kind: PunctKind::Dot });
        }
        if let Some(span) = self.pop_prefix_spanned(";") {
            return Some(Punct { span, kind: PunctKind::Semicolon });
        }
        if let Some(span) = self.pop_prefix_spanned("$") {
            return Some(Punct { span, kind: PunctKind::Dollar });
        }
        None
    }

    fn pop_token(&mut self) -> Result<Result<Token<Span>, (Position, Option<GroupKind>)>, TokenizeError> {
        self.trim_leading_whitespace()?;
        let start = self.position;
        if let Some(_) = self.pop_char_matching(|c| matches!(c, 'a'..='z' | 'A'..='Z' | '_')) {
            while self.pop_char_matching(|c| matches!(c, 'a'..='z' | 'A'..='Z' | '_' | '0'..='9')).is_some() {}
            let end = self.position;
            let span = self.span(start, end);
            let ident = Ident { span };
            return Ok(Ok(Token::Ident(ident)));
        }
        if let Some(_) = self.pop_char_matching(|c| matches!(c, '0'..='9')) {
            while self.pop_char_matching(|c| matches!(c, '0'..='9')).is_some() {}
            let end = self.position;
            let span = self.span(start, end);
            let val = BigUint::from_str(&self.full_src[start.byte..end.byte]).unwrap();
            let val = Spanned::new(span, val);
            return Ok(Ok(Token::Lit(val)));
        }
        if let Some(s) = self.pop_string()? {
            return Ok(Ok(Token::Str(s)));
        }
        if let Some(punct) = self.pop_punct() {
            return Ok(Ok(Token::Punct(punct)));
        }
        if self.pop_just('(') {
            let group = self.rest_of_group(GroupKind::RoundParen, start)?;
            return Ok(Ok(Token::Group(group)));
        }
        if self.pop_just('{') {
            let group = self.rest_of_group(GroupKind::CurlyBrace, start)?;
            return Ok(Ok(Token::Group(group)));
        }
        if self.pop_just(')') {
            return Ok(Err((start, Some(GroupKind::RoundParen))));
        }
        if self.pop_just('}') {
            return Ok(Err((start, Some(GroupKind::CurlyBrace))));
        }
        match self.pop_any_char() {
            None => Ok(Err((start, None))),
            Some(c) => {
                Err(TokenizeError::UnexpectedChar {
                    position: start,
                    c,
                })
            },
        }
    }

    fn pop_tokens(&mut self) -> Result<(Tokens<Span>, Option<(Position, GroupKind)>), TokenizeError> {
        let initial_position = self.position;
        let mut start_end_opt = None;
        let mut tokens = Vec::new();
        loop {
            let position = self.position;
            match self.pop_token()? {
                Ok(token) => {
                    let span = token.span();
                    start_end_opt = Some(match start_end_opt {
                        Some((start, _end)) => (start, span.end),
                        None => (span.start, span.end),
                    });
                    tokens.push(token);
                },
                Err((final_position, kind_opt)) => {
                    let (start, end) = start_end_opt.unwrap_or((initial_position, final_position));
                    let span = Span { full_src: self.full_src.clone(), start, end };
                    let tokens = Tokens { span, tokens };
                    break Ok((tokens, kind_opt.map(|kind| (position, kind))));
                },
            }
        }
    }

    pub fn tokenize(mut self) -> Result<Tokens<Span>, TokenizeError> {
        let (tokens, position_kind_opt) = self.pop_tokens()?;
        if let Some((position, kind)) = position_kind_opt {
            return Err(TokenizeError::UnexpectedClosingDelimiter { position, kind });
        }
        Ok(tokens)
    }
}

pub fn tokenize(full_src: &Arc<str>) -> Result<Tokens<Span>, TokenizeError> {
    Tokenizer::new(full_src.clone()).tokenize()
}

