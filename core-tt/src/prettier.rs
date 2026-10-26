use crate::priv_prelude::*;

pub enum Text {
    Arc(Arc<str>),
    Static(&'static str),
    String(String),
}

trait Width {
    fn width(&self) -> usize;
}

impl Width for str {
    fn width(&self) -> usize {
        self.encode_utf16().count()
    }
}

/*
impl Text {
    pub fn new() -> Text {
        Text::Static("")
    }

    pub fn push_text(&mut self, more: Text) {
        if self.is_empty() {
            *self = more;
            return;
        }

        self.push_str(&more);
    }

    pub fn push_str(&mut self, more: &str) {
        if more.is_empty() {
            return;
        }

        if let Text::String(s) = self {
            s.push_str(more);
        } else {
            let mut s = String::with_capacity(self.len() + more.len());
            s.push_str(self);
            s.push_str(more);
            *self = Text::String(s);
        }
    }
}
*/

impl ops::Deref for Text {
    type Target = str;

    fn deref(&self) -> &str {
        match self {
            Text::Arc(s) => s,
            Text::Static(s) => s,
            Text::String(s) => s,
        }
    }
}

impl From<&'static str> for Text {
    fn from(s: &'static str) -> Text {
        Text::Static(s)
    }
}

impl From<Arc<str>> for Text {
    fn from(s: Arc<str>) -> Text {
        Text::Arc(s)
    }
}

impl From<String> for Text {
    fn from(s: String) -> Text {
        Text::String(s)
    }
}

const RIBBON_WIDTH: usize = 50;

pub enum Doc {
    Concat {
        docs: Vec<Doc>,
    },
    Text {
        text: Text,
    },
    Indent {
        doc: Box<Doc>,
    },
    Newline {
        on_break: &'static str,
        on_flatten: &'static str,
    },
    Ungroup {
        doc: Box<Doc>,
    },
}

impl Doc {
    pub fn concat(docs: impl IntoIterator<Item = Doc>) -> Doc {
        let iter = docs.into_iter();
        let mut docs = Vec::new();
        for doc in iter {
            match doc {
                Doc::Concat { docs: more } => {
                    docs.extend(more);
                },
                Doc::Text { text } => {
                    if let Some(prev_doc) = docs.last_mut()
                    && let Doc::Text { text: prev_text } = prev_doc
                    && let Text::String(s) = prev_text
                    {
                        s.push_str(&text);
                    } else {
                        docs.push(Doc::Text { text });
                    }
                },
                doc => docs.push(doc),
            }
        }
        if docs.len() == 1 {
            return docs.pop().unwrap();
        }
        Doc::Concat { docs }
    }

    pub fn text(text: impl Into<Text>) -> Doc {
        Doc::Text { text: text.into() }
    }

    pub fn indent(self) -> Doc {
        if self.contains_newlines() {
            Doc::Indent { doc: Box::new(self) }
        } else {
            self
        }
    }

    pub fn newline(on_break: &'static str, on_flatten: &'static str) -> Doc {
        Doc::Newline { on_break, on_flatten }
    }

    pub fn group_strict(self) -> Doc {
        if self.contains_ungroups() {
            return self.ungroup();
        }
        self.group()
    }

    pub fn group(self) -> Doc {
        if self.subtract_width(RIBBON_WIDTH).is_none() {
            return self.ungroup();
        };
        self.flatten()
    }

    pub fn with_precedence(self, precedence: Precedence) -> PrecedenceDoc {
        PrecedenceDoc { precedence, doc: self }
    }

    pub fn render(&self, output: &mut fmt::Formatter, indent: usize) -> fmt::Result {
        match self {
            Doc::Concat { docs } => {
                for doc in docs {
                    doc.render(output, indent)?;
                }
            },
            Doc::Text { text } => {
                output.write_str(&text)?;
            },
            Doc::Indent { doc } => {
                doc.render(output, indent + 1)?;
            },
            Doc::Newline { on_break, on_flatten: _ } => {
                output.write_str(on_break)?;
                output.write_str("\n")?;
                for _ in 0..indent {
                    output.write_str("    ")?;
                }
            },
            Doc::Ungroup { doc } => {
                doc.render(output, indent)?;
            },
        }
        Ok(())
    }

    pub fn ungroup(self) -> Doc {
        let doc = match self {
            Doc::Ungroup { doc } => doc,
            doc => Box::new(doc),
        };
        Doc::Ungroup { doc }
    }

    fn contains_ungroups(&self) -> bool {
        match self {
            Doc::Concat { docs } => {
                docs.iter().any(|doc| doc.contains_ungroups())
            },
            Doc::Text { .. } => false,
            Doc::Indent { doc } => doc.contains_ungroups(),
            Doc::Newline { .. } => false,
            Doc::Ungroup { .. } => true,
        }
    }

    fn contains_newlines(&self) -> bool {
        match self {
            Doc::Concat { docs } => {
                docs.iter().any(|doc| doc.contains_newlines())
            },
            Doc::Text { .. } => false,
            Doc::Indent { .. } => true,
            Doc::Newline { .. } => true,
            Doc::Ungroup { .. } => true,
        }
    }

    fn leading_trailing_width(&self) -> (usize, Option<usize>) {
        match self {
            Doc::Concat { docs } => {
                let mut iter = docs.iter();
                let mut leading_width = 0;
                loop {
                    match iter.next() {
                        Some(doc) => {
                            let (next_leading_width, trailing_width_opt) = {
                                doc.leading_trailing_width()
                            };
                            leading_width += next_leading_width;
                            if let Some(start_trailing_width) = trailing_width_opt {
                                let mut trailing_width = 0;
                                let trailing_width = loop {
                                    match iter.next_back() {
                                        Some(doc) => {
                                            let (next_leading_width, next_trailing_width_opt) = {
                                                doc.leading_trailing_width()
                                            };
                                            match next_trailing_width_opt {
                                                Some(next_trailing_width) => {
                                                    trailing_width += next_trailing_width;
                                                    break trailing_width;
                                                },
                                                None => {
                                                    trailing_width += next_leading_width;
                                                },
                                            }
                                        },
                                        None => {
                                            trailing_width += start_trailing_width;
                                            break trailing_width;
                                        },
                                    }
                                };
                                break (leading_width, Some(trailing_width));
                            }
                        },
                        None => {
                            break (leading_width, None);
                        },
                    }
                }
            },
            Doc::Text { text } => {
                (text.width(), None)
            },
            Doc::Indent { doc } => {
                doc.leading_trailing_width()
            },
            Doc::Newline { on_break, on_flatten: _ } => {
                (on_break.width(), Some(0))
            },
            Doc::Ungroup { doc } => {
                doc.leading_trailing_width()
            },
        }
    }

    fn subtract_width(&self, mut remaining_width: usize) -> Option<usize> {
        match self {
            Doc::Concat { docs } => {
                for doc in docs {
                    remaining_width = doc.subtract_width(remaining_width)?;
                }
                Some(remaining_width)
            },
            Doc::Text { text } => {
                remaining_width.checked_sub(text.width())
            },
            Doc::Indent { doc } => {
                doc.subtract_width(remaining_width)
            },
            Doc::Newline { on_break: _, on_flatten } => {
                remaining_width.checked_sub(on_flatten.width())
            },
            Doc::Ungroup { doc } => {
                let (leading_width, trailing_width_opt) = {
                    doc.leading_trailing_width()
                };
                remaining_width = remaining_width.checked_sub(leading_width)?;
                match trailing_width_opt {
                    Some(trailing_width) => {
                        RIBBON_WIDTH.checked_sub(trailing_width)
                    },
                    None => Some(remaining_width),
                }
            },
        }
    }

    fn flatten(self) -> Doc {
        match self {
            Doc::Concat { docs } => {
                let docs = docs.into_iter().map(|doc| doc.flatten()).collect();
                Doc::Concat { docs }
            },
            Doc::Text { text } => {
                Doc::Text { text }
            },
            Doc::Indent { doc } => {
                doc.flatten()
            },
            Doc::Newline { on_break: _, on_flatten } => {
                Doc::text(on_flatten)
            },
            Doc::Ungroup { doc } => {
                Doc::Ungroup { doc }
            },
        }
    }
}

#[derive(Clone, Copy, PartialOrd, PartialEq)]
pub enum Precedence {
    Stmt = 0,
    Func = 1,
    Equal = 2,
    Add = 3,
    Mul = 4,
    Inj = 5,
    Proj = 6,
    App = 7,
    Atom = 8,
}

pub struct PrecedenceDoc {
    precedence: Precedence,
    doc: Doc,
}

impl PrecedenceDoc {
    pub fn with_precedence(self, required: Precedence) -> PrecedenceDoc {
        if required <= self.precedence {
            return self;
        }

        let precedence = Precedence::Atom;
        let doc = Doc::group(
            Doc::concat([
                Doc::text("{"),
                Doc::indent(
                    Doc::concat([
                        Doc::newline("", " "),
                        self.doc,
                    ]),
                ),
                Doc::newline("", " "),
                Doc::text("}"),
            ]),
        );
        PrecedenceDoc { precedence, doc }
    }
}

pub struct PrettyFmt {
    doc: Doc,
}

impl fmt::Display for PrettyFmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.doc.render(f, 0)
    }
}

impl fmt::Debug for PrettyFmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

pub trait Pprint: WellFormed {
    type Fmt: fmt::Display + fmt::Debug;

    fn pprint(
        self,
        ctx_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        params: Self::Params,
    ) -> Self::Fmt;
}

impl<T> Pprint for T
where
    T: Prettier,
{
    type Fmt = PrettyFmt;

    fn pprint(
        self,
        ctx_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        params: Self::Params,
    ) -> PrettyFmt
    where
        Self: Sized,
    {
        let doc = self.prettier(ctx_names, ctx, params).doc;
        PrettyFmt { doc }
    }
}

pub trait Prettier: WellFormed {
    fn prettier(
        self,
        ctx_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        params: Self::Params,
    ) -> PrecedenceDoc;

    fn pprint(
        self,
        ctx_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        params: Self::Params,
    ) -> PrettyFmt
    where
        Self: Sized,
    {
        let doc = self.prettier(ctx_names, ctx, params).doc;
        PrettyFmt { doc }
    }
}

impl<T> Prettier for Weaken<T>
where
    T: Contextual + Prettier,
{
    fn prettier(
        self,
        ctx_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        params: Self::Params,
    ) -> PrecedenceDoc {
        self.into_inner().prettier(ctx_names, ctx, params)
    }
}

impl<T> Prettier for Arc<T>
where
    T: Clone + Prettier,
{
    fn prettier(
        self,
        ctx_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        params: Self::Params,
    ) -> PrecedenceDoc {
        Arc::unwrap_or_clone(self).prettier(ctx_names, ctx, params)
    }
}

impl<T> Prettier for OrLazy<T>
where
    T: AsTmKind + Prettier,
{
    fn prettier(
        self,
        ctx_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        params: Self::Params,
    ) -> PrecedenceDoc {
        self.reduced().prettier(ctx_names, ctx, params)
    }
}

impl Prettier for FormKind {
    fn prettier(
        self,
        ctx_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        (): (),
    ) -> PrecedenceDoc {
        match self {
            FormKind::Name => {
                Doc::text("String").with_precedence(Precedence::Atom)
            },
            FormKind::Universe => {
                Doc::text("Type").with_precedence(Precedence::Atom)
            },
            FormKind::Nat => {
                Doc::text("Nat").with_precedence(Precedence::Atom)
            },
            FormKind::Never => {
                Doc::text("enum {}").with_precedence(Precedence::Atom)
            },
            FormKind::Unit => {
                Doc::text("struct {}").with_precedence(Precedence::Atom)
            },
            FormKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                let mut ty_fields = vec![
                    pretty_ty_field(ctx_names, ctx, lhs_name, lhs_ty),
                ];
                let mut rhs_ty = rhs_ty;
                let rhs_ty_opt = loop {
                    match rhs_ty.reduced().into_inner() {
                        TyKind::Form { form } => {
                            if matches!(&*form, FormKind::Never | FormKind::Sum { .. }) {
                                match Arc::unwrap_or_clone(form) {
                                    FormKind::Never => break None,
                                    FormKind::Sum { lhs_name, lhs_ty, rhs_ty: next_rhs_ty } => {
                                        ty_fields.push(
                                            pretty_ty_field(ctx_names, ctx, lhs_name, lhs_ty),
                                        );
                                        rhs_ty = next_rhs_ty;
                                    },
                                    _ => unreachable!(),
                                }
                            } else {
                                break Some(TyKind::Form { form });
                            }
                        },
                        TyKind::Stuck { stuck } => break Some(TyKind::Stuck { stuck }),
                    }
                };
                let rhs_ty_opt = rhs_ty_opt.map(|rhs_ty| {
                    let rhs_ty = {
                        rhs_ty
                        .prettier(ctx_names, ctx, ())
                        .with_precedence(Precedence::Func)
                        .doc
                    };
                    Doc::concat([
                        Doc::text(".."),
                        Doc::newline("", " "),
                        rhs_ty,
                    ])
                    .group()
                });

                pretty_list(
                    ty_fields,
                    rhs_ty_opt,
                    Doc::text("enum {"),
                    Doc::text("}"),
                    " ",
                )
                .with_precedence(Precedence::Atom)
            },

            FormKind::Sigma { head_name, head_ty, tail_ty } => {
                let orig_ctx_len = ctx.len();
                let mut ty_fields = vec![
                    pretty_ty_field(ctx_names, ctx, head_name.clone(), head_ty.clone()),
                ];
                
                let mut tail_ty = tail_ty.into_inner(ctx.len());
                ctx_names.push(head_name);
                ctx.push(head_ty);

                let tail_ty_opt = loop {
                    match tail_ty.reduced().into_inner() {
                        TyKind::Form { form } => {
                            if matches!(&*form, FormKind::Unit | FormKind::Sigma { .. }) {
                                match Arc::unwrap_or_clone(form) {
                                    FormKind::Unit => break None,
                                    FormKind::Sigma {
                                        head_name, head_ty, tail_ty: next_tail_ty,
                                    } => {
                                        ty_fields.push(
                                            pretty_ty_field(
                                                ctx_names,
                                                ctx,
                                                head_name.clone(),
                                                head_ty.clone(),
                                            ),
                                        );
                                        tail_ty = next_tail_ty.into_inner(ctx.len());
                                        ctx_names.push(head_name);
                                        ctx.push(head_ty);
                                    },
                                    _ => unreachable!(),
                                }
                            } else {
                                break Some(TyKind::Form { form });
                            }
                        },
                        TyKind::Stuck { stuck } => {
                            break Some(TyKind::Stuck { stuck });
                        },
                    }
                };
                let tail_ty_opt = tail_ty_opt.map(|tail_ty| {
                    let tail_ty = {
                        tail_ty
                        .prettier(ctx_names, ctx, ())
                        .with_precedence(Precedence::Func)
                        .doc
                    };
                    Doc::concat([
                        Doc::text(".."),
                        Doc::newline("", " "),
                        tail_ty,
                    ])
                    .group()
                });

                ctx_names.truncate(orig_ctx_len);
                ctx.truncate(orig_ctx_len);
                pretty_list(
                    ty_fields,
                    tail_ty_opt,
                    Doc::text("struct {"),
                    Doc::text("}"),
                    " ",
                )
                .with_precedence(Precedence::Atom)
            },

            FormKind::Pi { arg_name, arg_ty, res_ty } => {
                let orig_ctx_len = ctx.len();
                let mut ty_fields = vec![
                    pretty_ty_field(ctx_names, ctx, arg_name.clone(), arg_ty.clone()),
                ];

                let res_ty = res_ty.into_inner(ctx.len());
                ctx_names.push(arg_name);
                ctx.push(arg_ty);

                let res_ty = pretty_pi(ctx_names, ctx, res_ty, &mut ty_fields).doc;
                let res_ty = pretty_flat_or_braced(res_ty);
                ctx_names.truncate(orig_ctx_len);
                ctx.truncate(orig_ctx_len);

                let args_doc = {
                    pretty_list(
                        ty_fields,
                        None,
                        Doc::text("Fn("),
                        Doc::text(")"),
                        "",
                    )
                    .doc
                };
                
                ctx_names.truncate(orig_ctx_len);
                ctx.truncate(orig_ctx_len);
                Doc::concat([
                    args_doc,
                    Doc::text(" -> "),
                    res_ty,
                ])
                .with_precedence(Precedence::Func)
            },
        }
    }
}

impl Prettier for IntroKind {
    fn prettier(
        self,
        ctx_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        ty: Ty,
    ) -> PrecedenceDoc {
        match self {
            IntroKind::Tag { tag } => {
                let s: &str = &tag_as_text(tag);
                let s = format!("{:?}", s);
                Doc::text(s).with_precedence(Precedence::Atom)
            },

            IntroKind::Form { form } => {
                form.prettier(ctx_names, ctx, ())
            },

            IntroKind::Constant { ubig } => {
                Doc::text(format!("{}", ubig)).with_precedence(Precedence::Atom)
            },

            IntroKind::Succs { succ_count_m1, pred_tm } => {
                let succ_count = Doc::text(format!("{}", succ_count_m1 + 1usize));
                let pred_tm = {
                    pred_tm
                    .prettier(ctx_names, ctx, ty)
                    .with_precedence(Precedence::Add)
                    .doc
                    .group()
                };

                Doc::concat([
                    succ_count,
                    Doc::newline("", " "),
                    Doc::text("+"),
                    Doc::newline("", " "),
                    pred_tm,
                ])
                .with_precedence(Precedence::Add)
            },

            IntroKind::InjLhs { lhs_tm } => {
                let (lhs_name, lhs_ty, _) = ty.as_sum().unwrap();
                pretty_inj_lhs(ctx_names, ctx, lhs_name, lhs_ty, lhs_tm)
            },

            IntroKind::InjRhs { mut rhs_tm } => {
                let (lhs_name, _, mut rhs_ty) = ty.as_sum().unwrap();
                let mut lhs_names = vec![lhs_name];

                loop {
                    let rhs_tm = match rhs_tm.reduced() {
                        TmKind::Intro { intro } => {
                            if matches!(
                                &*intro,
                                IntroKind::InjLhs { .. } | IntroKind::InjRhs { .. },
                            ) {
                                match Arc::unwrap_or_clone(intro) {
                                    IntroKind::InjLhs { lhs_tm } => {
                                        let (lhs_name, lhs_ty, _) = rhs_ty.as_sum().unwrap();
                                        let num_injections = {
                                            lhs_names
                                            .into_iter()
                                            .position(|prev_lhs_name| {
                                                Unify::unify(prev_lhs_name, lhs_name.clone())
                                                .is_some()
                                            })
                                            .map_or(0, |n| n + 1)
                                        };
                                        let tm = {
                                            pretty_inj_lhs(
                                                ctx_names, ctx, lhs_name, lhs_ty, lhs_tm,
                                            )
                                            .with_precedence(Precedence::Inj)
                                            .doc
                                        };
                                        let mut docs = Vec::new();
                                        for _ in 0..num_injections {
                                            docs.push(Doc::text("..."));
                                            docs.push(Doc::newline("", " "));
                                        }
                                        docs.push(tm);

                                        break Doc::concat(docs).with_precedence(Precedence::Inj);
                                    },
                                    IntroKind::InjRhs { rhs_tm: next_rhs_tm } => {
                                        let (lhs_name, _, next_rhs_ty) = rhs_ty.as_sum().unwrap();
                                        lhs_names.push(lhs_name);
                                        rhs_ty = next_rhs_ty;
                                        rhs_tm = next_rhs_tm;
                                        continue;
                                    },
                                    _ => unreachable!(),
                                }
                            }
                            TmKind::Intro { intro }
                        },
                        TmKind::Proof => TmKind::Proof,
                        TmKind::Stuck { stuck } => TmKind::Stuck { stuck },
                    };

                    let mut docs = Vec::new();
                    for _ in 0..lhs_names.len() {
                        docs.push(Doc::text("..."));
                        docs.push(Doc::newline("", " "));
                    }
                    docs.push(
                        rhs_tm
                        .prettier(ctx_names, ctx, rhs_ty)
                        .with_precedence(Precedence::Inj)
                        .doc
                    );
                    break Doc::concat(docs).with_precedence(Precedence::Inj);
                }
            },

            IntroKind::Pair { head_tm, mut tail_tm } => {
                let (head_name, head_ty, tail_ty) = ty.as_sigma().unwrap();

                let mut tm_fields = vec![
                    pretty_tm_field(ctx_names, ctx, head_name, head_ty, head_tm.clone()),
                ];
                let mut tail_ty = tail_ty.bind(head_tm);

                let tail_tm_opt = loop {
                    match tail_tm.reduced().into_inner() {
                        TmKind::Intro { intro } => {
                            if matches!(&*intro, IntroKind::Pair { .. }) {
                                let IntroKind::Pair {
                                    head_tm, tail_tm: next_tail_tm,
                                } = Arc::unwrap_or_clone(intro) else { unreachable!() };

                                let (
                                    head_name,
                                    head_ty,
                                    next_tail_ty,
                                ) = tail_ty.as_sigma().unwrap();

                                tm_fields.push(
                                    pretty_tm_field(
                                        ctx_names,
                                        ctx,
                                        head_name,
                                        head_ty,
                                        head_tm.clone(),
                                    ),
                                );
                                tail_ty = next_tail_ty.bind(head_tm);
                                tail_tm = next_tail_tm;
                                continue;
                            }
                            break Some(TmKind::Intro { intro });
                        },
                        TmKind::Proof => {
                            if let Some(()) = tail_ty.clone().as_unit() {
                                break None;
                            }
                            break Some(TmKind::Proof);
                        },
                        TmKind::Stuck { stuck } => {
                            break Some(TmKind::Stuck { stuck });
                        },
                    }
                };
                let tail_tm_opt = tail_tm_opt.map(|tail_tm| {
                    let tail_tm = {
                        tail_tm
                        .prettier(ctx_names, ctx, tail_ty)
                        .with_precedence(Precedence::Equal)
                        .doc
                    };
                    Doc::concat([
                        Doc::text(".."),
                        Doc::newline("", " "),
                        tail_tm,
                    ])
                    .group()
                });

                pretty_list(
                    tm_fields,
                    tail_tm_opt,
                    Doc::text("("),
                    Doc::text(")"),
                    "",
                )
            },

            IntroKind::Func { res_tm } => {
                let orig_ctx_len = ctx.len();
                let (arg_name, arg_ty, res_ty) = ty.as_pi().unwrap();
                let mut ty_fields = vec![
                    pretty_ty_field(ctx_names, ctx, arg_name.clone(), arg_ty.clone()),
                ];
                
                let mut res_ty = res_ty.into_inner(ctx.len());
                let mut res_tm = res_tm.into_inner(ctx.len());
                ctx_names.push(arg_name);
                ctx.push(arg_ty);

                let res_tm = loop {
                    match res_tm.reduced() {
                        TmKind::Intro { intro } => {
                            if matches!(&*intro, IntroKind::Func { .. }) {
                                let IntroKind::Func {
                                    res_tm: next_res_tm,
                                } = Arc::unwrap_or_clone(intro) else { unreachable!() };
                                let (arg_name, arg_ty, next_res_ty) = res_ty.as_pi().unwrap();

                                ty_fields.push(
                                    pretty_ty_field(
                                        ctx_names,
                                        ctx,
                                        arg_name.clone(),
                                        arg_ty.clone(),
                                    ),
                                );
                                res_ty = next_res_ty.into_inner(ctx.len());
                                res_tm = next_res_tm.into_inner(ctx.len());
                                ctx_names.push(arg_name);
                                ctx.push(arg_ty);
                                continue;
                            }
                            break TmKind::Intro { intro };
                        },
                        tm => break tm,
                    }
                };

                let res_tm = {
                    res_tm
                    .prettier(ctx_names, ctx, res_ty)
                    .with_precedence(Precedence::Func)
                    .doc
                };

                ctx_names.truncate(orig_ctx_len);
                ctx.truncate(orig_ctx_len);

                let args_doc = {
                    pretty_list(ty_fields, None, Doc::text("fn("), Doc::text(")"), "")
                    .doc
                };
                Doc::concat([
                    args_doc,
                    Doc::newline("", " "),
                    Doc::text("=>"),
                    Doc::newline("", " "),
                    res_tm,
                ])
                .with_precedence(Precedence::Func)
            },
        }
    }
}

impl Prettier for NameKind {
    fn prettier(
        self,
        ctx_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        (): (),
    ) -> PrecedenceDoc {
        match self {
            NameKind::Tag { tag } => {
                Doc::text(tag_as_text(tag)).with_precedence(Precedence::Atom)
            },
            NameKind::Stuck { stuck } => {
                let stuck = {
                    stuck
                    .into_neutral()
                    .prettier(ctx_names, ctx, Ty::name())
                    .doc
                };
                Doc::concat([
                    Doc::text("$"),
                    stuck,
                ])
                .with_precedence(Precedence::Atom)
            },
        }
    }
}

impl Prettier for TyKind {
    fn prettier(
        self,
        ctx_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        (): (),
    ) -> PrecedenceDoc {
        match self {
            TyKind::Form { form } => {
                form.prettier(ctx_names, ctx, ())
            },
            TyKind::Stuck { stuck } => {
                stuck.into_neutral().prettier(ctx_names, ctx, Ty::universe())
            },
        }
    }
}

impl Prettier for TmKind {
    fn prettier(
        self,
        ctx_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        ty: Ty,
    ) -> PrecedenceDoc {
        match self {
            TmKind::Intro { intro } => {
                intro.prettier(ctx_names, ctx, ty)
            },
            TmKind::Proof => {
                Doc::text("_").with_precedence(Precedence::Atom)
            },
            TmKind::Stuck { stuck } => {
                stuck.into_neutral().prettier(ctx_names, ctx, ty)
            },
        }
    }
}

impl Prettier for NeutralKind {
    fn prettier(
        self,
        ctx_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        _ty: Ty,
    ) -> PrecedenceDoc {
        if let Some((func, args)) = neutral_as_app(ctx_names, ctx, self.clone()) {
            return pretty_app(ctx_names, ctx, func, args);
        }
        match self {
            NeutralKind::Var { index } => {
                let name = ctx_names[index].clone();
                let mut docs = {
                    ctx_names[(index + 1)..]
                    .iter()
                    .filter_map(|next_name| {
                        Unify::unify(name.clone(), next_name.clone())
                        .map(|_| Doc::text("^"))
                    })
                    .collect::<Vec<_>>()
                };
                docs.push(
                    name
                    .prettier(ctx_names, ctx, ())
                    .with_precedence(Precedence::Atom)
                    .doc
                );
                Doc::concat(docs).with_precedence(Precedence::Atom)
            },

            NeutralKind::Bind { .. } => {
                todo!()
            },

            NeutralKind::Add { tms } => {
                let mut tms = tms.into_iter();
                match tms.next() {
                    None => Doc::text("0").with_precedence(Precedence::Atom),
                    Some(tm) => {
                        let mut doc = {
                            tm
                            .prettier(ctx_names, ctx, Ty::nat())
                            .with_precedence(Precedence::Add)
                            .doc
                        };
                        for tm in tms {
                            let tm = {
                                tm
                                .prettier(ctx_names, ctx, Ty::nat())
                                .with_precedence(Precedence::Add)
                                .doc
                            };
                            doc = Doc::concat([
                                Doc::newline("", " "),
                                Doc::text("+"),
                                Doc::newline("", " "),
                                tm,
                            ]);
                        }
                        doc.with_precedence(Precedence::Add)
                    },
                }
            },

            NeutralKind::ProjHead { mut elim } => {
                let mut elim_ty = {
                    elim
                    .clone()
                    .reduced()
                    .as_stuck()
                    .unwrap()
                    .infer_ty(ctx)
                };
                let (head_name, _, _) = elim_ty.clone().as_sigma().unwrap();
                let mut bumps = Vec::new();
                loop {
                    if let NeutralKind::ProjTail { elim: next_elim } = Arc::unwrap_or_clone(
                        elim.clone().reduced().as_stuck().unwrap().into_neutral(),
                    ) {
                        let next_elim_ty = {
                            elim
                            .clone()
                            .reduced()
                            .as_stuck()
                            .unwrap()
                            .infer_ty(ctx)
                        };
                        let (next_head_name, _, _) = next_elim_ty.clone().as_sigma().unwrap();
                        if let Some(_) = Unify::unify(head_name.clone(), next_head_name) {
                            bumps.push(Doc::text("^"));
                        }
                        elim = next_elim;
                        elim_ty = next_elim_ty;
                        continue;
                    }
                    break;
                }

                let head_name = head_name.prettier(ctx_names, ctx, ()).doc;
                let elim = {
                    elim
                    .prettier(ctx_names, ctx, elim_ty)
                    .with_precedence(Precedence::Proj)
                    .doc
                };
                Doc::concat([
                    elim,
                    Doc::text("."),
                    Doc::concat(bumps),
                    head_name,
                ])
                .with_precedence(Precedence::Proj)
            },

            NeutralKind::ProjTail { elim } => {
                let elim_ty = {
                    elim
                    .clone()
                    .reduced()
                    .as_stuck()
                    .unwrap()
                    .infer_ty(ctx)
                };
                let elim = {
                    elim
                    .prettier(ctx_names, ctx, elim_ty)
                    .with_precedence(Precedence::Proj)
                    .doc
                };
                Doc::concat([
                    elim,
                    Doc::text("..."),
                ])
                .with_precedence(Precedence::Proj)
            },

            NeutralKind::ObsEqual { eq_ty, eq_tm_0, eq_tm_1 } => {
                let eq_tm_0 = {
                    eq_tm_0
                    .prettier(ctx_names, ctx, eq_ty.clone())
                    .with_precedence(Precedence::Add)
                    .doc
                    .group()
                };
                let eq_tm_1 = {
                    eq_tm_1
                    .prettier(ctx_names, ctx, eq_ty.clone())
                    .with_precedence(Precedence::Add)
                    .doc
                    .group()
                };

                Doc::concat([
                    eq_tm_0,
                    Doc::newline("", " "),
                    Doc::text("=="),
                    Doc::newline("", " "),
                    eq_tm_1,
                ])
                .with_precedence(Precedence::Equal)
            },

            | NeutralKind::Fold { .. }
            | NeutralKind::Explode { .. }
            | NeutralKind::Case { .. }
            | NeutralKind::App { .. }
            | NeutralKind::Cast { .. }
            => unreachable!(),
        }
    }
}

impl Prettier for StuckKind {
    fn prettier(
        self,
        ctx_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        (): (),
    ) -> PrecedenceDoc {
        let ty = self.clone().infer_ty(ctx);
        self.into_neutral().prettier(ctx_names, ctx, ty)
    }
}

fn upper_camel_case_to_lower_snake_case(
    s: &str,
) -> String {
    let mut ret = String::new();
    let mut iter = s.chars();
    let Some(c) = iter.next() else {
        return ret;
    };
    ret.extend(c.to_lowercase());
    for c in iter {
        if c.is_lowercase() {
            ret.push(c);
        } else {
            ret.push('_');
            ret.extend(c.to_lowercase());
        }
    }
    ret
}

const DEBUG_PRINT_META_TAGS: bool = false;

fn tag_as_text(tag: Tag) -> Text {
    match tag.kind {
        TagKind::Literal { s } => Text::from(s),
        TagKind::Meta { meta } => {
            let s = if DEBUG_PRINT_META_TAGS {
                format!("{:?}", meta)
            } else {
                if let MetaTag::Concat { tags } = &*meta
                && let Some(tag) = tags.last()
                {
                    return tag_as_text(tag.clone());
                }

                // TODO: be less hacky
                let mut s = format!("{:?}", meta);
                let len = s.find([' ', '(']).unwrap_or(s.len());
                s.truncate(len);
                let mut s = if meta.used_for_universe() {
                    s
                } else {
                    upper_camel_case_to_lower_snake_case(&s)
                };
                let hash = {
                    use std::hash::{BuildHasher, RandomState};
                    lazy_static! {
                        static ref META_TAG_HASHER: RandomState = RandomState::new();
                    }
                    META_TAG_HASHER.hash_one(&meta) as u16
                };

                use std::fmt::Write;
                write!(&mut s, "_{:04x}", hash).unwrap();
                s
            };
            Text::from(s)
        }
    }
}


fn pretty_flat_or_braced(doc: Doc) -> Doc {
    fn should_brace_strict(doc: &Doc) -> bool {
        match doc {
            Doc::Concat { docs } => {
                for doc in docs {
                    if should_brace_strict(doc) {
                        return true;
                    }
                }
                false
            },
            Doc::Text { .. } => false,
            Doc::Indent { .. } => false,
            Doc::Newline { .. } => true,
            Doc::Ungroup { doc } => should_brace_strict(doc),
        }
    }

    fn should_brace(doc: &Doc) -> Option<bool> {
        match doc {
            Doc::Concat { docs } => {
                let mut seen = false;
                for doc in docs {
                    if seen {
                        if should_brace_strict(doc) {
                            return Some(true);
                        }
                    } else {
                        match should_brace(doc) {
                            Some(false) => (),
                            None => seen = true,
                            Some(true) => return Some(true),
                        }
                    }
                }
                if seen {
                    None
                } else {
                    Some(false)
                }
            },
            Doc::Text { .. } => Some(false),
            Doc::Indent { .. } => Some(false),
            Doc::Newline { .. } => None,
            Doc::Ungroup { doc } => should_brace(doc),
        }
    }

    let doc = doc.group();
    if should_brace(&doc).unwrap_or(false) {
        Doc::concat([
            Doc::text("{"),
            Doc::indent(Doc::concat([
                Doc::newline("", ""),
                doc,
            ])),
            Doc::newline("", ""),
            Doc::text("}"),
        ])
        .ungroup()
    } else {
        doc
    }
}

fn pretty_list(
    items: Vec<Doc>,
    trailing_opt: Option<Doc>,
    start: Doc,
    end: Doc,
    on_flat_edge: &'static str,
) -> PrecedenceDoc {
    let mut docs = vec![start];
    let mut inner_docs = vec![Doc::newline("", on_flat_edge)];
    let mut any_pushed = false;
    for doc in items {
        if any_pushed {
            inner_docs.push(Doc::text(","));
            inner_docs.push(Doc::newline("", " "));
        }
        inner_docs.push(doc);
        any_pushed = true;
    }
    let nl = if let Some(trailing) = trailing_opt {
        if any_pushed {
            inner_docs.push(Doc::text(","));
            inner_docs.push(Doc::newline("", " "));
        }
        inner_docs.push(trailing);
        Doc::newline("", on_flat_edge)
    } else {
        Doc::newline(",", on_flat_edge)
    };
    docs.push(Doc::concat(inner_docs).indent());
    docs.push(nl);
    docs.push(end);
    Doc::concat(docs).group_strict().with_precedence(Precedence::Atom)
}

fn pretty_pi(
    ctx_names: &mut Vec<Name>,
    ctx: &mut Vec<Ty>,
    ty: Ty,
    ty_fields: &mut Vec<Doc>,
) -> PrecedenceDoc {
    let orig_ctx_len = ctx.len();
    let mut ty = ty;

    let ty = loop {
        match ty.reduced().into_inner() {
            TyKind::Form { form } => {
                if matches!(&*form, FormKind::Pi { .. }) {
                    let FormKind::Pi {
                        arg_name, arg_ty, res_ty: next_ty,
                    } = Arc::unwrap_or_clone(form) else { unreachable!() };
                    ty_fields.push(
                        pretty_ty_field(
                            ctx_names,
                            ctx,
                            arg_name.clone(),
                            arg_ty.clone(),
                        ),
                    );
                    ty = next_ty.into_inner(ctx.len());
                    ctx_names.push(arg_name);
                    ctx.push(arg_ty);
                } else {
                    break TyKind::Form { form };
                }
            },
            TyKind::Stuck { stuck } => break TyKind::Stuck { stuck },
        }
    };
    let ty = {
        ty
        .prettier(ctx_names, ctx, ())
        .with_precedence(Precedence::Func)
    };
    ctx_names.truncate(orig_ctx_len);
    ctx.truncate(orig_ctx_len);
    ty
}

fn pretty_func(
    ctx_names: &mut Vec<Name>,
    ctx: &mut Vec<Ty>,
    ty: Ty,
    tm: Tm,
    ty_fields: &mut Vec<Doc>,
) -> PrecedenceDoc {
    let orig_ctx_len = ctx.len();
    let mut ty = ty;
    let mut tm = tm.into_inner();

    let (ty, tm) = loop {
        match tm.reduced() {
            TmKind::Intro { intro } => {
                if matches!(&*intro, IntroKind::Func { .. }) {
                    let IntroKind::Func { res_tm } = Arc::unwrap_or_clone(intro) else {
                        unreachable!();
                    };
                    let (arg_name, arg_ty, res_ty) = ty.as_pi().unwrap();
                    ty_fields.push(
                        pretty_ty_field(
                            ctx_names,
                            ctx,
                            arg_name.clone(),
                            arg_ty.clone(),
                        ),
                    );
                    ty = res_ty.into_inner(ctx.len());
                    tm = res_tm.into_inner(ctx.len());
                    ctx_names.push(arg_name);
                    ctx.push(arg_ty);
                    continue;
                }
                break (ty, TmKind::Intro { intro });
            },
            tm => break (ty, tm),
        }
    };
    let tm = tm.prettier(ctx_names, ctx, ty).with_precedence(Precedence::Func);
    ctx_names.truncate(orig_ctx_len);
    ctx.truncate(orig_ctx_len);
    tm
}

fn pretty_ty_field(
    ctx_names: &mut Vec<Name>,
    ctx: &mut Vec<Ty>,
    name: Name,
    ty: Ty,
) -> Doc {
    let name = name.prettier(ctx_names, ctx, ()).with_precedence(Precedence::Atom).doc;
    let mut ty_fields = Vec::new();
    let ty = pretty_pi(ctx_names, ctx, ty, &mut ty_fields).doc;
    let ty = pretty_flat_or_braced(ty);

    if ty_fields.is_empty() {
        Doc::concat([
            name,
            Doc::text(": "),
            ty,
        ])
        .group()
    } else {
        let args_doc = pretty_list(
            ty_fields,
            None,
            Doc::text("("),
            Doc::text(")"),
            "",
        );
        Doc::concat([
            name,
            args_doc.doc,
            Doc::text(": "),
            ty,
        ])
        .group()
    }
}

fn pretty_tm_field(
    ctx_names: &mut Vec<Name>,
    ctx: &mut Vec<Ty>,
    name: Name,
    ty: Ty,
    tm: Tm,
) -> Doc {
    let name_doc = {
        name
        .clone()
        .prettier(ctx_names, ctx, ())
        .with_precedence(Precedence::Atom)
        .doc
    };

    if let Some(index) = tm.clone().as_var()
    && let Some(_) = Unify::unify(ctx_names[index].clone(), name.clone())
    && {
        ctx_names[(index + 1)..]
        .iter()
        .all(|next_name| Unify::unify(next_name.clone(), name.clone()).is_none())
    } {
        return name_doc;
    }

    let mut ty_fields = Vec::new();
    let tm = pretty_func(ctx_names, ctx, ty, tm, &mut ty_fields).doc;
    let tm = pretty_flat_or_braced(tm);

    if ty_fields.is_empty() {
        Doc::concat([
            name_doc,
            Doc::text(" = "),
            tm,
        ])
        .group()
    } else {
        let args_doc = pretty_list(
            ty_fields,
            None,
            Doc::text("("),
            Doc::text(")"),
            "",
        );
        Doc::concat([
            name_doc,
            args_doc.doc,
            Doc::text(" = "),
            tm,
        ])
        .group()
    }
}

fn pretty_inj_lhs(
    ctx_names: &mut Vec<Name>,
    ctx: &mut Vec<Ty>,
    lhs_name: Name,
    lhs_ty: Ty,
    lhs_tm: OrLazy<TmKind>,
) -> PrecedenceDoc {
    let lhs_tm = {
        lhs_tm
        .prettier(ctx_names, ctx, lhs_ty)
        .with_precedence(Precedence::Inj)
        .doc
        .group()
    };
    let lhs_name = lhs_name.prettier(ctx_names, ctx, ()).doc;

    Doc::concat([
        Doc::text("."),
        lhs_name,
        Doc::newline("", " "),
        lhs_tm,
    ])
    .with_precedence(Precedence::Inj)
}

fn neutral_as_app(
    ctx_names: &mut Vec<Name>,
    ctx: &mut Vec<Ty>,
    neutral_kind: NeutralKind,
) -> Option<(PrecedenceDoc, Vec<(Name, Ty, Tm)>)> {
    match neutral_kind {
        | NeutralKind::Var { .. }
        | NeutralKind::Bind { .. }
        | NeutralKind::Add { .. }
        | NeutralKind::ProjHead { .. }
        | NeutralKind::ProjTail { .. }
        | NeutralKind::ObsEqual { .. }
        => None,

        NeutralKind::Fold { elim, motive, zero_inhab, succ_inhab } => {
            let func = Doc::text("fold").with_precedence(Precedence::Atom);
            let args = vec![
                (
                    Name::from("Motive"),
                    Ty::pi(
                        Name::from("elim"),
                        Ty::nat(),
                        Scope::constant(Ty::universe()),
                    ),
                    motive.clone().map_without_capture(|ty| ty.into_tm()).into_func(),
                ),
                (
                    Name::from("on_zero"),
                    motive.clone().bind(Tm::zero()),
                    zero_inhab,
                ),
                (
                    Name::from("on_succ"),
                    Ty::pi(
                        Name::from("elim"),
                        Ty::nat(),
                        Scope::make(ctx.len(), |elim| {
                            Ty::pi(
                                Name::from("state"),
                                motive.clone().bind(elim.clone()),
                                Scope::constant(
                                    motive.bind(elim.succs(Ubig::ONE)),
                                ),
                            )
                        }),
                    ),
                    succ_inhab
                    .map_without_capture(|succ_inhab| succ_inhab.into_func())
                    .into_func()
                ),
                (
                    Name::from("elim"),
                    Ty::nat(),
                    elim,
                ),
            ];
            Some((func, args))
        },

        NeutralKind::Explode { motive } => {
            let func = Doc::text("explode").with_precedence(Precedence::Atom);
            let args = vec![
                (
                    Name::from("Motive"),
                    Ty::pi(
                        Name::from("elim"),
                        Ty::never(),
                        Scope::constant(Ty::universe()),
                    ),
                    motive.clone().map_without_capture(|ty| Weaken::new(ty).into_tm()).into_func(),
                ),
                (
                    Name::from("elim"),
                    Ty::never(),
                    Tm::proof(),
                ),
            ];
            Some((func, args))
        },

        NeutralKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab } => {
            let sum_ty = elim.clone().as_stuck().unwrap().infer_ty(ctx);
            let (_, lhs_ty, rhs_ty) = sum_ty.clone().as_sum().unwrap();

            let func = Doc::text("case").with_precedence(Precedence::Atom);
            let args = vec![
                (
                    Name::from("lhs_name"),
                    Ty::name(),
                    lhs_name.into_tm(),
                ),
                (
                    Name::from("Lhs"),
                    Ty::universe(),
                    lhs_ty.clone().into_tm(),
                ),
                (
                    Name::from("Rhs"),
                    Ty::universe(),
                    rhs_ty.clone().into_tm(),
                ),
                (
                    Name::from("Motive"),
                    Ty::pi(
                        Name::from("elim"),
                        sum_ty.clone(),
                        Scope::constant(Ty::universe()),
                    ),
                    motive.clone().map_without_capture(|ty| ty.into_tm()).into_func(),
                ),
                (
                    Name::from("on_lhs"),
                    Ty::pi(
                        Name::from("lhs"),
                        lhs_ty,
                        Scope::make(ctx.len(), |lhs| {
                            motive
                            .clone()
                            .bind(lhs.inj_lhs())
                        }),
                    ),
                    lhs_inhab.into_func(),
                ),
                (
                    Name::from("on_rhs"),
                    Ty::pi(
                        Name::from("rhs"),
                        rhs_ty,
                        Scope::make(ctx.len(), |rhs| {
                            motive
                            .clone()
                            .bind(rhs.inj_rhs())
                        }),
                    ),
                    rhs_inhab.into_func(),
                ),
                (
                    Name::from("elim"),
                    sum_ty,
                    elim,
                ),
            ];
            Some((func, args))
        },

        NeutralKind::App { elim, arg_tm } => {
            let elim = elim.as_stuck().unwrap();
            let (arg_name, arg_ty, _) = elim.clone().infer_ty(ctx).as_pi().unwrap();
            let (func, mut args) = match neutral_as_app(
                ctx_names,
                ctx,
                Arc::unwrap_or_clone(elim.clone().into_inner().into_neutral()),
            ) {
                Some((func, args)) => (func, args),
                None => {
                    let func = elim.prettier(ctx_names, ctx, ());
                    (func, Vec::new())
                },
            };
            args.push((arg_name, arg_ty, arg_tm));
            Some((func, args))
        },

        NeutralKind::Cast { ty_0, ty_1, tm_0 } => {
            let func = Doc::text("cast").with_precedence(Precedence::Atom);
            let args = vec![
                (
                    Name::from("From"),
                    Ty::universe(),
                    ty_0.clone().into_tm(),
                ),
                (
                    Name::from("Into"),
                    Ty::universe(),
                    ty_1.clone().into_tm(),
                ),
                (
                    Name::from("elim"),
                    Ty::obs_equal(
                        Ty::universe(),
                        ty_0.clone().into_tm(),
                        ty_1.into_tm(),
                    ),
                    Tm::proof(),
                ),
                (
                    Name::from("val"),
                    ty_0,
                    tm_0,
                ),
            ];
            Some((func, args))
        },
    }
}

fn pretty_app(
    ctx_names: &mut Vec<Name>,
    ctx: &mut Vec<Ty>,
    func: PrecedenceDoc,
    args: Vec<(Name, Ty, Tm)>,
) -> PrecedenceDoc {
    let tm_fields = {
        args
        .into_iter()
        .map(|(name, ty, tm)| pretty_tm_field(ctx_names, ctx, name, ty, tm))
        .collect::<Vec<_>>()
    };
    let args_doc = pretty_list(
        tm_fields,
        None,
        Doc::text("("),
        Doc::text(")"),
        "",
    );
    let func = func.with_precedence(Precedence::Proj).doc;
    Doc::concat([func, args_doc.doc]).with_precedence(Precedence::App)
}

