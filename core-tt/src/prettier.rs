use crate::priv_prelude::*;

fn insert_newlines(s: &mut String, positions: &[usize]) {
    assert!(positions.is_sorted());
    assert!(positions.iter().copied().all(|position| s.is_char_boundary(position)));
    assert!(s.len().strict_add(positions.len()) < isize::MAX as usize);
    s.reserve(positions.len());

    let (ptr, len, cap) = mem::take(s).into_raw_parts();
    let mut unshifted_end = len;

    for (index, position) in positions.iter().copied().enumerate().rev() {
        unsafe {
            let count = unshifted_end.unchecked_sub(position);
            let src = ptr.add(position);
            let nl = src.add(index);
            let dst = nl.add(1);
            ptr::copy(src, dst, count);
            ptr::write(nl, b'\n');
        }
        unshifted_end = position;
    }

    *s = unsafe {
        String::from_raw_parts(ptr, len.unchecked_add(positions.len()), cap)
    };
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

const LINE_WIDTH: usize = 100;
const RIBBON_WIDTH: usize = 60;
const INDENT_STR: &'static str = "    ";

fn line_fits(indent: usize, width: usize) -> bool {
    width <= RIBBON_WIDTH && width + indent * INDENT_STR.len() <= LINE_WIDTH
}

struct PrettyLines {
    precedence: Precedence,
    lines: Vec<(usize, String)>,
}


impl PrettyLines {
    pub fn from_string(s: impl Into<String>) -> PrettyLines {
        let s = s.into();
        assert!(!s.contains('\n'));
        let precedence = Precedence::Atom;
        let lines = vec![(0, s)];
        PrettyLines { precedence, lines }
    }

    pub fn with_precedence(mut self, required: Precedence) -> PrettyLines {
        if required <= self.precedence {
            return self;
        }

        self.precedence = Precedence::Atom;

        let ((indent, line), lines) = self.lines.split_first_mut().unwrap();
        let indent = *indent;
        if lines.is_empty() && line_fits(
            indent,
            line.encode_utf16().count() + "{ ".len() + " }".len(),
        ) {
            line.insert_str(0, "{ ");
            line.push_str(" }");
            return self;
        }

        for (indent, _line) in self.lines.iter_mut() {
            *indent += 1;
        }
        self.lines.insert(0, (indent, String::from("{")));
        self.lines.push((indent, String::from("}")));
        self
    }

    pub fn glue_or_break_all<I>(
        pretties: I,
        precedence: Precedence,
    ) -> PrettyLines
    where
        I: IntoIterator<Item = PrettyLines>,
        for<'a> &'a I: IntoIterator<Item = &'a PrettyLines>,
    {
        let mut iter = (&pretties).into_iter();
        let (indent, mut last_line_width) = {
            let pretty = iter.next().unwrap();
            assert!(pretty.precedence >= precedence);
            let (indent, line) = pretty.lines.last().unwrap();
            let line_width = line.encode_utf16().count();
            (*indent, line_width)
        };
        let do_glue = loop {
            if !line_fits(indent, last_line_width) {
                break false;
            }
            let Some(pretty) = iter.next() else {
                break true;
            };
            assert!(pretty.precedence >= precedence);
            let ((next_indent, line), lines) = pretty.lines.split_first().unwrap();
            assert_eq!(indent, *next_indent);
            last_line_width += line.encode_utf16().count();
            if let Some((next_indent, line)) = lines.last() {
                if !line_fits(indent, last_line_width) {
                    break false;
                }
                assert_eq!(indent, *next_indent);
                last_line_width = line.encode_utf16().count();
            }
        };
        drop(iter);

        let lines = if do_glue {
            let mut lines = Vec::with_capacity(
                (&pretties)
                .into_iter()
                .map(|pretty| pretty.lines.len().strict_sub(1))
                .sum::<usize>()
                + 1,
            );
            let mut iter = pretties.into_iter();
            let (_, mut last_line) = {
                let pretty = iter.next().unwrap();
                let num_lines = pretty.lines.len();
                let mut line_iter = pretty.lines.into_iter();
                lines.extend(line_iter.by_ref().take(num_lines.strict_sub(1)));
                line_iter.next().unwrap()
            };
            for pretty in iter {
                let num_lines = pretty.lines.len();
                let mut line_iter = pretty.lines.into_iter();
                let (_, line) = line_iter.next().unwrap();
                last_line.push_str(&line);
                if let Some(num_intermediate_lines) = num_lines.checked_sub(2) {
                    lines.push((indent, last_line));
                    lines.extend(line_iter.by_ref().take(num_intermediate_lines));
                    let (_, next_last_line) = line_iter.next().unwrap();
                    last_line = next_last_line;
                }
            }
            lines.push((indent, last_line));
            lines
        } else {
            let mut lines = Vec::with_capacity(
                (&pretties).into_iter().map(|pretty| pretty.lines.len()).sum()
            );
            for pretty in pretties {
                lines.extend(pretty.lines);
            }
            lines
        };
        PrettyLines { precedence, lines }
    }
}

trait Prettier: WellFormed {
    fn prettier(
        self,
        var_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        params: Self::Params,
    ) -> PrettyLines;
}

impl<T> Prettier for Weaken<T>
where
    T: Contextual,
    T: Prettier,
{
    fn prettier(
        self,
        var_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        params: T::Params,
    ) -> PrettyLines {
        self.into_inner().prettier(var_names, ctx, params)
    }
}

impl<T> Prettier for Arc<T>
where
    T: Clone,
    T: Prettier,
{
    fn prettier(
        self,
        var_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        params: T::Params,
    ) -> PrettyLines {
        Arc::unwrap_or_clone(self).prettier(var_names, ctx, params)
    }
}

impl<T> Prettier for OrLazy<T>
where
    T: Prettier,
    T: AsTmKind,
{
    fn prettier(
        self,
        var_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        params: T::Params,
    ) -> PrettyLines {
        self.reduced().prettier(var_names, ctx, params)
    }
}

fn pretty_ty_field(
    var_names: &mut Vec<Name>,
    ctx: &mut Vec<Ty>,
    name: PrettyLines,
    ty: Ty,
) -> PrettyLines {
    todo!()
}

fn pretty_tm_field(
    var_names: &mut Vec<Name>,
    ctx: &mut Vec<Ty>,
    name: PrettyLines,
    ty: Ty,
    tm: Tm,
) -> PrettyLines {
    let ctx_len = ctx.len();
    let mut ty = ty;
    let mut tm = tm;
    let mut args = Vec::new();
    loop {
        let Some((arg_name, arg_ty, res_ty)) = ty.as_sigma() else {
            break;
        };
        let arg_name = arg_name.prettier(var_names, ctx, ());
        let arg = pretty_ty_field(var_names, ctx, arg_name, arg_ty.clone());
        args.push(arg);
        ty = res_ty.into_inner(ctx.len());
        tm = match tm.reduced().into_inner() {
            TmKind::Intro { intro } => {
                let IntroKind::Func { res_tm } = Arc::unwrap_or_clone(intro) else {
                    unreachable!();
                };
                res_tm.into_inner(ctx.len())
            },
            _ => {
                tm.app(Tm::var(ctx.len()))
            },
        };
        ctx.push(arg_ty);
    }
}

impl Prettier for IntroKind {
    fn prettier(
        self,
        var_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        ty: Ty,
    ) -> PrettyLines {
        fn pretty_inj_lhs(
            var_names: &mut Vec<Name>,
            ctx: &mut Vec<Ty>,
            lhs_name: Name,
            lhs_ty: Ty,
            lhs_tm: Tm,
        ) -> (PrettyLines, PrettyLines) {
            let mut lhs_name = lhs_name.prettier(var_names, ctx, ());
            let lhs_tm = {
                lhs_tm
                .prettier(var_names, ctx, lhs_ty)
                .with_precedence(Precedence::Inj)
            };
            let (_, line) = lhs_name.lines.first_mut().unwrap();
            line.insert_str(0, ".");
            if {
                let (_, line) = lhs_tm.lines.first_mut().unwrap();
                !line.starts_with("(")
            } {
                line.push(' ');
            }
            (lhs_name, lhs_tm)
        }

        match self {
            IntroKind::Tag { tag } => {
                PrettyLines::from_string(format!("{:?}", tag.as_string()))
            },

            IntroKind::Form { form } => {
                form.prettier(var_names, ctx, ())
            },

            IntroKind::Constant { ubig } => {
                PrettyLines::from_string(format!("{}", ubig))
            },

            IntroKind::Succs { succ_count_m1, pred_tm } => {
                let succ_count = PrettyLines::from_string(
                    format!("{}", succ_count_m1 + 1),
                );
                let add = PrettyLines::from_string("+");
                let pred_tm = {
                    pred_tm
                    .prettier(var_names, ctx, ty)
                    .with_precedence(Precedence::Add)
                };
                PrettyLines::glue_or_break_all(
                    [succ_count, add, pred_tm],
                    Precedence::Add,
                )
            },

            IntroKind::InjLhs { lhs_tm } => {
                let (lhs_name, lhs_ty, _) = ty.as_sum().unwrap();
                let (lhs_name, lhs_tm) = pretty_inj_lhs(
                    var_names,
                    ctx,
                    lhs_name,
                    lhs_ty,
                    Weaken::new(lhs_tm),
                );
                PrettyLines::glue_or_break_all([lhs_name, lhs_tm], Precedence::Inj)
            },

            IntroKind::InjRhs { rhs_tm } => {
                let mut rhs_tm = rhs_tm;
                let (mut lhs_names, mut rhs_ty) = {
                    let (lhs_name, _, rhs_ty) = ty.as_sum().unwrap();
                    (vec![lhs_name], rhs_ty)
                };
                loop {
                    if let Some(intro) = rhs_tm.clone().reduced().as_intro() {
                        match Arc::unwrap_or_clone(intro) {
                            IntroKind::InjRhs { rhs_tm: next_rhs_tm } => {
                                let (lhs_name, _, next_rhs_ty) = rhs_ty.as_sum().unwrap();
                                lhs_names.push(lhs_name);
                                rhs_tm = next_rhs_tm;
                                rhs_ty = next_rhs_ty;
                                continue;
                            },
                            IntroKind::InjLhs { lhs_tm } => {
                                let (final_lhs_name, lhs_ty, _) = rhs_ty.as_sum().unwrap();
                                while let Some(lhs_name) = lhs_names.pop() {
                                    if let Some(_) = Unify::unify(
                                        lhs_name,
                                        final_lhs_name.clone(),
                                    ) {
                                        lhs_names.push(final_lhs_name.clone());
                                        break;
                                    }
                                }
                                let mut pretties = {
                                    lhs_names
                                    .into_iter()
                                    .map(|_| PrettyLines::from_string("... "))
                                    .collect::<Vec<_>>()
                                };
                                let (lhs_name, lhs_tm) = pretty_inj_lhs(
                                    var_names,
                                    ctx,
                                    final_lhs_name,
                                    lhs_ty,
                                    Weaken::new(lhs_tm),
                                );
                                pretties.push(lhs_name);
                                pretties.push(lhs_tm);
                                break PrettyLines::glue_or_break_all(pretties, Precedence::Inj);
                            },
                            _ => (),
                        }
                    }
                    let mut pretties = {
                        lhs_names
                        .into_iter()
                        .map(|_| PrettyLines::from_string("... "))
                        .collect::<Vec<_>>()
                    };
                    let rhs_tm = rhs_tm.prettier(var_names, ctx, rhs_ty);
                    pretties.push(rhs_tm);
                    break PrettyLines::glue_or_break_all(pretties, Precedence::Inj);
                }
            },

            IntroKind::Pair { head_tm, tail_tm } => {
                let (head_name, head_ty, tail_ty) = ty.as_sigma().unwrap();
                let head_name = head_name.prettier(var_names, ctx, ());
                let head_field = 
            },

            IntroKind::Func { res_tm } => {
                let (arg_name, arg_ty, res_ty) = ty.as_pi().unwrap();
                todo!()
            },
        }
    }
}

impl Prettier for FormKind {
    fn prettier(
        self,
        var_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        (): (),
    ) -> PrettyLines {
        todo!()
    }
}

impl Prettier for NameKind {
    fn prettier(
        self,
        var_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        (): (),
    ) -> PrettyLines {
        todo!()
    }
}

impl Prettier for TyKind {
    fn prettier(
        self,
        var_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        (): (),
    ) -> PrettyLines {
        todo!()
    }
}

impl Prettier for TmKind {
    fn prettier(
        self,
        var_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        ty: Ty,
    ) -> PrettyLines {
        match self {
            TmKind::Intro { intro } => intro.prettier(var_names, ctx, ty),
            TmKind::Proof => PrettyLines::from_string("_"),
            TmKind::Stuck { stuck } => stuck.prettier(var_names, ctx, ()),
        }
    }
}

impl Prettier for StuckKind {
    fn prettier(
        self,
        var_names: &mut Vec<Name>,
        ctx: &mut Vec<Ty>,
        (): (),
    ) -> PrettyLines {
        todo!()
    }
}

impl Tag {
    fn as_string(&self) -> std::borrow::Cow<'_, str> {
        match &self.kind {
            TagKind::Literal { s } => std::borrow::Cow::Borrowed(&s),
            TagKind::Meta { meta } => {
                // TODO: be less hacky.
                use std::fmt::Write;
                let mut s = String::from("@");
                write!(&mut s, "{:?}", meta).unwrap();
                let len = s.split(' ').next().unwrap().len();
                s.truncate(len);
                std::borrow::Cow::Owned(s)
            },
        }
    }
}
