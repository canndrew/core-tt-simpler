#![no_main]

use {
    std::{mem, sync::Arc},
    arbitrary::Arbitrary,
    libfuzzer_sys::fuzz_target,
    core_tt_simpler::{
        Ubig, Tag,
        Ty, Tm, Scope,
        Unify,
    },
};

#[derive(Debug)]
struct FuzzTm {
    var_tys: Vec<Ty>,
    ty: Ty,
    tm: Tm,
}

impl FuzzTm {
    pub fn scoped_0(&self) -> Option<(Ty, Tm)> {
        if !self.var_tys.is_empty() {
            return None;
        }
        Some((self.ty.clone(), self.tm.clone()))
    }

    pub fn scoped_1(&self, ctx_len: usize) -> Option<(Ty, Scope<(Ty, Tm)>)> {
        if self.var_tys.len() != 1 {
            return None;
        }
        let var_ty = self.var_tys[0].clone();
        let scoped = Scope::new(
            ctx_len,
            (self.ty.clone(), self.tm.clone()),
        );
        Some((var_ty, scoped))
    }

    pub fn scoped_2(&self, ctx_len: usize) -> Option<(Ty, Scope<(Ty, Scope<(Ty, Tm)>)>)> {
        if self.var_tys.len() != 2 {
            return None;
        }
        let var_ty_0 = self.var_tys[0].clone();
        let var_ty_1 = self.var_tys[1].clone();

        let scoped = Scope::new(
            ctx_len + 1,
            (self.ty.clone(), self.tm.clone()),
        );
        let scoped = Scope::new(
            ctx_len,
            (var_ty_1, scoped),
        );

        Some((var_ty_0, scoped))
    }
}

#[derive(Arbitrary, Debug)]
enum Op {
    EnterScope,
    ExitScope,

    Name,
    Tag {
        index: usize,
    },

    Universe,

    NatTy,
    Zero,
    Succs {
        succ_count: u8,
    },
    Fold,

    Equal,
    Refl,
    // TODO
    //Cong,

    Never,
    Explode,

    UnitTy,
    UnitTm,

    Sum,
    InjLhs,
    InjRhs,
    Case,

    Sigma,
    Pair,
    ProjHead,
    ProjTail,

    Pi,
    Func,
    App,
}

#[derive(Debug)]
struct State {
    ctx: Vec<Ty>,
    stacks: Vec<Vec<FuzzTm>>,
    stack: Vec<FuzzTm>,
    tags: Vec<Arc<str>>,
}

impl State {
    pub fn new() -> State {
        State {
            ctx: Vec::new(),
            stacks: Vec::new(),
            stack: Vec::new(),
            tags: Vec::new(),
        }
    }

    pub fn push(&mut self, ty: Ty, tm: Tm) {
        let var_tys = Vec::new();
        self.stack.push(FuzzTm { var_tys, ty, tm });
    }

    pub fn execute(&mut self, op: Op) -> Option<()> {
        let ctx_len = self.ctx.len();
        match op {
            Op::EnterScope => {
                let var_ty = self.stack.last()?;
                let (var_ty_ty, var_ty) = var_ty.scoped_0()?;
                var_ty_ty.as_universe()?;
                let var_ty = var_ty.into_ty();

                let tm = Tm::var(ctx_len);
                self.ctx.push(var_ty.clone());
                self.stacks.push(mem::take(&mut self.stack));
                self.push(var_ty, tm);
            },

            Op::ExitScope => {
                if self.stacks.is_empty() {
                    return None;
                }
                let mut body = self.stack.pop()?;
                let var_ty = self.ctx.pop().unwrap();
                let stack = self.stacks.pop().unwrap();
                self.stack = stack;

                body.var_tys.insert(0, var_ty);
                self.stack.push(body);
            },

            Op::Name => {
                let ty = Ty::universe();
                let tm = Ty::name().into_tm();
                self.push(ty, tm);
            },

            Op::Tag { index } => {
                let index = index % (self.tags.len() + 1);
                let tag = Tag::from(
                    self
                    .tags
                    .get(index)
                    .cloned()
                    .unwrap_or_else(|| {
                        let tag = Arc::from(format!("v{}", self.tags.len()));
                        self.tags.push(tag);
                        self.tags.last().unwrap().clone()
                    })
                );

                let ty = Ty::name();
                let tm = Tm::tag(tag);
                self.push(ty, tm);
            },

            Op::Universe => {
                let ty = Ty::universe();
                let tm = Ty::universe().into_tm();
                self.push(ty, tm);
            },

            Op::NatTy => {
                let ty = Ty::universe();
                let tm = Ty::nat().into_tm();
                self.push(ty, tm);
            },

            Op::Zero => {
                let ty = Ty::nat();
                let tm = Tm::constant(Ubig::ZERO);
                self.push(ty, tm);
            },

            Op::Succs { succ_count } => {
                let pred_tm = self.stack.last()?;
                let (pred_tm_ty, pred_tm) = pred_tm.scoped_0()?;
                pred_tm_ty.as_nat()?;

                let ty = Ty::nat();
                let tm = pred_tm.succs(succ_count);
                self.push(ty, tm);
            },

            Op::Fold => {
                let index = self.stack.len().checked_sub(4)?;
                let elim = &self.stack[index];
                let motive = &self.stack[index + 1];
                let zero_inhab = &self.stack[index + 2];
                let succ_inhab = &self.stack[index + 3];

                let (elim_ty, elim) = elim.scoped_0()?;
                elim_ty.as_nat()?;

                let (motive_elim_ty, motive) = motive.scoped_1(ctx_len)?;
                motive_elim_ty.as_nat()?;
                let (motive_ty, motive) = motive.lift_tuple();
                motive_ty.try_strengthen().ok()?.as_universe()?;
                let motive = motive.map_without_capture(|motive| motive.into_ty());

                let (zero_inhab_ty, zero_inhab) = zero_inhab.scoped_0()?;
                Unify::unify(
                    &mut self.ctx,
                    (),
                    zero_inhab_ty,
                    motive
                    .clone()
                    .bind(Tm::zero())
                )?;

                let (succ_inhab_elim_ty, succ_inhab) = succ_inhab.scoped_2(ctx_len)?;
                succ_inhab_elim_ty.as_nat()?;
                let (succ_inhab_state_ty, succ_inhab) = succ_inhab.lift_tuple();
                Unify::unify(
                    &mut self.ctx,
                    (Ty::nat(), Scope::constant(())),
                    succ_inhab_state_ty,
                    motive.clone(),
                )?;
                let (succ_inhab_ty, succ_inhab) = {
                    succ_inhab.map_without_capture(Scope::lift_tuple).lift_tuple()
                };
                Unify::unify(
                    &mut self.ctx,
                    (Ty::nat(), Scope::constant(())),
                    succ_inhab_ty
                    .try_map_without_capture(|succ_inhab_ty| {
                        succ_inhab_ty.try_strengthen().ok()
                    })?,
                    Scope::make(
                        ctx_len,
                        |elim| motive.clone().bind(elim.succs(Ubig::ONE)),
                    ),
                )?;

                let ty = motive.clone().bind(elim.clone());
                let tm = Tm::fold(elim, motive, zero_inhab, succ_inhab);
                self.push(ty, tm);
            },

            Op::Equal => {
                let index = self.stack.len().checked_sub(2)?;
                let eq_tm_0 = &self.stack[index];
                let eq_tm_1 = &self.stack[index + 1];

                let (eq_ty_0, eq_tm_0) = eq_tm_0.scoped_0()?;
                let (eq_ty_1, eq_tm_1) = eq_tm_1.scoped_0()?;
                let eq_ty = Unify::unify(&mut self.ctx, (), eq_ty_0, eq_ty_1)?;

                let ty = Ty::universe();
                let tm = Ty::obs_equal(eq_ty, eq_tm_0, eq_tm_1).into_tm();
                self.push(ty, tm);
            },

            Op::Refl => {
                let eq_tm = self.stack.last()?;
                let (eq_ty, eq_tm) = eq_tm.scoped_0()?;

                let ty = Ty::obs_equal(eq_ty, eq_tm.clone(), eq_tm.clone());
                let tm = eq_tm.obs_refl();
                self.push(ty, tm);
            },

            /*
            Op::Cong => {
                let index = self.stack.len().checked_sub(3)?;
                let elim = &self.stack[index];
                let motive = &self.stack[index + 1];
                let inhab = &self.stack[index + 2];

                let (elim_ty, elim) = elim.scoped_0()?;
                let (eq_ty, eq_tm_0, eq_tm_1) = elim_ty.as_equal()?;

                let (motive_eq_tm_1_ty, motive) = motive.scoped_2(self.stacks.len())?;
                if !motive.inner().inner().is_prop() {
                    return None;
                }
                let eq_ty = Unify::unify(motive_eq_tm_1_ty, eq_ty)?;
                let (motive_elim_ty, motive) = motive.lift_tuple();
                motive_elim_ty
                .try_map(self.stacks.len(), |eq_tm_1, motive_elim_ty| {
                    Unify::unify(
                        motive_elim_ty,
                        Ty::equal(eq_ty.clone(), eq_tm_0.clone(), eq_tm_1)
                    )
                })?;
                let (motive_ty, motive) = motive.map_without_capture(Scope::lift_tuple).lift_tuple();
                motive_ty.try_strengthen().ok()?.try_strengthen().ok()?.as_universe()?;
                let motive = motive.map_without_capture(|motive| {
                    motive.map_without_capture(|motive| motive.into_ty())
                });

                let (inhab_ty, inhab) = inhab.scoped_0()?;
                Unify::unify(
                    inhab_ty,
                    motive
                    .clone()
                    .bind(eq_tm_0.clone())
                    .bind(eq_tm_0.refl())
                )?;

                let ty = motive.clone().bind(eq_tm_1).bind(elim.clone());
                let tm = Tm::cong(elim, motive, inhab);
                self.push(ty, tm);
            },
            */

            Op::Never => {
                let ty = Ty::universe();
                let tm = Ty::never().into_tm();
                self.push(ty, tm);
            },

            Op::Explode => {
                let index = self.stack.len().checked_sub(2)?;
                let elim = &self.stack[index];
                let motive = &self.stack[index + 1];
                
                let (elim_ty, elim) = elim.scoped_0()?;
                elim_ty.as_never()?;

                let (motive_elim_ty, motive) = motive.scoped_1(ctx_len)?;
                motive_elim_ty.as_never()?;
                let (motive_ty, motive) = motive.lift_tuple();
                motive_ty.try_strengthen().ok()?.as_universe()?;
                let motive = motive.map_without_capture(|motive| motive.into_ty());

                let ty = motive.clone().bind(elim.clone());
                let tm = Tm::explode(elim, motive);
                self.push(ty, tm);
            },

            Op::UnitTy => {
                let ty = Ty::universe();
                let tm = Ty::unit().into_tm();
                self.push(ty, tm);
            },

            Op::UnitTm => {
                let ty = Ty::unit();
                let tm = Tm::unit();
                self.push(ty, tm);
            },

            Op::Sum => {
                let index = self.stack.len().checked_sub(3)?;
                let lhs_name = &self.stack[index];
                let lhs_ty = &self.stack[index + 1];
                let rhs_ty = &self.stack[index + 2];

                let (lhs_name_ty, lhs_name) = lhs_name.scoped_0()?;
                lhs_name_ty.as_name()?;
                let lhs_name = lhs_name.into_name();

                let (lhs_ty_ty, lhs_ty) = lhs_ty.scoped_0()?;
                lhs_ty_ty.as_universe()?;
                let lhs_ty = lhs_ty.into_ty();

                let (rhs_ty_ty, rhs_ty) = rhs_ty.scoped_0()?;
                rhs_ty_ty.as_universe()?;
                let rhs_ty = rhs_ty.into_ty();

                let ty = Ty::universe();
                let tm = Ty::sum(lhs_name, lhs_ty, rhs_ty).into_tm();
                self.push(ty, tm);
            },

            Op::InjLhs => {
                let index = self.stack.len().checked_sub(3)?;
                let lhs_name = &self.stack[index];
                let lhs_tm = &self.stack[index + 1];
                let rhs_ty = &self.stack[index + 2];

                let (lhs_name_ty, lhs_name) = lhs_name.scoped_0()?;
                lhs_name_ty.as_name()?;
                let lhs_name = lhs_name.into_name();

                let (lhs_ty, lhs_tm) = lhs_tm.scoped_0()?;

                let (rhs_ty_ty, rhs_ty) = rhs_ty.scoped_0()?;
                rhs_ty_ty.as_universe()?;
                let rhs_ty = rhs_ty.into_ty();

                let ty = Ty::sum(lhs_name, lhs_ty, rhs_ty);
                let tm = lhs_tm.inj_lhs();
                self.push(ty, tm);
            },

            Op::InjRhs => {
                let index = self.stack.len().checked_sub(3)?;
                let lhs_name = &self.stack[index];
                let lhs_ty = &self.stack[index + 1];
                let rhs_tm = &self.stack[index + 2];

                let (lhs_name_ty, lhs_name) = lhs_name.scoped_0()?;
                lhs_name_ty.as_name()?;
                let lhs_name = lhs_name.into_name();

                let (lhs_ty_ty, lhs_ty) = lhs_ty.scoped_0()?;
                lhs_ty_ty.as_universe()?;
                let lhs_ty = lhs_ty.into_ty();

                let (rhs_ty, rhs_tm) = rhs_tm.scoped_0()?;

                let ty = Ty::sum(lhs_name, lhs_ty, rhs_ty);
                let tm = rhs_tm.inj_rhs();
                self.push(ty, tm);
            },

            Op::Case => {
                let index = self.stack.len().checked_sub(4)?;
                let elim = &self.stack[index];
                let motive = &self.stack[index + 1];
                let lhs_inhab = &self.stack[index + 2];
                let rhs_inhab = &self.stack[index + 3];

                let (elim_ty, elim) = elim.scoped_0()?;
                let (_lhs_name, lhs_ty, rhs_ty) = elim_ty.clone().as_sum()?;

                let (motive_elim_ty, motive) = motive.scoped_1(ctx_len)?;
                Unify::unify(&mut self.ctx, (), motive_elim_ty, elim_ty)?;
                let (motive_ty, motive) = motive.lift_tuple();
                motive_ty.try_strengthen().ok()?.as_universe()?;
                let motive = motive.map_without_capture(|motive| motive.into_ty());

                let (lhs_inhab_var_ty, lhs_inhab) = lhs_inhab.scoped_1(ctx_len)?;
                Unify::unify(&mut self.ctx, (), lhs_inhab_var_ty, lhs_ty.clone())?;
                let (lhs_inhab_ty, lhs_inhab) = lhs_inhab.lift_tuple();
                Unify::unify(
                    &mut self.ctx,
                    (lhs_ty.clone(), Scope::constant(())),
                    lhs_inhab_ty,
                    Scope::make(ctx_len, |lhs| {
                        motive.clone().bind(lhs.inj_lhs())
                    }),
                )?;

                let (rhs_inhab_var_ty, rhs_inhab) = rhs_inhab.scoped_1(ctx_len)?;
                Unify::unify(&mut self.ctx, (), rhs_inhab_var_ty, rhs_ty.clone())?;
                let (rhs_inhab_ty, rhs_inhab) = rhs_inhab.lift_tuple();
                Unify::unify(
                    &mut self.ctx,
                    (rhs_ty.clone(), Scope::constant(())),
                    rhs_inhab_ty,
                    Scope::make(ctx_len, |rhs| {
                        motive.clone().bind(rhs.inj_rhs())
                    }),
                )?;

                let ty = motive.clone().bind(elim.clone());
                let tm = Tm::case(elim, motive, lhs_inhab, rhs_inhab);
                self.push(ty, tm);
            },

            Op::Sigma => {
                let index = self.stack.len().checked_sub(3)?;
                let head_name = &self.stack[index];
                let head_ty = &self.stack[index + 1];
                let tail_ty = &self.stack[index + 2];

                let (head_name_ty, head_name) = head_name.scoped_0()?;
                head_name_ty.as_name()?;
                let head_name = head_name.into_name();

                let (head_ty_ty, head_ty) = head_ty.scoped_0()?;
                head_ty_ty.as_universe()?;
                let head_ty = head_ty.into_ty();

                let (tail_ty_var_ty, tail_ty) = tail_ty.scoped_1(ctx_len)?;
                let head_ty = Unify::unify(&mut self.ctx, (), tail_ty_var_ty, head_ty)?;
                let (tail_ty_ty, tail_ty) = tail_ty.lift_tuple();
                tail_ty_ty.try_strengthen().ok()?.as_universe()?;
                let tail_ty = tail_ty.map_without_capture(|tail_ty| tail_ty.into_ty());

                let ty = Ty::universe();
                let tm = Ty::sigma(head_name, head_ty, tail_ty).into_tm();
                self.push(ty, tm);
            },

            Op::Pair => {
                let index = self.stack.len().checked_sub(4)?;
                let head_name = &self.stack[index];
                let head_tm = &self.stack[index + 1];
                let tail_ty = &self.stack[index + 2];
                let tail_tm = &self.stack[index + 3];

                let (head_name_ty, head_name) = head_name.scoped_0()?;
                head_name_ty.as_name()?;
                let head_name = head_name.into_name();

                let (head_ty, head_tm) = head_tm.scoped_0()?;

                let (tail_ty_var_ty, tail_ty) = tail_ty.scoped_1(ctx_len)?;
                let head_ty = Unify::unify(&mut self.ctx, (), tail_ty_var_ty, head_ty)?;
                let (tail_ty_ty, tail_ty) = tail_ty.lift_tuple();
                tail_ty_ty.try_strengthen().ok()?.as_universe()?;
                let tail_ty = tail_ty.map_without_capture(|tail_ty| tail_ty.into_ty());

                let (bound_tail_ty, tail_tm) = tail_tm.scoped_0()?;
                Unify::unify(
                    &mut self.ctx,
                    (),
                    bound_tail_ty,
                    tail_ty
                    .clone()
                    .bind(head_tm.clone()),
                )?;

                let ty = Ty::sigma(head_name, head_ty, tail_ty);
                let tm = head_tm.pair(tail_tm);
                self.push(ty, tm);
            },

            Op::ProjHead => {
                let elim = self.stack.last()?;
                let (elim_ty, elim) = elim.scoped_0()?;
                let (_head_name, head_ty, _tail_ty) = elim_ty.as_sigma()?;

                let ty = head_ty;
                let tm = elim.proj_head();
                self.push(ty, tm);
            },

            Op::ProjTail => {
                let elim = self.stack.last()?;
                let (elim_ty, elim) = elim.scoped_0()?;
                let (_head_name, _head_ty, tail_ty) = elim_ty.as_sigma()?;

                let ty = tail_ty.bind(elim.clone().proj_head());
                let tm = elim.proj_tail();
                self.push(ty, tm);
            },

            Op::Pi => {
                let index = self.stack.len().checked_sub(3)?;
                let arg_name = &self.stack[index];
                let arg_ty = &self.stack[index + 1];
                let res_ty = &self.stack[index + 2];

                let (arg_name_ty, arg_name) = arg_name.scoped_0()?;
                arg_name_ty.as_name()?;
                let arg_name = arg_name.into_name();

                let (arg_ty_ty, arg_ty) = arg_ty.scoped_0()?;
                arg_ty_ty.as_universe()?;
                let arg_ty = arg_ty.into_ty();

                let (res_ty_var_ty, res_ty) = res_ty.scoped_1(ctx_len)?;
                let arg_ty = Unify::unify(&mut self.ctx, (), res_ty_var_ty, arg_ty)?;
                let (res_ty_ty, res_ty) = res_ty.lift_tuple();
                res_ty_ty.try_strengthen().ok()?.as_universe()?;
                let res_ty = res_ty.map_without_capture(|res_ty| res_ty.into_ty());

                let ty = Ty::universe();
                let tm = Ty::pi(arg_name, arg_ty, res_ty).into_tm();
                self.push(ty, tm);
            },

            Op::Func => {
                let index = self.stack.len().checked_sub(2)?;
                let arg_name = &self.stack[index];
                let res_tm = &self.stack[index + 1];

                let (arg_name_ty, arg_name) = arg_name.scoped_0()?;
                arg_name_ty.as_name()?;
                let arg_name = arg_name.into_name();

                let (arg_ty, res_tm) = res_tm.scoped_1(ctx_len)?;
                let (res_ty, res_tm) = res_tm.lift_tuple();

                let ty = Ty::pi(arg_name, arg_ty, res_ty);
                let tm = Tm::func(res_tm);
                self.push(ty, tm);
            },

            Op::App => {
                let index = self.stack.len().checked_sub(2)?;
                let elim = &self.stack[index];
                let arg_tm = &self.stack[index + 1];

                let (elim_ty, elim) = elim.scoped_0()?;
                let (_arg_name, arg_ty, res_ty) = elim_ty.as_pi()?;

                let (arg_tm_ty, arg_tm) = arg_tm.scoped_0()?;
                Unify::unify(&mut self.ctx, (), arg_tm_ty, arg_ty)?;

                let ty = res_ty.bind(arg_tm.clone());
                let tm = elim.app(arg_tm);

                self.push(ty, tm);
            },
        };
        Some(())
    }
}

fuzz_target!(|ops: Vec<Op>| {
    let mut state = State::new();
    for op in ops {
        //println!("state == {:#?}", state);
        //println!("running: {:?}", op);
        let _ = state.execute(op);
    }
});

