//#![feature(maybe_uninit_fill)]
//#![feature(disjoint_bitor)]
//#![feature(uint_gather_scatter_bits)]
//#![feature(funnel_shifts)]
//#![feature(exact_bitshifts)]

#![allow(unstable_name_collisions)]

mod priv_prelude;
mod slice;
mod fmt;
mod from_str;
mod convert;
mod ubig;
mod cmp;

mod add;
mod sub;
mod mul;
mod div;
mod bitor;
mod bitand;
mod shifts;

mod bmi2;
mod unstable;

#[cfg(test)]
mod test;

pub use crate::ubig::Ubig;

