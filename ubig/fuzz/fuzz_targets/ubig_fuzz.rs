#![no_main]

use {
    std::{
        num::NonZeroUsize,
        str::FromStr,
    },
    arbitrary::Arbitrary,
    libfuzzer_sys::fuzz_target,
    num::{BigUint, Zero, One, CheckedSub},
    ubig::Ubig,
};

#[derive(Arbitrary, Debug)]
enum Op {
    Clone,
    Drop,
    Eq,
    Ord,
    FromUsizeSlice {
        words: Vec<usize>,
    },
    AsUsizeSlice,
    BitWidth,
    TruncatedBitWidth {
        len: u16,
    },
    IsPowerOfTwo,
    NthPowerOfTwo {
        n: u16,
    },
    NthPowerOfTwoMinusOne {
        n: u16,
    },
    TrailingOnes,
    TrailingZeros,
    CountOnes,
    GetBit {
        index: u16,
    },
    SetBit {
        index: u16,
        bit: bool,
    },
    SetBitRangeToZero {
        start: u16,
        len: u16,
    },
    SetBitRangeToOne {
        start: u16,
        len: u16,
    },
    ShiftRemoveBit {
        index: u16,
    },

    ExtractBits,
    DepositBits,
    Truncate {
        len: u16,
    },
    CloneTruncate {
        len: u16,
    },
    Increment,
    Decrement,
    Ilog2Exact,
    CheckedSub,

    BitorAssignRef,
    BitorAssignOwned,
    BitorAssignUsize {
        rhs: usize,
    },
    BitorRef,
    BitorOwned,

    BitandAssignRef,
    BitandAssignOwned,
    BitandAssignUsize {
        rhs: usize,
    },
    BitandRef,
    BitandOwned,

    AddAssignRef,
    AddAssignOwned,
    AddAssignUsize {
        rhs: usize,
    },
    AddRef,
    AddOwned,
    MulAssignRef,
    MulAssignOwned,
    MulAssignUsize {
        rhs: usize,
    },
    MulRef,
    MulOwned,
    CheckedDivRem,
    DivAssignUsize {
        rhs: NonZeroUsize,
    },
    RemAssignUsize {
        rhs: NonZeroUsize,
    },
    Fmt,
    Parse {
        digits: Vec<u8>,
    },
}

fn big_uint_as_usizes(that: &BigUint) -> Vec<usize> {
    cfg_select! {
        target_pointer_width = "32" => {
            that.iter_u32_digits().map(|digit| digit as usize).collect()
        },
        target_pointer_width = "64" => {
            that.iter_u64_digits().map(|digit| digit as usize).collect()
        },
    }
}

fn assert_equal(this: &Ubig, that: &BigUint) {
    let this_slice = this.as_usize_slice();
    let that_vec = big_uint_as_usizes(that);
    let that_slice = &that_vec[..];
    assert_eq!(this_slice, that_slice);
}

impl Op {
    pub fn perform(self, stack: &mut Vec<(Ubig, BigUint)>) {
        match self {
            Op::Clone => {
                let Some((this, that)) = stack.last() else {
                    return;
                };
                let new_this = this.clone();
                let new_that = that.clone();
                assert_equal(&new_this, &new_that);
                stack.push((new_this, new_that));
            },
            Op::Drop => {
                let _ = stack.pop();
            },
            Op::Eq => {
                let len = stack.len();
                let Some(index) = len.checked_sub(2) else {
                    return;
                };
                let (this_0, that_0) = &stack[index];
                let (this_1, that_1) = &stack[index + 1];
                let eq_0 = this_0 == this_1;
                let eq_1 = that_0 == that_1;
                assert_eq!(eq_0, eq_1);
            },
            Op::Ord => {
                let len = stack.len();
                let Some(index) = len.checked_sub(2) else {
                    return;
                };
                let (this_0, that_0) = &stack[index];
                let (this_1, that_1) = &stack[index + 1];
                let cmp_0 = this_0.partial_cmp(this_1);
                let cmp_1 = that_0.partial_cmp(that_1);
                assert_eq!(cmp_0, cmp_1);
            },
            Op::FromUsizeSlice { words } => {
                let new_this = Ubig::from_usize_slice(&words);
                let words_u32: Vec<u32> = {
                    words
                    .into_iter()
                    .flat_map(|word| {
                        (0..(usize::BITS / u32::BITS)).map(move |offset| {
                            (word >> (offset * 32)) as u32
                        })
                    })
                    .collect()
                };
                let new_that = BigUint::from_slice(&words_u32);
                assert_equal(&new_this, &new_that);
                stack.push((new_this, new_that));
            },
            Op::AsUsizeSlice => {
                let Some((this, that)) = stack.last() else {
                    return;
                };
                let this_slice = this.as_usize_slice();
                let that_vec = big_uint_as_usizes(that);
                let that_slice = &that_vec[..];
                assert_eq!(this_slice, that_slice);
            },
            Op::BitWidth => {
                let Some((this, that)) = stack.last() else {
                    return;
                };
                let this_bit_width = this.bit_width();
                let that_bit_width: usize = that.bits().try_into().unwrap();
                assert_eq!(this_bit_width, that_bit_width);
            },
            Op::TruncatedBitWidth { len } => {
                let len = len as usize;
                let Some((this, that)) = stack.last() else {
                    return;
                };
                let this_truncated_bit_width = this.truncated_bit_width(len);
                let that = that % (BigUint::one() << len);
                let that_truncated_bit_width: usize = that.bits().try_into().unwrap();
                assert_eq!(this_truncated_bit_width, that_truncated_bit_width);
            },
            Op::IsPowerOfTwo => {
                let Some((this, that)) = stack.last() else {
                    return;
                };
                let this_is_power_of_two = this.is_power_of_two();
                let that_is_power_of_two = that.trailing_zeros().map_or(false, |zeros| {
                    zeros + 1 == that.bits()
                });
                assert_eq!(this_is_power_of_two, that_is_power_of_two);
            },
            Op::NthPowerOfTwo { n } => {
                let new_this = Ubig::nth_power_of_two(n as usize);
                let new_that = BigUint::ONE << n;
                assert_equal(&new_this, &new_that);
                stack.push((new_this, new_that));
            },
            Op::NthPowerOfTwoMinusOne { n } => {
                let new_this = Ubig::nth_power_of_two_minus_one(n as usize);
                let new_that = (BigUint::ONE << n) - 1u32;
                assert_equal(&new_this, &new_that);
                stack.push((new_this, new_that));
            },
            Op::TrailingOnes => {
                let Some((this, that)) = stack.last() else {
                    return;
                };
                let this_trailing_ones = this.trailing_ones() as u64;
                let that_trailing_ones = that.trailing_ones();
                assert_eq!(this_trailing_ones, that_trailing_ones);
            },
            Op::TrailingZeros => {
                let Some((this, that)) = stack.last() else {
                    return;
                };
                let this_trailing_zeros = this.trailing_zeros().map(|zeros| zeros as u64);
                let that_trailing_zeros = that.trailing_zeros();
                assert_eq!(this_trailing_zeros, that_trailing_zeros);
            },
            Op::CountOnes => {
                let Some((this, that)) = stack.last() else {
                    return;
                };
                let this_ones = this.count_ones() as u64;
                let that_ones = that.count_ones();
                assert_eq!(this_ones, that_ones);
            },
            Op::GetBit { index } => {
                let Some((this, that)) = stack.last() else {
                    return;
                };
                let this_bit = this.get_bit(index as usize);
                let that_bit = that.bit(index as u64);
                assert_eq!(this_bit, that_bit);
            },
            Op::SetBit { index, bit } => {
                let Some((this, that)) = stack.last_mut() else {
                    return;
                };
                this.set_bit(index as usize, bit);
                that.set_bit(index as u64, bit);
                assert_equal(this, that);
            },
            Op::SetBitRangeToZero { start, len } => {
                let Some((this, that)) = stack.last_mut() else {
                    return;
                };
                this.set_bit_range_to_zero(start as usize, start as usize + len as usize);
                for index in (start as u64)..(start as u64 + len as u64) {
                    that.set_bit(index, false);
                }
                assert_equal(this, that);
            },
            Op::SetBitRangeToOne { start, len } => {
                let Some((this, that)) = stack.last_mut() else {
                    return;
                };
                this.set_bit_range_to_one(start as usize, start as usize + len as usize);
                for index in (start as u64)..(start as u64 + len as u64) {
                    that.set_bit(index, true);
                }
                assert_equal(this, that);
            },

            Op::ShiftRemoveBit { index } => {
                let Some((this, that)) = stack.last_mut() else {
                    return;
                };
                let this_bit = this.shift_remove_bit(index as usize);
                let that_bit = that.bit(index as u64);
                *that = {
                    let lower_mask = (BigUint::one() << index) - 1u32;
                    let upper_mask_len = that.bits().saturating_sub(index as u64);
                    let upper_mask = {
                        ((BigUint::one() << upper_mask_len) - 1u32)
                        << index
                    };

                    let lower = &*that & lower_mask;
                    let upper = (&*that >> 1) & upper_mask;
                    lower | upper
                };
                assert_eq!(this_bit, that_bit);
                assert_equal(this, that);
            },

            Op::ExtractBits => {
                let Some((mut this_0, that_0)) = stack.pop() else {
                    return;
                };
                let Some((this_1, that_1)) = stack.last() else {
                    stack.push((this_0, that_0));
                    return;
                };
                this_0.extract_bits(this_1.as_usize_slice());
                let that_1_vec = big_uint_as_usizes(that_1);
                let that_0 = {
                    let mut new_that_0 = BigUint::ZERO;
                    let mut write_index = 0;

                    for (read_word_index, that_1_word) in that_1_vec.into_iter().enumerate() {
                        for read_bit_index in 0..usize::BITS {
                            let bit_1 = (that_1_word >> read_bit_index) & 1 == 1;
                            if bit_1 {
                                let read_index = {
                                    (read_word_index * usize::BITS as usize)
                                    .strict_add(read_bit_index as usize)
                                };
                                let bit_0 = that_0.bit(read_index as u64);
                                new_that_0.set_bit(write_index, bit_0);
                                write_index += 1;
                            }
                        }
                    }
                    new_that_0
                };

                assert_equal(&this_0, &that_0);
                stack.push((this_0, that_0));
            },
            Op::DepositBits => {
                let Some((mut this_0, that_0)) = stack.pop() else {
                    return;
                };
                let Some((this_1, that_1)) = stack.last() else {
                    stack.push((this_0, that_0));
                    return;
                };
                this_0.deposit_bits(this_1.as_usize_slice());
                let that_1_vec = big_uint_as_usizes(that_1);
                let that_0 = {
                    let mut new_that_0 = BigUint::ZERO;
                    let mut read_index = 0;

                    for (write_word_index, that_1_word) in that_1_vec.into_iter().enumerate() {
                        for write_bit_index in 0..usize::BITS {
                            let bit_1 = (that_1_word >> write_bit_index) & 1 == 1;
                            if bit_1 {
                                let write_index = {
                                    (write_word_index * usize::BITS as usize)
                                    .strict_add(write_bit_index as usize)
                                };
                                let bit_0 = that_0.bit(read_index);
                                new_that_0.set_bit(write_index as u64, bit_0);
                                read_index += 1;
                            }

                        }
                    }
                    new_that_0
                };

                assert_equal(&this_0, &that_0);
                stack.push((this_0, that_0));
            },
            Op::Truncate { len } => {
                let Some((this, that)) = stack.last_mut() else {
                    return;
                };
                this.truncate(len as usize);
                *that %= BigUint::ONE << len;
                assert_equal(this, that);
            },
            Op::CloneTruncate { len } => {
                let Some((this, that)) = stack.last() else {
                    return;
                };
                let new_this = this.clone_truncate(len as usize);
                let new_that = that % (BigUint::ONE << len);
                assert_equal(&new_this, &new_that);
                stack.push((new_this, new_that));
            },
            Op::Increment => {
                let Some((mut this, mut that)) = stack.pop() else {
                    return;
                };
                this.increment();
                that += 1u32;
                assert_equal(&this, &that);
                stack.push((this, that));
            },
            Op::Decrement => {
                let Some((mut this, mut that)) = stack.pop() else {
                    return;
                };
                let this_non_zero = this.decrement();
                let that_non_zero = if that.is_zero() {
                    false
                } else {
                    that -= 1u32;
                    true
                };
                assert_eq!(this_non_zero, that_non_zero);
                assert_equal(&this, &that);
                stack.push((this, that));
            },

            Op::BitorAssignRef => {
                let Some((mut this_0, mut that_0)) = stack.pop() else {
                    return;
                };
                let Some((this_1, that_1)) = stack.last() else {
                    stack.push((this_0, that_0));
                    return;
                };
                this_0 |= this_1;
                that_0 |= that_1;
                assert_equal(&this_0, &that_0);
                stack.push((this_0, that_0));
            },
            Op::BitorAssignOwned => {
                let Some((mut this_0, mut that_0)) = stack.pop() else {
                    return;
                };
                let Some((this_1, that_1)) = stack.pop() else {
                    stack.push((this_0, that_0));
                    return;
                };
                this_0 |= this_1;
                that_0 |= that_1;
                assert_equal(&this_0, &that_0);
                stack.push((this_0, that_0));
            },
            Op::BitorAssignUsize { rhs } => {
                let Some((mut this, mut that)) = stack.pop() else {
                    return;
                };
                this |= rhs;
                that |= BigUint::from(rhs);
                assert_equal(&this, &that);
                stack.push((this, that));
            },
            Op::BitorRef => {
                let Some(index) = stack.len().checked_sub(2) else {
                    return;
                };
                let (this_0, that_0) = &stack[index];
                let (this_1, that_1) = &stack[index + 1];
                let new_this = this_0 | this_1;
                let new_that = that_0 | that_1;
                assert_equal(&new_this, &new_that);
                stack.push((new_this, new_that));
            },
            Op::BitorOwned => {
                if stack.len() < 2 {
                    return;
                }
                let (this_0, that_0) = stack.pop().unwrap();
                let (this_1, that_1) = stack.pop().unwrap();
                let new_this = this_0 | this_1;
                let new_that = that_0 | that_1;
                assert_equal(&new_this, &new_that);
                stack.push((new_this, new_that));
            },

            Op::BitandAssignRef => {
                let Some((mut this_0, mut that_0)) = stack.pop() else {
                    return;
                };
                let Some((this_1, that_1)) = stack.last() else {
                    stack.push((this_0, that_0));
                    return;
                };
                this_0 &= this_1;
                that_0 &= that_1;
                assert_equal(&this_0, &that_0);
                stack.push((this_0, that_0));
            },
            Op::BitandAssignOwned => {
                let Some((mut this_0, mut that_0)) = stack.pop() else {
                    return;
                };
                let Some((this_1, that_1)) = stack.pop() else {
                    stack.push((this_0, that_0));
                    return;
                };
                this_0 &= this_1;
                that_0 &= that_1;
                assert_equal(&this_0, &that_0);
                stack.push((this_0, that_0));
            },
            Op::BitandAssignUsize { rhs } => {
                let Some((mut this, mut that)) = stack.pop() else {
                    return;
                };
                this &= rhs;
                that &= BigUint::from(rhs);
                assert_equal(&this, &that);
                stack.push((this, that));
            },
            Op::BitandRef => {
                let Some(index) = stack.len().checked_sub(2) else {
                    return;
                };
                let (this_0, that_0) = &stack[index];
                let (this_1, that_1) = &stack[index + 1];
                let new_this = this_0 & this_1;
                let new_that = that_0 & that_1;
                assert_equal(&new_this, &new_that);
                stack.push((new_this, new_that));
            },
            Op::BitandOwned => {
                if stack.len() < 2 {
                    return;
                }
                let (this_0, that_0) = stack.pop().unwrap();
                let (this_1, that_1) = stack.pop().unwrap();
                let new_this = this_0 & this_1;
                let new_that = that_0 & that_1;
                assert_equal(&new_this, &new_that);
                stack.push((new_this, new_that));
            },

            Op::Ilog2Exact => {
                let Some((this, that)) = stack.last() else {
                    return;
                };
                let this_ilog2_exact = this.ilog2_exact();
                let that_ilog2_exact: Option<usize> = match that.trailing_zeros() {
                    None => None,
                    Some(that_zeros) => {
                        let that_width = that.bits();
                        if that_width == that_zeros + 1 {
                            Some(that_zeros.try_into().unwrap())
                        } else {
                            None
                        }
                    },
                };
                assert_eq!(this_ilog2_exact, that_ilog2_exact);
            },
            Op::CheckedSub => {
                let Some(index) = stack.len().checked_sub(2) else {
                    return;
                };
                let (this_0, that_0) = &stack[index];
                let (this_1, that_1) = &stack[index + 1];
                let new_this_opt = this_0.checked_sub(this_1);
                let new_that_opt = that_0.checked_sub(that_1);
                match (new_this_opt, new_that_opt) {
                    (None, None) => (),
                    (Some(new_this), Some(new_that)) => {
                        assert_equal(&new_this, &new_that);
                        stack.push((new_this, new_that))
                    },
                    _ => panic!(),
                }
            },
            Op::AddAssignRef => {
                let Some((mut this_0, mut that_0)) = stack.pop() else {
                    return;
                };
                let Some((this_1, that_1)) = stack.last() else {
                    stack.push((this_0, that_0));
                    return;
                };
                this_0 += this_1;
                that_0 += that_1;
                assert_equal(&this_0, &that_0);
                stack.push((this_0, that_0));
            },
            Op::AddAssignOwned => {
                let Some((mut this_0, mut that_0)) = stack.pop() else {
                    return;
                };
                let Some((this_1, that_1)) = stack.pop() else {
                    stack.push((this_0, that_0));
                    return;
                };
                this_0 += this_1;
                that_0 += that_1;
                assert_equal(&this_0, &that_0);
                stack.push((this_0, that_0));
            },
            Op::AddAssignUsize { rhs } => {
                let Some((mut this, mut that)) = stack.pop() else {
                    return;
                };
                this += rhs;
                that += BigUint::from(rhs);
                assert_equal(&this, &that);
                stack.push((this, that));
            },
            Op::AddRef => {
                let Some(index) = stack.len().checked_sub(2) else {
                    return;
                };
                let (this_0, that_0) = &stack[index];
                let (this_1, that_1) = &stack[index + 1];
                let new_this = this_0 + this_1;
                let new_that = that_0 + that_1;
                assert_equal(&new_this, &new_that);
                stack.push((new_this, new_that));
            },
            Op::AddOwned => {
                if stack.len() < 2 {
                    return;
                }
                let (this_0, that_0) = stack.pop().unwrap();
                let (this_1, that_1) = stack.pop().unwrap();
                let new_this = this_0 + this_1;
                let new_that = that_0 + that_1;
                assert_equal(&new_this, &new_that);
                stack.push((new_this, new_that));
            },
            Op::MulAssignRef => {
                let Some((mut this_0, mut that_0)) = stack.pop() else {
                    return;
                };
                let Some((this_1, that_1)) = stack.last() else {
                    stack.push((this_0, that_0));
                    return;
                };
                if this_0.bit_width() + this_1.bit_width() > u16::MAX as usize {
                    return;
                }
                this_0 *= this_1;
                that_0 *= that_1;
                assert_equal(&this_0, &that_0);
                stack.push((this_0, that_0));
            },
            Op::MulAssignOwned => {
                let Some((mut this_0, mut that_0)) = stack.pop() else {
                    return;
                };
                let Some((this_1, that_1)) = stack.pop() else {
                    stack.push((this_0, that_0));
                    return;
                };
                if this_0.bit_width() + this_1.bit_width() > u16::MAX as usize {
                    return;
                }
                this_0 *= this_1;
                that_0 *= that_1;
                assert_equal(&this_0, &that_0);
                stack.push((this_0, that_0));
            },
            Op::MulAssignUsize { rhs } => {
                let Some((mut this, mut that)) = stack.pop() else {
                    return;
                };
                this *= rhs;
                that *= BigUint::from(rhs);
                assert_equal(&this, &that);
                stack.push((this, that));
            },
            Op::MulRef => {
                let Some(index) = stack.len().checked_sub(2) else {
                    return;
                };
                let (this_0, that_0) = &stack[index];
                let (this_1, that_1) = &stack[index + 1];
                if this_0.bit_width() + this_1.bit_width() > u16::MAX as usize {
                    return;
                }
                let new_this = this_0 * this_1;
                let new_that = that_0 * that_1;
                assert_equal(&new_this, &new_that);
                stack.push((new_this, new_that));
            },
            Op::MulOwned => {
                if stack.len() < 2 {
                    return;
                }
                let (this_0, that_0) = stack.pop().unwrap();
                let (this_1, that_1) = stack.pop().unwrap();
                if this_0.bit_width() + this_1.bit_width() > u16::MAX as usize {
                    return;
                }
                let new_this = this_0 * this_1;
                let new_that = that_0 * that_1;
                assert_equal(&new_this, &new_that);
                stack.push((new_this, new_that));
            },
            Op::CheckedDivRem => {
                if stack.len() < 2 {
                    return;
                }
                let (this_0, that_0) = stack.pop().unwrap();
                let (this_1, that_1) = stack.pop().unwrap();
                let new_thiss_opt = this_0.checked_div_rem(&this_1);
                let new_thats_opt = if that_1.is_zero() {
                    None
                } else {
                    let div = &that_0 / &that_1;
                    let rem = that_0 % that_1;
                    Some((div, rem))
                };
                let (new_thiss, new_thats) = match (new_thiss_opt, new_thats_opt) {
                    (None, None) => return,
                    (Some(new_thiss), Some(new_thats)) => (new_thiss, new_thats),
                    _ => unreachable!(),
                };
                let (new_this_0, new_this_1) = new_thiss;
                let (new_that_0, new_that_1) = new_thats;
                assert_equal(&new_this_0, &new_that_0);
                assert_equal(&new_this_1, &new_that_1);
                stack.push((new_this_0, new_that_0));
                stack.push((new_this_1, new_that_1));
            },
            Op::DivAssignUsize { rhs } => {
                let Some((mut this, mut that)) = stack.pop() else {
                    return;
                };
                this /= rhs;
                that /= BigUint::from(rhs.get());
                assert_equal(&this, &that);
                stack.push((this, that));
            },
            Op::RemAssignUsize { rhs } => {
                let Some((mut this, mut that)) = stack.pop() else {
                    return;
                };
                this %= rhs;
                that %= BigUint::from(rhs.get());
                assert_equal(&this, &that);
                stack.push((this, that));
            },
            Op::Fmt => {
                let Some((this, that)) = stack.last() else {
                    return;
                };
                let this_s = this.to_string();
                let that_s = that.to_string();
                assert_eq!(this_s, that_s);
            },
            Op::Parse { digits } => {
                if digits.is_empty() {
                    return;
                }
                let s: String = {
                    digits
                    .into_iter()
                    .map(|d| ((d % 10) + ('0' as u8)) as char)
                    .collect()
                };
                let this = Ubig::from_str(&s).unwrap();
                let that = BigUint::from_str(&s).unwrap();
                assert_equal(&this, &that);
                stack.push((this, that));
            },
        }
    }
}

fuzz_target!(|ops: Vec<Op>| {
    let mut stack = Vec::new();
    for op in ops {
        op.perform(&mut stack);
    }
});

