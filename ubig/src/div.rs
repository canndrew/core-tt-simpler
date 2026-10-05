use crate::priv_prelude::*;

unsafe fn wide_div_unchecked(
    lo: usize,
    hi: usize,
    divisor: NonZeroUsize,
) -> (usize, usize) {
    cfg_select! {
        target_pointer_width = "64" => {
            #[allow(non_camel_case_types)]
            type usize2 = u128;
        }
        target_pointer_width = "32" => {
            #[allow(non_camel_case_types)]
            type usize2 = u64;
        }
        target_pointer_width = "16" => {
            #[allow(non_camel_case_types)]
            type usize2 = u32;
        }
        _ => {
            compile_error!("unsupported pointer width");
        }
    }

    unsafe {
        assert_unchecked(hi < divisor.get());
    }
    let lo = lo as usize2;
    let hi = hi as usize2;
    let divisor = divisor.get() as usize2;
    let full = (hi << usize::BITS) | lo;
    let dividend = unsafe { full.checked_div(divisor).unwrap_unchecked() };
    let modulus = unsafe { full.checked_rem(divisor).unwrap_unchecked() };
    let dividend = unsafe { usize::try_from(dividend).unwrap_unchecked() };
    let modulus = unsafe { usize::try_from(modulus).unwrap_unchecked() };
    (dividend, modulus)
}

pub(crate) fn div_assign_slice_usize(
    lhs: &mut [usize],
    rhs: NonZeroUsize,
) -> usize {
    let mut carry = 0;
    for lhs_word in lhs.iter_mut().rev() {
        let (word, next_carry) = unsafe { wide_div_unchecked(*lhs_word, carry, rhs) };
        *lhs_word = word;
        carry = next_carry;
    }
    carry
}

unsafe fn unchecked_div_rem_assign_slice_slice_trimmed(
    lhs: &mut [usize],
    rhs: &[usize],
    div_output: &mut [MaybeUninit<usize>],
) {
    let div_output = div_output.write_filled(0);
    let Some(mut lhs_full_words) = lhs.len().checked_sub(1) else {
        return;
    };
    let mut lhs_width = {
        let (&last, rest) = unsafe { lhs.split_last().unwrap_unchecked() };
        unsafe {
            assert_unchecked(last != 0);
            (last.bit_width() as usize).unchecked_add(rest.len().strict_mul(USIZE_BITS))
        }
    };
    let rhs_width = {
        let (&last, rest) = unsafe { rhs.split_last().unwrap_unchecked() };
        unsafe {
            assert_unchecked(last != 0);
            (last.bit_width() as usize).unchecked_add(rest.len().strict_mul(USIZE_BITS))
        }
    };
    loop {
        let Some(shift) = lhs_width.checked_sub(rhs_width) else {
            return;
        };
        let word_shift = shift / USIZE_BITS;
        let bit_shift = (shift % USIZE_BITS) as u32;

        let mut borrow = false;
        if bit_shift == 0 {
            for (index, lhs_word) in unsafe {
                lhs
                .get_unchecked_mut(word_shift..(lhs_full_words.unchecked_add(1)))
                .iter_mut()
                .enumerate()
            } {
                let rhs_word = unsafe { *rhs.get_unchecked(index) };
                let (word, next_borrow) = lhs_word.borrowing_sub(rhs_word, borrow);
                *lhs_word = word;
                borrow = next_borrow;
            }
        } else {
            let shr = unsafe { usize::BITS.unchecked_sub(bit_shift) };
            let mut rhs_lo = 0;
            for (index, lhs_word) in unsafe {
                lhs
                .get_unchecked_mut(word_shift..(lhs_full_words.unchecked_add(1)))
                .iter_mut()
                .enumerate()
            } {
                let rhs_hi = rhs.get(index).copied().unwrap_or(0);
                let rhs_word = unsafe { rhs_hi.unchecked_funnel_shr(rhs_lo, shr) };
                let (word, next_borrow) = lhs_word.borrowing_sub(rhs_word, borrow);
                *lhs_word = word;
                borrow = next_borrow;
                rhs_lo = rhs_hi;
            }
        };

        let shift = if borrow {
            let mut carry = false;
            if bit_shift == 0 {
                for (index, lhs_word) in unsafe {
                    lhs
                    .get_unchecked_mut(word_shift..(lhs_full_words.unchecked_add(1)))
                    .iter_mut()
                    .enumerate()
                } {
                    let rhs_word = unsafe { *rhs.get_unchecked(index) };
                    let (word, next_carry) = lhs_word.carrying_add(rhs_word, carry);
                    *lhs_word = word;
                    carry = next_carry;
                }
            } else {
                let shr = unsafe { usize::BITS.unchecked_sub(bit_shift) };
                let mut rhs_lo = 0;
                for (index, lhs_word) in unsafe {
                    lhs
                    .get_unchecked_mut(word_shift..(lhs_full_words.unchecked_add(1)))
                    .iter_mut()
                    .enumerate()
                } {
                    let rhs_hi = rhs.get(index).copied().unwrap_or(0);
                    let rhs_word = unsafe { rhs_hi.unchecked_funnel_shr(rhs_lo, shr) };
                    let (word, next_carry) = lhs_word.carrying_add(rhs_word, carry);
                    *lhs_word = word;
                    carry = next_carry;
                    rhs_lo = rhs_hi;
                }
            }
            unsafe { assert_unchecked(carry) };

            let Some(shift) = shift.checked_sub(1) else {
                return;
            };

            let word_shift = shift / USIZE_BITS;
            let bit_shift = (shift % USIZE_BITS) as u32;
            let mut borrow = false;
            if bit_shift == 0 {
                for (index, lhs_word) in unsafe {
                    lhs
                    .get_unchecked_mut(word_shift..(lhs_full_words.unchecked_add(1)))
                    .iter_mut()
                    .enumerate()
                } {
                    let rhs_word = rhs.get(index).copied().unwrap_or(0);
                    let (word, next_borrow) = lhs_word.borrowing_sub(rhs_word, borrow);
                    *lhs_word = word;
                    borrow = next_borrow;
                }
            } else {
                let shr = unsafe { usize::BITS.unchecked_sub(bit_shift) };
                let mut rhs_lo = 0;
                for (index, lhs_word) in unsafe {
                    lhs
                    .get_unchecked_mut(word_shift..(lhs_full_words.unchecked_add(1)))
                    .iter_mut()
                    .enumerate()
                } {
                    let rhs_hi = rhs.get(index).copied().unwrap_or(0);
                    let rhs_word = unsafe { rhs_hi.unchecked_funnel_shr(rhs_lo, shr) };
                    let (word, next_borrow) = lhs_word.borrowing_sub(rhs_word, borrow);
                    *lhs_word = word;
                    borrow = next_borrow;
                    rhs_lo = rhs_hi;
                }
            }
            unsafe { assert_unchecked(!borrow) };
            shift
        } else {
            shift
        };
        div_output.set_bit_to_one(shift);

        loop {
            let last = unsafe { *lhs.get_unchecked(lhs_full_words) };
            if last != 0 {
                lhs_width = unsafe {
                    (last.bit_width() as usize)
                    .unchecked_add(lhs_full_words.unchecked_mul(USIZE_BITS))
                };
                break;
            }
            let Some(next_lhs_full_words) = lhs_full_words.checked_sub(1) else {
                return;
            };
            lhs_full_words = next_lhs_full_words;
        }
    }
}

impl Ubig {
    pub fn div_rem_non_zero_usize(mut self, rhs: NonZeroUsize) -> (Ubig, usize) {
        if self.is_inline() {
            let lhs = unsafe { self.get_small_inline() };
            let div = unsafe { Ubig::from_small_usize_unchecked(lhs / rhs) };
            let rem = lhs % rhs;
            return (div, rem);
        }

        let lhs = unsafe { self.get_heap_slice_mut() };
        let rem = div_assign_slice_usize(lhs, rhs);

        if lhs.bit_width() < USIZE_BITS {
            let lhs_word = unsafe { *lhs.get_unchecked(0) };
            self = unsafe { Ubig::from_small_usize_unchecked(lhs_word) };
        }

        (self, rem)
    }

    pub fn checked_div_rem_slice(mut self, rhs: &[usize]) -> Option<(Ubig, Ubig)> {
        let rhs = rhs.trim_zeros();
        if rhs.is_empty() {
            return None;
        }

        if self.is_inline() {
            let (&rhs_last, rhs_rest) = unsafe { rhs.split_last().unwrap_unchecked() };
            if !rhs_rest.is_empty() {
                return Some((Ubig::ZERO, self));
            }
            let lhs = unsafe { self.get_small_inline() };
            let rhs_last = unsafe { NonZeroUsize::new_unchecked(rhs_last) };
            let div = unsafe { Ubig::from_small_usize_unchecked(lhs / rhs_last) };
            let rem = unsafe { Ubig::from_small_usize_unchecked(lhs % rhs_last) };
            return Some((div, rem));
        }

        let mut lhs = unsafe { self.get_heap_slice_mut() };
        let lhs_width = loop {
            let next_len = unsafe { lhs.len().unchecked_sub(1) };
            let last = unsafe { *lhs.get_unchecked(next_len) };
            if last != 0 {
                break unsafe {
                    (last.bit_width() as usize)
                    .unchecked_add(next_len.unchecked_mul(USIZE_BITS))
                };
            }
            lhs = unsafe {
                lhs.get_unchecked_mut(..next_len)
            };
        };
        let rhs_width = unsafe {
            let (&last, rest) = rhs.split_last().unwrap_unchecked();
            (last.bit_width() as usize)
            .unchecked_add(rest.len().strict_mul(USIZE_BITS))
        };

        let Some(diff) = lhs_width.checked_sub(rhs_width) else {
            return Some((Ubig::ZERO, self));
        };
        let output_width = unsafe { diff.unchecked_add(1) };
        if output_width <= USIZE_BITS {
            let mut div = MaybeUninit::uninit();
            let div_buffer = std::slice::from_mut(&mut div);
            let div = unsafe {
                unchecked_div_rem_assign_slice_slice_trimmed(
                    lhs, rhs, div_buffer,
                );
                div.assume_init()
            };
            let div = Ubig::from_usize(div);
            let (&first, rest) = unsafe { lhs.split_first().unwrap_unchecked() };
            if rest.is_zero() && (first & HIGH_BIT_MASK) == 0 {
                self = unsafe { Ubig::from_small_usize_unchecked(first) };
            }

            return Some((div, self));
        }

        let capacity = output_width.div_ceil(USIZE_BITS);
        let div = unsafe {
            Ubig::new_with_capacity(capacity, |output| {
                unchecked_div_rem_assign_slice_slice_trimmed(
                    lhs, rhs, output,
                );
            })
        };
        let (&first, rest) = unsafe { lhs.split_first().unwrap_unchecked() };
        if rest.is_zero() && (first & HIGH_BIT_MASK) == 0 {
            self = unsafe { Ubig::from_small_usize_unchecked(first) };
        }

        Some((div, self))
    }

    pub fn checked_div_rem(self, rhs: &Ubig) -> Option<(Ubig, Ubig)> {
        if rhs.is_inline() {
            let rhs = unsafe { rhs.get_small_inline() };
            let rhs = NonZeroUsize::new(rhs)?;
            let (div, rem) = self.div_rem_non_zero_usize(rhs);
            let rem = unsafe { Ubig::from_small_usize_unchecked(rem) };
            return Some((div, rem));
        }

        let rhs = rhs.as_usize_slice_untrimmed();
        self.checked_div_rem_slice(rhs)
    }
}

impl ops::DivAssign<NonZeroUsize> for Ubig {
    fn div_assign(&mut self, rhs: NonZeroUsize) {
        if self.is_inline() {
            let lhs = unsafe { self.get_small_inline() };
            *self = unsafe { Ubig::from_small_usize_unchecked(lhs / rhs) };
            return;
        }

        let lhs = unsafe { self.get_heap_slice_mut() };
        div_assign_slice_usize(lhs, rhs);

        if lhs.bit_width() < USIZE_BITS {
            let lhs_word = unsafe { *lhs.get_unchecked(0) };
            *self = unsafe { Ubig::from_small_usize_unchecked(lhs_word) };
        }
    }
}

impl ops::RemAssign<NonZeroUsize> for Ubig {
    fn rem_assign(&mut self, rhs: NonZeroUsize) {
        if self.is_inline() {
            let lhs = unsafe { self.get_small_inline() };
            *self = unsafe { Ubig::from_small_usize_unchecked(lhs % rhs) };
            return;
        }

        let lhs = unsafe { self.get_heap_slice_mut() };
        let rem = div_assign_slice_usize(lhs, rhs);
        *self = Ubig::from_usize(rem);
    }
}

impl ops::Div<NonZeroUsize> for Ubig {
    type Output = Ubig;

    fn div(mut self, rhs: NonZeroUsize) -> Ubig {
        self /= rhs;
        self
    }
}

impl ops::Rem<NonZeroUsize> for Ubig {
    type Output = usize;

    fn rem(mut self, rhs: NonZeroUsize) -> usize {
        if self.is_inline() {
            let lhs = unsafe { self.get_small_inline() };
            return lhs % rhs;
        }

        let lhs = unsafe { self.get_heap_slice_mut() };
        div_assign_slice_usize(lhs, rhs)
    }
}

