use crate::priv_prelude::*;

/// A `usize`-sized, small-size optimized, unsigned big int type.
///
/// Values less than or equal to `isize::MAX` are always stored inline. Greater values are
/// heap allocated as a `Vec` of `usize` digits.
pub struct Ubig {
    storage: UbigStorage,
}

union UbigStorage {
    small_inline: usize,
    ptr_tagged: NonNull<usize>,
}

impl std::hash::Hash for Ubig {
    fn hash<H: std::hash::Hasher>(&self, hasher: &mut H) {
        let slice = self.as_usize_slice();
        std::hash::Hash::hash(slice, hasher)
    }
}

impl Clone for Ubig {
    fn clone(&self) -> Ubig {
        if self.is_inline() {
            unsafe {
                let small_inline = self.get_small_inline();
                Ubig::from_small_usize_unchecked(small_inline)
            }
        } else {
            unsafe {
                let slice = self.get_heap_slice_trimmed();
                Ubig::from_usize_slice(slice)
            }
        }
    }
}

impl Drop for Ubig {
    fn drop(&mut self) {
        if self.is_inline() {
            return;
        }
        unsafe {
            let ptr = self.get_heap_ptr();
            let words_len = ptr.read();
            let full_len = words_len.unchecked_add(1);
            let vec = Vec::from_parts(ptr, full_len, full_len);
            drop(vec);
        }
    }
}

impl Default for Ubig {
    fn default() -> Ubig {
        Ubig::ZERO
    }
}

unsafe impl Sync for Ubig {}
unsafe impl Send for Ubig {}

pub(crate) const USIZE_BITS: usize = usize::BITS as usize;
pub(crate) const HIGH_BIT_MASK: usize = 1 << (USIZE_BITS - 1);

impl Ubig {
    pub const ZERO: Ubig = Ubig { storage: UbigStorage { small_inline: 0 } };
    pub const ONE: Ubig = Ubig { storage: UbigStorage { small_inline: 1 } };

    pub fn is_zero(&self) -> bool {
        let inline = unsafe { self.storage.small_inline };
        inline == 0
    }

    pub(crate) fn from_usize(val: usize) -> Ubig {
        if (val & HIGH_BIT_MASK) == 0 {
            unsafe { Ubig::from_small_usize_unchecked(val) }
        } else {
            unsafe {
                Ubig::new_with_capacity(1, |slice| {
                    slice.get_unchecked_mut(0).write(val);
                })
            }
        }
    }

    pub(crate) unsafe fn from_small_usize_unchecked(val: usize) -> Ubig {
        unsafe {
            assert_unchecked((val & HIGH_BIT_MASK) == 0);
        }
        Ubig { storage: UbigStorage { small_inline: val } }
    }

    pub fn from_usize_slice(slice: &[usize]) -> Ubig {
        let slice = slice.trim_zeros();
        unsafe {
            Ubig::from_usize_slice_trimmed(slice)
        }
    }

    pub(crate) unsafe fn from_usize_slice_trimmed(slice: &[usize]) -> Ubig {
        unsafe {
            assert_unchecked(
                slice.last().copied().map(|word| word != 0).unwrap_or(true)
            );
            assert_unchecked(
                slice.len().checked_mul(USIZE_BITS).is_some()
            );
        }
        let Some((&first, rest)) = slice.split_first() else {
            return Ubig::ZERO;
        };
        if rest.is_empty() && ((first & HIGH_BIT_MASK) == 0) {
            return unsafe { Ubig::from_small_usize_unchecked(first) };
        }
        unsafe {
            Ubig::new_with_capacity(slice.len(), |output_slice| {
                output_slice.write_copy_of_slice(slice);
            })
        }
    }

    pub(crate) fn as_usize_slice_untrimmed(&self) -> &[usize] {
        if self.is_inline() {
            let inline_ref = unsafe {
                let inline_ref = &self.storage.small_inline;
                assert_unchecked((*inline_ref & HIGH_BIT_MASK) == 0);
                inline_ref
            };
            std::slice::from_ref(inline_ref)
        } else {
            unsafe { self.get_heap_slice_untrimmed() }
        }
    }

    pub(crate) fn bit_capacity(&self) -> usize {
        if self.is_inline() {
            const { USIZE_BITS - 1 }
        } else {
            unsafe {
                let ptr = self.get_heap_ptr();
                ptr.read().unchecked_mul(USIZE_BITS)
            }
        }
    }

    pub fn as_usize_slice(&self) -> &[usize] {
        let slice = self.as_usize_slice_untrimmed();
        slice.trim_zeros()
    }

    pub(crate) fn is_inline(&self) -> bool {
        let raw_inline = unsafe { self.storage.small_inline };
        (raw_inline & HIGH_BIT_MASK) == 0
    }

    pub(crate) unsafe fn get_small_inline(&self) -> usize {
        let small_inline = unsafe { self.storage.small_inline };
        unsafe {
            assert_unchecked((small_inline & HIGH_BIT_MASK) == 0);
        }
        small_inline
    }

    pub(crate) unsafe fn get_heap_ptr(&self) -> NonNull<usize> {
        let ptr_tagged = unsafe { self.storage.ptr_tagged };
        ptr_tagged.map_addr(|addr| {
            let addr = addr.get();
            unsafe {
                assert_unchecked((addr & HIGH_BIT_MASK) == HIGH_BIT_MASK);
                let addr = addr << 1;
                NonZeroUsize::new_unchecked(addr)
            }
        })
    }

    pub(crate) unsafe fn from_heap_ptr(ptr: NonNull<usize>) -> Ubig {
        let ptr_tagged = ptr.map_addr(|addr| {
            let addr = addr.get();
            unsafe {
                let addr = addr.unchecked_shr_exact(1).unchecked_disjoint_bitor(HIGH_BIT_MASK);
                NonZeroUsize::new_unchecked(addr)
            }
        });
        Ubig { storage: UbigStorage { ptr_tagged } }
    }

    pub(crate) unsafe fn new_with_capacity(
        words_capacity: usize,
        func: impl FnOnce(&mut [MaybeUninit<usize>]),
    ) -> Ubig {
        if words_capacity == 0 {
            func(&mut []);
            return Ubig::ZERO;
        }
        unsafe {
            assert_unchecked(words_capacity.checked_mul(USIZE_BITS).is_some());
            let mut vec = Vec::with_capacity(words_capacity.unchecked_add(1));
            {
                let slice = vec.spare_capacity_mut();
                let (len, slice) = slice.split_first_mut().unwrap_unchecked();
                let words_len = slice.len();
                len.write(words_len);
                let (requested_slice, remaining_slice) = slice.split_at_mut_unchecked(words_capacity);
                func(requested_slice);
                let requested_slice = requested_slice.assume_init_ref();
                let (&first, remaining) = requested_slice.split_first().unwrap_unchecked();
                if remaining.is_zero() && (first & HIGH_BIT_MASK == 0) {
                    return Ubig::from_small_usize_unchecked(first);
                }
                remaining_slice.write_filled(0);
            }
            let (ptr, _, _) = vec.into_parts();
            Ubig::from_heap_ptr(ptr)
        }
    }

    pub(crate) unsafe fn get_heap_slice_untrimmed(&self) -> &[usize] {
        unsafe {
            let ptr = self.get_heap_ptr();
            let len = ptr.read();
            let slice = NonNull::slice_from_raw_parts(ptr.add(1), len);
            let slice = slice.as_ref();
            assert_unchecked({
                let (&first, rest) = slice.split_first().unwrap_unchecked();
                !(rest.is_zero() && (first & HIGH_BIT_MASK == 0))
            });
            slice
        }
    }

    pub(crate) unsafe fn get_heap_slice_trimmed(&self) -> &[usize] {
        let slice = unsafe { self.get_heap_slice_untrimmed() };
        slice.trim_zeros()
    }

    pub(crate) unsafe fn get_heap_slice_mut(&mut self) -> &mut [usize] {
        unsafe {
            let ptr = self.get_heap_ptr();
            let len = ptr.read();
            let mut slice = NonNull::slice_from_raw_parts(ptr.add(1), len);
            let slice = slice.as_mut();
            assert_unchecked({
                let (&first, rest) = slice.split_first().unwrap_unchecked();
                !(rest.is_zero() && (first & HIGH_BIT_MASK == 0))
            });
            slice
        }
    }

    pub fn bit_width(&self) -> usize {
        if self.is_inline() {
            let val = unsafe { self.get_small_inline() };
            val.bit_width() as usize
        } else {
            let mut slice = unsafe { self.get_heap_slice_untrimmed() };
            loop {
                let (&last, next_slice) = unsafe {
                    slice.split_last().unwrap_unchecked()
                };
                if last == 0 {
                    slice = next_slice;
                    continue;
                }
                break unsafe {
                    (last.bit_width() as usize)
                    .unchecked_add(next_slice.len().unchecked_mul(USIZE_BITS))
                };
            }
        }
    }

    pub fn is_power_of_two(&self) -> bool {
        if self.is_inline() {
            let val = unsafe { self.get_small_inline() };
            val.is_power_of_two()
        } else {
            let slice = unsafe { self.get_heap_slice_trimmed() };
            let (&last, remaining) = unsafe {
                slice.split_last().unwrap_unchecked()
            };
            last.is_power_of_two() && remaining.is_zero()
        }
    }

    pub fn trailing_ones(&self) -> usize {
        if self.is_inline() {
            let val = unsafe { self.get_small_inline() };
            val.trailing_ones() as usize
        } else {
            let words = unsafe { self.get_heap_slice_trimmed() };
            let mut total = 0usize;
            for word in words.iter().copied() {
                let ones = word.trailing_ones() as usize;
                total = total.strict_add(ones);
                if ones != USIZE_BITS {
                    break;
                }
            }
            total
        }
    }

    pub fn trailing_zeros(&self) -> Option<usize> {
        if self.is_inline() {
            let val = unsafe { self.get_small_inline() };
            let zeros = val.trailing_zeros() as usize;
            if zeros == USIZE_BITS {
                return None;
            }
            Some(zeros)
        } else {
            let words = unsafe { self.get_heap_slice_trimmed() };
            let mut iter = words.iter().copied();
            let mut word = unsafe { iter.next().unwrap_unchecked() };
            let mut total = 0usize;
            loop {
                let zeros = word.trailing_zeros() as usize;
                total = total.strict_add(zeros);
                if zeros != USIZE_BITS {
                    break;
                }
                word = unsafe { iter.next().unwrap_unchecked() };
            }
            Some(total)
        }
    }

    pub fn count_ones(&self) -> usize {
        if self.is_inline() {
            let val = unsafe { self.get_small_inline() };
            val.count_ones() as usize
        } else {
            let words = unsafe { self.get_heap_slice_trimmed() };
            let mut total = 0usize;
            for word in words.iter().copied() {
                let ones = word.count_ones() as usize;
                total = total.strict_add(ones);
            }
            total
        }
    }

    pub fn get_bit(&self, index: usize) -> bool {
        if self.is_inline() {
            if index < (USIZE_BITS - 1) {
                let small_inline = unsafe { self.get_small_inline() };
                (small_inline & (1 << index)) != 0
            } else {
                false
            }
        } else {
            let slice = unsafe { self.get_heap_slice_untrimmed() };
            let word_index = index / USIZE_BITS;
            let bit_index = index % USIZE_BITS;
            let Some(word) = slice.get(word_index).copied() else {
                return false;
            };
            (word & (1 << bit_index)) != 0
        }
    }

    pub fn set_bit_range_to_zero(&mut self, start: usize, end: usize) {
        let run_len = end.strict_sub(start);
        if run_len == 0 {
            return;
        }

        if self.is_inline() {
            if end < USIZE_BITS {
                let bits = !(((1 << run_len) - 1) << start);
                unsafe {
                    self.storage.small_inline &= bits;
                }
            } else if start < USIZE_BITS {
                let bits = (1 << start) - 1;
                unsafe {
                    self.storage.small_inline &= bits;
                }
            }
            return;
        }

        let slice = unsafe { self.get_heap_slice_mut() };

        if slice.bit_width() <= end && slice.bit_width_of_prefix(start) < USIZE_BITS {
            let word = unsafe { *slice.get_unchecked(0) };
            let bits = if end < USIZE_BITS {
                !(((1 << run_len) - 1) << start)
            } else if start < USIZE_BITS {
                (1 << start) - 1
            } else {
                !0
            };
            let small_inline = word & bits;
            *self = unsafe { Ubig::from_small_usize_unchecked(small_inline) };
            return;
        }

        let word_start = start / USIZE_BITS;
        let bit_start = start % USIZE_BITS;
        let word_end = end / USIZE_BITS;
        let bit_end = end % USIZE_BITS;

        if word_end < slice.len() {
            if word_start == word_end {
                let word = unsafe { slice.get_unchecked_mut(word_start) };
                let bits = unsafe {
                    !(
                        (1usize.unchecked_shl(run_len as u32).unchecked_sub(1))
                        .unchecked_shl(bit_start as u32)
                    )
                };
                *word &= bits;
                return;
            }

            let word = unsafe { slice.get_unchecked_mut(word_start) };
            let bits = unsafe {
                1usize.unchecked_shl(bit_start as u32).unchecked_sub(1)
            };
            *word &= bits;

            unsafe {
                slice.get_unchecked_mut(word_start.unchecked_add(1)..word_end).fill(0)
            }

            let word = unsafe { slice.get_unchecked_mut(word_end) };
            let bits = unsafe {
                (!0usize).unchecked_shl(bit_end as u32)
            };
            *word &= bits;
            return;
        }

        if word_start < slice.len() {
            let word = unsafe { slice.get_unchecked_mut(word_start) };
            let bits = unsafe {
                1usize.unchecked_shl(bit_start as u32).unchecked_sub(1)
            };
            *word &= bits;

            unsafe {
                slice.get_unchecked_mut(word_start.unchecked_add(1)..).fill(0)
            }
        }
    }

    pub fn set_bit_range_to_one(&mut self, start: usize, end: usize) {
        let run_len = end.strict_sub(start);
        if run_len == 0 {
            return;
        }

        if self.is_inline() {
            if end < USIZE_BITS {
                let bits = ((1 << run_len) - 1) << start;
                unsafe {
                    self.storage.small_inline |= bits;
                }
            } else {
                let word_start = start / USIZE_BITS;
                let bit_start = start % USIZE_BITS;
                let word_end = end / USIZE_BITS;
                let bit_end = end % USIZE_BITS;
                *self = unsafe {
                    Ubig::new_with_capacity(word_end + ((bit_end != 0) as usize), |output| {
                        let small_inline = self.get_small_inline();
                        if word_start == 0 {
                            output.get_unchecked_mut(0).write(small_inline | ((!0) << bit_start));
                            for index in 1..word_end {
                                output.get_unchecked_mut(index).write(!0);
                            }
                            if bit_end != 0 {
                                output.get_unchecked_mut(word_end).write((1 << bit_end) - 1);
                            }
                        } else if word_start == word_end {
                            output.get_unchecked_mut(0).write(small_inline);
                            for index in 1..word_start {
                                output.get_unchecked_mut(index).write(0);
                            }
                            output.get_unchecked_mut(word_start).write(
                                (1usize.unchecked_shl(run_len as u32) - 1) << bit_start
                            );
                        } else {
                            output.get_unchecked_mut(0).write(small_inline);
                            for index in 1..word_start {
                                output.get_unchecked_mut(index).write(0);
                            }
                            output.get_unchecked_mut(word_start).write((!0) << bit_start);
                            for index in word_start.unchecked_add(1)..word_end {
                                output.get_unchecked_mut(index).write(!0);
                            }
                            if bit_end != 0 {
                                output.get_unchecked_mut(word_end).write((1 << bit_end) - 1);
                            }
                        }
                    })
                };
            }
        } else {
            let word_start = start / USIZE_BITS;
            let bit_start = start % USIZE_BITS;
            let word_end = end / USIZE_BITS;
            let bit_end = end % USIZE_BITS;
            let slice = unsafe { self.get_heap_slice_mut() };
            let required_len = word_end + (bit_end != 0) as usize;
            if slice.len() < required_len {
                *self = unsafe {
                    Ubig::new_with_capacity(required_len, |output| {
                        if word_start < slice.len() {
                            for index in 0..word_start {
                                let word = *slice.get_unchecked(index);
                                output.get_unchecked_mut(index).write(word);
                            }

                            let word = *slice.get_unchecked(word_start);
                            let bits = (!0) << bit_start;
                            output.get_unchecked_mut(word_start).write(word | bits);
                            for index in word_start.unchecked_add(1)..word_end {
                                output.get_unchecked_mut(index).write(!0);
                            }
                            if bit_end != 0 {
                                output.get_unchecked_mut(word_end).write((1 << bit_end) - 1);
                            }
                        } else {
                            for index in 0..slice.len() {
                                let word = *slice.get_unchecked(index);
                                output.get_unchecked_mut(index).write(word);
                            }
                            for index in slice.len()..word_start {
                                output.get_unchecked_mut(index).write(0);
                            }
                            if word_start == word_end {
                                let bits = (1usize.unchecked_shl(run_len as u32) - 1) << bit_start;
                                output.get_unchecked_mut(word_start).write(bits);
                            } else {
                                output.get_unchecked_mut(word_start).write((!0) << bit_start);
                                for index in word_start.unchecked_add(1)..word_end {
                                    output.get_unchecked_mut(index).write(!0);
                                }
                                if bit_end != 0 {
                                    output.get_unchecked_mut(word_end).write((1 << bit_end) - 1);
                                }
                            }
                        }
                    })
                };
            } else {
                if word_start == word_end {
                    unsafe {
                        let bits = (1usize.unchecked_shl(run_len as u32) - 1) << bit_start;
                        *slice.get_unchecked_mut(word_start) |= bits;
                    }
                } else {
                    unsafe {
                        *slice.get_unchecked_mut(word_start) |= (!0) << bit_start;
                        for index in word_start.unchecked_add(1)..word_end {
                            *slice.get_unchecked_mut(index) = !0;
                        }
                        if bit_end != 0 {
                            *slice.get_unchecked_mut(word_end) |= (1 << bit_end) - 1;
                        }
                    }
                }
            }
        }
    }

    #[inline(always)]
    pub fn set_bit(&mut self, index: usize, bit: bool) {
        if bit {
            self.set_bit_to_one(index)
        } else {
            self.set_bit_to_zero(index)
        }
    }

    pub fn set_bit_to_zero(&mut self, index: usize) {
        if self.is_inline() {
            if index < (USIZE_BITS - 1) {
                unsafe {
                    self.storage.small_inline &= !(1 << index);
                }
            }
        } else {
            let word_index = index / USIZE_BITS;
            let bit_index = index % USIZE_BITS;
            let first_opt = {
                let slice = unsafe { self.get_heap_slice_mut() };
                let Some(word) = slice.get_mut(word_index) else {
                    return;
                };
                *word &= !(1 << bit_index);

                let (first, rest) = unsafe { slice.split_first().unwrap_unchecked() };
                if (*first & HIGH_BIT_MASK == 0) && rest.is_zero() {
                    Some(*first)
                } else {
                    None
                }
            };
            if let Some(first) = first_opt {
                *self = unsafe { Ubig::from_small_usize_unchecked(first) };
            }
        }
    }

    pub fn set_bit_to_one(&mut self, index: usize) {
        if self.is_inline() {
            if index < (USIZE_BITS - 1) {
                unsafe {
                    self.storage.small_inline |= 1 << index;
                }
            } else {
                let small_inline = unsafe { self.get_small_inline() };
                let word_index = index / USIZE_BITS;
                let bit_index = index % USIZE_BITS;
                *self = unsafe {
                    Ubig::new_with_capacity(1 + word_index, |slice| {
                        if word_index == 0 {
                            let word = small_inline.unchecked_disjoint_bitor(HIGH_BIT_MASK);
                            slice.get_unchecked_mut(0).write(word);
                        } else {
                            slice.get_unchecked_mut(0).write(small_inline);
                            slice.get_unchecked_mut(1..word_index).write_filled(0);
                            slice.get_unchecked_mut(word_index).write(1 << bit_index);
                        }
                    })
                };
            }
        } else {
            let word_index = index / USIZE_BITS;
            let bit_index = index % USIZE_BITS;
            let slice = unsafe { self.get_heap_slice_mut() };
            if word_index < slice.len() {
                unsafe {
                    *slice.get_unchecked_mut(word_index) |= 1 << bit_index;
                }
            } else {
                *self = unsafe {
                    Ubig::new_with_capacity(word_index + 1, |output| {
                        for (index, word) in slice.iter().copied().enumerate() {
                            output.get_unchecked_mut(index).write(word);
                        }
                        for index in slice.len()..word_index {
                            output.get_unchecked_mut(index).write(0);
                        }
                        output.get_unchecked_mut(word_index).write(1 << bit_index);
                    })
                };
            }
        }
    }

    pub fn shift_remove_bit(&mut self, index: usize) -> bool {
        unsafe fn shift_remove_bit_usize(
            word: usize,
            bit_index: u32,
        ) -> (usize, bool) {
            unsafe {
                assert_unchecked(bit_index < usize::BITS);

                let lower_mask = 1usize.unchecked_shl(bit_index).unchecked_sub(1);
                let shifted = word.unchecked_shr(1);
                let new_word = {
                    (word & lower_mask).unchecked_disjoint_bitor(shifted & !lower_mask)
                };
                let bit = word.unchecked_shr(bit_index) & 1 == 1;
                (new_word, bit)
            }
        }

        let word_index = index / USIZE_BITS;
        let bit_index = (index % USIZE_BITS) as u32;

        if self.is_inline() {
            if word_index > 0 {
                return false;
            }
            return unsafe {
                let inline = self.get_small_inline();
                let (new_inline, bit) = shift_remove_bit_usize(inline, bit_index);
                self.storage.small_inline = new_inline;
                bit
            };
        }

        let slice = unsafe { self.get_heap_slice_mut() };

        let Some(word) = slice.get_mut(word_index) else {
            return false;
        };

        let (new_word, bit) = unsafe { shift_remove_bit_usize(*word, bit_index) };
        *word = new_word;

        let mut index = word_index;
        loop {
            let next_index = unsafe { index.unchecked_add(1) };
            let Some(next_word) = slice.get(next_index).copied() else {
                break;
            };

            let lo_bit = next_word & 1;
            let hi_bit = unsafe { lo_bit.unchecked_shl(const { usize::BITS - 1 }) };
            let word = unsafe { slice.get_unchecked_mut(index) };
            unsafe {
                *word = word.unchecked_disjoint_bitor(hi_bit);
            };

            let new_next_word = unsafe { next_word.unchecked_shr(1) };
            unsafe {
                *slice.get_unchecked_mut(next_index) = new_next_word;
            }

            index = next_index;
        }

        let (first, rest) = unsafe { slice.split_first().unwrap_unchecked() };
        if rest.is_zero() && *first & HIGH_BIT_MASK == 0 {
            let word = *first;
            *self = unsafe { Ubig::from_small_usize_unchecked(word) };
        }

        bit
    }

    pub fn nth_power_of_two(n: usize) -> Ubig {
        if n < (USIZE_BITS - 1) {
            let small_inline = 1 << n;
            unsafe { Ubig::from_small_usize_unchecked(small_inline) }
        } else {
            let word_index = n / USIZE_BITS;
            let bit_index = n % USIZE_BITS;
            unsafe {
                Ubig::new_with_capacity(word_index + 1, |slice| {
                    slice.get_unchecked_mut(..word_index).write_filled(0);
                    slice.get_unchecked_mut(word_index).write(1 << bit_index);
                })
            }
        }
    }

    pub fn nth_power_of_two_minus_one(n: usize) -> Ubig {
        if n < USIZE_BITS {
            let small_inline = (1 << n) - 1;
            unsafe { Ubig::from_small_usize_unchecked(small_inline) }
        } else {
            let word_index = n / USIZE_BITS;
            let bit_index = n % USIZE_BITS;
            unsafe {
                Ubig::new_with_capacity(word_index + (bit_index != 0) as usize, |slice| {
                    slice.get_unchecked_mut(..word_index).write_filled(!0);
                    if bit_index != 0 {
                        slice.get_unchecked_mut(word_index).write((1 << bit_index) - 1);
                    }
                })
            }
        }
    }

    pub fn extract_bits(&mut self, mask: &[usize]) {
        if self.is_inline() {
            let small_inline = unsafe { &mut self.storage.small_inline };
            let mask = mask.first().copied().unwrap_or(0);
            *small_inline = small_inline.extract_bits(mask);
            return;
        }

        let slice = unsafe { self.get_heap_slice_mut() };
        let num_words = cmp::min(slice.len(), mask.len());

        let final_bit_count = {
            let mut index = num_words;
            loop {
                let Some(next_index) = index.checked_sub(1) else {
                    break 0;
                };
                index = next_index;

                let slice_word = unsafe { *slice.get_unchecked(index) };
                let mask_word = unsafe { *mask.get_unchecked(index) };
                let word = slice_word & mask_word;
                let lz = word.leading_zeros() as usize;
                if lz == USIZE_BITS {
                    continue;
                }

                let mut final_bit_count = if lz == 0 {
                    mask_word.count_ones() as usize
                } else {
                    let mask_len = unsafe { USIZE_BITS.unchecked_sub(lz) };
                    let mask_mask = unsafe {
                        1usize
                        .unchecked_shl(mask_len as u32)
                        .unchecked_sub(1)
                    };
                    (mask_word & mask_mask).count_ones() as usize
                };
                for index in 0..index {
                    let mask_word = unsafe { *mask.get_unchecked(index) };
                    final_bit_count = unsafe { 
                        final_bit_count.unchecked_add(mask_word.count_ones() as usize)
                    };
                }
                break final_bit_count;
            }
        };

        if final_bit_count < USIZE_BITS {
            let mut small_inline = 0usize;
            let mut write_position = 0usize;
            for read_word_index in 0..num_words {
                let slice_word = unsafe { *slice.get_unchecked(read_word_index) };
                let mask_word = unsafe { *mask.get_unchecked(read_word_index) };
                let num_kept_bits = mask_word.count_ones() as usize;
                let new_bits = slice_word.extract_bits(mask_word);

                small_inline = unsafe {
                    small_inline
                    .unchecked_disjoint_bitor(
                        new_bits.unchecked_shl(write_position as u32)
                    )
                };
                write_position = unsafe { write_position.unchecked_add(num_kept_bits) };
                if write_position >= USIZE_BITS - 1 {
                    break;
                }
            }
            *self = unsafe { Ubig::from_small_usize_unchecked(small_inline) };
            return;
        }

        if let Some(excess) = slice.get_mut(num_words..) {
            excess.fill(0);
        }
        let mut write_position = 0;
        for read_word_index in 0..num_words {
            let slice_word = mem::replace(
                unsafe { slice.get_unchecked_mut(read_word_index) },
                0,
            );
            let mask_word = unsafe { *mask.get_unchecked(read_word_index) };
            let num_kept_bits = mask_word.count_ones() as usize;
            let new_bits = slice_word.extract_bits(mask_word);
            let write_word_index = write_position / USIZE_BITS;
            let write_bit_index = write_position % USIZE_BITS;
            unsafe {
                let output_word = slice.get_unchecked_mut(write_word_index);
                *output_word = {
                    output_word
                    .unchecked_disjoint_bitor(
                        new_bits.unchecked_shl(write_bit_index as u32)
                    )
                };
            }
            let num_bits_written = unsafe { USIZE_BITS.unchecked_sub(write_bit_index) };
            if num_bits_written < num_kept_bits {
                let output_word = unsafe {
                    slice.get_unchecked_mut(write_word_index.unchecked_add(1))
                };
                *output_word = unsafe {
                    new_bits.unchecked_shr(num_bits_written as u32)
                };
            }
            write_position = unsafe { write_position.unchecked_add(num_kept_bits) };
        }
    }

    /*
    pub fn extract_lower_bits_and_shift(&mut self, mask: &[usize], len: usize) {
        assert!(mask.bit_width() <= len);
        let self_bit_width = self.bit_width();
        if self_bit_width <= len {
            self.extract_bits(mask);
            return 
        }

        if self.is_inline() {
            let small_inline = unsafe { &mut self.storage.small_inline };
            let mask = mask.first().copied().unwrap_or(0);
            *small_inline = unsafe {
                small_inline
                .extract_bits(mask)
                .unchecked_disjoint_bitor(
                    small_inline
                    .unchecked_shr((len as u32).unchecked_sub(mask.count_ones()))
                )
            };
            return;
        }

        let slice = unsafe { self.get_heap_slice_mut() };
        let num_words = cmp::min(slice.len(), mask.len());

        let final_bit_count = unsafe {
            self_bit_width.unchecked_sub(
                len.unchecked_sub(mask.count_ones()),
            )
        };

        if final_bit_count < USIZE_BITS {
            let word_cut = len / USIZE_BITS;
            let bit_cut = len % USIZE_BITS;

            let mut small_inline = 0usize;
            let mut write_position = 0usize;
            if !mask.is_empty() {
                for read_word_index in 0..unsafe { num_words.unchecked_sub(1) } {
                    let slice_word = unsafe { *slice.get_unchecked(read_word_index) };
                    let mask_word = unsafe { *mask.get_unchecked(read_word_index) };
                    let num_kept_bits = mask_word.count_ones() as usize;
                    let new_bits = slice_word.extract_bits(mask_word);

                    small_inline = unsafe {
                        small_inline
                        .unchecked_disjoint_bitor(
                            new_bits.unchecked_shl(write_position as u32)
                        )
                    };
                    write_position = unsafe { write_position.unchecked_add(num_kept_bits) };
                }

                let slice_word = unsafe { *slice.get_unchecked(num_words) };
                let mask_word = unsafe { *mask.get_unchecked(num_words) };
                let num_kept_bits = mask_word.count_ones() as usize;
                let new_bits = slice_word.extract_bits(mask_word);

                if word_cut < mask.len() {
                    let trailing_bits = unsafe { slice_word.unchecked_shr(bit_cut as u32) };
                    let new_bits = unsafe {
                        new_bits
                        .unchecked_disjoint_bitor(trailing_bits)
                    };
                    small_inline = unsafe {
                        small_inline
                        .unchecked_disjoint_bitor(
                            new_bits.unchecked_shl(write_position as u32)
                        )
                    };
                    write_position = unsafe {
                        write_position
                        .unchecked_add(num_kept_bits)
                        .unchecked_add(USIZE_BITS.unchecked_sub(bit_cut))
                    };
                } else {
                    small_inline = unsafe {
                        small_inline
                        .unchecked_disjoint_bitor(
                            new_bits.unchecked_shl(write_position as u32)
                        )
                    };
                    write_position = unsafe { write_position.unchecked_add(num_kept_bits) };
                }
            }


            for index in word_cut..unsafe { slice.len().unchecked_sub(1) } {
            }
            *self = unsafe { Ubig::from_small_usize_unchecked(small_inline) };
            return;
        }

        if let Some(excess) = slice.get_mut(num_words..) {
            excess.fill(0);
        }
        let mut write_position = 0;
        for read_word_index in 0..num_words {
            let slice_word = mem::replace(
                unsafe { slice.get_unchecked_mut(read_word_index) },
                0,
            );
            let mask_word = unsafe { *mask.get_unchecked(read_word_index) };
            let num_kept_bits = mask_word.count_ones() as usize;
            let new_bits = slice_word.extract_bits(mask_word);
            let write_word_index = write_position / USIZE_BITS;
            let write_bit_index = write_position % USIZE_BITS;
            unsafe {
                let output_word = slice.get_unchecked_mut(write_word_index);
                *output_word = {
                    output_word
                    .unchecked_disjoint_bitor(
                        new_bits.unchecked_shl(write_bit_index as u32)
                    )
                };
            }
            let num_bits_written = unsafe { USIZE_BITS.unchecked_sub(write_bit_index) };
            if num_bits_written < num_kept_bits {
                let output_word = unsafe {
                    slice.get_unchecked_mut(write_word_index.unchecked_add(1))
                };
                *output_word = unsafe {
                    new_bits.unchecked_shr(num_bits_written as u32)
                };
            }
            write_position = unsafe { write_position.unchecked_add(num_kept_bits) };
        }
    }
    */

    // assumes the mask is exactly the length (in words) of the output
    pub(crate) unsafe fn deposit_bits_exact_mask(&mut self, mask: &[usize], mask_ones: usize) {
        let Some((&first, rest)) = mask.split_first() else {
            *self = Ubig::ZERO;
            return;
        };
        if rest.is_empty() {
            let slice = self.as_usize_slice_untrimmed();
            let word = unsafe { *slice.get_unchecked(0) };
            let new_word = word.deposit_bits(first);
            *self = Ubig::from_usize(new_word);
            return;
        }

        if self.is_inline() {
            let small_inline = unsafe { self.get_small_inline() };

            *self = unsafe {
                Ubig::new_with_capacity(mask.len(), |output| {
                    let mut read_position = mask_ones;
                    for (index, mask_word) in mask.iter().copied().enumerate().rev() {
                        let mask_word_ones = mask_word.count_ones() as usize;
                        read_position = read_position.unchecked_sub(mask_word_ones);
                        let bits = small_inline.unchecked_shr(read_position as u32);
                        let new_word = bits.deposit_bits(mask_word);
                        output.get_unchecked_mut(index).write(new_word);
                    }
                })
            };
            return;
        }

        let slice = unsafe { self.get_heap_slice_mut() };
        if mask.len() <= slice.len() {
            unsafe {
                slice.get_unchecked_mut(mask.len()..).fill(0);

                let mut read_position = mask_ones;
                let mut read_word_index = read_position / USIZE_BITS;
                let mut hi = 0;
                let mut lo = slice.get(read_word_index).copied().unwrap_or(0);
                for (index, mask_word) in mask.iter().copied().enumerate().rev() {
                    let mask_word_ones = mask_word.count_ones() as usize;
                    read_position = read_position.unchecked_sub(mask_word_ones);
                    let next_read_word_index = read_position / USIZE_BITS;
                    if next_read_word_index < read_word_index {
                        hi = lo;
                        lo = *slice.get_unchecked(next_read_word_index);
                    };
                    read_word_index = next_read_word_index;
                    let read_bit_index = read_position % USIZE_BITS;

                    let bits = hi.unchecked_funnel_shr(lo, read_bit_index as u32);
                    let new_word = bits.deposit_bits(mask_word);
                    *slice.get_unchecked_mut(index) = new_word;
                }
            }
            return;
        }

        *self = unsafe {
            Ubig::new_with_capacity(mask.len(), |output| {
                let mut read_position = mask_ones;
                let mut read_word_index = read_position / USIZE_BITS;
                let mut hi = 0;
                let mut lo = slice.get(read_word_index).copied().unwrap_or(0);
                for (index, mask_word) in mask.iter().copied().enumerate().rev() {
                    let mask_word_ones = mask_word.count_ones() as usize;
                    read_position = read_position.unchecked_sub(mask_word_ones);
                    let next_read_word_index = read_position / USIZE_BITS;
                    if next_read_word_index < read_word_index {
                        hi = lo;
                        lo = *slice.get_unchecked(next_read_word_index);
                    };
                    read_word_index = next_read_word_index;
                    let read_bit_index = read_position % USIZE_BITS;

                    let bits = hi.unchecked_funnel_shr(lo, read_bit_index as u32);
                    let new_word = bits.deposit_bits(mask_word);
                    output.get_unchecked_mut(index).write(new_word);
                }
            })
        }
    }

    pub fn deposit_bits(&mut self, mask: &[usize]) {
        let full_bit_width = self.bit_width();
        let mut relevant_mask_words = 0usize;
        let mut relevant_mask_ones = 0usize;
        loop {
            if relevant_mask_ones >= full_bit_width {
                let mask = unsafe { mask.get_unchecked(..relevant_mask_words) };
                return unsafe {
                    self.deposit_bits_exact_mask(mask, relevant_mask_ones);
                };
            }
            let Some(mask_word) = mask.get(relevant_mask_words) else {
                let mask_ones_required = {
                    let word_index = relevant_mask_ones / USIZE_BITS;
                    let bit_index = relevant_mask_ones % USIZE_BITS;
                    let slice = self.as_usize_slice();
                    let last_word = unsafe { *slice.get_unchecked(word_index) };
                    let masked_last_word = last_word & ((1 << bit_index) - 1);
                    let last_bit_width = masked_last_word.bit_width() as usize;
                    if last_bit_width > 0 {
                        unsafe {
                            word_index
                            .unchecked_mul(USIZE_BITS)
                            .unchecked_add(last_bit_width)
                        }
                    } else {
                        let mut index = word_index;
                        loop {
                            let Some(next_index) = index.checked_sub(1) else {
                                break 0;
                            };
                            index = next_index;
                            let word = unsafe { *slice.get_unchecked(index) };
                            let bit_width = word.bit_width() as usize;
                            if bit_width == 0 {
                                continue;
                            }
                            break unsafe {
                                index
                                .unchecked_mul(USIZE_BITS)
                                .unchecked_add(bit_width)
                            };
                        }
                    }
                };
                let mut relevant_mask_words = 0usize;
                let mut relevant_mask_ones = 0;
                loop {
                    if relevant_mask_ones >= mask_ones_required {
                        break;
                    };
                    let mask_word = unsafe { *mask.get_unchecked(relevant_mask_words) };
                    relevant_mask_words += 1;
                    relevant_mask_ones += mask_word.count_ones() as usize;
                }
                let mask = unsafe { mask.get_unchecked(..relevant_mask_words) };
                return unsafe {
                    self.deposit_bits_exact_mask(mask, relevant_mask_ones);
                };
            };
            relevant_mask_words += 1;
            relevant_mask_ones += mask_word.count_ones() as usize;
        };
    }

    pub fn truncate(&mut self, len: usize) {
        if self.is_inline() {
            if len < (USIZE_BITS - 1) {
                unsafe {
                    self.storage.small_inline &= (1 << len) - 1;
                }
            }
        } else {
            let slice = unsafe { self.get_heap_slice_mut() };
            if unsafe { slice.len().unchecked_mul(USIZE_BITS) } <= len {
                return;
            }
            if len < USIZE_BITS {
                let word = unsafe { *slice.get_unchecked(0) };
                let mask = (1 << len) - 1;
                let small_inline = word & mask;
                *self = unsafe { Ubig::from_small_usize_unchecked(small_inline) };
            } else {
                let word_index = len / USIZE_BITS;
                let bit_index = len % USIZE_BITS;
                let first_word = unsafe { *slice.get_unchecked(0) };
                let need_heap = {
                    ((first_word & HIGH_BIT_MASK) != 0)
                    || (1..word_index).any(|index| {
                        (unsafe { *slice.get_unchecked(index) }) != 0
                    })
                    || {
                        let last_word = unsafe { *slice.get_unchecked(word_index) };
                        let mask = (1 << bit_index) - 1;
                        (last_word & mask) != 0
                    }
                };
                if need_heap {
                    unsafe {
                        *slice.get_unchecked_mut(word_index) &= (1 << bit_index) - 1;
                    }
                    for index in word_index.strict_add(1)..slice.len() {
                        unsafe {
                            *slice.get_unchecked_mut(index) = 0;
                        }
                    }
                } else {
                    *self = unsafe { Ubig::from_small_usize_unchecked(first_word) };
                }
            }
        }
    }

    pub fn clone_truncate(&self, len: usize) -> Ubig {
        if self.is_inline() {
            let small_inline = unsafe { self.get_small_inline() };
            if len < (USIZE_BITS - 1) {
                let mask = (1 << len) - 1;
                let small_inline = small_inline & mask;
                unsafe { Ubig::from_small_usize_unchecked(small_inline) }
            } else {
                unsafe { Ubig::from_small_usize_unchecked(small_inline) }
            }
        } else {
            let slice = unsafe { self.get_heap_slice_untrimmed() };
            if unsafe { slice.len().unchecked_mul(USIZE_BITS) } <= len {
                Ubig::from_usize_slice(slice)
            } else if len < USIZE_BITS {
                let word = unsafe { *slice.get_unchecked(0) };
                let mask = (1 << len) - 1;
                let small_inline = word & mask;
                unsafe { Ubig::from_small_usize_unchecked(small_inline) }
            } else {
                let word_index = len / USIZE_BITS;
                let bit_index = len % USIZE_BITS;
                let first_word = unsafe { *slice.get_unchecked(0) };
                let need_heap = {
                    ((first_word & HIGH_BIT_MASK) != 0)
                    || (1..word_index).any(|index| {
                        (unsafe { *slice.get_unchecked(index) }) != 0
                    })
                    || (
                        (bit_index != 0) && {
                            let last_word = unsafe { *slice.get_unchecked(word_index) };
                            let mask = (1 << bit_index) - 1;
                            (last_word & mask) != 0
                        }
                    )
                };
                if need_heap {
                    unsafe {
                        Ubig::new_with_capacity(
                            word_index + ((bit_index != 0) as usize),
                            |output| {
                                for index in 0..word_index {
                                    let word = *slice.get_unchecked(index);
                                    output.get_unchecked_mut(index).write(word);
                                }
                                if bit_index != 0 {
                                    let word = *slice.get_unchecked(word_index);
                                    let mask = (1 << bit_index) - 1;
                                    output.get_unchecked_mut(word_index).write(word & mask);
                                }
                            },
                        )
                    }
                } else {
                    unsafe { Ubig::from_small_usize_unchecked(first_word) }
                }
            }
        }
    }

    pub fn ilog2_exact(&self) -> Option<usize> {
        let slice = self.as_usize_slice_untrimmed();
        slice.ilog2_exact()
    }

    pub fn truncated_bit_width(&self, len: usize) -> usize {
        self.as_usize_slice().bit_width_of_prefix(len)
    }

    pub fn increment(&mut self) {
        if self.is_inline() {
            let small_inline = unsafe { &mut self.storage.small_inline };
            if *small_inline == HIGH_BIT_MASK - 1 {
                *self = unsafe {
                    Ubig::new_with_capacity(1, |output| {
                        output.get_unchecked_mut(0).write(HIGH_BIT_MASK);
                    })
                };
                return;
            }
            *small_inline = unsafe { small_inline.unchecked_add(1) };
            return;
        }

        let slice = unsafe { self.get_heap_slice_mut() };
        if slice.iter().all(|word| *word == !0) {
            let len = slice.len();
            *self = unsafe {
                let new_len = len.unchecked_add(1);
                Ubig::new_with_capacity(new_len, |output| {
                    for index in 0..len {
                        output.get_unchecked_mut(index).write(0);
                    }
                    output.get_unchecked_mut(len).write(1);
                })
            };
            return;
        }

        for word in slice {
            if let Some(new_word) = word.checked_add(1) {
                *word = new_word;
                break;
            }
            *word = 0;
        }
    }

    pub fn decrement(&mut self) -> bool {
        if self.is_inline() {
            let inline = unsafe { &mut self.storage.small_inline };
            return match inline.checked_sub(1) {
                None => false,
                Some(new_inline) => {
                    *inline = new_inline;
                    true
                },
            };
        }

        let slice = unsafe { self.get_heap_slice_mut() };
        let (&first, rest) = unsafe { slice.split_first().unwrap_unchecked() };
        if first == HIGH_BIT_MASK && rest.is_zero() {
            *self = unsafe { Ubig::from_small_usize_unchecked(HIGH_BIT_MASK - 1) };
            return true;
        }

        for word in slice {
            if let Some(new_word) = word.checked_sub(1) {
                *word = new_word;
                break;
            }
            *word = !0;
        }

        true
    }

    pub fn position_of_nth_one(&self, n: usize) -> Option<usize> {
        self.as_usize_slice().position_of_nth_one(n)
    }

    pub fn pow(self, n: usize) -> Ubig {
        let tz = n.trailing_zeros();
        if tz == usize::BITS {
            return Ubig::ONE;
        }

        let mut state = self;
        for _ in 0..tz {
            state = &state * &state;
        }
        let mut n = n.unbounded_shr(unsafe { tz.unchecked_add(1) });
        if n == 0 {
            return state;
        }

        let mut total = state.clone();
        while n != 0 {
            state = &state * &state;
            if n & 1 == 1 {
                total *= &state;
            }
            n >>= 1;
        }
        total
    }
}

