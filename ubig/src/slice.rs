use crate::priv_prelude::*;

pub(crate) trait UsizeSliceExt {
    fn is_zero(&self) -> bool;
    fn trim_zeros(&self) -> &[usize];
    fn bit_width(&self) -> usize;
    fn ilog2_exact(&self) -> Option<usize>;
    #[expect(unused)]
    fn count_zeros(&self) -> usize;
    #[expect(unused)]
    fn count_ones(&self) -> usize;
    fn bit_width_of_prefix(&self, len: usize) -> usize;
    #[expect(unused)]
    fn count_ones_until_limit(&self, num_ones: usize) -> (usize, usize);
    #[expect(unused)]
    fn get_usize_at_bit_index(&self, bit_index: usize) -> usize;
    #[expect(unused)]
    fn spare_bit_capacity(&self) -> usize;
    fn position_of_nth_one(&self, n: usize) -> Option<usize>;
    fn set_bit_to_one(&mut self, index: usize);
}

impl UsizeSliceExt for [usize] {
    fn is_zero(&self) -> bool {
        self.iter().all(|word| *word == 0)
    }

    fn trim_zeros(&self) -> &[usize] {
        let mut slice = self;
        while let Some((last, next_slice)) = slice.split_last() {
            if *last != 0 {
                break;
            }
            slice = next_slice;
        }
        slice
    }

    fn bit_width(&self) -> usize {
        let mut slice = self;
        while let Some((last, next_slice)) = slice.split_last() {
            if *last != 0 {
                let last_bits = last.bit_width() as usize;
                let rest_bits = next_slice.len().strict_mul(USIZE_BITS);
                let total = unsafe { rest_bits.unchecked_add(last_bits) };
                return total;
            }
            slice = next_slice;
        }
        0
    }

    fn ilog2_exact(&self) -> Option<usize> {
        let slice = self.trim_zeros();
        let (last, rest) = slice.split_last()?;
        if !last.is_power_of_two() {
            return None;
        }
        if !rest.is_zero() {
            return None;
        }
        let last_bits = unsafe { last.bit_width().unchecked_sub(1) as usize };
        let rest_bits = rest.len().strict_mul(USIZE_BITS);
        let bits = unsafe { rest_bits.unchecked_add(last_bits) };
        Some(bits)
    }

    fn count_zeros(&self) -> usize {
        let mut total = 0usize;
        for word in self.iter().copied() {
            total = total.strict_add(word.count_zeros() as usize);
        }
        total
    }

    fn count_ones(&self) -> usize {
        let mut total = 0usize;
        for word in self.iter().copied() {
            total = total.strict_add(word.count_ones() as usize);
        }
        total
    }

    fn bit_width_of_prefix(&self, len: usize) -> usize {
        let word_index = len / USIZE_BITS;
        let bit_index = len % USIZE_BITS;
        if word_index < self.len() {
            let last_word = unsafe { *self.get_unchecked(word_index) };
            let masked_last_word = last_word & ((1 << bit_index) - 1);
            let last_bit_width = masked_last_word.bit_width() as usize;
            if last_bit_width > 0 {
                let before = word_index.strict_mul(USIZE_BITS);
                unsafe {
                    before.unchecked_add(last_bit_width)
                }
            } else {
                let mut index = word_index;
                loop {
                    let Some(next_index) = index.checked_sub(1) else {
                        break 0;
                    };
                    index = next_index;
                    let word = unsafe { *self.get_unchecked(index) };
                    let bit_width = word.bit_width() as usize;
                    if bit_width == 0 {
                        continue;
                    }
                    let before = index.strict_mul(USIZE_BITS);
                    break unsafe {
                        before.unchecked_add(bit_width)
                    };
                }
            }
        } else {
            self.bit_width()
        }
    }

    fn count_ones_until_limit(&self, ones_limit: usize) -> (usize, usize) {
        let mut num_words = 0usize;
        let mut num_ones = 0usize;
        loop {
            if num_ones >= ones_limit {
                break;
            }
            let Some(word) = self.get(num_words) else {
                break;
            };
            num_words += 1;
            num_ones += word.count_ones() as usize;
        }
        (num_words, num_ones)
    }

    fn get_usize_at_bit_index(&self, bit_index: usize) -> usize {
        let word_index = bit_index / USIZE_BITS;
        let bit_index = (bit_index % USIZE_BITS) as u32;

        let Some(lo) = self.get(word_index).copied() else {
            return 0;
        };
        let hi = self.get(unsafe { word_index.unchecked_add(1) }).copied().unwrap_or(0);
        unsafe {
            hi.unchecked_funnel_shr(lo, bit_index)
        }
    }

    fn spare_bit_capacity(&self) -> usize {
        let total_capacity = self.len().strict_mul(USIZE_BITS);
        let width = self.bit_width();
        unsafe { total_capacity.unchecked_sub(width) }
    }

    fn position_of_nth_one(&self, n: usize) -> Option<usize> {
        let mut index = 0;
        let mut n = n;
        for word in self.iter().copied() {
            let ones = word.count_ones() as usize;
            let Some(next_n) = n.checked_sub(ones) else {
                let mut word = word;
                loop {
                    let trailing = word.trailing_ones() as usize;
                    let Some(next_n) = n.checked_sub(trailing) else {
                        return Some(n + index);
                    };
                    n = next_n;
                    word >>= trailing;
                    index += trailing;
                    let trailing = word.trailing_zeros() as usize;
                    word >>= trailing;
                    index += trailing;
                }
            };
            n = next_n;
            index += USIZE_BITS;
        }
        None
    }

    fn set_bit_to_one(&mut self, index: usize) {
        let word_index = index / USIZE_BITS;
        let bit_index = (index % USIZE_BITS) as u32;
        let Some(word) = self.get_mut(word_index) else {
            return;
        };
        let bits = 1 << bit_index;
        *word |= bits;
    }
}

