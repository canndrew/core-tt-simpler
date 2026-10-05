use crate::priv_prelude::*;

impl ops::BitAndAssign<usize> for Ubig {
    fn bitand_assign(&mut self, rhs: usize) {
        if self.is_inline() {
            let lhs = unsafe { self.get_small_inline() };
            let word = lhs & rhs;
            *self = unsafe { Ubig::from_small_usize_unchecked(word) };
            return;
        }

        let lhs = unsafe {
            let slice = self.get_heap_slice_untrimmed();
            *slice.first().unwrap_unchecked()
        };
        let word = lhs & rhs;
        *self = Ubig::from_usize(word);
    }
}

impl ops::BitAndAssign<&[usize]> for Ubig {
    fn bitand_assign(&mut self, rhs: &[usize]) {
        let rhs = rhs.trim_zeros();
        let Some((&rhs_first, rhs_rest)) = rhs.split_first() else {
            *self = Ubig::ZERO;
            return;
        };

        if self.is_inline() {
            let lhs = unsafe { self.get_small_inline() };
            let word = lhs & rhs_first;
            *self = unsafe { Ubig::from_small_usize_unchecked(word) };
            return;
        }

        let lhs = unsafe { self.get_heap_slice_mut() };
        let (&lhs_first, lhs_rest) = unsafe { lhs.split_first().unwrap_unchecked() };
        if {
            lhs_rest
            .iter()
            .copied()
            .zip(rhs_rest.iter().copied())
            .all(|(lhs_word, rhs_word)| lhs_word & rhs_word == 0)
        } {
            let word = lhs_first & rhs_first;
            *self = Ubig::from_usize(word);
            return;
        }

        let lhs_slice = unsafe { self.get_heap_slice_mut() };
        for (lhs_word, rhs_word) in lhs_slice.iter_mut().zip(rhs.iter().copied().chain(iter::repeat(0))) {
            *lhs_word = *lhs_word & rhs_word;
        }
    }
}

impl ops::BitAndAssign<&Ubig> for Ubig {
    fn bitand_assign(&mut self, rhs: &Ubig) {
        *self &= rhs.as_usize_slice()
    }
}

impl ops::BitAndAssign<Ubig> for Ubig {
    fn bitand_assign(&mut self, rhs: Ubig) {
        let mut rhs = rhs;
        let lhs = self;
        let rhs = &mut rhs;

        if lhs.bit_capacity() > rhs.bit_capacity() {
            mem::swap(lhs, rhs);
        }

        *lhs &= &*rhs;
    }
}

impl ops::BitAnd<usize> for Ubig {
    type Output = usize;

    fn bitand(self, rhs: usize) -> usize {
        &self & rhs
    }
}

impl ops::BitAnd<&[usize]> for Ubig {
    type Output = Ubig;

    fn bitand(mut self, rhs: &[usize]) -> Ubig {
        self &= rhs;
        self
    }
}

impl ops::BitAnd<&Ubig> for Ubig {
    type Output = Ubig;

    fn bitand(mut self, rhs: &Ubig) -> Ubig {
        self &= rhs;
        self
    }
}

impl ops::BitAnd<Ubig> for Ubig {
    type Output = Ubig;

    fn bitand(mut self, rhs: Ubig) -> Ubig {
        self &= rhs;
        self
    }
}

impl ops::BitAnd<usize> for &Ubig {
    type Output = usize;

    fn bitand(self, rhs: usize) -> usize {
        if self.is_inline() {
            let lhs = unsafe { self.get_small_inline() };
            return lhs & rhs;
        }
        
        let lhs = unsafe {
            let slice = self.get_heap_slice_untrimmed();
            *slice.first().unwrap_unchecked()
        };
        lhs & rhs
    }
}

impl ops::BitAnd<&[usize]> for &Ubig {
    type Output = Ubig;

    fn bitand(self, rhs: &[usize]) -> Ubig {
        let lhs = self.as_usize_slice();
        let rhs = rhs.trim_zeros();
        let mut len = cmp::min(lhs.len(), rhs.len());
        let last_word = loop {
            let Some(next_len) = len.checked_sub(1) else {
                return Ubig::ZERO;
            };
            let lhs_word = unsafe { *lhs.get_unchecked(next_len) };
            let rhs_word = unsafe { *rhs.get_unchecked(next_len) };
            let word = lhs_word & rhs_word;
            if word != 0 {
                break word;
            }
            len = next_len;
        };
        if len == 1 {
            return Ubig::from_usize(last_word);
        }

        unsafe {
            Ubig::new_with_capacity(len, |output| {
                for (index, output_word) in output.iter_mut().enumerate() {
                    let lhs_word = *lhs.get_unchecked(index);
                    let rhs_word = *rhs.get_unchecked(index);
                    let word = lhs_word & rhs_word;
                    output_word.write(word);
                }
            })
        }
    }
}

impl ops::BitAnd<&Ubig> for &Ubig {
    type Output = Ubig;

    fn bitand(self, rhs: &Ubig) -> Ubig {
        rhs & self.as_usize_slice()
    }
}

impl ops::BitAnd<Ubig> for &Ubig {
    type Output = Ubig;

    fn bitand(self, rhs: Ubig) -> Ubig {
        rhs & self
    }
}

impl ops::BitAnd<&Ubig> for usize {
    type Output = usize;

    fn bitand(self, rhs: &Ubig) -> usize {
        rhs & self
    }
}

impl ops::BitAnd<Ubig> for usize {
    type Output = usize;

    fn bitand(self, rhs: Ubig) -> usize {
        rhs & self
    }
}

impl ops::BitAnd<&Ubig> for &[usize] {
    type Output = Ubig;

    fn bitand(self, rhs: &Ubig) -> Ubig {
        rhs & self
    }
}

impl ops::BitAnd<Ubig> for &[usize] {
    type Output = Ubig;

    fn bitand(self, rhs: Ubig) -> Ubig {
        rhs & self
    }
}

