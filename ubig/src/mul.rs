use crate::priv_prelude::*;

fn slice_mul_assign_usize(lhs: &mut [usize], rhs: usize) {
    let mut carry = 0;
    for lhs_word in lhs.iter_mut() {
        let (ret_word, next_carry) = lhs_word.carrying_mul(rhs, carry);
        *lhs_word = ret_word;
        carry = next_carry;
    }
}

fn slice_add_assign_mul(lhs: &[usize], rhs: &[usize], output: &mut [usize]) {
    for (lhs_index, lhs_word) in lhs.iter().copied().enumerate().take(output.len()) {
        let mut carry = 0;
        for (rhs_index, rhs_word) in rhs.iter().copied().enumerate() {
            let Some(output_word) = output.get_mut(lhs_index + rhs_index) else {
                break;
            };
            let (ret_word, next_carry) = lhs_word.carrying_mul_add(rhs_word, *output_word, carry);
            *output_word = ret_word;
            carry = next_carry;
        }
        if let Some(output) = output.get_mut((lhs_index + rhs.len())..) {
            crate::add::add_assign_slice_usize(output, carry);
        };
    }
}

fn slice_mul_usize(lhs: &[usize], rhs: usize, output: &mut [MaybeUninit<usize>]) {
    let mut carry = 0;
    for (index, output_word) in output.iter_mut().enumerate() {
        let lhs_word = lhs.get(index).copied().unwrap_or(0);
        let (ret_word, next_carry) = lhs_word.carrying_mul(rhs, carry);
        output_word.write(ret_word);
        carry = next_carry;
    }
}

impl ops::MulAssign<usize> for Ubig {
    fn mul_assign(&mut self, rhs: usize) {
        if self.is_inline() {
            let lhs = unsafe { self.get_small_inline() };
            let (lo, hi) = lhs.carrying_mul(rhs, 0);
            *self = Ubig::from_usize_slice(&[lo, hi]);
            return;
        }

        if rhs == 0 {
            *self = Ubig::ZERO;
            return;
        }

        let lhs = unsafe { self.get_heap_slice_mut() };
        let lhs_capacity = unsafe { lhs.len().unchecked_mul(USIZE_BITS) };
        let lhs_width = lhs.bit_width();
        let rhs_width = rhs.bit_width() as usize;
        let width = lhs_width.strict_add(rhs_width);

        if lhs_capacity >= width {
            slice_mul_assign_usize(lhs, rhs);
            return;
        }

        let capacity = width.div_ceil(USIZE_BITS);

        *self = unsafe {
            Ubig::new_with_capacity(capacity, |output| {
                slice_mul_usize(lhs, rhs, output);
            })
        };
    }
}

impl ops::MulAssign<&[usize]> for Ubig {
    fn mul_assign(&mut self, rhs: &[usize]) {
        let rhs = rhs.trim_zeros();
        let Some((&rhs_first, rhs_rest)) = rhs.split_first() else {
            *self = Ubig::ZERO;
            return;
        };
        if rhs_rest.is_empty() {
            *self *= rhs_first;
            return;
        }
    
        if self.is_inline() {
            let lhs = unsafe { self.get_small_inline() };
            if lhs == 0 {
                return;
            }

            let lhs_width = lhs.bit_width() as usize;
            let rhs_width = rhs.bit_width() as usize;
            let width = lhs_width.strict_add(rhs_width);
            let capacity = width.div_ceil(USIZE_BITS);

            *self = unsafe {
                Ubig::new_with_capacity(capacity, |output| {
                    slice_mul_usize(rhs, lhs, output);
                })
            };
            return;
        }

        let lhs = unsafe { self.get_heap_slice_untrimmed() };
        let lhs_width = lhs.bit_width() as usize;
        let rhs_width = rhs.bit_width() as usize;
        let width = lhs_width.strict_add(rhs_width);
        let capacity = width.div_ceil(USIZE_BITS);

        *self = unsafe {
            Ubig::new_with_capacity(capacity, |output| {
                let output = output.write_filled(0);
                slice_add_assign_mul(lhs, rhs, output);
            })
        };
    }
}

impl ops::MulAssign<&Ubig> for Ubig {
    fn mul_assign(&mut self, rhs: &Ubig) {
        if rhs.is_inline() {
            let rhs = unsafe { rhs.get_small_inline() };
            *self *= rhs;
            return;
        }

        let rhs = unsafe { rhs.get_heap_slice_untrimmed() };
        *self *= rhs;
    }
}

impl ops::MulAssign<Ubig> for Ubig {
    fn mul_assign(&mut self, rhs: Ubig) {
        let mut rhs = rhs;
        let lhs = self;
        let rhs = &mut rhs;

        if lhs.bit_capacity() < rhs.bit_capacity() {
            mem::swap(lhs, rhs);
        }

        *lhs *= &*rhs;
    }
}

impl ops::Mul<usize> for Ubig {
    type Output = Ubig;

    fn mul(mut self, rhs: usize) -> Ubig {
        self *= rhs;
        self
    }
}

impl ops::Mul<&[usize]> for Ubig {
    type Output = Ubig;

    fn mul(mut self, rhs: &[usize]) -> Ubig {
        self *= rhs;
        self
    }
}

impl ops::Mul<&Ubig> for Ubig {
    type Output = Ubig;

    fn mul(mut self, rhs: &Ubig) -> Ubig {
        self *= rhs;
        self
    }
}

impl ops::Mul<Ubig> for Ubig {
    type Output = Ubig;

    fn mul(mut self, rhs: Ubig) -> Ubig {
        self *= rhs;
        self
    }
}

impl ops::Mul<usize> for &Ubig {
    type Output = Ubig;

    fn mul(self, rhs: usize) -> Ubig {
        if self.is_inline() {
            let lhs = unsafe { self.get_small_inline() };
            let (lo, hi) = lhs.carrying_mul(rhs, 0);
            return Ubig::from_usize_slice(&[lo, hi]);
        }

        if rhs == 0 {
            return Ubig::ZERO;
        }

        let lhs = unsafe { self.get_heap_slice_trimmed() };
        let lhs_width = lhs.bit_width();
        let rhs_width = rhs.bit_width() as usize;
        let width = lhs_width.strict_add(rhs_width);
        let capacity = width.div_ceil(USIZE_BITS);

        unsafe {
            Ubig::new_with_capacity(capacity, |output| {
                slice_mul_usize(lhs, rhs, output);
            })
        }
    }
}

impl ops::Mul<&[usize]> for &Ubig {
    type Output = Ubig;

    fn mul(self, rhs: &[usize]) -> Ubig {
        let rhs = rhs.trim_zeros();
        let Some((&rhs_first, rhs_rest)) = rhs.split_first() else {
            return Ubig::ZERO;
        };
        if rhs_rest.is_empty() {
            return self * rhs_first;
        }

        if self.is_inline() {
            let lhs = unsafe { self.get_small_inline() };
            if lhs == 0 {
                return Ubig::ZERO;
            }

            let lhs_width = lhs.bit_width() as usize;
            let rhs_width = rhs.bit_width();
            let width = lhs_width.strict_add(rhs_width);
            let capacity = width.div_ceil(USIZE_BITS);

            return unsafe {
                Ubig::new_with_capacity(capacity, |output| {
                    slice_mul_usize(rhs, lhs, output);
                })
            };
        }

        let lhs = unsafe { self.get_heap_slice_trimmed() };
        let lhs_width = lhs.bit_width();
        let rhs_width = rhs.bit_width() as usize;
        let width = lhs_width.strict_add(rhs_width);
        let capacity = width.div_ceil(USIZE_BITS);

        unsafe {
            Ubig::new_with_capacity(capacity, |output| {
                let output = output.write_filled(0);
                slice_add_assign_mul(lhs, rhs, output);
            })
        }
    }
}

impl ops::Mul<&Ubig> for &Ubig {
    type Output = Ubig;

    fn mul(self, rhs: &Ubig) -> Ubig {
        if rhs.is_inline() {
            let rhs = unsafe { rhs.get_small_inline() };
            return self * rhs;
        }

        let rhs = unsafe { rhs.get_heap_slice_untrimmed() };
        self * rhs
    }
}

impl ops::Mul<Ubig> for &Ubig {
    type Output = Ubig;

    fn mul(self, rhs: Ubig) -> Ubig {
        rhs * self
    }
}

impl ops::Mul<Ubig> for usize {
    type Output = Ubig;

    fn mul(self, rhs: Ubig) -> Ubig {
        rhs * self
    }
}

impl ops::Mul<Ubig> for &[usize] {
    type Output = Ubig;

    fn mul(self, rhs: Ubig) -> Ubig {
        rhs * self
    }
}

impl ops::Mul<&Ubig> for usize {
    type Output = Ubig;

    fn mul(self, rhs: &Ubig) -> Ubig {
        rhs * self
    }
}

impl ops::Mul<&Ubig> for &[usize] {
    type Output = Ubig;

    fn mul(self, rhs: &Ubig) -> Ubig {
        rhs * self
    }
}

