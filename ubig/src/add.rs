use crate::priv_prelude::*;

fn add_slice_slice(
    lhs: &[usize],
    rhs: &[usize],
    output: &mut [MaybeUninit<usize>],
) {
    let mut carry = false;
    for (index, output_word) in output.iter_mut().enumerate() {
        let lhs_word = lhs.get(index).copied().unwrap_or(0);
        let rhs_word = rhs.get(index).copied().unwrap_or(0);
        let (word, next_carry) = lhs_word.carrying_add(rhs_word, carry);
        output_word.write(word);
        carry = next_carry;
    }
}

fn add_slice_usize(
    lhs: &[usize],
    rhs: usize,
    output: &mut [MaybeUninit<usize>],
) {
    let mut rhs = rhs;
    for (index, output_word) in output.iter_mut().enumerate() {
        let lhs_word = lhs.get(index).copied().unwrap_or(0);
        let (word, next_rhs) = lhs_word.overflowing_add(rhs);
        output_word.write(word);
        rhs = next_rhs as usize;
    }
}

fn add_assign_slice_slice<'r>(
    lhs: &mut [usize],
    rhs: &'r [usize],
) -> (&'r [usize], bool) {
    let mut carry = false;
    for (index, lhs_word) in lhs.iter_mut().enumerate() {
        let rhs_word = match rhs.get(index).copied() {
            None => {
                if carry { 0 } else { return (&[], false) }
            },
            Some(rhs_word) => rhs_word,
        };
        let (word, next_carry) = lhs_word.carrying_add(rhs_word, carry);
        *lhs_word = word;
        carry = next_carry;
    }
    let slice = rhs.get(lhs.len()..).unwrap_or(&[]);
    (slice, carry)
}

pub(crate) fn add_assign_slice_usize(
    lhs: &mut [usize],
    rhs: usize,
) -> usize {
    let mut rhs = rhs;
    for lhs_word in lhs.iter_mut() {
        if rhs == 0 {
            return 0;
        }
        let (word, next_rhs) = lhs_word.overflowing_add(rhs);
        *lhs_word = word;
        rhs = next_rhs as usize;
    }
    rhs
}


impl ops::AddAssign<usize> for Ubig {
    fn add_assign(&mut self, rhs: usize) {
        if self.is_inline() {
            let lhs = unsafe { self.get_small_inline() };
            let (word, overflow) = lhs.overflowing_add(rhs);
            *self = Ubig::from_usize_slice(&[word, overflow as usize]);
            return;
        }

        let lhs = unsafe { self.get_heap_slice_mut() };
        let carry = add_assign_slice_usize(lhs, rhs);
        if carry == 0 {
            return;
        }

        *self = unsafe {
            Ubig::new_with_capacity(lhs.len().strict_add(1), |output| {
                output.get_unchecked_mut(..lhs.len()).write_copy_of_slice(lhs);
                output.get_unchecked_mut(lhs.len()).write(carry);
            })
        };
    }
}

impl ops::AddAssign<&[usize]> for Ubig {
    fn add_assign(&mut self, rhs: &[usize]) {
        let rhs = rhs.trim_zeros();

        if self.is_inline() {
            let lhs = unsafe { self.get_small_inline() };

            let lhs_width = lhs.bit_width() as usize;
            let rhs_width = rhs.bit_width();
            let width = cmp::max(lhs_width, rhs_width).strict_add(1);
            if width <= USIZE_BITS {
                let rhs = rhs.first().copied().unwrap_or(0);
                let word = unsafe { lhs.unchecked_add(rhs) };
                *self = Ubig::from_usize(word);
                return;
            }

            let capacity = width.div_ceil(USIZE_BITS);
            *self = unsafe {
                Ubig::new_with_capacity(capacity, |output| {
                    let mut lhs = lhs;
                    for (index, output_word) in output.iter_mut().enumerate() {
                        let rhs = rhs.get(index).copied().unwrap_or(0);
                        let (word, next_lhs) = lhs.overflowing_add(rhs);
                        output_word.write(word);
                        lhs = next_lhs as usize;
                    }
                })
            };
            return;
        }

        let lhs = unsafe { self.get_heap_slice_mut() };

        let (remaining, carry) = add_assign_slice_slice(lhs, rhs);
        if remaining.is_empty() && !carry {
            return;
        }

        let will_overflow_again = carry && {
            remaining.iter().copied().all(|word| word == usize::MAX)
        };
        let max_len = cmp::max(lhs.len(), rhs.len());
        let capacity = max_len + will_overflow_again as usize;

        *self = unsafe {
            Ubig::new_with_capacity(capacity, |output| {
                output.get_unchecked_mut(..lhs.len()).write_copy_of_slice(lhs);
                let remaining = {
                    output
                    .get_unchecked_mut(lhs.len()..)
                    .get_unchecked_mut(..remaining.len())
                    .write_copy_of_slice(remaining)
                };
                let overflow = add_assign_slice_usize(remaining, carry as usize);
                if overflow != 0 {
                    output.get_unchecked_mut(max_len).write(overflow);
                }
            })
        };
    }
}

impl ops::AddAssign<&Ubig> for Ubig {
    fn add_assign(&mut self, rhs: &Ubig) {
        *self += rhs.as_usize_slice_untrimmed();
    }
}

impl ops::AddAssign<Ubig> for Ubig {
    fn add_assign(&mut self, rhs: Ubig) {
        let mut rhs = rhs;
        let lhs = self;
        let rhs = &mut rhs;

        if lhs.bit_capacity() < rhs.bit_capacity() {
            mem::swap(lhs, rhs);
        }

        *lhs += &*rhs;
    }
}

impl ops::Add<usize> for Ubig {
    type Output = Ubig;

    fn add(mut self, rhs: usize) -> Ubig {
        self += rhs;
        self
    }
}

impl ops::Add<Ubig> for usize {
    type Output = Ubig;

    fn add(self, rhs: Ubig) -> Ubig {
        rhs + self
    }
}

impl ops::Add<&[usize]> for Ubig {
    type Output = Ubig;

    fn add(mut self, rhs: &[usize]) -> Ubig {
        self += rhs;
        self
    }
}

impl ops::Add<Ubig> for &[usize] {
    type Output = Ubig;

    fn add(self, rhs: Ubig) -> Ubig {
        rhs + self
    }
}

impl ops::Add<&Ubig> for Ubig {
    type Output = Ubig;

    fn add(mut self, rhs: &Ubig) -> Ubig {
        self += rhs;
        self
    }
}

impl ops::Add<Ubig> for Ubig {
    type Output = Ubig;

    fn add(mut self, rhs: Ubig) -> Ubig {
        self += rhs;
        self
    }
}

impl ops::Add<usize> for &Ubig {
    type Output = Ubig;

    fn add(self, rhs: usize) -> Ubig {
        let lhs = self.as_usize_slice();

        let lhs_width = lhs.bit_width();
        let rhs_width = rhs.bit_width() as usize;
        let required_width = cmp::max(lhs_width, rhs_width).strict_add(1);
        if required_width <= USIZE_BITS {
            let lhs_word = lhs.first().copied().unwrap_or(0);
            let word = unsafe { lhs_word.unchecked_add(rhs) };
            return Ubig::from_usize(word);
        }

        let capacity = required_width.div_ceil(USIZE_BITS);
        return unsafe {
            Ubig::new_with_capacity(capacity, |output| {
                add_slice_usize(lhs, rhs, output);
            })
        };
    }
}

impl ops::Add<&Ubig> for usize {
    type Output = Ubig;

    fn add(self, rhs: &Ubig) -> Ubig {
        rhs + self
    }
}

impl ops::Add<&[usize]> for &Ubig {
    type Output = Ubig;

    fn add(self, rhs: &[usize]) -> Ubig {
        let lhs = self.as_usize_slice();
        let rhs = rhs.trim_zeros();

        let lhs_width = lhs.bit_width();
        let rhs_width = rhs.bit_width();
        let required_width = cmp::max(lhs_width, rhs_width).strict_add(1);
        if required_width <= USIZE_BITS {
            let lhs_word = lhs.first().copied().unwrap_or(0);
            let rhs_word = rhs.first().copied().unwrap_or(0);
            let word = unsafe { lhs_word.unchecked_add(rhs_word) };
            return Ubig::from_usize(word);
        }

        let capacity = required_width.div_ceil(USIZE_BITS);
        return unsafe {
            Ubig::new_with_capacity(capacity, |output| {
                add_slice_slice(lhs, rhs, output);
            })
        };
    }
}

impl ops::Add<&Ubig> for &[usize] {
    type Output = Ubig;

    fn add(self, rhs: &Ubig) -> Ubig {
        rhs + self
    }
}

impl ops::Add<&Ubig> for &Ubig {
    type Output = Ubig;

    fn add(self, rhs: &Ubig) -> Ubig {
        self + rhs.as_usize_slice_untrimmed()
    }
}

impl ops::Add<Ubig> for &Ubig {
    type Output = Ubig;

    fn add(self, rhs: Ubig) -> Ubig {
        rhs + self
    }
}

