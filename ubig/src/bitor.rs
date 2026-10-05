use crate::priv_prelude::*;

impl ops::BitOrAssign<usize> for Ubig {
    fn bitor_assign(&mut self, rhs: usize) {
        if self.is_inline() {
            let lhs = unsafe { self.get_small_inline() };
            let word = lhs | rhs;
            *self = Ubig::from_usize(word);
            return;
        }

        let word = unsafe {
            let slice = self.get_heap_slice_mut();
            slice.first_mut().unwrap_unchecked()
        };
        *word |= rhs;
    }
}

impl ops::BitOrAssign<&[usize]> for Ubig {
    fn bitor_assign(&mut self, rhs: &[usize]) {
        let rhs = rhs.trim_zeros();
        if self.is_inline() {
            let small_inline = unsafe { self.get_small_inline() };
            let Some((&first, rest)) = rhs.split_first() else {
                return;
            };
            if rest.is_empty() {
                *self = Ubig::from_usize(small_inline | first);
            } else {
                *self = unsafe {
                    Ubig::new_with_capacity(rhs.len(), |output| {
                        output.get_unchecked_mut(0).write(small_inline | first);
                        for index in 1..rhs.len() {
                            let word = *rhs.get_unchecked(index);
                            output.get_unchecked_mut(index).write(word);
                        }
                    })
                };
            }
        } else {
            let lhs = unsafe { self.get_heap_slice_mut() };
            if lhs.len() < rhs.len() {
                *self = unsafe {
                    Ubig::new_with_capacity(rhs.len(), |output| {
                        for index in 0..lhs.len() {
                            let lhs_word = *lhs.get_unchecked(index);
                            let rhs_word = *rhs.get_unchecked(index);
                            output.get_unchecked_mut(index).write(lhs_word | rhs_word);
                        }
                        for index in lhs.len()..rhs.len() {
                            let word = *rhs.get_unchecked(index);
                            output.get_unchecked_mut(index).write(word);
                        }
                    })
                };
            } else {
                for index in 0..rhs.len() {
                    let lhs_word = unsafe { lhs.get_unchecked_mut(index) };
                    let rhs_word = unsafe { *rhs.get_unchecked(index) };
                    *lhs_word |= rhs_word;
                }
            }
        }
    }
}

impl ops::BitOrAssign<&Ubig> for Ubig {
    fn bitor_assign(&mut self, rhs: &Ubig) {
        *self |= rhs.as_usize_slice()
    }
}

impl ops::BitOrAssign<Ubig> for Ubig {
    fn bitor_assign(&mut self, rhs: Ubig) {
        let mut rhs = rhs;
        let lhs = self;
        let rhs = &mut rhs;

        if lhs.bit_capacity() < rhs.bit_capacity() {
            mem::swap(lhs, rhs);
        }

        *lhs |= &*rhs;
    }
}

impl ops::BitOr<usize> for Ubig {
    type Output = Ubig;

    fn bitor(mut self, rhs: usize) -> Ubig {
        self |= rhs;
        self
    }
}

impl ops::BitOr<&[usize]> for Ubig {
    type Output = Ubig;

    fn bitor(mut self, rhs: &[usize]) -> Ubig {
        self |= rhs;
        self
    }
}

impl ops::BitOr<&Ubig> for Ubig {
    type Output = Ubig;

    fn bitor(mut self, rhs: &Ubig) -> Ubig {
        self |= rhs;
        self
    }
}

impl ops::BitOr<Ubig> for Ubig {
    type Output = Ubig;

    fn bitor(mut self, rhs: Ubig) -> Ubig {
        self |= rhs;
        self
    }
}

impl ops::BitOr<usize> for &Ubig {
    type Output = Ubig;

    fn bitor(self, rhs: usize) -> Ubig {
        if self.is_inline() {
            let lhs = unsafe { self.get_small_inline() };
            let word = lhs | rhs;
            return Ubig::from_usize(word);
        }

        let slice = unsafe { self.get_heap_slice_trimmed() };

        unsafe {
            Ubig::new_with_capacity(slice.len(), |output| {
                let output = output.write_copy_of_slice(slice);
                *output.get_unchecked_mut(0) |= rhs;
            })
        }
    }
}

impl ops::BitOr<&[usize]> for &Ubig {
    type Output = Ubig;

    fn bitor(self, rhs: &[usize]) -> Ubig {
        let rhs = rhs.trim_zeros();

        if self.is_inline() {
            let lhs = unsafe { self.get_small_inline() };

            let Some((&rhs_first, rhs_rest)) = rhs.split_first() else {
                return unsafe { Ubig::from_small_usize_unchecked(lhs) };
            };
            if rhs_rest.is_empty() {
                let word = lhs | rhs_first;
                return Ubig::from_usize(word);
            }

            return unsafe {
                Ubig::new_with_capacity(rhs.len(), |output| {
                    let output = output.write_copy_of_slice(rhs);
                    *output.get_unchecked_mut(0) |= lhs;
                })
            };
        }

        let lhs = unsafe { self.get_heap_slice_trimmed() };
        let capacity = cmp::max(lhs.len(), rhs.len());

        unsafe {
            Ubig::new_with_capacity(capacity, |output| {
                for (index, output_word) in output.iter_mut().enumerate() {
                    let lhs_word = lhs.get(index).copied().unwrap_or(0);
                    let rhs_word = rhs.get(index).copied().unwrap_or(0);
                    output_word.write(lhs_word | rhs_word);
                }
            })
        }
    }
}

impl ops::BitOr<&Ubig> for &Ubig {
    type Output = Ubig;

    fn bitor(self, rhs: &Ubig) -> Ubig {
        if self.is_inline() {
            let lhs = unsafe { self.get_small_inline() };
            return rhs | lhs;
        }

        let lhs = unsafe { self.get_heap_slice_untrimmed() };
        rhs | lhs
    }
}

impl ops::BitOr<Ubig> for &Ubig {
    type Output = Ubig;

    fn bitor(self, rhs: Ubig) -> Ubig {
        rhs | self
    }
}

impl ops::BitOr<Ubig> for usize {
    type Output = Ubig;

    fn bitor(self, rhs: Ubig) -> Ubig {
        rhs | self
    }
}

impl ops::BitOr<Ubig> for &[usize] {
    type Output = Ubig;

    fn bitor(self, rhs: Ubig) -> Ubig {
        rhs | self
    }
}

impl ops::BitOr<&Ubig> for usize {
    type Output = Ubig;

    fn bitor(self, rhs: &Ubig) -> Ubig {
        rhs | self
    }
}

impl ops::BitOr<&Ubig> for &[usize] {
    type Output = Ubig;

    fn bitor(self, rhs: &Ubig) -> Ubig {
        rhs | self
    }
}

