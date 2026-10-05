use crate::priv_prelude::*;

impl Ubig {
    pub fn checked_sub(&self, rhs: &Ubig) -> Option<Ubig> {
        if self.is_inline() {
            let lhs_inline = unsafe { self.get_small_inline() };
            if !rhs.is_inline() {
                return None;
            }
            let rhs_inline = unsafe { rhs.get_small_inline() };
            let inline = lhs_inline.checked_sub(rhs_inline)?;
            let ret = unsafe { Ubig::from_small_usize_unchecked(inline) };
            return Some(ret);
        }

        let lhs_slice = unsafe { self.get_heap_slice_trimmed() };
        let rhs_slice = rhs.as_usize_slice();
        if rhs_slice.len() > lhs_slice.len() {
            return None;
        }

        let required_words = {
            let mut required_words = 0;
            let mut borrow = false;
            let mut index = 0;
            while let Some(rhs_word) = rhs_slice.get(index).copied() {
                let lhs_word = unsafe { *lhs_slice.get_unchecked(index) };
                let (word, next_borrow) = lhs_word.borrowing_sub(rhs_word, borrow);
                borrow = next_borrow;
                index += 1;
                if word != 0 {
                    required_words = index;
                }
            }
            let remaining_lhs_slice = unsafe { lhs_slice.get_unchecked(rhs_slice.len()..) };
            match remaining_lhs_slice.split_last() {
                None => {
                    if borrow {
                        return None;
                    }
                    required_words
                },
                Some((&last, middle)) => {
                    if borrow && last == 1 && middle.iter().all(|word| *word == 0) {
                        unsafe { lhs_slice.len().unchecked_sub(1) }
                    } else {
                        lhs_slice.len()
                    }
                },
            }
        };

        if required_words <= 1 {
            let lhs_word = unsafe { *lhs_slice.get_unchecked(0) };
            let Some(rhs_word) = rhs_slice.first().copied() else {
                let ret = unsafe {
                    Ubig::new_with_capacity(1, |output| {
                        output.get_unchecked_mut(0).write(lhs_word);
                    })
                };
                return Some(ret);
            };
            let word = lhs_word.wrapping_sub(rhs_word);
            return Some(Ubig::from_usize(word));
        }

        let ret = unsafe {
            Ubig::new_with_capacity(required_words, |output| {
                let mut borrow = false;
                let mut index = 0;
                loop {
                    let Some(output_word) = output.get_mut(index) else {
                        return;
                    };
                    let Some(rhs_word) = rhs_slice.get(index).copied() else {
                        break;
                    };
                    let lhs_word = *lhs_slice.get_unchecked(index);
                    index += 1;
                    let (word, next_borrow) = lhs_word.borrowing_sub(rhs_word, borrow);
                    borrow = next_borrow;
                    output_word.write(word);
                }
                while borrow {
                    let Some(output_word) = output.get_mut(index) else {
                        return;
                    };
                    let lhs_word = *lhs_slice.get_unchecked(index);
                    index += 1;
                    let (word, next_borrow) = lhs_word.overflowing_sub(1);
                    borrow = next_borrow;
                    output_word.write(word);
                }
                while let Some(output_word) = output.get_mut(index) {
                    let lhs_word = *lhs_slice.get_unchecked(index);
                    index += 1;
                    output_word.write(lhs_word);
                }
            })
        };
        Some(ret)
    }

    #[track_caller]
    pub fn strict_sub(&self, rhs: &Ubig) -> Ubig {
        match self.checked_sub(rhs) {
            Some(ret) => ret,
            None => panic!("Ubig::strict_sub(): attempt to subtract with overflow"),
        }
    }

    pub unsafe fn unchecked_sub(&self, rhs: &Ubig) -> Ubig {
        unsafe {
            self.checked_sub(rhs).unwrap_unchecked()
        }
    }
}

