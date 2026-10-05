use crate::priv_prelude::*;

#[expect(unused)]
pub(crate) fn slice_shl_assign(lhs: &mut [usize], rhs: usize) {
    let rhs_words = rhs / USIZE_BITS;
    let rhs_bits = (rhs % USIZE_BITS) as u32;

    if rhs_words >= lhs.len() {
        lhs.fill(0);
        return;
    }

    if rhs_bits == 0 {
        let copy_len = unsafe { lhs.len().unchecked_sub(rhs_words) };
        lhs.copy_within(..copy_len, rhs_words);
        lhs[..rhs_words].fill(0);
        return;
    }

    let mut write_index = unsafe { lhs.len().unchecked_sub(1) };
    let mut read_index = unsafe { write_index.unchecked_sub(rhs_words) };
    let mut hi = unsafe { *lhs.get_unchecked(read_index) };
    
    loop {
        let Some(next_read_index) = read_index.checked_sub(1) else {
            unsafe {
                let word = hi.unchecked_shl(rhs_bits);
                *lhs.get_unchecked_mut(write_index) = word;
                write_index = write_index.unchecked_sub(1);
                lhs.get_unchecked_mut(..write_index).fill(0);
            };
            return;
        };
        unsafe {
            let lo = *lhs.get_unchecked(next_read_index);
            let word = hi.unchecked_funnel_shl(lo, rhs_bits);
            *lhs.get_unchecked_mut(write_index) = word;
            write_index = write_index.unchecked_sub(1);
            hi = lo;
        }
        read_index = next_read_index;
    }
}

/*
#[expect(unused)]
pub(crate) fn slice_shl(lhs: &[usize], rhs: usize, output: &mut [MaybeUninit<usize>]) {
    let rhs_words = rhs / USIZE_BITS;
    let rhs_bits = rhs % USIZE_BITS;

    if rhs_words >= output.len() {
        output.write_filled(0);
        return;
    }

    if let Some(zeroed_start) = output.len().checked_sub(rhs_words.strict_add(lhs.len())) {
        unsafe {
            output.get_unchecked_mut(zeroed_start..).write_filled(0);
        }
    }

    if rhs_bits == 0 {
        let read_len = unsafe { lhs.len().unchecked_sub(rhs_words) };
        let write_len = :qa
    }

}
*/

