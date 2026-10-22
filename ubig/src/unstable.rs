use crate::priv_prelude::*;

pub(crate) trait UsizeUnstable {
    unsafe fn unchecked_shr_exact(self, rhs: u32) -> usize;
    #[expect(unused)]
    unsafe fn unchecked_funnel_shl(self, lo: usize, bit_index: u32) -> usize;
    #[expect(unused)]
    unsafe fn unchecked_funnel_shr(self, lo: usize, bit_index: u32) -> usize;
    unsafe fn unchecked_disjoint_bitor(self, other: usize) -> usize;
    fn extract_bits(self, mask: usize) -> usize;
    fn deposit_bits(self, mask: usize) -> usize;
}

impl UsizeUnstable for usize {
    unsafe fn unchecked_shr_exact(self, rhs: u32) -> usize {
        unsafe {
            let ret = self.unchecked_shr(rhs);
            assert_unchecked((ret << rhs) == self);
            ret
        }
    }

    unsafe fn unchecked_funnel_shl(self, lo: usize, bit_index: u32) -> usize {
        unsafe {
            let lo = lo.unbounded_shr(usize::BITS.unchecked_sub(bit_index));
            let hi = self.unchecked_shl(bit_index);
            lo.unchecked_disjoint_bitor(hi)
        }
    }

    unsafe fn unchecked_funnel_shr(self, lo: usize, bit_index: u32) -> usize {
        unsafe {
            let lo = lo.unchecked_shr(bit_index);
            let hi = self.unbounded_shl(usize::BITS.unchecked_sub(bit_index));
            lo.unchecked_disjoint_bitor(hi)
        }
    }

    unsafe fn unchecked_disjoint_bitor(self, other: usize) -> usize {
        unsafe {
            assert_unchecked(self & other == 0);
        }
        self | other
    }

    fn extract_bits(self, mask: usize) -> usize {
        crate::bmi2::pext(self, mask)
    }

    fn deposit_bits(self, mask: usize) -> usize {
        crate::bmi2::pdep(self, mask)
    }
}

pub(crate) trait U32Unstable {
    unsafe fn unchecked_shl_exact(self, rhs: u32) -> u32;
    unsafe fn unchecked_disjoint_bitor(self, other: u32) -> u32;
}

impl U32Unstable for u32 {
    unsafe fn unchecked_shl_exact(self, rhs: u32) -> u32 {
        unsafe {
            let ret = self.unchecked_shl(rhs);
            assert_unchecked((ret >> rhs) == self);
            ret
        }
    }

    unsafe fn unchecked_disjoint_bitor(self, other: u32) -> u32 {
        unsafe {
            assert_unchecked(self & other == 0);
        }
        self | other
    }
}

pub(crate) trait MaybeUninitSliceUnstable<T> {
    fn write_filled(&mut self, val: T) -> &mut [T]
    where
        T: Clone;
}

impl<T> MaybeUninitSliceUnstable<T> for [MaybeUninit<T>] {
    fn write_filled(&mut self, val: T) -> &mut [T]
    where
        T: Clone,
    {
        for output in self.iter_mut() {
            output.write(val.clone());
        }
        unsafe { self.assume_init_mut() }
    }
}

