pub(crate) fn pext_fallback(val: usize, mask: usize) -> usize {
    let mut val = val;
    let mut mask = mask;
    let mut ret = 0;
    let mut write_position = 0;
    for _ in 0..usize::BITS {
        if mask & 1 == 1 {
            ret |= (val & 1) << write_position;
            write_position += 1;
        }
        mask >>= 1;
        val >>= 1;
    }
    ret
}

pub(crate) fn pdep_fallback(val: usize, mask: usize) -> usize {
    let mut ret = 0;
    let mut val = val;
    let mut mask = mask;
    for position in 0..usize::BITS {
        if mask & 1 == 1 {
            ret |= (val & 1) << position;
            val >>= 1;
        }
        mask >>= 1;
    }
    ret
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "bmi2")]
pub(crate) unsafe fn pext_x86_64(val: u64, mask: u64) -> u64 {
    std::arch::x86_64::_pext_u64(val, mask)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "bmi2")]
pub(crate) unsafe fn pdep_x86_64(val: u64, mask: u64) -> u64 {
    std::arch::x86_64::_pdep_u64(val, mask)
}

#[cfg(target_arch = "x86_64")]
pub fn pext(val: usize, mask: usize) -> usize {
    if std::arch::is_x86_feature_detected!("bmi2") {
        unsafe { pext_x86_64(val as u64, mask as u64) as usize }
    } else {
        pext_fallback(val, mask)
    }
}

#[cfg(target_arch = "x86_64")]
pub fn pdep(val: usize, mask: usize) -> usize {
    if std::arch::is_x86_feature_detected!("bmi2") {
        unsafe { pdep_x86_64(val as u64, mask as u64) as usize }
    } else {
        pdep_fallback(val, mask)
    }
}

#[cfg(not(target_arch = "x86_64"))]
pub fn pext(val: usize, mask: usize) -> usize {
    pext_fallback(val, mask)
}

#[expect(unused)]
#[cfg(not(target_arch = "x86_64"))]
pub fn pdep(val: usize, mask: usize) -> usize {
    pdep_fallback(val, mask)
}

