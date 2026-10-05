use crate::priv_prelude::*;

impl From<usize> for Ubig {
    fn from(val: usize) -> Ubig {
        Ubig::from_usize(val)
    }
}

cfg_select! {
    target_pointer_width = "16" => {
        impl From<u32> for Ubig {
            fn from(val: u32) -> Ubig {
                let v0 = (val & (usize::MAX as u32)) as usize;
                let v1 = (val >> 16) as usize;
                Ubig::from_usize_slice(&[v0, v1])
            }
        }

        impl From<u64> for Ubig {
            fn from(val: u64) -> Ubig {
                let v0 = (val & (usize::MAX as u64)) as usize;
                let v1 = ((val >> 16) & (usize::MAX as u64)) as usize;
                let v2 = ((val >> 32) & (usize::MAX as u64)) as usize;
                let v3 = (val >> 48) as usize;
                Ubig::from_usize_slice(&[v0, v1, v2, v3])
            }
        }

        impl From<u128> for Ubig {
            fn from(val: u64) -> Ubig {
                let v0 = (val & (usize::MAX as u128)) as usize;
                let v1 = ((val >> 16) & (usize::MAX as u128)) as usize;
                let v2 = ((val >> 32) & (usize::MAX as u128)) as usize;
                let v3 = ((val >> 48) & (usize::MAX as u128)) as usize;
                let v4 = ((val >> 64) & (usize::MAX as u128)) as usize;
                let v5 = ((val >> 80) & (usize::MAX as u128)) as usize;
                let v6 = ((val >> 96) & (usize::MAX as u128)) as usize;
                let v7 = ((val >> 112) & (usize::MAX as u128)) as usize;
                Ubig::from_usize_slice(&[v0, v1, v2, v3, v4, v5, v6, v7])
            }
        }

        impl<'a> TryInto<u32> for &'a Ubig {
            type Error = &'a Ubig;

            fn try_into(self) -> Result<u32, &'a Ubig> {
                let val = if self.is_inline() {
                    let val = unsafe { self.get_small_inline() };
                    val as u32
                } else {
                    let slice = unsafe { self.get_heap_slice_trimmed() };

                    if let Some(high_words) = slice.get(2..)
                    && !high_words.is_empty()
                    {
                        return Err(self);
                    }

                    let v0 = slice.get(0).copied().unwrap_or(0) as u32;
                    let v1 = slice.get(1).copied().unwrap_or(0) as u32;
                    (v1 << 16) | v0
                };
                Ok(val)
            }
        }

        impl<'a> TryInto<u64> for &'a Ubig {
            type Error = &'a Ubig;

            fn try_into(self) -> Result<u64, &'a Ubig> {
                let val = if self.is_inline() {
                    let val = unsafe { self.get_small_inline() };
                    val as u64
                } else {
                    let slice = unsafe { self.get_heap_slice_trimmed() };

                    if let Some(high_words) = slice.get(4..)
                    && !high_words.is_empty()
                    {
                        return Err(self);
                    }

                    let v0 = slice.get(0).copied().unwrap_or(0) as u64;
                    let v1 = slice.get(1).copied().unwrap_or(0) as u64;
                    let v2 = slice.get(2).copied().unwrap_or(0) as u64;
                    let v3 = slice.get(3).copied().unwrap_or(0) as u64;
                    (v3 << 48) | (v2 << 32) | (v1 << 16) | v0
                };
                Ok(val)
            }
        }

        impl<'a> TryInto<u128> for &'a Ubig {
            type Error = &'a Ubig;

            fn try_into(self) -> Result<u128, &'a Ubig> {
                let val = if self.is_inline() {
                    let val = unsafe { self.get_small_inline() };
                    val as u128
                } else {
                    let slice = unsafe { self.get_heap_slice_trimmed() };

                    if let Some(high_words) = slice.get(8..)
                    && !high_words.is_empty()
                    {
                        return Err(self);
                    }

                    let v0 = slice.get(0).copied().unwrap_or(0) as u128;
                    let v1 = slice.get(1).copied().unwrap_or(0) as u128;
                    let v2 = slice.get(2).copied().unwrap_or(0) as u128;
                    let v3 = slice.get(3).copied().unwrap_or(0) as u128;
                    let v4 = slice.get(4).copied().unwrap_or(0) as u128;
                    let v5 = slice.get(5).copied().unwrap_or(0) as u128;
                    let v6 = slice.get(6).copied().unwrap_or(0) as u128;
                    let v7 = slice.get(7).copied().unwrap_or(0) as u128;
                    (v7 << 112) |
                    (v6 << 96) |
                    (v5 << 80) |
                    (v4 << 64) |
                    (v3 << 48) |
                    (v2 << 32) |
                    (v1 << 16) |
                    v0
                };
                Ok(val)
            }
        }
    },
    target_pointer_width = "32" => {
        impl From<u32> for Ubig {
            fn from(val: u32) -> Ubig {
                Ubig::from_usize(val as usize)
            }
        }

        impl From<u64> for Ubig {
            fn from(val: u64) -> Ubig {
                let v0 = (val & (usize::MAX as u64)) as usize;
                let v1 = (val >> 32) as usize;
                Ubig::from_usize_slice(&[v0, v1])
            }
        }

        impl From<u128> for Ubig {
            fn from(val: u64) -> Ubig {
                let v0 = (val & (usize::MAX as u128)) as usize;
                let v1 = ((val >> 32) & (usize::MAX as u128)) as usize;
                let v2 = ((val >> 64) & (usize::MAX as u128)) as usize;
                let v3 = (val >> 96) as usize;
                Ubig::from_usize_slice(&[v0, v1, v2, v3])
            }
        }

        impl<'a> TryInto<u32> for &'a Ubig {
            type Error = &'a Ubig;

            fn try_into(self) -> Result<u32, &'a Ubig> {
                let val: usize = self.try_into()?;
                Ok(val as usize)
            }
        }

        impl<'a> TryInto<u64> for &'a Ubig {
            type Error = &'a Ubig;

            fn try_into(self) -> Result<u64, &'a Ubig> {
                let val = if self.is_inline() {
                    let val = unsafe { self.get_small_inline() };
                    val as u64
                } else {
                    let slice = unsafe { self.get_heap_slice_trimmed() };

                    if let Some(high_words) = slice.get(2..)
                    && !high_words.is_empty()
                    {
                        return Err(self);
                    }

                    let v0 = slice.get(0).copied().unwrap_or(0) as u64;
                    let v1 = slice.get(1).copied().unwrap_or(0) as u64;
                    (v1 << 32) | v0
                };
                Ok(val)
            }
        }

        impl<'a> TryInto<u128> for &'a Ubig {
            type Error = &'a Ubig;

            fn try_into(self) -> Result<u128, &'a Ubig> {
                let val = if self.is_inline() {
                    let val = unsafe { self.get_small_inline() };
                    val as u128
                } else {
                    let slice = unsafe { self.get_heap_slice_trimmed() };

                    if let Some(high_words) = slice.get(4..)
                    && !high_words.is_empty()
                    {
                        return Err(self);
                    }

                    let v0 = slice.get(0).copied().unwrap_or(0) as u128;
                    let v1 = slice.get(1).copied().unwrap_or(0) as u128;
                    let v2 = slice.get(2).copied().unwrap_or(0) as u128;
                    let v3 = slice.get(3).copied().unwrap_or(0) as u128;
                    (v3 << 96) | (v2 << 64) | (v1 << 32) | v0
                };
                Ok(val)
            }
        }
    },
    target_pointer_width = "64" => {
        impl From<u32> for Ubig {
            fn from(val: u32) -> Ubig {
                Ubig::from_usize(val as usize)
            }
        }

        impl From<u64> for Ubig {
            fn from(val: u64) -> Ubig {
                Ubig::from_usize(val as usize)
            }
        }

        impl From<u128> for Ubig {
            fn from(val: u128) -> Ubig {
                let v0 = (val & (usize::MAX as u128)) as usize;
                let v1 = (val >> 64) as usize;
                Ubig::from_usize_slice(&[v0, v1])
            }
        }

        impl<'a> TryInto<u32> for &'a Ubig {
            type Error = &'a Ubig;

            fn try_into(self) -> Result<u32, &'a Ubig> {
                let val: usize = self.try_into()?;
                match val.try_into() {
                    Ok(val) => Ok(val),
                    Err(_) => Err(self),
                }
            }
        }

        impl<'a> TryInto<u64> for &'a Ubig {
            type Error = &'a Ubig;

            fn try_into(self) -> Result<u64, &'a Ubig> {
                let val: usize = self.try_into()?;
                Ok(val as u64)
            }
        }

        impl<'a> TryInto<u128> for &'a Ubig {
            type Error = &'a Ubig;

            fn try_into(self) -> Result<u128, &'a Ubig> {
                let val = if self.is_inline() {
                    let val = unsafe { self.get_small_inline() };
                    val as u128
                } else {
                    let slice = unsafe { self.get_heap_slice_trimmed() };

                    if let Some(high_words) = slice.get(2..)
                    && !high_words.is_empty()
                    {
                        return Err(self);
                    }

                    let v0 = slice.get(0).copied().unwrap_or(0) as u128;
                    let v1 = slice.get(1).copied().unwrap_or(0) as u128;
                    (v1 << 64) | v0
                };
                Ok(val)
            }
        }

        impl From<&Ubig> for f32 {
            fn from(val: &Ubig) -> f32 {
                let width = val.bit_width();
                let Some(high_index) = width.checked_sub(1) else {
                    return 0.0;
                };
                if high_index > 127 {
                    return f32::INFINITY;
                }

                const MANTISSA_SIZE: u32 = 23;
                const MANTISSA_MASK: usize = (1 << MANTISSA_SIZE) - 1;
                const EXPONENT_BIAS: u32 = 127;

                let slice = val.as_usize_slice();
                let high_word_index = high_index / USIZE_BITS;
                let high_bit_index = (high_index % USIZE_BITS) as u32;
                let word = unsafe { *slice.get_unchecked(high_word_index) };
                let shifted = if high_bit_index < MANTISSA_SIZE {
                    let shift = MANTISSA_SIZE - high_bit_index;
                    let prev_word = {
                        high_word_index
                        .checked_sub(1)
                        .map(|index| unsafe { *slice.get_unchecked(index) })
                        .unwrap_or(0)
                    };
                    unsafe {
                        word.unchecked_funnel_shl(prev_word, shift)
                    }
                } else {
                    let shift = high_bit_index - MANTISSA_SIZE;
                    unsafe {
                        word.unchecked_shr(shift)
                    }
                };
                let mantissa = (shifted & MANTISSA_MASK) as u32;

                let exponent = unsafe {
                    u32::try_from(high_index)
                    .unwrap_unchecked()
                    .unchecked_add(EXPONENT_BIAS)
                    .unchecked_shl_exact(MANTISSA_SIZE)
                };
                let bits = unsafe { mantissa.unchecked_disjoint_bitor(exponent) };
                f32::from_bits(bits)
            }
        }
    },
    _ => {
        compile_error!("unsupported target_pointer_width");
    },
}

impl From<u8> for Ubig {
    fn from(val: u8) -> Ubig {
        Ubig::from_usize(val as usize)
    }
}

impl From<u16> for Ubig {
    fn from(val: u16) -> Ubig {
        Ubig::from_usize(val as usize)
    }
}

impl<'a> TryInto<u8> for &'a Ubig {
    type Error = &'a Ubig;

    fn try_into(self) -> Result<u8, &'a Ubig> {
        let val: usize = self.try_into()?;
        let val: u8 = match val.try_into() {
            Ok(val) => val,
            Err(_) => return Err(self),
        };
        Ok(val)
    }
}

impl<'a> TryInto<u16> for &'a Ubig {
    type Error = &'a Ubig;

    fn try_into(self) -> Result<u16, &'a Ubig> {
        let val: usize = self.try_into()?;
        let val: u16 = match val.try_into() {
            Ok(val) => val,
            Err(_) => return Err(self),
        };
        Ok(val)
    }
}

impl<'a> TryInto<usize> for &'a Ubig {
    type Error = &'a Ubig;

    fn try_into(self) -> Result<usize, &'a Ubig> {
        if self.is_inline() {
            let small_inline = unsafe { self.get_small_inline() };
            return Ok(small_inline);
        }

        let slice = unsafe { self.get_heap_slice_trimmed() };
        match slice.split_first() {
            None => Ok(0),
            Some((first, rest)) => {
                if rest.is_empty() {
                    Ok(*first)
                } else {
                    Err(self)
                }
            },
        }
    }
}

macro_rules! impl_owned_try_into {
    ($ty:ident) => {
        impl TryInto<$ty> for Ubig {
            type Error = Ubig;

            fn try_into(self) -> Result<$ty, Ubig> {
                match (&self).try_into() {
                    Ok(val) => Ok(val),
                    Err(_) => Err(self),
                }
            }
        }
    };
}

impl_owned_try_into!(u8);
impl_owned_try_into!(u16);
impl_owned_try_into!(u32);
impl_owned_try_into!(u64);
impl_owned_try_into!(u128);
impl_owned_try_into!(usize);

impl From<Ubig> for f32 {
    fn from(val: Ubig) -> f32 {
        f32::from(&val)
    }
}

#[cfg(test)]
mod test {
    use crate::priv_prelude::*;

    #[test]
    fn uint_from_into_round_trip() {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(0);
        for _ in 0..100 {
            let val_0: u8 = rng.random();
            let val_1 = Ubig::from(val_0);
            let val_2: u8 = val_1.try_into().unwrap();
            assert_eq!(val_0, val_2);
        }
        for _ in 0..100 {
            let val_0: u16 = rng.random();
            let val_1 = Ubig::from(val_0);
            let val_2: u16 = val_1.try_into().unwrap();
            assert_eq!(val_0, val_2);
        }
        for _ in 0..100 {
            let val_0: u32 = rng.random();
            let val_1 = Ubig::from(val_0);
            let val_2: u32 = val_1.try_into().unwrap();
            assert_eq!(val_0, val_2);
        }
        for _ in 0..100 {
            let val_0: u64 = rng.random();
            let val_1 = Ubig::from(val_0);
            let val_2: u64 = val_1.try_into().unwrap();
            assert_eq!(val_0, val_2);
        }
        for _ in 0..100 {
            let val_0: u128 = rng.random();
            let val_1 = Ubig::from(val_0);
            let val_2: u128 = val_1.try_into().unwrap();
            assert_eq!(val_0, val_2);
        }
    }

    #[test]
    fn uint_try_into_overflow() {
        let val_0 = u8::MAX;
        let mut val_1 = Ubig::from(val_0);
        val_1.increment();
        assert!(<Ubig as TryInto<u8>>::try_into(val_1).is_err());
        
        let val_0 = u16::MAX;
        let mut val_1 = Ubig::from(val_0);
        val_1.increment();
        assert!(<Ubig as TryInto<u16>>::try_into(val_1).is_err());

        let val_0 = u32::MAX;
        let mut val_1 = Ubig::from(val_0);
        val_1.increment();
        assert!(<Ubig as TryInto<u32>>::try_into(val_1).is_err());

        let val_0 = u64::MAX;
        let mut val_1 = Ubig::from(val_0);
        val_1.increment();
        assert!(<Ubig as TryInto<u64>>::try_into(val_1).is_err());

        let val_0 = u128::MAX;
        let mut val_1 = Ubig::from(val_0);
        val_1.increment();
        assert!(<Ubig as TryInto<u128>>::try_into(val_1).is_err());

        let val_0 = usize::MAX;
        let mut val_1 = Ubig::from(val_0);
        val_1.increment();
        assert!(<Ubig as TryInto<usize>>::try_into(val_1).is_err());
    }

    #[test]
    fn into_f32() {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(0);
        for _ in 0..100 {
            let val: u128 = rng.random();
            let shift: u8 = rng.random();
            let val_0 = val >> (shift % 128);
            let val_1 = Ubig::from(val_0);
            let val_f32_0 = val_0 as f32;
            let val_f32_1 = f32::from(val_1);
            assert!(
                val_f32_0 == val_f32_1
                || val_f32_0.next_down() == val_f32_1
                || val_f32_0.next_up() == val_f32_1
            );
        }
    }
}

