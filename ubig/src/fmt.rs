use crate::priv_prelude::*;

impl fmt::Debug for Ubig {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

#[inline]
fn generic_fmt<const DIGIT_BASE: usize>(
    f: &mut fmt::Formatter,
    ubig: &Ubig,
    alt_prefix: &'static str,
    inline: impl Fn(&mut fmt::Formatter, usize) -> fmt::Result,
    write: impl Fn(&mut fmt::Formatter, usize) -> fmt::Result,
    write_zero_padded: impl Fn(&mut fmt::Formatter, usize, usize) -> fmt::Result,
) -> fmt::Result {
    if ubig.is_inline() {
        let small_inline = unsafe { ubig.get_small_inline() };
        return inline(f, small_inline);
    }

    let slice = unsafe { ubig.get_heap_slice_trimmed() };
    let bit_width = slice.bit_width();

    let digits_per_chunk = usize::MAX.ilog(DIGIT_BASE);
    let chunk_base = NonZeroUsize::new(DIGIT_BASE.pow(digits_per_chunk)).unwrap();
    let relative_length_m256: usize = 256usize.div_ceil(chunk_base.get().ilog2() as usize);

    let mut chunks = Vec::with_capacity(bit_width.strict_mul(relative_length_m256) / 256);
    let mut buffer = slice.to_vec();
    let mut buffer: &mut [usize] = &mut *buffer;

    while !buffer.is_empty() {
        let chunk = crate::div::div_assign_slice_usize(buffer, chunk_base);
        chunks.push(chunk);
        unsafe {
            if buffer.last().copied().unwrap_unchecked() == 0 {
                buffer = buffer.get_unchecked_mut(..buffer.len().unchecked_sub(1));
            }
        }
    }

    let rendered_width = unsafe {
        let (&last, rest) = chunks.split_last().unwrap_unchecked();
        1usize
        .unchecked_add(last.checked_ilog(DIGIT_BASE).unwrap_unchecked() as usize)
        .unchecked_add(rest.len().unchecked_mul(digits_per_chunk as usize))
        .unchecked_add(f.sign_plus() as usize)
        .unchecked_add(f.alternate() as usize * alt_prefix.len())
    };

    let spare_width = {
        f
        .width()
        .and_then(|width| width.checked_sub(rendered_width))
        .unwrap_or(0)
    };

    let right_pad_fill_opt = if f.sign_aware_zero_pad() {
        if f.sign_plus() {
            f.write_str("+")?;
        }
        if f.alternate() {
            f.write_str(alt_prefix)?;
        }
        repeat_char(f, '0', spare_width)?;
        None
    } else {
        let (left_pad, right_pad) = match f.width() {
            None => (0, 0),
            Some(width) => {
                let spare_width = width.saturating_sub(rendered_width);
                match f.align() {
                    None | Some(fmt::Alignment::Left) => (0, spare_width),
                    Some(fmt::Alignment::Center) => (spare_width / 2, spare_width.div_ceil(2)),
                    Some(fmt::Alignment::Right) => (spare_width, 0),
                }
            },
        };
        let fill = f.fill();
        repeat_char(f, fill, left_pad)?;
        if f.sign_plus() {
            f.write_str("+")?;
        }
        if f.alternate() {
            f.write_str(alt_prefix)?;
        }
        Some((right_pad, fill))
    };

    let (&last, rest) = unsafe { chunks.split_last().unwrap_unchecked() };
    write(f, last)?;
    for chunk in rest.iter().copied().rev() {
        write_zero_padded(f, chunk, digits_per_chunk as usize)?;
    }

    if let Some((right_pad, fill)) = right_pad_fill_opt {
        repeat_char(f, fill, right_pad)?;
    }

    Ok(())
}

impl fmt::Display for Ubig {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        generic_fmt::<10>(
            f,
            self,
            "",
            |f, chunk| fmt::Display::fmt(&chunk, f),
            |f, chunk| write!(f, "{}", chunk),
            |f, chunk, width| write!(f, "{:0width$}", chunk),
        )
    }
}

impl fmt::LowerHex for Ubig {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        generic_fmt::<16>(
            f,
            self,
            "0x",
            |f, chunk| fmt::LowerHex::fmt(&chunk, f),
            |f, chunk| write!(f, "{:x}", chunk),
            |f, chunk, width| write!(f, "{:0width$x}", chunk),
        )
    }
}

impl fmt::UpperHex for Ubig {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        generic_fmt::<16>(
            f,
            self,
            "0X",
            |f, chunk| fmt::UpperHex::fmt(&chunk, f),
            |f, chunk| write!(f, "{:X}", chunk),
            |f, chunk, width| write!(f, "{:0width$X}", chunk),
        )
    }
}

impl fmt::Binary for Ubig {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        generic_fmt::<2>(
            f,
            self,
            "0b",
            |f, chunk| fmt::Binary::fmt(&chunk, f),
            |f, chunk| write!(f, "{:b}", chunk),
            |f, chunk, width| write!(f, "{:0width$b}", chunk),
        )
    }
}

impl fmt::Octal for Ubig {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        generic_fmt::<8>(
            f,
            self,
            "0o",
            |f, chunk| fmt::Octal::fmt(&chunk, f),
            |f, chunk| write!(f, "{:o}", chunk),
            |f, chunk, width| write!(f, "{:0width$o}", chunk),
        )
    }
}

fn repeat_char(f: &mut fmt::Formatter, c: char, n: usize) -> fmt::Result {
    for _ in 0..n {
        write!(f, "{}", c)?;
    }
    Ok(())
}

#[cfg(test)]
mod test {
    use crate::priv_prelude::*;
    use std::fmt::Write;

    #[test]
    fn test_fmt() {
        fn generic_test(
            base: usize,
            write_usize: impl Fn(&mut String, usize),
            write_ubig: impl Fn(&mut String, &Ubig),
        ) {
            let mut rng = Xoshiro256PlusPlus::seed_from_u64(0);
            for num_chunks in 1..20 {
                let mut total = Ubig::ZERO;
                let mut multiplier = Ubig::ONE;
                let mut chunks = Vec::with_capacity(num_chunks);
                for _ in 0..num_chunks {
                    let chunk: usize = crate::test::random_usize(&mut rng);
                    chunks.push(chunk);
                    let num_digits = chunk.checked_ilog(base).unwrap_or(0);
                    total += chunk * &multiplier;
                    multiplier *= base.pow(num_digits);
                    multiplier *= base;
                }

                let mut fmt_chunks = String::new();
                for chunk in chunks.iter().copied().rev() {
                    write_usize(&mut fmt_chunks, chunk);
                }
                let mut fmt_ubig = String::new();
                write_ubig(&mut fmt_ubig, &total);

                assert_eq!(fmt_ubig, fmt_chunks);
            }
        }

        generic_test(
            10,
            |s, val| write!(s, "{}", val).unwrap(),
            |s, val| write!(s, "{}", val).unwrap(),
        );
        generic_test(
            16,
            |s, val| write!(s, "{:x}", val).unwrap(),
            |s, val| write!(s, "{:x}", val).unwrap(),
        );
        generic_test(
            16,
            |s, val| write!(s, "{:X}", val).unwrap(),
            |s, val| write!(s, "{:X}", val).unwrap(),
        );
        generic_test(
            2,
            |s, val| write!(s, "{:b}", val).unwrap(),
            |s, val| write!(s, "{:b}", val).unwrap(),
        );
        generic_test(
            8,
            |s, val| write!(s, "{:o}", val).unwrap(),
            |s, val| write!(s, "{:o}", val).unwrap(),
        );
    }
}

