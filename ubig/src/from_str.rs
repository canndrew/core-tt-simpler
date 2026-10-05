use crate::priv_prelude::*;

#[derive(Clone, Copy, Debug)]
pub struct ParseIntError {
    kind: ParseIntErrorKind,
}

#[derive(Clone, Copy, Debug)]
enum ParseIntErrorKind {
    InvalidDigit {
        position: usize,
        c: char,
    },
    Empty,
}

impl FromStr for Ubig {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Ubig, ParseIntError> {
        let mut total = Ubig::ZERO;
        let s = s.strip_prefix("+").unwrap_or(s);
        if s.is_empty() {
            return Err(ParseIntError {
                kind: ParseIntErrorKind::Empty,
            });
        }
        for (position, c) in s.chars().enumerate() {
            let Some(d) = c.to_digit(10) else {
                return Err(ParseIntError {
                    kind: ParseIntErrorKind::InvalidDigit { position, c },
                });
            };
            total *= 10;
            total += d as usize;
        }
        Ok(total)
    }
}

impl fmt::Display for ParseIntError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let ParseIntError { kind } = self;
        match kind {
            ParseIntErrorKind::InvalidDigit { position, c } => {
                write!(f, "invalid digit {:?} at position {}", c, position)
            },
            ParseIntErrorKind::Empty => {
                write!(f, "empty string cannot be parsed as an integer")
            },
        }
    }
}

impl std::error::Error for ParseIntError {}

