use crate::priv_prelude::*;

impl PartialEq<Ubig> for Ubig {
    fn eq(&self, rhs: &Ubig) -> bool {
        PartialEq::eq(self.as_usize_slice(), rhs.as_usize_slice())
    }
}

impl Eq for Ubig {}

impl PartialOrd<Ubig> for Ubig {
    fn partial_cmp(&self, rhs: &Ubig) -> Option<Ordering> {
        Some(Ord::cmp(self, rhs))
    }
}

impl Ord for Ubig {
    fn cmp(&self, rhs: &Ubig) -> Ordering {
        let lhs = self.as_usize_slice();
        let rhs = rhs.as_usize_slice();
        match lhs.len().cmp(&rhs.len()) {
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
            Ordering::Equal => {
                lhs.iter().rev().cmp(rhs.iter().rev())
            },
        }
    }
}

impl PartialEq<usize> for Ubig {
    fn eq(&self, rhs: &usize) -> bool {
        PartialEq::eq(self, &[*rhs])
    }
}

impl<const LEN: usize> PartialEq<[usize; LEN]> for Ubig {
    fn eq(&self, rhs: &[usize; LEN]) -> bool {
        PartialEq::eq(self, rhs.as_slice())
    }
}

impl PartialEq<[usize]> for Ubig {
    fn eq(&self, rhs: &[usize]) -> bool {
        let lhs = self.as_usize_slice();
        let rhs = rhs.trim_zeros();
        lhs == rhs
    }
}

impl PartialOrd<usize> for Ubig {
    fn partial_cmp(&self, rhs: &usize) -> Option<Ordering> {
        PartialOrd::partial_cmp(self, &[*rhs])
    }
}

impl<const LEN: usize> PartialOrd<[usize; LEN]> for Ubig {
    fn partial_cmp(&self, rhs: &[usize; LEN]) -> Option<Ordering> {
        PartialOrd::partial_cmp(self, rhs.as_slice())
    }
}

impl PartialOrd<[usize]> for Ubig {
    fn partial_cmp(&self, rhs: &[usize]) -> Option<Ordering> {
        let lhs = self.as_usize_slice();
        let rhs = rhs.trim_zeros();
        match lhs.len().cmp(&rhs.len()) {
            Ordering::Less => Some(Ordering::Less),
            Ordering::Greater => Some(Ordering::Greater),
            Ordering::Equal => {
                Some(lhs.iter().rev().cmp(rhs.iter().rev()))
            },
        }
    }
}

impl PartialEq<Ubig> for usize {
    fn eq(&self, rhs: &Ubig) -> bool {
        PartialEq::eq(rhs, self)
    }
}

impl PartialEq<Ubig> for [usize] {
    fn eq(&self, rhs: &Ubig) -> bool {
        PartialEq::eq(rhs, self)
    }
}

impl PartialOrd<Ubig> for usize {
    fn partial_cmp(&self, rhs: &Ubig) -> Option<Ordering> {
        Some(PartialOrd::partial_cmp(rhs, self)?.reverse())
    }
}

impl PartialOrd<Ubig> for [usize] {
    fn partial_cmp(&self, rhs: &Ubig) -> Option<Ordering> {
        Some(PartialOrd::partial_cmp(rhs, self)?.reverse())
    }
}

