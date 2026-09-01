use crate::priv_prelude::*;

#[derive(Clone, PartialEq)]
pub struct Usages {
    ubig: Ubig,
}

impl Usages {
    pub fn empty() -> Usages {
        let ubig = Ubig::ZERO;
        Usages { ubig }
    }

    pub fn single_var(index: usize) -> Usages {
        let ubig = Ubig::nth_power_of_two(index);
        Usages { ubig }
    }

    pub fn as_single_var(&self) -> Option<usize> {
        self.ubig.ilog2_exact()
    }

    pub fn ones(len: usize) -> Usages {
        let ubig = Ubig::nth_power_of_two_minus_one(len);
        Usages { ubig }
    }

    pub fn count_ones(&self) -> usize {
        self.ubig.count_ones()
    }

    pub fn ctx_len(&self) -> usize {
        self.ubig.bit_width()
    }

    pub fn truncated_ctx_len(&self, limit: usize) -> usize {
        self.ubig.truncated_bit_width(limit)
    }

    pub fn get(&self, index: usize) -> bool {
        self.ubig.get_bit(index)
    }

    pub fn pop_scoped(&mut self, ctx_len: usize) -> bool {
        match self.ubig.bit_width().cmp(&ctx_len.strict_add(1)) {
            cmp::Ordering::Less => false,
            cmp::Ordering::Equal => {
                self.ubig.set_bit(ctx_len, false);
                true
            },
            cmp::Ordering::Greater => panic!(),
        }
    }

    pub fn clone_truncate(&self, ctx_len: usize) -> Usages {
        let ubig = self.ubig.clone_truncate(ctx_len);
        Usages { ubig }
    }

    pub fn or_assign(&mut self, other: &Usages) {
        self.ubig |= &other.ubig;
    }

    pub fn or_assign_truncated(&mut self, other: &Usages, ctx_len: usize) {
        let ubig = other.ubig.clone_truncate(ctx_len);
        self.ubig |= ubig;
    }

    pub fn set_to_zero(&mut self, index: usize) {
        self.ubig.set_bit(index, false);
    }

    pub fn set_to_one(&mut self, index: usize) {
        self.ubig.set_bit(index, true);
    }

    pub fn push_one(&mut self) {
        self.ubig.set_bit(self.ubig.bit_width(), true);
    }

    pub fn push_ones(&mut self, n: usize) {
        let ctx_len = self.ubig.bit_width();
        self.ubig.set_bit_range_to_one(ctx_len, ctx_len + n);
    }

    pub fn set_range_to_zero(&mut self, start: usize, end: usize) {
        self.ubig.set_bit_range_to_zero(start, end);
    }

    pub fn set_run_to_one(&mut self, start: usize, run_length: usize) {
        self.ubig.set_bit_range_to_one(start, start + run_length);
    }

    pub fn truncate(&mut self, len: usize) {
        self.ubig.truncate(len);
    }

    pub fn filter(&mut self, usages: &Usages) {
        debug_assert!({
            let iter_0 = usages.ubig.as_usize_slice().iter().copied().chain(iter::repeat(0));
            let iter_1 = self.ubig.as_usize_slice().iter().copied();
            iter_0.zip(iter_1).all(|(word_0, word_1)| (!word_0 & word_1) == 0)
        });
        self.ubig.extract_bits(usages.ubig.as_usize_slice());
    }

    pub fn unfilter(&mut self, usages: &Usages) {
        debug_assert!(usages.count_ones() >= self.ctx_len());
        self.ubig.deposit_bits(usages.ubig.as_usize_slice());
    }

    pub fn unfiltered(mut self, usages: &Usages) -> Usages {
        self.unfilter(usages);
        self
    }

    pub fn filter_index(&self, index: usize) -> usize {
        let ubig = self.ubig.clone_truncate(index);
        ubig.count_ones()
    }

    pub fn unfilter_index(&self, index: usize) -> usize {
        self.ubig.position_of_nth_one(index).unwrap()
    }

    pub fn merge_all<const LEN: usize>(usagess: [&Usages; LEN]) -> Usages {
        let mut ubig = Ubig::ZERO;
        for usages in usagess.iter() {
            ubig |= &usages.ubig;
        }
        Usages { ubig }
    }

    pub fn merge_all_mut<const LEN: usize>(usagess: [&mut Usages; LEN]) -> Usages {
        let ret = Usages::merge_all(usagess.each_ref().map(|usages| &**usages));
        for usages in usagess {
            usages.filter(&ret);
        }
        ret
    }
}

impl fmt::Debug for Usages {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let ctx_len = self.ctx_len();
        write!(f, "[")?;
        for index in 0..ctx_len {
            let bit = self.ubig.get_bit(index);
            write!(f, "{}", bit as u32)?;
        }
        write!(f, "]")?;
        Ok(())
    }
}

