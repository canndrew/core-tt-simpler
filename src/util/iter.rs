use crate::priv_prelude::*;

#[expect(unused)]
pub fn merge_enumerated<T>(
    iter_0: impl IntoIterator<Item = (usize, T)>,
    iter_1: impl IntoIterator<Item = (usize, T)>,
) -> impl Iterator<Item = (usize, Which<T>)> {
    let iter_0 = iter_0.into_iter();
    let iter_1 = iter_1.into_iter();
    MergeEnumerated::Both { iter_0, iter_1 }
}

#[expect(unused)]
pub enum Which<T> {
    Left(T),
    Right(T),
    Both(T, T),
}

#[expect(unused)]
enum MergeEnumerated<I0, I1, T> {
    Finished,
    DrainingLeft {
        iter_0: I0,
    },
    DrainingRight {
        iter_1: I1,
    },
    Both {
        iter_0: I0,
        iter_1: I1,
    },
    HaveLeft {
        iter_0: I0,
        iter_1: I1,
        index_0: usize,
        val_0: T,
    },
    HaveRight {
        iter_0: I0,
        iter_1: I1,
        index_1: usize,
        val_1: T,
    },
}

impl<I0, I1, T> Iterator for MergeEnumerated<I0, I1, T>
where
    I0: Iterator<Item = (usize, T)>,
    I1: Iterator<Item = (usize, T)>,
{
    type Item = (usize, Which<T>);

    fn next(&mut self) -> Option<(usize, Which<T>)> {
        let state = mem::replace(self, MergeEnumerated::Finished);
        let (iter_0, iter_1, index_0, index_1, val_0, val_1) = match state {
            MergeEnumerated::Finished => return None,
            MergeEnumerated::DrainingLeft { mut iter_0 } => {
                let (index, val) = iter_0.next()?;
                return Some((index, Which::Left(val)));
            },
            MergeEnumerated::DrainingRight { mut iter_1 } => {
                let (index, val) = iter_1.next()?;
                return Some((index, Which::Right(val)));
            },
            MergeEnumerated::Both { mut iter_0, mut iter_1 } => {
                match (iter_0.next(), iter_1.next()) {
                    (None, None) => return None,
                    (Some((index, val)), None) => {
                        *self = MergeEnumerated::DrainingLeft { iter_0 };
                        return Some((index, Which::Left(val)));
                    },
                    (None, Some((index, val))) => {
                        *self = MergeEnumerated::DrainingRight { iter_1 };
                        return Some((index, Which::Right(val)));
                    },
                    (Some((index_0, val_0)), Some((index_1, val_1))) => {
                        (iter_0, iter_1, index_0, index_1, val_0, val_1)
                    },
                }
            },
            MergeEnumerated::HaveLeft { iter_0, mut iter_1, index_0, val_0 } => {
                match iter_1.next() {
                    None => {
                        *self = MergeEnumerated::DrainingLeft { iter_0 };
                        return Some((index_0, Which::Left(val_0)));
                    },
                    Some((index_1, val_1)) => {
                        (iter_0, iter_1, index_0, index_1, val_0, val_1)
                    },
                }
            },
            MergeEnumerated::HaveRight { mut iter_0, iter_1, index_1, val_1 } => {
                match iter_0.next() {
                    None => {
                        *self = MergeEnumerated::DrainingRight { iter_1 };
                        return Some((index_1, Which::Right(val_1)));
                    },
                    Some((index_0, val_0)) => {
                        (iter_0, iter_1, index_0, index_1, val_0, val_1)
                    },
                }
            },
        };
        match index_0.cmp(&index_1) {
            cmp::Ordering::Less => {
                *self = MergeEnumerated::HaveRight {
                    iter_0, iter_1, index_1, val_1,
                };
                Some((index_0, Which::Left(val_0)))
            },
            cmp::Ordering::Greater => {
                *self = MergeEnumerated::HaveLeft {
                    iter_0, iter_1, index_0, val_0,
                };
                Some((index_1, Which::Right(val_1)))
            },
            cmp::Ordering::Equal => {
                *self = MergeEnumerated::Both { iter_0, iter_1 };
                Some((index_0, Which::Both(val_0, val_1)))
            },
        }
    }
}

