pub mod iter;

pub fn max_all<I>(iter: I) -> I::Item
where
    I: IntoIterator,
    I::Item: Ord + Default,
{
    iter
    .into_iter()
    .max()
    .unwrap_or_default()
}

pub fn as_equal<T: PartialEq>(val_0: T, val_1: &T) -> Option<T> {
    if val_0 == *val_1 {
        Some(val_0)
    } else {
        None
    }
}

