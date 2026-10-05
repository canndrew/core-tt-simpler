use crate::priv_prelude::*;

thread_local! {
    static INDENT: Cell<usize> = Cell::new(0);
}

#[allow(unused)]
#[derive(Clone, Copy, Debug)]
pub struct Indent(usize);

impl fmt::Display for Indent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Indent(amount) = self;
        for _ in 0..*amount {
            f.write_str("    ")?;
        }
        Ok(())
    }
}

#[allow(unused)]
pub fn get_indent() -> Indent {
    Indent(INDENT.get())
}

#[allow(unused)]
pub fn indent<R>(func: impl FnOnce() -> R) -> R {
    let amount = INDENT.get();
    INDENT.set(amount + 1);
    let ret = func();
    INDENT.set(amount);
    ret
}


