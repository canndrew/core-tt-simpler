use crate::priv_prelude::*;
use std::cell::Cell;

thread_local! {
    pub static DEBUG_INDENT: Cell<usize> = const { Cell::new(0) };
    pub static RENDERED_DEBUG_INDENT: Cell<usize> = const { Cell::new(0) };
}

#[allow(unused)]
pub struct Indenter {
    indent: usize,
}

impl Indenter {
    #[allow(unused)]
    pub fn new() -> Indenter {
        let indent = DEBUG_INDENT.get();
        DEBUG_INDENT.set(indent + 1);
        Indenter { indent }
    }
}

impl Drop for Indenter {
    fn drop(&mut self) {
        let indent = self.indent;
        DEBUG_INDENT.set(indent);
        loop {
            let rendered_indent = RENDERED_DEBUG_INDENT.get();
            if rendered_indent <= indent {
                break;
            }
            let new_rendered_indent = rendered_indent - 1;
            for _ in 0..new_rendered_indent {
                print!("    ");
            }
            println!("}}");
            RENDERED_DEBUG_INDENT.set(new_rendered_indent);
        }
    }
}

#[allow(unused)]
macro_rules! debug_indent {
    () => {
        let _indenter = crate::debug::Indenter::new();
    };
}

macro_rules! debug {
    ($($t:tt)*) => {{
        let indent = crate::debug::DEBUG_INDENT.get();
        loop {
            let rendered_indent = crate::debug::RENDERED_DEBUG_INDENT.get();
            if rendered_indent == indent {
                break;
            }
            for _ in 0..rendered_indent {
                print!("    ");
            }
            println!("{{");
            crate::debug::RENDERED_DEBUG_INDENT.set(rendered_indent + 1);
        }

        let s = format!($($t)*);
        for line in s.lines() {
            for _ in 0..indent {
                print!("    ");
            }
            println!("{}", line);
        }
    }};
}

#[allow(unused)]
pub struct PrintOnPanic<T: fmt::Display> {
    val: T,
}

impl<T: fmt::Display> PrintOnPanic<T> {
    #[allow(unused)]
    pub fn new(val: T) -> PrintOnPanic<T> {
        PrintOnPanic { val }
    }
}

impl<T: fmt::Display> Drop for PrintOnPanic<T> {
    fn drop(&mut self) {
        if std::thread::panicking() {
            debug!("{}", self.val);
        }
    }
}

#[allow(unused)]
macro_rules! print_on_panic {
    ($($t:tt)*) => {
        let print_on_panic_args = format_args!(
            "[{}:{}] {}", file!(), line!(), format_args!($($t)*),
        );
        let _x = crate::debug::PrintOnPanic::new(print_on_panic_args);
    };
}

pub(crate) use {debug_indent, debug, print_on_panic};

