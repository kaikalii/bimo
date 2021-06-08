use std::io::{stdout, Write};

use once_cell::sync::Lazy;

use crate::value::{RustFunction, Value};

macro_rules! functions {
    ($($name:ident ($($arg:ident),*) $f:expr),* $(,)?) => {
        pub static FUNCTIONS: Lazy<Vec<(&str, RustFunction)>> = Lazy::new(|| vec![
            $((
                stringify!($name),
                RustFunction::new(&[$(stringify!($arg)),*], $f)
            ),)*
        ]);
    };
}

functions!(
    print(msg) | rt | {
        print!("{}", rt.format(&rt.val("msg")));
        let _ = stdout().flush();
        Ok(Value::Nil)
    },
    println(msg) | rt | {
        println!("{}", rt.format(&rt.val("msg")));
        Ok(Value::Nil)
    }
);
