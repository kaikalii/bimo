use std::io::{stdout, Write};

use once_cell::sync::Lazy;

use crate::{
    interpret::RuntimeErrorKind,
    value::{RustFunction, Value},
};

macro_rules! functions {
    ($($name:ident ($($arg:ident),*) = $f:expr),* $(,)?) => {
        pub static FUNCTIONS: Lazy<Vec<(&str, RustFunction)>> = Lazy::new(|| vec![
            $((
                stringify!($name),
                RustFunction::new(&[$(stringify!($arg)),*], $f)
            ),)*
        ]);
    };
}

macro_rules! require_type {
    ($input:expr, $span:expr, $variant:ident($name:ident), $expr:expr) => {{
        let input = $input;
        if let Value::$variant($name) = input {
            $expr
        } else {
            return Err(RuntimeErrorKind::Generic(format!(
                "Expected type {}",
                stringify!($variant).to_lowercase()
            ))
            .span($span.clone()));
        }
    }};
}

functions!(
    print(msg) = |rt, _| {
        print!("{}", rt.format(&rt.val("msg")));
        let _ = stdout().flush();
        Ok(Value::Nil)
    },
    println(msg) = |rt, _| {
        println!("{}", rt.format(&rt.val("msg")));
        Ok(Value::Nil)
    },
    sqrt(n) = |rt, span| {
        Ok(require_type!(
            rt.val("n"),
            span,
            Num(num),
            Value::Num(num.to_f64().sqrt().into())
        ))
    }
);
