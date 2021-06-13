use std::io::{stdout, Write};

use once_cell::sync::Lazy;

use crate::{
    num::Num,
    runtime::RuntimeErrorKind,
    value::{RustFunction, Value},
};

macro_rules! functions {
    ($($name:ident ($($arg:ident),*) = |$rt:ident, $span:tt| $expr:expr),* $(,)?) => {
        pub static FUNCTIONS: Lazy<Vec<(&str, RustFunction)>> = Lazy::new(|| vec![
            $((
                stringify!($name),
                RustFunction::new(&[$(stringify!($arg)),*], |$rt, $span| {
                    $(let $arg = $rt.val(stringify!($arg));)*
                    $expr
                })
            ),)*
        ]);
    };
}

macro_rules! require_type {
    ($input:expr, $span:expr, $($variant:ident($name:ident) => $expr:expr),* $(,)?) => {{
        let input = $input;
        match input {
            $(Value::$variant($name) => $expr,)*
            _ => {
                let types = [$(stringify!($variant)),*];
                return Err(RuntimeErrorKind::Generic(format!(
                    "Expected {}, but found {}",
                    types
                        .iter()
                        .enumerate()
                        .map(|(i, name)| format!(
                            "{}{}",
                            if i == types.len() - 1 {
                                if types.len() == 2 { " or " } else { ", or "}
                            }
                            else if i > 0 { ", " } else { "" }, name.to_lowercase()))
                        .collect::<String>(),
                    input.type_name()
                ))
                .span($span.clone()));
            }
        }
    }};
}

functions!(
    print(msg) = |rt, _| {
        print!("{}", rt.format(&msg));
        let _ = stdout().flush();
        Ok(Value::Nil)
    },
    println(msg) = |rt, _| {
        println!("{}", rt.format(&msg));
        Ok(Value::Nil)
    },
    sqrt(n) = |rt, span| {
        Ok(require_type!(
            n,
            span,
            Num(num) => Value::Num(num.to_f64().sqrt().into())
        ))
    },
    len(v) = |rt, span| {
        Ok(Value::Num(Num::Int(require_type!(
            v,
            span,
            String(s) => s.len(),
            List(list) => list.len(),
        ) as i64)))
    },
);
