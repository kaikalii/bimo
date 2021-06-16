use std::{
    cell::RefCell,
    collections::HashMap,
    fs,
    io::{stdout, Write},
    path::PathBuf,
    rc::Rc,
};

use once_cell::sync::Lazy;

use crate::{
    bimo_list,
    error::{BimoError, BimoResult},
    list::List,
    num::Num,
    pattern::Pattern,
    value::{static_str, RustFunction, Value},
};

#[macro_export]
macro_rules! bimo_function {
    ($($arg:ident,)* |$rt:ident, $span:tt| $expr:expr) => {
        RustFunction::new(&[$(stringify!($arg)),*], |$rt, $span| {
            $(let $arg = $rt.val(stringify!($arg));)*
            $expr
        })
    }
}

macro_rules! functions {
    ($($name:ident ($($arg:ident),*) = |$rt:ident, $span:tt| $expr:expr),* $(,)?) => {
        pub static FUNCTIONS: Lazy<Vec<(&str, RustFunction)>> = Lazy::new(|| vec![
            $((
                stringify!($name),
                bimo_function!($($arg,)* |$rt, $span| $expr),
            ),)*
        ]);
    };
}

macro_rules! require_type {
    ($input:expr, $span:expr, $($pattern:pat => $expr:expr),* $(,)?) => {{
        let input = $input;
        match input {
            $($pattern => $expr,)*
            _ => {
                let types = [$(stringify!($pattern)),*];
                return Err(BimoError::new(
                    format!(
                        "Expected {}, but found {}",
                        types
                            .iter()
                            .enumerate()
                            .map(|(i, name)| format!(
                                "{}{}",
                                if i > 0 && i == types.len() - 1 {
                                    if types.len() == 2 { " or " } else { ", or "}
                                }
                                else if i > 0 { ", " } else { "" }, name))
                            .collect::<String>(),
                        input.type_name()
                    ),
                    $span.clone()
                ))
            }
        }
    }};
}

functions!(
    print(msg) = |rt, _| {
        print!("{}", msg);
        let _ = stdout().flush();
        Ok(Value::Nil)
    },
    println(msg) = |rt, _| {
        println!("{}", msg);
        Ok(Value::Nil)
    },
    sqrt(n) = |rt, span| {
        Ok(require_type!(
            n,
            span,
            Value::Num(num) => Value::Num(num.to_f64().sqrt().into())
        ))
    },
    len(v) = |rt, span| {
        Ok(Value::Num(Num::Int(require_type!(
            v,
            span,
            Value::String(s) => s.len(),
            Value::List(list) => list.len(),
        ) as i64)))
    },
    range(start, count) = |rt, _| {
        let state = bimo_list!(start, count);
        let function = bimo_function!(state, |rt, span| {
            let [start, count] = require_type!(state, span, Value::List(list) => list.split());
            let start = require_type!(start, span, Value::Num(n) => n);
            let count = require_type!(count, span, Value::Num(n) => n);
            Ok(if count.to_i64() > 0 {
                bimo_list!(bimo_list!(start + Num::Int(1), count - Num::Int(1)), start)
            } else {
                Value::Nil
            })
        })
        .scope(rt);
        Ok(bimo_list!(state, function))
    },
    collect(iter) = |rt, span| {
        let [mut state, next] = require_type!(iter, span, Value::List(list) => list.split());
        let mut list = List::new();
        loop {
            let [new_state, item] = require_type!(
                rt.call(&next, &[state], span)?,
                span,
                Value::Nil => break,
                Value::List(list) => list.split(),
            );
            state = new_state;
            list.push(item);
        }
        Ok(list.into())
    },
    filter(iter, filter) = |rt, _| {
        let state = bimo_list!(iter, filter);
        let function = bimo_function!(state, |rt, span| {
            let [iter, filter] = require_type!(state, span, Value::List(list) => list.split());
            let [mut state, next] = require_type!(iter, span, Value::List(list) => list.split());
            Ok(loop {
                let [new_state, item] = require_type!(
                    rt.call(&next, &[state], span)?,
                    span,
                    Value::Nil => break Value::Nil,
                    Value::List(list) => list.split(),
                );
                state = new_state;
                if rt
                    .call(&filter, std::slice::from_ref(&item), span)?
                    .is_truthy()
                {
                    let iter = bimo_list!(state, next);
                    let state = bimo_list!(iter, filter);
                    break bimo_list!(state, item);
                }
            })
        })
        .scope(rt);
        Ok(bimo_list!(state, function))
    },
    map(iter, transform) = |rt, _| {
        let state = bimo_list!(iter, transform);
        let function = bimo_function!(state, |rt, span| {
            let [iter, transform] = require_type!(state, span, Value::List(list) => list.split());
            let [mut state, next] = require_type!(iter, span, Value::List(list) => list.split());
            let [new_state, item] = require_type!(
                rt.call(&next, &[state], span)?,
                span,
                Value::Nil => return Ok(Value::Nil),
                Value::List(list) => list.split(),
            );
            state = new_state;
            let item = rt.call(&transform, std::slice::from_ref(&item), span)?;
            let iter = bimo_list!(state, next);
            let state = bimo_list!(iter, transform);
            Ok(bimo_list!(state, item))
        })
        .scope(rt);
        Ok(bimo_list!(state, function))
    },
    foreach(iter, function) = |rt, span| {
        let [mut state, next] = require_type!(iter, span, Value::List(list) => list.split());
        loop {
            let [new_state, item] = require_type!(
                rt.call(&next, &[state], span)?,
                span,
                Value::Nil => break,
                Value::List(list) => list.split(),
            );
            state = new_state;
            rt.call(&function, &[item], span)?;
        }
        Ok(Value::Nil)
    },
    eval(code) = |rt, span| {
        let code = require_type!(code, span, Value::String(s) => s);
        rt.eval(static_str(&code), "")
    },
    mod(path) = |rt, span| {
        let path = require_type!(path, span, Value::String(s) => PathBuf::from(&*s))
            .with_extension("bimo");
        thread_local! {
            static LOADED_MODULES: RefCell<HashMap<PathBuf, BimoResult<'static>>> = HashMap::new().into();
        }
        LOADED_MODULES.with(|map| match map.try_borrow_mut() {
            Ok(mut map) => map
                .entry(path)
                .or_insert_with_key(|path| match fs::read_to_string(&path) {
                    Ok(code) => rt.eval(static_str(&code), path),
                    Err(e) => Err(BimoError::new(
                        format!("Error opening {}: {}", path.to_string_lossy(), e),
                        span.clone(),
                    )),
                })
                .clone(),
            Err(_) => Err(BimoError::new(
                format!(
                    "Circular dependency detected when loading {}",
                    path.to_string_lossy()
                ),
                span.clone(),
            )),
        })
    }
);

macro_rules! patterns {
    ($(($name:literal, $f:expr)),* $(,)?) => {
        thread_local! {
            pub static PATTERNS: Vec<(&'static str, Rc<Pattern<'static>>)> = vec![$(($name, Rc::new(Pattern::builtin($name, $f)))),*];
        }
    }
}

patterns!(
    ("int", |val| {
        Ok(if let Value::Num(num) = val {
            Value::Num(num.to_i64().into())
        } else {
            Value::Nil
        })
    }),
    ("num", |val| {
        Ok(if let Value::Num(_) = val {
            val.clone()
        } else {
            Value::Nil
        })
    }),
    ("bool", |val| {
        Ok(if let Value::Bool(_) = val {
            val.clone()
        } else {
            Value::Nil
        })
    }),
    ("string", |val| {
        Ok(if let Value::String(_) = val {
            val.clone()
        } else {
            Value::Nil
        })
    }),
    ("fn", |val| {
        Ok(if let Value::Function(_) = val {
            val.clone()
        } else {
            Value::Nil
        })
    }),
);
