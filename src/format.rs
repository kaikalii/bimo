use std::{fmt, rc::Rc};

use itertools::Itertools;

use crate::{entity::Key, runtime::Runtime, value::Value};

pub struct ValueFormatter<'i, 'r> {
    runtime: &'r Runtime<'i>,
    value: &'r Value<'i>,
}

impl<'i, 'r> ValueFormatter<'i, 'r> {
    pub fn new(runtime: &'r Runtime<'i>, value: &'r Value<'i>) -> Self {
        ValueFormatter { runtime, value }
    }
}

impl<'i, 'r> fmt::Debug for ValueFormatter<'i, 'r> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.value {
            Value::String(s) => s.fmt(f),
            _ => write!(f, "{}", self),
        }
    }
}

impl<'i, 'r> fmt::Display for ValueFormatter<'i, 'r> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.value {
            Value::Nil => "nil".fmt(f),
            Value::Bool(b) => b.fmt(f),
            Value::Num(n) => n.fmt(f),
            Value::String(s) => s.fmt(f),
            Value::Tag(ident) => {
                write!(f, "#{}", ident.name)
            }
            Value::List(list) => {
                write!(f, "[")?;
                for (i, val) in list.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", self.runtime.format(val))?;
                }
                write!(f, "]")
            }
            Value::Entity(entity) => {
                write!(f, "{{")?;
                for (i, (key, val)) in entity.iter().sorted_by_key(|(key, _)| *key).enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    match key {
                        Key::Field(ident) => {
                            write!(f, "{}: {:?}", ident.name, self.runtime.format(val))?
                        }
                        Key::Tag(ident) => write!(f, "#{}", ident.name)?,
                        Key::Value(key) => write!(
                            f,
                            "{:?} => {:?}",
                            self.runtime.format(&key),
                            self.runtime.format(val)
                        )?,
                    }
                }
                write!(f, "}}")
            }
            Value::Function(function) => write!(f, "function({:p})", Rc::as_ptr(function)),
            Value::Pattern(pattern) => write!(f, "pattern({:p})", Rc::as_ptr(pattern)),
        }
    }
}
