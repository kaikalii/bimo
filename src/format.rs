use std::{fmt, rc::Rc};

use itertools::Itertools;

use crate::{
    entity::Key,
    pattern::{FieldPattern, FieldPatternType, Pattern, PatternType},
    runtime::Runtime,
    value::Value,
};

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
            Value::Pattern(pattern) => write!(f, "{}", self.runtime.format_pattern(pattern)),
        }
    }
}

pub struct PatternFormatter<'i, 'r> {
    runtime: &'r Runtime<'i>,
    pattern: &'r Pattern<'i>,
}

impl<'i, 'r> PatternFormatter<'i, 'r> {
    pub fn new(runtime: &'r Runtime<'i>, pattern: &'r Pattern<'i>) -> Self {
        PatternFormatter { runtime, pattern }
    }
}

impl<'i, 'r> fmt::Debug for PatternFormatter<'i, 'r> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl<'i, 'r> fmt::Display for PatternFormatter<'i, 'r> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.pattern.ty {
            PatternType::Single(ident) => write!(f, "{}", ident.name),
            PatternType::Nil(_) => write!(f, "nil"),
            PatternType::Bool { b, .. } => write!(f, "{}", b),
            PatternType::Int { int, .. } => write!(f, "{}", int),
            PatternType::String { string, .. } => write!(f, "{}", string),
            PatternType::List { patterns, .. } => {
                write!(f, "[")?;
                for (i, pattern) in patterns.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", self.runtime.format_pattern(pattern))?;
                }
                write!(f, "]")
            }
            PatternType::Entity { patterns, .. } => {
                write!(f, "{{")?;
                for (i, pattern) in patterns.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", self.runtime.format_field_pattern(pattern))?;
                }
                write!(f, "}}")
            }
        }
    }
}

pub struct FieldPatternFormatter<'i, 'r> {
    runtime: &'r Runtime<'i>,
    pattern: &'r FieldPattern<'i>,
}

impl<'i, 'r> FieldPatternFormatter<'i, 'r> {
    pub fn new(runtime: &'r Runtime<'i>, pattern: &'r FieldPattern<'i>) -> Self {
        FieldPatternFormatter { runtime, pattern }
    }
}

impl<'i, 'r> fmt::Debug for FieldPatternFormatter<'i, 'r> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl<'i, 'r> fmt::Display for FieldPatternFormatter<'i, 'r> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.pattern.ty {
            FieldPatternType::SameName(ident) => {
                write!(f, "{}", ident.name)
            }
            FieldPatternType::Pattern { field, pattern, .. } => {
                write!(
                    f,
                    "{}: {}",
                    field.name,
                    self.runtime.format_pattern(pattern)
                )
            }
        }
    }
}
