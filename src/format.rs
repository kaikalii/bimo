use std::{fmt, rc::Rc};

use itertools::Itertools;

use crate::{
    entity::Key,
    pattern::{FieldPattern, FieldPatternType, Pattern, PatternType},
    value::Value,
};

pub struct FormatSettings {}

impl Default for FormatSettings {
    fn default() -> Self {
        FormatSettings {}
    }
}

impl FormatSettings {
    pub fn format<'r, T>(&'r self, value: &'r T) -> Formatter<'r, T> {
        Formatter {
            settings: self,
            value,
        }
    }
}

pub struct Formatter<'r, T> {
    settings: &'r FormatSettings,
    value: &'r T,
}

impl<'i, 'r> fmt::Debug for Formatter<'r, Value<'i>> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.value {
            Value::String(s) => s.fmt(f),
            _ => write!(f, "{}", self),
        }
    }
}

impl<'i, 'r> fmt::Display for Formatter<'r, Value<'i>> {
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
                    write!(f, "{}", self.settings.format(val))?;
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
                            write!(f, "{}: {:?}", ident.name, self.settings.format(val))?
                        }
                        Key::Tag(ident) => write!(f, "#{}", ident.name)?,
                        Key::Value(key) => write!(
                            f,
                            "{:?} => {:?}",
                            self.settings.format(key),
                            self.settings.format(val)
                        )?,
                    }
                }
                write!(f, "}}")
            }
            Value::Function(function) => write!(f, "function({:p})", Rc::as_ptr(function)),
            Value::Pattern(pattern) => write!(f, "{}", self.settings.format(&**pattern)),
        }
    }
}

impl<'i, 'r> fmt::Debug for Formatter<'r, Pattern<'i>> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl<'i, 'r> fmt::Display for Formatter<'r, Pattern<'i>> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.value.ty {
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
                    write!(f, "{}", self.settings.format(pattern))?;
                }
                write!(f, "]")
            }
            PatternType::Entity { patterns, .. } => {
                write!(f, "{{")?;
                for (i, pattern) in patterns.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", self.settings.format(pattern))?;
                }
                write!(f, "}}")
            }
        }
    }
}

impl<'i, 'r> fmt::Debug for Formatter<'r, FieldPattern<'i>> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl<'i, 'r> fmt::Display for Formatter<'r, FieldPattern<'i>> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.value.ty {
            FieldPatternType::SameName(ident) => {
                write!(f, "{}", ident.name)
            }
            FieldPatternType::Pattern { field, pattern, .. } => {
                write!(f, "{}: {}", field.name, self.settings.format(pattern))
            }
        }
    }
}
