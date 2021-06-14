use std::{fmt, rc::Rc};

use itertools::Itertools;

use crate::{
    ast::StringPart,
    entity::Key,
    pattern::{FieldPattern, Pattern, StringPattern},
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
                    write!(f, "{:?}", self.settings.format(val))?;
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
        match self.value {
            Pattern::Single(ident) | Pattern::Value(ident) => write!(f, "{}", ident.name),
            Pattern::Bound { left, right, .. } => write!(
                f,
                "{}: {}",
                self.settings.format(&**left),
                self.settings.format(&**right)
            ),
            Pattern::Nil(_) => write!(f, "nil"),
            Pattern::Bool { b, .. } => write!(f, "{}", b),
            Pattern::Int { int, .. } => write!(f, "{}", int),
            Pattern::String { pattern, .. } => write!(f, "{}", pattern.borrow()),
            Pattern::List { patterns, .. } => {
                write!(f, "[")?;
                for (i, pattern) in patterns.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", self.settings.format(pattern))?;
                }
                write!(f, "]")
            }
            Pattern::Entity { patterns, .. } => {
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
        match self.value {
            FieldPattern::SameName(ident) => {
                write!(f, "{}", ident.name)
            }
            FieldPattern::Pattern { field, pattern, .. } => {
                write!(f, "{}: {}", field.name, self.settings.format(pattern))
            }
        }
    }
}

impl<'i> fmt::Display for StringPattern<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "\"")?;
        if let Some(s) = &self.resolved {
            write!(f, "{}", s)?;
        } else {
            for part in &self.parts {
                match part {
                    StringPart::Raw(s) => write!(f, "{}", s)?,
                    StringPart::Format(node) => write!(f, "{{{}}}", node.span().as_str())?,
                }
            }
        }
        write!(f, "\"")
    }
}
