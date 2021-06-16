use std::{cell::RefCell, fmt, rc::Rc};

use regex::Regex;

use crate::{
    ast::{FileSpan, Ident, StringPart},
    error::BimoResult,
    fmt::FormatSettings,
    value::Value,
};

#[derive(Clone)]
pub struct StringPattern<'i> {
    pub is_regex: bool,
    pub parts: Vec<StringPart<'i>>,
    pub resolved: Option<Rc<Regex>>,
}

#[derive(Clone)]
pub enum Pattern<'i> {
    Single(Ident<'i>),
    Bound {
        left: Box<Pattern<'i>>,
        right: Box<Pattern<'i>>,
        span: FileSpan<'i>,
    },
    Value(Ident<'i>),
    List {
        patterns: Vec<Pattern<'i>>,
        span: FileSpan<'i>,
    },
    Entity {
        patterns: Vec<FieldPattern<'i>>,
        span: FileSpan<'i>,
    },
    Nil(FileSpan<'i>),
    Bool {
        b: bool,
        span: FileSpan<'i>,
    },
    Int {
        int: i64,
        span: FileSpan<'i>,
    },
    String {
        pattern: RefCell<StringPattern<'i>>,
        span: FileSpan<'i>,
    },
    Builtin {
        f: Rc<dyn Fn(&Value<'i>) -> BimoResult<'i>>,
        name: String,
    },
}

impl<'i> Pattern<'i> {
    pub fn builtin(
        name: impl Into<String>,
        f: impl Fn(&Value<'i>) -> BimoResult<'i> + 'static,
    ) -> Self {
        Pattern::Builtin {
            name: name.into(),
            f: Rc::new(f),
        }
    }
}

#[derive(Clone)]
pub enum FieldPattern<'i> {
    SameName(Ident<'i>),
    Pattern {
        field: Ident<'i>,
        pattern: Pattern<'i>,
        span: FileSpan<'i>,
    },
}

impl<'i> fmt::Debug for Pattern<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        FormatSettings::default().format(self).fmt(f)
    }
}

impl<'i> fmt::Display for Pattern<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        FormatSettings::default().format(self).fmt(f)
    }
}

impl<'i> fmt::Debug for FieldPattern<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        FormatSettings::default().format(self).fmt(f)
    }
}

impl<'i> fmt::Display for FieldPattern<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        FormatSettings::default().format(self).fmt(f)
    }
}
