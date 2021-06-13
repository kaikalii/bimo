use std::{
    cell::RefCell,
    cmp::Ordering,
    collections::HashMap,
    fmt,
    hash::{Hash, Hasher},
    rc::Rc,
    sync::Mutex,
};

use once_cell::sync::Lazy;

use crate::{
    ast::{Ident, Node, Params},
    entity::Entity,
    list::List,
    num::Num,
    pattern::Pattern,
    runtime::{BimoFn, Runtime, Scope},
};

#[derive(Debug, Clone)]
pub enum Value<'i> {
    Nil,
    Bool(bool),
    Num(Num),
    Tag(Ident<'i>),
    String(Rc<str>),
    List(List<'i>),
    Entity(Entity<'i>),
    Function(Rc<Function<'i>>),
    Pattern(Rc<Pattern<'i>>),
}

impl<'i> Value<'i> {
    pub fn is_truthy(&self) -> bool {
        !matches!(self, Value::Nil | Value::Bool(false))
    }
    pub fn type_name(&self) -> &'static str {
        match self {
            Value::Nil => "nil",
            Value::Bool(_) => "bool",
            Value::Num(_) => "number",
            Value::Tag(_) => "tag",
            Value::String(_) => "string",
            Value::List(_) => "list",
            Value::Entity(_) => "entity",
            Value::Function(_) => "function",
            Value::Pattern(_) => "pattern",
        }
    }
    pub fn discriminant_index(&self) -> u8 {
        match self {
            Value::Nil => 0,
            Value::Bool(_) => 1,
            Value::Num(_) => 2,
            Value::Tag(_) => 3,
            Value::String(_) => 4,
            Value::List(_) => 5,
            Value::Entity(_) => 6,
            Value::Function(_) => 7,
            Value::Pattern(_) => 8,
        }
    }
}

impl<'i> Default for Value<'i> {
    fn default() -> Self {
        Value::Nil
    }
}

impl<'i> PartialEq for Value<'i> {
    fn eq(&self, other: &Value<'i>) -> bool {
        match (self, other) {
            (Value::Nil, Value::Nil) => true,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Num(a), Value::Num(b)) => a == b,
            (Value::String(a), Value::String(b)) => a == b,
            (Value::Tag(a), Value::Tag(b)) => a == b,
            (Value::List(a), Value::List(b)) => a == b,
            (Value::Function(a), Value::Function(b)) => Rc::ptr_eq(a, b),
            (Value::Entity(a), Value::Entity(b)) => a == b,
            (Value::Pattern(a), Value::Pattern(b)) => Rc::ptr_eq(a, b),
            _ => false,
        }
    }
}

impl<'i> Eq for Value<'i> {}

impl<'i> PartialOrd for Value<'i> {
    fn partial_cmp(&self, other: &Value<'i>) -> Option<Ordering> {
        match (self, other) {
            (Value::Nil, Value::Nil) => Some(Ordering::Equal),
            (Value::Bool(a), Value::Bool(b)) => a.partial_cmp(b),
            (Value::Num(a), Value::Num(b)) => a.partial_cmp(b),
            (Value::String(a), Value::String(b)) => a.partial_cmp(b),
            (Value::Tag(a), Value::Tag(b)) => a.partial_cmp(b),
            (Value::List(a), Value::List(b)) => a.partial_cmp(b),
            (Value::Function(a), Value::Function(b)) => Rc::as_ptr(a).partial_cmp(&Rc::as_ptr(b)),
            (Value::Entity(a), Value::Entity(b)) => a.partial_cmp(b),
            (Value::Pattern(a), Value::Pattern(b)) => Rc::as_ptr(a).partial_cmp(&Rc::as_ptr(b)),
            (a, b) => a.discriminant_index().partial_cmp(&b.discriminant_index()),
        }
    }
}

impl<'i> Ord for Value<'i> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl<'i> Hash for Value<'i> {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        self.discriminant_index().hash(state);
        match self {
            Value::Nil => {}
            Value::Bool(b) => b.hash(state),
            Value::Num(n) => n.hash(state),
            Value::String(s) => s.hash(state),
            Value::Tag(id) => id.hash(state),
            Value::List(list) => list.hash(state),
            Value::Entity(entity) => entity.hash(state),
            Value::Function(function) => Rc::as_ptr(function).hash(state),
            Value::Pattern(pattern) => Rc::as_ptr(pattern).hash(state),
        }
    }
}

#[derive(Debug, Clone)]
pub struct BimoFunction<'i> {
    pub scope: Scope<'i>,
    pub params: Params<'i>,
    pub body: RefCell<Node<'i>>,
}

#[derive(Clone, Copy)]
pub struct RustFunction<'i> {
    pub params: &'static [&'static str],
    pub f: BimoFn<'i>,
}

impl<'i> RustFunction<'i> {
    pub fn new(params: &'static [&'static str], f: BimoFn<'i>) -> Self {
        RustFunction { params, f }
    }
    pub fn scope(self, runtime: &Runtime<'i>) -> Function<'i> {
        Function::Rust(self, runtime.scope.clone())
    }
}

impl<'i> fmt::Debug for RustFunction<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "buil-in function")
    }
}

#[derive(Debug, Clone)]
pub enum Function<'i> {
    Bimo(BimoFunction<'i>),
    Rust(RustFunction<'i>, Scope<'i>),
}

impl<'i> From<bool> for Value<'i> {
    fn from(b: bool) -> Self {
        Value::Bool(b)
    }
}

impl<'i> From<i64> for Value<'i> {
    fn from(i: i64) -> Self {
        Value::Num(i.into())
    }
}

impl<'i> From<f64> for Value<'i> {
    fn from(r: f64) -> Self {
        Value::Num(r.into())
    }
}

impl<'i> From<Num> for Value<'i> {
    fn from(num: Num) -> Self {
        Value::Num(num)
    }
}

impl<'i> From<&'i str> for Value<'i> {
    fn from(s: &'i str) -> Self {
        Value::String(s.into())
    }
}

impl<'i> From<String> for Value<'i> {
    fn from(s: String) -> Self {
        Value::String(s.into())
    }
}

impl<'i> From<Function<'i>> for Value<'i> {
    fn from(f: Function<'i>) -> Self {
        Value::Function(f.into())
    }
}

impl<'i> From<List<'i>> for Value<'i> {
    fn from(list: List<'i>) -> Self {
        Value::List(list)
    }
}

impl<'i> From<Entity<'i>> for Value<'i> {
    fn from(e: Entity<'i>) -> Self {
        Value::Entity(e)
    }
}

static STRINGS: Lazy<Mutex<HashMap<String, &'static str>>> =
    Lazy::new(|| Mutex::new(HashMap::new()));

pub(crate) fn static_str(s: &str) -> &'static str {
    *STRINGS
        .lock()
        .unwrap()
        .entry(s.into())
        .or_insert_with(|| Box::leak(Box::new(s.to_owned())))
}
