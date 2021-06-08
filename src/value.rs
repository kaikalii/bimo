#![allow(dead_code)]

use std::{
    cell::RefCell,
    cmp::Ordering,
    collections::{HashMap, VecDeque},
    fmt,
    hash::{BuildHasher, Hash, Hasher},
    rc::Rc,
};

use seahash::SeaHasher;

use crate::{
    ast::{Ident, Items, Params},
    interpret::{BimoFn, Scope},
    num::Num,
};

#[derive(Clone)]
pub struct HashState;

impl BuildHasher for HashState {
    type Hasher = SeaHasher;
    fn build_hasher(&self) -> Self::Hasher {
        SeaHasher::new()
    }
}

#[derive(Debug, Clone)]
pub enum Value<'i> {
    Nil,
    Bool(bool),
    Num(Num),
    Tag(Ident<'i>),
    String(Rc<str>),
    List(Rc<VecDeque<Value<'i>>>),
    Entity(Rc<HashMap<Key<'i>, Value<'i>, HashState>>),
    Function(Rc<Function<'i>>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Key<'i> {
    Tag(Ident<'i>),
    Field(Ident<'i>),
    Value(Value<'i>),
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
        }
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
            (Value::Entity(a), Value::Entity(b)) => {
                Rc::ptr_eq(a, b)
                    || a.len() == b.len()
                        && a.iter().all(|(k, v)| b.get(k).map_or(false, |v2| v == v2))
            }
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
            (Value::Entity(a), Value::Entity(b)) => {
                if self == other {
                    Some(Ordering::Equal)
                } else {
                    Rc::as_ptr(a).partial_cmp(&Rc::as_ptr(b))
                }
            }
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
            Value::List(list) => (**list).hash(state),
            Value::Entity(entity) => Rc::as_ptr(entity).hash(state),
            Value::Function(function) => Rc::as_ptr(function).hash(state),
        }
    }
}

#[derive(Debug, Clone)]
pub struct BimoFunction<'i> {
    pub scope: Scope<'i>,
    pub params: Params<'i>,
    pub items: RefCell<Items<'i>>,
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
}

impl<'i> fmt::Debug for RustFunction<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "buil-in function")
    }
}

#[derive(Debug, Clone)]
pub enum Function<'i> {
    Bimo(BimoFunction<'i>),
    Rust(RustFunction<'i>),
}
