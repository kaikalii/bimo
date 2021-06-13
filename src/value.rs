#![allow(dead_code)]

use std::{
    cell::RefCell,
    cmp::Ordering,
    collections::{
        hash_map::{self, Entry},
        HashMap, VecDeque,
    },
    fmt,
    hash::{BuildHasher, Hash, Hasher},
    rc::Rc,
};

use seahash::SeaHasher;

use crate::{
    ast::{Ident, Node, Params},
    num::Num,
    runtime::{BimoFn, Scope},
};

#[derive(Clone, Default)]
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
    Entity(Entity<'i>),
    Function(Rc<Function<'i>>),
}

#[derive(Debug, Clone, Default)]
pub struct Entity<'i> {
    map: Rc<HashMap<Key<'i>, Value<'i>, HashState>>,
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

impl<'i> Entity<'i> {
    pub fn new() -> Self {
        Self::with_capacity(0)
    }
    pub fn with_capacity(capacity: usize) -> Self {
        Entity {
            map: Rc::new(HashMap::with_capacity_and_hasher(capacity, HashState)),
        }
    }
    pub fn get(&self, key: impl AsRef<Key<'i>>) -> &Value<'i> {
        if let Some(val) = self.map.get(key.as_ref()) {
            val
        } else {
            &Value::Nil
        }
    }
    pub fn set(&mut self, key: Key<'i>, val: Value<'i>) {
        let map = Rc::make_mut(&mut self.map);
        if let Value::Nil = val {
            map.remove(&key);
        } else {
            map.insert(key, val);
        }
    }
    pub fn entry(&mut self, key: Key<'i>) -> Entry<Key<'i>, Value<'i>> {
        Rc::make_mut(&mut self.map).entry(key)
    }
    pub fn try_into_iter(self) -> Result<hash_map::IntoIter<Key<'i>, Value<'i>>, Self> {
        match Rc::try_unwrap(self.map) {
            Ok(map) => Ok(map.into_iter()),
            Err(map) => Err(Entity { map }),
        }
    }
    pub fn iter(&self) -> hash_map::Iter<Key<'i>, Value<'i>> {
        self.map.iter()
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
            Value::Entity(entity) => entity.hash(state),
            Value::Function(function) => Rc::as_ptr(function).hash(state),
        }
    }
}

impl<'i> PartialEq for Entity<'i> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.map, &other.map)
            || self.map.len() == other.map.len()
                && self
                    .map
                    .iter()
                    .all(|(k, v)| other.map.get(k).map_or(false, |v2| v == v2))
    }
}

impl<'i> Eq for Entity<'i> {}

impl<'i> PartialOrd for Entity<'i> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self == other {
            Some(Ordering::Equal)
        } else {
            Rc::as_ptr(&self.map).partial_cmp(&Rc::as_ptr(&other.map))
        }
    }
}

impl<'i> Ord for Entity<'i> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl<'i> Hash for Entity<'i> {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        Rc::as_ptr(&self.map).hash(state)
    }
}

impl<'a, 'i> IntoIterator for &'a Entity<'i> {
    type Item = (&'a Key<'i>, &'a Value<'i>);
    type IntoIter = hash_map::Iter<'a, Key<'i>, Value<'i>>;
    fn into_iter(self) -> Self::IntoIter {
        self.map.iter()
    }
}

impl<'i> AsRef<Key<'i>> for Key<'i> {
    fn as_ref(&self) -> &Key<'i> {
        self
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
