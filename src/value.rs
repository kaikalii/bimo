#![allow(dead_code)]

use std::{
    collections::{HashMap, VecDeque},
    hash::BuildHasher,
    rc::Rc,
};

use seahash::SeaHasher;

use crate::{
    ast::{IdentId, Items, Params, TagId},
    interpret::Scope,
};

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
    Int(i64),
    Real(f64),
    Tag(TagId),
    String(String),
    List(Rc<VecDeque<Value<'i>>>),
    Entity(Rc<HashMap<Key, Value<'i>, HashState>>),
    Function(Rc<Function<'i>>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Key {
    Field(IdentId),
    Tag(TagId),
    Int(i64),
    String(String),
}

impl<'i> Value<'i> {
    pub fn is_truthy(&self) -> bool {
        !matches!(self, Value::Nil | Value::Bool(false))
    }
    pub fn type_name(&self) -> &'static str {
        match self {
            Value::Nil => "nil",
            Value::Bool(_) => "bool",
            Value::Int(_) => "int",
            Value::Real(_) => "real",
            Value::Tag(_) => "tag",
            Value::String(_) => "string",
            Value::List(_) => "list",
            Value::Entity(_) => "entity",
            Value::Function(_) => "function",
        }
    }
}

impl<'i> PartialEq for Value<'i> {
    fn eq(&self, other: &Value<'i>) -> bool {
        match (self, other) {
            (Value::Nil, Value::Nil) => true,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Int(a), Value::Real(b)) => (*a as f64 - b).abs() < f64::EPSILON,
            (Value::Real(a), Value::Int(b)) => (a - *b as f64).abs() < f64::EPSILON,
            (Value::Real(a), Value::Real(b)) => (a - b).abs() < f64::EPSILON,
            (Value::String(a), Value::String(b)) => a == b,
            (Value::Tag(a), Value::Tag(b)) => a == b,
            (Value::List(a), Value::List(b)) => a == b,
            (Value::Entity(a), Value::Entity(b)) => {
                Rc::ptr_eq(a, b) || { a.iter().all(|(k, v)| b.get(k).map_or(false, |v2| v == v2)) }
            }
            _ => false,
        }
    }
}

impl<'i> Eq for Value<'i> {}

#[derive(Debug, Clone)]
pub struct Function<'i> {
    pub scope: Scope<'i>,
    pub params: Params<'i>,
    pub items: Items<'i>,
}
