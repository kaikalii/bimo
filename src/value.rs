#![allow(dead_code)]

use std::{
    collections::{HashMap, VecDeque},
    rc::Rc,
};

use crate::ast::{IdentId, TagId};

#[derive(Debug, Clone)]
pub enum Value {
    Nil,
    Bool(bool),
    Int(i64),
    Real(f64),
    Tag(TagId),
    String(String),
    List(Rc<VecDeque<Value>>),
    Entity(Rc<HashMap<Key, Value>>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Key {
    Field(IdentId),
    Int(i64),
    String(String),
}

impl Value {
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
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
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

impl Eq for Value {}
