#![allow(dead_code)]

use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
    mem::discriminant,
    rc::Rc,
};

pub type FieldId = u64;
pub type TagId = u64;

#[derive(Debug, Clone)]
pub enum Value {
    Nil,
    Bool(bool),
    Int(i64),
    Real(f64),
    Tag(TagId),
    String(String),
    List(Rc<Vec<Value>>),
    Entity(Rc<HashMap<Key, Value, seahash::State>>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Key {
    Field(FieldId),
    Int(i64),
    String(String),
}

#[allow(clippy::derive_hash_xor_eq)]
impl Hash for Key {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        discriminant(self).hash(state);
        match self {
            Key::Field(id) => id.hash(state),
            Key::Int(i) => i.hash(state),
            Key::String(s) => s[..s.len().min(32)].hash(state),
        }
    }
}
