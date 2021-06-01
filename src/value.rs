#![allow(dead_code)]

use std::{
    collections::{HashMap, VecDeque},
    rc::Rc,
};

use crate::ast::{FieldId, TagId};

#[derive(Debug, Clone)]
pub enum Value {
    Nil,
    Bool(bool),
    Int(i64),
    Real(f64),
    Tag(TagId),
    String(String),
    List(Rc<VecDeque<Value>>),
    Entity(Rc<HashMap<Key, Value, seahash::State>>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Key {
    Field(FieldId),
    Int(i64),
    String(String),
}
