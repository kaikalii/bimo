use std::collections::HashMap;

use crate::{ast::FieldId, value::Value};

pub type BimoFn = fn(&mut Runtime);

pub struct Runtime {
    scopes: Vec<Scope>,
}

pub struct Scope {
    pub values: HashMap<FieldId, Value>,
}

impl Runtime {
    pub fn new() -> Self {
        Runtime { scopes: vec![] }
    }
}
