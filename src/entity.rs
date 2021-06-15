use std::{
    cmp::Ordering,
    collections::{hash_map, HashMap},
    hash::{BuildHasher, Hash, Hasher},
    rc::Rc,
};

use seahash::SeaHasher;

use crate::value::Value;

#[derive(Clone, Default)]
pub struct HashState;

impl BuildHasher for HashState {
    type Hasher = SeaHasher;
    fn build_hasher(&self) -> Self::Hasher {
        SeaHasher::new()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Key<'i> {
    Tag(&'i str),
    Field(&'i str),
    Value(Value<'i>),
}

#[derive(Debug, Clone, Default)]
pub struct Entity<'i> {
    map: Rc<HashMap<Key<'i>, Value<'i>, HashState>>,
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
        self.try_get(key).unwrap_or(&Value::Nil)
    }
    pub fn try_get(&self, key: impl AsRef<Key<'i>>) -> Option<&Value<'i>> {
        self.map.get(key.as_ref())
    }
    pub fn set(&mut self, key: Key<'i>, val: Value<'i>) {
        let map = Rc::make_mut(&mut self.map);
        if let Value::Nil = val {
            map.remove(&key);
        } else {
            map.insert(key, val);
        }
    }
    pub fn entry(&mut self, key: Key<'i>) -> hash_map::Entry<Key<'i>, Value<'i>> {
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
