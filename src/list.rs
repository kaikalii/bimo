use std::{
    cmp::Ordering,
    collections::{vec_deque, VecDeque},
    fmt,
    hash::{Hash, Hasher},
    iter::FromIterator,
    rc::Rc,
};

use crate::value::Value;

#[derive(Clone)]
pub struct List<'i> {
    list: Rc<VecDeque<Value<'i>>>,
}

impl<'i> List<'i> {
    pub fn len(&self) -> usize {
        self.list.len()
    }
    pub fn get(&self, index: usize) -> Option<&Value<'i>> {
        self.list.get(index)
    }
    pub fn iter(&self) -> vec_deque::Iter<'_, Value<'i>> {
        self.list.iter()
    }
}

impl<'i> PartialEq for List<'i> {
    fn eq(&self, other: &Self) -> bool {
        self.list == other.list
    }
}

impl<'i> Eq for List<'i> {}

impl<'i> PartialOrd for List<'i> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.list.partial_cmp(&other.list)
    }
}

impl<'i> Ord for List<'i> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl<'i> Hash for List<'i> {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        self.list.hash(state);
    }
}

impl<'i> fmt::Debug for List<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.list.fmt(f)
    }
}

impl<'i> FromIterator<Value<'i>> for List<'i> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = Value<'i>>,
    {
        List {
            list: Rc::new(iter.into_iter().collect()),
        }
    }
}

impl<'i, 'a> IntoIterator for &'a List<'i> {
    type Item = &'a Value<'i>;
    type IntoIter = vec_deque::Iter<'a, Value<'i>>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'i> IntoIterator for List<'i> {
    type Item = Value<'i>;
    type IntoIter = vec_deque::IntoIter<Value<'i>>;
    fn into_iter(self) -> Self::IntoIter {
        match Rc::try_unwrap(self.list) {
            Ok(list) => list,
            Err(list) => (*list).clone(),
        }
        .into_iter()
    }
}
