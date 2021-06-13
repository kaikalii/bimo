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

impl<'i> Default for List<'i> {
    fn default() -> Self {
        List::new()
    }
}

impl<'i> List<'i> {
    pub fn new() -> Self {
        List {
            list: Rc::new(VecDeque::new()),
        }
    }
    pub fn with_capacity(capacity: usize) -> Self {
        List {
            list: Rc::new(VecDeque::with_capacity(capacity)),
        }
    }
    pub fn len(&self) -> usize {
        self.list.len()
    }
    pub fn push(&mut self, val: Value<'i>) {
        Rc::make_mut(&mut self.list).push_back(val);
    }
    pub fn get(&self, index: usize) -> Option<&Value<'i>> {
        self.list.get(index)
    }
    pub fn iter(&self) -> vec_deque::Iter<'_, Value<'i>> {
        self.list.iter()
    }
    pub fn split<const N: usize>(self) -> [Value<'i>; N]
    where
        [Value<'i>; N]: Default,
    {
        let mut array: [Value<'i>; N] = Default::default();
        for (item, value) in array.iter_mut().zip(self.into_iter()) {
            *item = value;
        }
        array
    }
}

#[macro_export]
macro_rules! bimo_list {
    ($($item:expr),* $(,)?) => {
        crate::value::Value::List(std::iter::empty()$(.chain(std::iter::once($item.into())))*.collect())
    };
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
