use std::{
    cell::UnsafeCell,
    cmp::Ordering,
    collections::{vec_deque, VecDeque},
    fmt,
    hash::{Hash, Hasher},
    iter::FromIterator,
    ops::Index,
    rc::Rc,
};

use crate::value::Value;

type ListInner<'i> = VecDeque<Value<'i>>;

#[derive(Clone)]
pub enum List<'i> {
    Eager(Rc<ListInner<'i>>),
    Lazy(Rc<UnsafeCell<LazyList<'i>>>),
}

pub struct LazyList<'i> {
    iter: Box<dyn Iterator<Item = Value<'i>> + 'i>,
    cache: ListInner<'i>,
}

impl<'i> List<'i> {
    pub fn lazy<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Value<'i>> + 'i,
    {
        let iter = iter.into_iter();
        List::Lazy(Rc::new(UnsafeCell::new(LazyList {
            cache: if let (_, Some(max)) = iter.size_hint() {
                VecDeque::with_capacity(max)
            } else {
                VecDeque::new()
            },
            iter: Box::new(iter),
        })))
    }
    pub fn len(&self) -> Option<usize> {
        match self {
            List::Eager(list) => Some(list.len()),
            List::Lazy(list) => {
                let list = unsafe { &*list.get() };
                if let (_, Some(remaining)) = list.iter.size_hint() {
                    Some(list.cache.len() + remaining)
                } else {
                    None
                }
            }
        }
    }
    pub fn get(&self, index: usize) -> Option<&Value<'i>> {
        match self {
            List::Eager(list) => list.get(index),
            List::Lazy(list) => {
                let list = unsafe { &*list.get() };
                list.cache.get(index).or_else(|| self.iter().nth(index))
            }
        }
    }
    pub fn iter(&self) -> Iter<'i, '_> {
        match self {
            List::Eager(list) => Iter::Eager(list.iter()),
            List::Lazy(list) => Iter::Lazy(LazyIter { list, index: 0 }),
        }
    }
}

impl<'i> Index<usize> for List<'i> {
    type Output = Value<'i>;
    #[track_caller]
    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).unwrap_or_else(|| {
            panic!(
                "index out of bounds: the index is {} but the length is {}",
                index,
                self.len().unwrap_or(usize::MAX)
            )
        })
    }
}

impl<'i> PartialEq for List<'i> {
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other)
    }
}

impl<'i> Eq for List<'i> {}

impl<'i> PartialOrd for List<'i> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        for (a, b) in self.iter().zip(other) {
            match a.partial_cmp(b) {
                Some(Ordering::Equal) => (),
                non_eq => return non_eq,
            }
        }
        self.len()
            .unwrap_or(usize::MAX)
            .partial_cmp(&other.len().unwrap_or(usize::MAX))
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
        for val in self {
            val.hash(state);
        }
    }
}

impl<'i> fmt::Debug for List<'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

impl<'i> FromIterator<Value<'i>> for List<'i> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = Value<'i>>,
    {
        List::Eager(Rc::new(iter.into_iter().collect()))
    }
}

impl<'i, 'a> IntoIterator for &'a List<'i> {
    type Item = &'a Value<'i>;
    type IntoIter = Iter<'i, 'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub enum Iter<'i, 'a> {
    Eager(vec_deque::Iter<'a, Value<'i>>),
    Lazy(LazyIter<'i, 'a>),
}

pub struct LazyIter<'i, 'a> {
    list: &'a UnsafeCell<LazyList<'i>>,
    index: usize,
}

impl<'i, 'a> Iterator for Iter<'i, 'a> {
    type Item = &'a Value<'i>;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Iter::Eager(iter) => iter.next(),
            Iter::Lazy(iter) => {
                let list = unsafe { &mut *iter.list.get() };
                if iter.index >= list.cache.len() {
                    if let Some(val) = list.iter.next() {
                        list.cache.push_back(val.clone());
                        list.cache.back()
                    } else {
                        None
                    }
                } else {
                    iter.index += 1;
                    Some(&list.cache[iter.index])
                }
            }
        }
    }
}
