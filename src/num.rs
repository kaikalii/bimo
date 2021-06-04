use std::{
    cmp::*,
    fmt,
    hash::{Hash, Hasher},
    ops::*,
};

#[derive(Clone, Copy)]
pub enum Num {
    Int(i64),
    Real(f64),
}

impl From<i64> for Num {
    fn from(i: i64) -> Self {
        Num::Int(i)
    }
}

impl From<f64> for Num {
    fn from(r: f64) -> Self {
        Num::Real(r)
    }
}

impl Default for Num {
    fn default() -> Self {
        Num::Int(0)
    }
}

macro_rules! bin_assign {
    ($trait:ident, $method:ident) => {
        impl $trait for Num {
            fn $method(&mut self, other: Self) {
                match (&mut *self, other) {
                    (Num::Int(a), Num::Int(b)) => $trait::$method(a, b),
                    (Num::Int(a), Num::Real(b)) => {
                        let mut a = *a as f64;
                        $trait::$method(&mut a, b);
                        *self = Num::Real(a);
                    }
                    (Num::Real(a), Num::Int(b)) => $trait::$method(a, b as f64),
                    (Num::Real(a), Num::Real(b)) => $trait::$method(a, b),
                }
            }
        }
    };
}

bin_assign!(AddAssign, add_assign);
bin_assign!(SubAssign, sub_assign);
bin_assign!(MulAssign, mul_assign);
bin_assign!(DivAssign, div_assign);
bin_assign!(RemAssign, rem_assign);

macro_rules! bin_op {
    ($trait:ident, $method:ident, $assign_trait:ident, $assign_method:ident) => {
        impl $trait for Num {
            type Output = Self;
            fn $method(mut self, other: Self) -> Self::Output {
                $assign_trait::$assign_method(&mut self, other);
                self
            }
        }
    };
}

bin_op!(Add, add, AddAssign, add_assign);
bin_op!(Sub, sub, SubAssign, sub_assign);
bin_op!(Mul, mul, MulAssign, mul_assign);
bin_op!(Div, div, DivAssign, div_assign);
bin_op!(Rem, rem, RemAssign, rem_assign);

impl Neg for Num {
    type Output = Self;
    fn neg(self) -> Self::Output {
        match self {
            Num::Int(i) => Num::Int(-i),
            Num::Real(r) => Num::Real(-r),
        }
    }
}

fn f64_eq(a: f64, b: f64) -> bool {
    a.is_nan() && b.is_nan() || a == b
}

fn f64_cmp(a: f64, b: f64) -> Ordering {
    if a.is_nan() {
        if b.is_nan() {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    } else if b.is_nan() {
        Ordering::Less
    } else {
        a.partial_cmp(&b).unwrap()
    }
}

impl PartialEq for Num {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Num::Int(a), Num::Int(b)) => a == b,
            (Num::Int(a), Num::Real(b)) => f64_eq(*a as f64, *b),
            (Num::Real(a), Num::Int(b)) => f64_eq(*a, *b as f64),
            (Num::Real(a), Num::Real(b)) => f64_eq(*a, *b),
        }
    }
}

impl Eq for Num {}

impl PartialOrd for Num {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(match (self, other) {
            (Num::Int(a), Num::Int(b)) => return a.partial_cmp(b),
            (Num::Int(a), Num::Real(b)) => f64_cmp(*a as f64, *b),
            (Num::Real(a), Num::Int(b)) => f64_cmp(*a, *b as f64),
            (Num::Real(a), Num::Real(b)) => f64_cmp(*a, *b),
        })
    }
}

impl Ord for Num {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl Hash for Num {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        (match self {
            Num::Int(i) => *i as f64,
            Num::Real(r) => *r,
        })
        .to_bits()
        .hash(state)
    }
}

impl fmt::Debug for Num {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Num::Int(i) => i.fmt(f),
            Num::Real(r) => r.fmt(f),
        }
    }
}

impl fmt::Display for Num {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Num::Int(i) => i.fmt(f),
            Num::Real(r) => r.fmt(f),
        }
    }
}
