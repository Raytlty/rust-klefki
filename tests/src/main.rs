#![feature(trait_alias)]
use std::any::{Any, TypeId};
use std::cmp::PartialEq;
use std::fmt::Debug;

pub struct Group<'a> {
    x: &'a dyn Any,
    y: &'a dyn Any,
}

pub struct SecGroup {
    x: Box<dyn Field>,
    y: Box<dyn Field>,
}

trait Field {
    fn inverse() -> Self
    where
        Self: Sized;
    fn sec_inverse() -> Self
    where
        Self: Sized;
    fn op(&self, rhs: &dyn Any) -> Self
    where
        Self: Sized;
    fn sec_op(&self, rhs: &dyn Any) -> Self
    where
        Self: Sized;
}

trait ConstP {
    const P: i32 = 9627i32;
}

#[derive(Clone, Debug, PartialEq)]
struct FiniteField {
    value: i32,
}

impl ConstP for FiniteField {}

impl Field for FiniteField {
    fn inverse() -> Self {
        FiniteField {
            value: FiniteField::P,
        }
    }

    fn sec_inverse() -> Self {
        FiniteField {
            value: -FiniteField::P,
        }
    }

    fn op(&self, rhs: &dyn Any) -> Self {
        if rhs.type_id() == TypeId::of::<i32>() {
            let res = rhs
                .downcast_ref::<i32>()
                .expect("op downcast_ref to i32 failed");
            FiniteField {
                value: self.value + res,
            }
        } else if rhs.type_id() == TypeId::of::<FiniteField>() {
            let res = rhs
                .downcast_ref::<FiniteField>()
                .expect("op downcast_ref to FiniteField failed");
            FiniteField {
                value: self.value + res.value,
            }
        } else {
            unreachable!();
        }
    }

    fn sec_op(&self, rhs: &dyn Any) -> Self {
        if rhs.type_id() == TypeId::of::<i32>() {
            let res = rhs
                .downcast_ref::<i32>()
                .expect("op downcast_ref to i32 failed");
            FiniteField {
                value: self.value * res,
            }
        } else if rhs.type_id() == TypeId::of::<FiniteField>() {
            let res = rhs
                .downcast_ref::<FiniteField>()
                .expect("op downcast_ref to FiniteField failed");
            FiniteField {
                value: self.value * res.value,
            }
        } else {
            unreachable!();
        }
    }
}

use std::ops::{Add, Div, Mul, Sub};

impl Add for FiniteField {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        self.op(&rhs)
    }
}

fn from_any(x: &dyn Any) {
    println!("{:?}", x.type_id() == TypeId::of::<Group>());
}

fn from_any2(x: &dyn Any) {
    println!("{:?}", x.type_id() == TypeId::of::<FiniteField>());
}

fn main() {
    let a = FiniteField { value: 1 };
    let b = FiniteField { value: 2 };
    let g = Group {
        x: &FiniteField { value: 1 },
        y: &FiniteField { value: 2 },
    };

    from_any2(g.x);
    //let c: Box<dyn Field> = Box::new(FiniteField { value: 3 });
    //let raw = Box::into_raw(c);
    //unsafe {
    //println!("{:?}", raw.type_id());
    //println!("{:?}", TypeId::of::<FiniteField>());
    //}
    //println!("{:?}", TypeId::of::<Group>());
    //println!("{:?}", TypeId::of::<SecGroup>());
}
