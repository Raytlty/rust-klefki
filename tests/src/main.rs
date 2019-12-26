#![feature(trait_alias)]
use std::any::{Any, TypeId};
use std::cmp::PartialEq;
use std::fmt::Debug;

trait SubField {}
struct SubFiniteField {}

impl SubField for SubFiniteField {}

trait Field {
    fn inverse() -> Self
    where
        Self: Sized;
    fn sec_inverse() -> Self
    where
        Self: Sized;
    //fn op(&self, rhs: &dyn ) -> Self
    //where
    //Self: Sized;
    //fn sec_op(&self, rhs: &dyn Any) -> Self
    //where
    //Self: Sized;
    fn op(&self, rhs: &dyn SubFiniteField) -> Self
    where
        Self: Sized;
    fn sec_op(&self, rhs: &dyn SubFiniteField) -> Self
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

    fn op(&self, rhs: &dyn SubField) -> Self {
         
    }

    fn sec_op(&self, rhs: &dyn SubField) -> Self {

    }

    //fn op(&self, rhs: &dyn Any) -> Self {
        //if rhs.type_id() == TypeId::of::<i32>() {
            //let res = rhs
                //.downcast_ref::<i32>()
                //.expect("op downcast_ref to i32 failed");
            //FiniteField {
                //value: self.value + res,
            //}
        //} else if rhs.type_id() == TypeId::of::<FiniteField>() {
            //let res = rhs
                //.downcast_ref::<FiniteField>()
                //.expect("op downcast_ref to FiniteField failed");
            //FiniteField {
                //value: self.value + res.value,
            //}
        //} else {
            //unreachable!();
        //}
    //}

    //fn sec_op(&self, rhs: &dyn Any) -> Self {
        //if rhs.type_id() == TypeId::of::<i32>() {
            //let res = rhs
                //.downcast_ref::<i32>()
                //.expect("op downcast_ref to i32 failed");
            //FiniteField {
                //value: self.value * res,
            //}
        //} else if rhs.type_id() == TypeId::of::<FiniteField>() {
            //let res = rhs
                //.downcast_ref::<FiniteField>()
                //.expect("op downcast_ref to FiniteField failed");
            //FiniteField {
                //value: self.value * res.value,
            //}
        //} else {
            //unreachable!();
        //}
    }
}

use std::ops::{Add, Div, Mul, Sub};

impl Add for FiniteField {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        self.op(&rhs)
    }
}

fn test_impl_trait_parameters(x: &impl Field<i32>) {
    //let x = x as &FiniteField;
    let y = x.value;
    println!("{}", y + 2);
}

fn main() {
    let a = FiniteField { value: 1 };
    test_impl_trait_parameters(&a);
}
