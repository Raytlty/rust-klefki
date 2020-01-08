use crate::types::algebra::registers::InCompleteField;
use rug::Complex;
use std::any::Any;

pub trait Identity {
    fn identity() -> Self;
}

pub trait SecIdentity {
    fn sec_identity() -> Self;
}

pub trait FieldClone {
    fn clone_box(&self) -> Box<dyn Field>;
}

impl<T> FieldClone for T
where
    T: 'static + Field + Clone,
{
    fn clone_box(&self) -> Box<dyn Field> {
        Box::new(self.clone())
    }
}

impl Clone for Box<dyn Field> {
    fn clone(&self) -> Box<dyn Field> {
        self.clone_box()
    }
}

pub trait Field: FieldClone {
    fn inverse(&self) -> InCompleteField<Complex>;
    fn sec_inverse(&self) -> InCompleteField<Complex>;
    fn op(&self, g: &dyn Any) -> InCompleteField<Complex>;
    fn sec_op(&self, g: &dyn Any) -> InCompleteField<Complex>;
    fn name(&self) -> String;
    fn value(&self) -> Complex;
}

pub trait Group {
    fn inverse(&self) -> Self
    where
        Self: Sized;
    fn op(&self, g: &dyn Any) -> Self
    where
        Self: Sized;
}

pub trait SecGroup {
    fn sec_inverse(&self) -> Self
    where
        Self: Sized;
    fn sec_op(&self, g: &dyn Any) -> Self
    where
        Self: Sized;
}

pub trait MatMul<Rhs = Self> {
    type Output;
    fn mat_mul(&self, rhs: Rhs) -> Self::Output;
}

pub trait Pow<Rhs = Self> {
    type Output;
    fn pow(&self, rhs: Rhs) -> Self::Output;
}

pub trait Not {
    fn not(&self) -> bool;
}

pub trait ConstP<'a> {
    const P: &'a str;
}

pub trait ConstA<'a> {
    const A: &'a str;
}

pub trait ConstB<'a> {
    const B: &'a str;
}

pub trait ConstN<'a> {
    const N: &'a str;
}
