use std::cmp::{Ord, PartialEq, PartialOrd};
use std::ops::{Add, Div, Mul, Neg, Sub};

pub trait Groupid: Add + Sub + Neg + Mul + Div + GeneralOp
where
    Self: Sized,
{
}

impl<T> Groupid for T where
    T: Add<Output = T>
        + Sub<Output = T>
        + Neg<Output = T>
        + Mul<Output = T>
        + Div<Output = T>
        + GeneralOp<RHS = T, Output = T>
{
}

pub trait Pow<RHS = Self> {
    type MOD;
    type Output;
    fn pow(&self, rhs: RHS, mode: Self::MOD) -> Self::Output;
}

pub trait Not {
    fn not(&self) -> bool;
}

pub trait MatMul {
    type RHS;
    type Output;
    fn mat_mul(&self, rhs: Self::RHS) -> Self::Output;
}

pub trait Xor {
    type RHS;
    type Output;
    fn xor(&self, rhs: Self::RHS) -> Self::Output;
}

pub trait GeneralOp {
    type Output;
    type RHS;
    fn op(&self, g: Self::RHS) -> Self::Output;
}

pub trait GeneralIdentity {
    type Output;
    fn identity(&self) -> Self::Output;
}

pub trait GeneralInverse {
    type Output;
    fn inverse(&self) -> Self::Output;
}

pub trait GeneralField {
    type Output;
    type RHS;
    fn sec_op(&self, rhs: Self::RHS) -> Self::Output;
    fn sec_inverse(&self) -> Self::Output;
    fn sec_identity(&self) -> Self::Output;
    fn invert(&self) -> Self::Output {
        self.sec_inverse()
    }
}
