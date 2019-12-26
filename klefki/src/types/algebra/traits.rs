use std::any::Any;

pub trait Identity {
    fn identity() -> Self;
}

pub trait SecIdentity {
    fn sec_identity() -> Self;
}

pub trait Field {
    fn inverse(&self) -> Self
    where
        Self: Sized;
    fn sec_inverse(&self) -> Self
    where
        Self: Sized;
    fn op(&self, g: &dyn Any) -> Self
    where
        Self: Sized;
    fn sec_op(&self, g: &dyn Any) -> Self
    where
        Self: Sized;
}

pub trait ParamField = Field + Pow + Not + MatMul;

pub trait Group {
    fn inverse(&self) -> Self
    where
        Self: Sized;
    fn op(&self, g: &dyn Field) -> Self
    where
        Self: Sized;
}

pub trait SecGroup {
    fn sec_inverse(&self) -> Self
    where
        Self: Sized;
    fn sec_op(&self, g: &dyn Field) -> Self
    where
        Self: Sized;
}

pub trait MatMul {
    fn mat_mul(&self, rhs: Self) -> Self;
}

pub trait Pow {
    fn pow(&self, rhs: Self) -> Self;
}

pub trait Not {
    fn not(&self) -> Self;
}

pub trait ConstP<'a> {
    const P: &'a str;
}

pub trait ConstA {
    const A: i32;
}

pub trait ConstB {
    const B: i32;
}

pub trait ConstN<'a> {
    const N: &'a str;
}
