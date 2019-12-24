use crate::constrant::{
    SECP256K1_Gx, SECP256K1_Gy, SECP256K1_A, SECP256K1_B, SECP256K1_N, SECP256K1_P,
};
use rug::Integer;
use std::cell::RefCell;
use std::cmp::{Ord, PartialEq, PartialOrd};
use std::ops::{Add, Div, Mul, Neg, Sub};

pub trait ConstP<'a> {
    const P: &'a str;
}

pub trait ConstA<'a> {
    const A: &'a str;
}

pub trait ConstB<'a> {
    const B: &'a str;
}

pub trait Functor: Add + Sub + Neg + Mul + Div + GeneralOp
where
    Self: Sized,
{
}

impl<T> Functor for T where
    T: Add<Output = T>
        + Sub<Output = T>
        + Neg<Output = T>
        + Mul<Output = T>
        + Div<Output = T>
        + GeneralOp<Rhs = T, Output = T>
{
}

pub trait Groupid:
    Ord
    + PartialEq
    + PartialOrd
    + GeneralOp<Rhs = Self, Output = Self>
    + Add<Output = Self>
    + Mul<Output = Self>
where
    Self: Sized,
{
}

pub trait SemiGroup: Groupid
where
    Self: Sized,
{
}

pub trait Monoid: SemiGroup + Not + Pow + MatMul
where
    Self: Sized,
{
}

// Like Marker
pub trait Group {
    fn inner() -> SealedPrimitive
    where
        Self: Sized,
    {
        SealedPrimitive::default()
    }
}
pub trait Field: Group {}

pub trait Pow<Rhs = Self, Mod = Self, Output = Self> {
    fn pow(&self, rhs: Rhs, mode: Mod) -> Output;
}

pub trait Not {
    fn not(&self) -> bool;
}

pub trait MatMul<Rhs = Self, Output = Self> {
    type RHS;
    type Output;
    fn mat_mul(&self, rhs: Rhs) -> Output;
}

pub trait Xor<Rhs = Self, Output = Self> {
    fn xor(&self, rhs: Rhs) -> Output;
}

pub trait Invert {
    fn invert(&self) -> Self;
}

pub trait GeneralOp {
    type Rhs;
    type Output;
    fn op(&self, g: Self::Rhs) -> Self::Output;
}

pub trait Identity {
    fn identity() -> Self;
}

pub trait GeneralGroup: Monoid + Sub<Output = Self> + Neg<Output = Self>
where
    Self: Sized,
{
    fn inverse(&self) -> Box<dyn Group>;
}

pub trait GeneralField: GeneralGroup + Pow + Invert
where
    Self: Sized,
{
    fn sec_op(&self, rhs: Box<dyn Field>) -> Box<dyn Field>;
    fn sec_inverse(&self) -> Box<dyn Field>;
}

pub struct SealedPrimitive {
    N: RefCell<Option<Integer>>,
    A: RefCell<Option<Integer>>,
    B: RefCell<Option<Integer>>,
    P: RefCell<Option<Integer>>,
    G: RefCell<Option<Box<dyn Group>>>,
}

impl Default for SealedPrimitive {
    fn default() -> Self {
        let N = SECP256K1_N;
        let A = SECP256K1_A;
        let B = SECP256K1_B;
        let P = SECP256K1_P;
        SealedPrimitive::from_str_and_int(N, P, A, B, None)
    }
}

impl SealedPrimitive {
    pub fn from_str(
        N: &'static str,
        A: &'static str,
        B: &'static str,
        P: &'static str,
        G: Option<Box<dyn Group>>,
    ) -> Self {
        let n = Integer::from_str_radix(N, 16).expect("Cannot parse from string");
        let a = Integer::from_str_radix(A, 16).expect("Cannot parse from string");
        let b = Integer::from_str_radix(B, 16).expect("Cannot parse from string");
        let p = Integer::from_str_radix(P, 16).expect("Cannot parse from string");
        SealedPrimitive {
            A: RefCell::new(Some(a)),
            B: RefCell::new(Some(b)),
            N: RefCell::new(Some(n)),
            P: RefCell::new(Some(p)),
            G: RefCell::new(G),
        }
    }

    pub fn from_str_and_int(
        N: &'static str,
        P: &'static str,
        A: i32,
        B: i32,
        G: Option<Box<dyn Group>>,
    ) -> Self {
        let n = Integer::from_str_radix(N, 16).expect("Cannot parse from string");
        let p = Integer::from_str_radix(P, 16).expect("Cannot parse from string");
        let a = Integer::from(A);
        let b = Integer::from(B);
        SealedPrimitive {
            A: RefCell::new(Some(a)),
            B: RefCell::new(Some(b)),
            N: RefCell::new(Some(n)),
            P: RefCell::new(Some(p)),
            G: RefCell::new(G),
        }
    }

    pub fn new() -> Self {
        SealedPrimitive::default()
    }
}
