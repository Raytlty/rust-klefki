use crate::constrant::{COMPLEX_PREC, SECP256K1_P};
use crate::types::algebra::{constA, constB, constP, Field, GeneralField, SealedPrimitive};
use rug::{Assign, Complex, Integer};
use std::any::{Any, TypeId};
use std::cmp::{Ord, PartialEq, PartialOrd};
use std::ops::{Add, Div, Mul, Neg, Sub};

pub struct FiniteFieldSecp256k1 {
    pub value: Complex,
}

pub struct FiniteFieldCyclicSecp256k1 {
    pub value: Complex,
}

impl<'a> constP<'a> for FiniteFieldSecp256k1 {
    const P: &'a str = SECP256K1_P;
}

impl<'a> constP<'a> for FiniteFieldCyclicSecp256k1 {
    const P: &'a str = SECP256K1_P;
}

impl FiniteFieldSecp256k1 {
    pub fn new(input: &str) -> Self {
        FiniteFieldSecp256k1 {
            value: Integer::from_str_radix(input, 16).expect("Cannot parse from string")
                + Complex::new(COMPLEX_PREC),
        }
    }
}

impl FiniteFieldCyclicSecp256k1 {
    pub fn new(input: &str) -> Self {
        FiniteFieldCyclicSecp256k1 {
            value: Integer::from_str_radix(input, 16).expect("Cannot parse from string")
                + Complex::new(COMPLEX_PREC),
        }
    }
}
