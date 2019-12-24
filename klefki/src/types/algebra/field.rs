use crate::constrant::{IntPrimitive, COMPLEX_PREC, SECP256K1_P};
use crate::types::algebra::{
    ConstA, ConstB, ConstP, Field, GeneralField, Identity, SealedPrimitive,
};
use rug::ops::Pow;
use rug::{Assign, Complex, Float, Integer};
use std::any::{Any, TypeId};
use std::cmp::{Ord, PartialEq, PartialOrd};
use std::ops::{Add, Div, Mul, Neg, Sub};

pub struct FiniteFieldSecp256k1 {
    pub value: Complex,
}

pub struct FiniteFieldCyclicSecp256k1 {
    pub value: Complex,
}

impl<'a> ConstP<'a> for FiniteFieldSecp256k1 {
    const P: &'a str = SECP256K1_P;
}

impl<'a> ConstP<'a> for FiniteFieldCyclicSecp256k1 {
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

identity_finitefield!(FiniteFieldSecp256k1, Identity);
identity_finitefield!(FiniteFieldCyclicSecp256k1, Identity);
sec_identity_finitefield!(FiniteFieldSecp256k1);
sec_identity_finitefield!(FiniteFieldCyclicSecp256k1);
inverse_finitefield!(FiniteFieldSecp256k1);
inverse_finitefield!(FiniteFieldCyclicSecp256k1);
sec_inverse_finitefield!(FiniteFieldSecp256k1);
sec_inverse_finitefield!(FiniteFieldCyclicSecp256k1);
mod_finitefield!(FiniteFieldSecp256k1);
mod_finitefield!(FiniteFieldCyclicSecp256k1);
op_finitefield!(FiniteFieldSecp256k1);
op_finitefield!(FiniteFieldCyclicSecp256k1);
