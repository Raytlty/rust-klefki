use crate::constrant::{
    IntPrimitive, COMPLEX_PREC, SECP256K1_A, SECP256K1_B, SECP256K1_N, SECP256K1_P,
};
use crate::types::algebra::{ConstA, ConstB, ConstN, ConstP, Field, Group, Identity, MatMul};

pub struct EllipticCurveCyclicSubgroupSecp256k1 {
    x: Box<dyn Group>,
    y: Box<dyn Group>,
    g: Box<dyn Group>,
}

impl<'a> ConstA<'a> for EllipticCurveCyclicSubgroupSecp256k1 {
    const A: &'a str = SECP256K1_A;
}

impl EllipticCurveCyclicSubgroupSecp256k1 {
    pub fn new() {}
}

impl Field for EllipticCurveCyclicSubgroupSecp256k1 {}
impl Group for EllipticCurveCyclicSubgroupSecp256k1 {}
