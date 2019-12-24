use crate::constrant::{
    IntPrimitive, COMPLEX_PREC, SECP256K1_A, SECP256K1_B, SECP256K1_N, SECP256K1_P,
};
use crate::types::algebra::{ConstA, ConstB, ConstN, ConstP, Field, Group, Identity, MatMul};

pub struct EllipticCurveCyclicSubgroupSecp256k1 {
    x: Box<dyn Group>,
    y: Box<dyn Group>,
    g: Box<dyn Group>,
}

impl ConstA for EllipticCurveCyclicSubgroupSecp256k1 {
    const A: i32 = SECP256K1_A;
}

impl ConstB for EllipticCurveCyclicSubgroupSecp256k1 {
    const B: i32 = SECP256K1_B;
}

impl<'a> ConstN<'a> for EllipticCurveCyclicSubgroupSecp256k1 {
    const N: &'a str = SECP256K1_N;
}

impl Field for EllipticCurveCyclicSubgroupSecp256k1 {}
impl Group for EllipticCurveCyclicSubgroupSecp256k1 {}
