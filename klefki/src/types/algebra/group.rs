use crate::constrant::{
    IntPrimitive, COMPLEX_PREC, SECP256K1_A, SECP256K1_B, SECP256K1_N, SECP256K1_P,
};
use crate::types::algebra::field::FiniteField;
use crate::types::algebra::traits::{
    ConstA, ConstB, ConstN, ConstP, Field, Group, Identity, ParamField, SecGroup, SecIdentity,
};
use rug::{ops::Pow, Assign, Complex, Float, Integer};
use std::marker::PhantomData;

pub struct EllipticCurveCyclicSubgroupSecp256k1<T>
where
    T: ParamField,
{
    x: T,
    y: T,
    _marker: PhantomData<T>,
}

impl<T> ConstA for EllipticCurveCyclicSubgroupSecp256k1<T>
where
    T: ParamField,
{
    const A: i32 = SECP256K1_A;
}

impl<T> ConstB for EllipticCurveCyclicSubgroupSecp256k1<T>
where
    T: ParamField,
{
    const B: i32 = SECP256K1_B;
}

impl<'a, T> ConstN<'a> for EllipticCurveCyclicSubgroupSecp256k1<T>
where
    T: ParamField,
{
    const N: &'a str = SECP256K1_N;
}

macro_rules! elliptic_curve_group {
    ($structName: ident, $fieldStruct: ident) => {
        impl<$fieldStruct> Group for $structName<$fieldStruct> {
            fn inverse(&self) -> Self {
                $structName {
                    x: self.x.clone(),
                    y: -self.y.clone(),
                }
            }

            fn op(&self, g: &impl ParamField) -> Self {}
        }
    };
}
