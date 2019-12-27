use crate::constrant::{
    IntPrimitive, COMPLEX_PREC, SECP256K1_A, SECP256K1_B, SECP256K1_GX, SECP256K1_GY, SECP256K1_N,
    SECP256K1_P, SECP256R1_A, SECP256R1_B, SECP256R1_GX, SECP256R1_GY, SECP256R1_N, SECP256R1_P,
};
use crate::types::algebra::field::FiniteFieldSecp256k1;
use crate::types::algebra::traits::{
    ConstA, ConstB, ConstN, ConstP, Field, Group, Identity, SecGroup, SecIdentity,
};
use rug::{ops::Pow, Assign, Complex, Float, Integer};
use std::marker::PhantomData;

pub struct EllipticCurveCyclicSubgroupSecp256k1 {
    x: Box<dyn Field>,
    y: Box<dyn Field>,
}

pub struct EllipticCurveGroupSecp256k1 {
    x: Box<dyn Field>,
    y: Box<dyn Field>,
}

pub struct JacobianGroupSecp256k1 {
    x: Box<dyn Field>,
    y: Box<dyn Field>,
}

pub struct EllipticCurveGroupSecp256r1 {
    x: Box<dyn Field>,
    y: Box<dyn Field>,
}

pub struct JacobianGroupSecp256r1 {
    x: Box<dyn Field>,
    y: Box<dyn Field>,
}

pub struct EllipticCurveCyclicSubgroupSecp256r1 {
    x: Box<dyn Field>,
    y: Box<dyn Field>,
}

macro_rules! impl_const {
    () => {};
    (
        $structName:ident
        $trait_lt:tt
        $($trait_name: ident, $variable_name:ident, $trait_input:ident;)*
    ) => {
        $(
            impl<$trait_lt> $trait_name<$trait_lt> for $structName {
                const $variable_name: &$trait_lt str = $trait_input;
            }
        )*
    };
}

impl_const!(
    EllipticCurveGroupSecp256k1
    'a
    ConstA, A, SECP256K1_A;
    ConstB, B, SECP256K1_B;
    ConstN, N, SECP256K1_N;
);

impl_const!(
    EllipticCurveCyclicSubgroupSecp256k1
    'a
    ConstA, A, SECP256K1_A;
    ConstB, B, SECP256K1_B;
    ConstN, N, SECP256K1_N;
);

impl_const!(
    JacobianGroupSecp256k1
    'a
    ConstA, A, SECP256K1_A;
    ConstB, B, SECP256K1_B;
);

impl_const!(
    EllipticCurveGroupSecp256r1
    'a
    ConstA, A, SECP256K1_A;
    ConstB, B, SECP256K1_B;
);

impl_const!(
    JacobianGroupSecp256r1
    'a
    ConstA, A, SECP256R1_A;
    ConstB, B, SECP256R1_B;
);

impl_const!(
    EllipticCurveCyclicSubgroupSecp256r1
    'a
    ConstA, A, SECP256R1_A;
    ConstB, B, SECP256R1_B;
    ConstN, N, SECP256R1_N;
);

impl EllipticCurveGroupSecp256k1 {
    fn G_p() -> EllipticCurveCyclicSubgroupSecp256k1 {
        EllipticCurveCyclicSubgroupSecp256k1 {
            x: Box::new(FiniteFieldSecp256k1::new(SECP256K1_GX)),
            y: Box::new(FiniteFieldSecp256k1::new(SECP256K1_GY)),
        }
    }
}

impl EllipticCurveGroupSecp256r1 {
    fn G_p() -> EllipticCurveGroupSecp256r1 {
        EllipticCurveGroupSecp256r1 {
            x: Box::new(FiniteFieldSecp256k1::new(SECP256R1_GX)),
            y: Box::new(FiniteFieldSecp256k1::new(SECP256R1_GY)),
        }
    }
}

mod cast_group {

    use super::{
        EllipticCurveCyclicSubgroupSecp256k1, EllipticCurveCyclicSubgroupSecp256r1,
        EllipticCurveGroupSecp256k1, EllipticCurveGroupSecp256r1, JacobianGroupSecp256k1,
        JacobianGroupSecp256r1,
    };
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

            //fn op(&self, g: &dyn Any) -> Self {}
        }
    };
}
