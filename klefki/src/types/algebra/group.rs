use crate::constrant::{
    IntPrimitive, COMPLEX_PREC, SECP256K1_A, SECP256K1_B, SECP256K1_GX, SECP256K1_GY, SECP256K1_N,
    SECP256K1_P, SECP256R1_A, SECP256R1_B, SECP256R1_GX, SECP256R1_GY, SECP256R1_N, SECP256R1_P,
};
use crate::types::algebra::field::{FiniteFieldSecp256k1, FiniteFieldSecp256r1};
use crate::types::algebra::traits::{
    ConstA, ConstB, ConstN, ConstP, Field, Group, Identity, SecGroup, SecIdentity,
};
use rug::{ops::Pow, Assign, Complex, Float, Integer};
use std::any::{Any, TypeId};
use std::marker::PhantomData;

lazy_static! {
    static ref SECP256k1X: FiniteFieldSecp256k1 = FiniteFieldSecp256k1::new(SECP256K1_GX);
    static ref SECP256k1Y: FiniteFieldSecp256k1 = FiniteFieldSecp256k1::new(SECP256K1_GY);
    static ref SECP256r1X: FiniteFieldSecp256r1 = FiniteFieldSecp256r1::new(SECP256R1_GX);
    static ref SECP256r1Y: FiniteFieldSecp256r1 = FiniteFieldSecp256r1::new(SECP256R1_GY);
}

#[derive(Clone)]
pub struct EllipticCurveCyclicSubgroupSecp256k1 {
    x: Box<dyn Field>,
    y: Box<dyn Field>,
}

#[derive(Clone)]
pub struct EllipticCurveGroupSecp256k1 {
    x: Box<dyn Field>,
    y: Box<dyn Field>,
}

#[derive(Clone)]
pub struct JacobianGroupSecp256k1 {
    x: Box<dyn Field>,
    y: Box<dyn Field>,
}

#[derive(Clone)]
pub struct EllipticCurveGroupSecp256r1 {
    x: Box<dyn Field>,
    y: Box<dyn Field>,
}

#[derive(Clone)]
pub struct JacobianGroupSecp256r1 {
    x: Box<dyn Field>,
    y: Box<dyn Field>,
}

#[derive(Clone)]
pub struct EllipticCurveCyclicSubgroupSecp256r1 {
    x: Box<dyn Field>,
    y: Box<dyn Field>,
}

macro_rules! impl_const {
    () => {};
    (
        $structName:ident
        $impl_lt:tt
        $($trait_name: ident, $variable_name:ident, $trait_input:ident;)*
    ) => {
        $(
            impl<$impl_lt> $trait_name<$impl_lt> for $structName
            {
                const $variable_name: &$impl_lt str = $trait_input;
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
            x: Box::new(SECP256k1X.clone()),
            y: Box::new(SECP256k1Y.clone()),
        }
    }
}

impl EllipticCurveGroupSecp256r1 {
    fn G_p() -> EllipticCurveGroupSecp256r1 {
        EllipticCurveGroupSecp256r1 {
            x: Box::new(SECP256k1X.clone()),
            y: Box::new(SECP256k1Y.clone()),
        }
    }
}

pub(crate) mod cast_to_group {

    use super::{
        EllipticCurveCyclicSubgroupSecp256k1, EllipticCurveCyclicSubgroupSecp256r1,
        EllipticCurveGroupSecp256k1, EllipticCurveGroupSecp256r1, JacobianGroupSecp256k1,
        JacobianGroupSecp256r1,
    };
    use crate::types::algebra::field::cast_to_field::RegisterField;
    use std::any::{Any, TypeId};

    pub enum RegisterGroup {
        V1(EllipticCurveGroupSecp256k1),
        V2(EllipticCurveGroupSecp256r1),
        V3(EllipticCurveCyclicSubgroupSecp256k1),
        V4(EllipticCurveCyclicSubgroupSecp256r1),
        V5(JacobianGroupSecp256k1),
        V6(JacobianGroupSecp256r1),
    }

    impl RegisterGroup {
        pub fn into_field(&self) -> (RegisterField, RegisterField) {
            match self {
                RegisterGroup::V1(group) => (
                    RegisterField::from_field_boxed(&group.x),
                    RegisterField::from_field_boxed(&group.y),
                ),
                RegisterGroup::V2(group) => (
                    RegisterField::from_field_boxed(&group.x),
                    RegisterField::from_field_boxed(&group.y),
                ),
                RegisterGroup::V3(group) => (
                    RegisterField::from_field_boxed(&group.x),
                    RegisterField::from_field_boxed(&group.y),
                ),
                RegisterGroup::V4(group) => (
                    RegisterField::from_field_boxed(&group.x),
                    RegisterField::from_field_boxed(&group.y),
                ),
                RegisterGroup::V5(group) => (
                    RegisterField::from_field_boxed(&group.x),
                    RegisterField::from_field_boxed(&group.y),
                ),
                RegisterGroup::V6(group) => (
                    RegisterField::from_field_boxed(&group.x),
                    RegisterField::from_field_boxed(&group.y),
                ),
                _ => unreachable!(),
            }
        }
        pub fn from_any(x: &dyn Any) -> RegisterGroup {
            if TypeId::of::<EllipticCurveGroupSecp256k1>() == x.type_id() {
                RegisterGroup::V1(
                    x.downcast_ref::<EllipticCurveGroupSecp256k1>()
                        .expect(
                            "RegisterGroup downcast_ref from EllipticCurveGroupSecp256k1 Failed",
                        )
                        .clone(),
                )
            } else if TypeId::of::<EllipticCurveGroupSecp256r1>() == x.type_id() {
                RegisterGroup::V2(
                    x.downcast_ref::<EllipticCurveGroupSecp256r1>()
                        .expect(
                            "RegisterGroup downcast_ref from EllipticCurveGroupSecp256r1 Failed",
                        )
                        .clone(),
                )
            } else if TypeId::of::<EllipticCurveCyclicSubgroupSecp256k1>() == x.type_id() {
                RegisterGroup::V3(
                   x.downcast_ref::<EllipticCurveCyclicSubgroupSecp256k1>()
                        .expect(
                            "RegisterGroup downcast_ref from EllipticCurveCyclicSubgroupSecp256r1 Failed",
                        )
                        .clone()
                )
            } else if TypeId::of::<EllipticCurveCyclicSubgroupSecp256r1>() == x.type_id() {
                RegisterGroup::V4(
                    x.downcast_ref::<EllipticCurveCyclicSubgroupSecp256r1>()
                        .expect(
                            "RegisterGroup downcast_ref from EllipticCurveCyclicSubgroupSecp256r1 Failed",
                        )
                        .clone()
                )
            } else if TypeId::of::<JacobianGroupSecp256k1>() == x.type_id() {
                RegisterGroup::V5(
                    x.downcast_ref::<JacobianGroupSecp256k1>()
                        .expect("RegisterGroup downcast_ref from JacobianGroupSecp256k1 Failed")
                        .clone(),
                )
            } else {
                RegisterGroup::V6(
                    x.downcast_ref::<JacobianGroupSecp256r1>()
                        .expect("RegisterGroup downcast_ref from JacobianGroupSecp256r1 Failed")
                        .clone(),
                )
            }
        }
    }
}

macro_rules! elliptic_curve_group {
    ($structName: ident) => {
        impl Group for $structName {
            fn inverse(&self) -> Self {
                $structName {
                    x: self.x.clone(),
                    y: -self.y.clone(),
                }
            }

            fn op(&self, g: &dyn Any) -> Self {
                let group = RegisterGroup::from_any(g);
                let x1 = RegisterField::from_field_boxed(self.x);
                let y1 = RegisterField::from_field_boxed(self.y);
                let (x2, y2) = group.into_field();
            }
        }
    };
}
