use crate::types::algebra::{
    field::{
        FiniteFieldCyclicSecp256k1, FiniteFieldCyclicSecp256r1, FiniteFieldSecp256k1,
        FiniteFieldSecp256r1,
    },
    group::{
        EllipticCurveCyclicSubgroupSecp256k1, EllipticCurveCyclicSubgroupSecp256r1,
        EllipticCurveGroupSecp256k1, EllipticCurveGroupSecp256r1, JacobianGroupSecp256k1,
        JacobianGroupSecp256r1,
    },
    traits::{MatMul, Pow},
};

macro_rules! arith_combat {
    ($Group: ty, $($Field: ident;)*) => { $(
        impl MatMul<$Field> for $Group {
            type Output = $Group;
            fn mat_mul(&self, rhs: &$Field) -> $Group {
                self.scalar(rhs)
            }
        }

        impl Pow<$Field> for $Group {
            type Output = $Group;
            fn pow(&self, rhs: &$Field) -> $Group {
                self.scalar(rhs)
            }
        }
    )*
    };
}

arith_combat!(
    EllipticCurveGroupSecp256k1,
    FiniteFieldSecp256k1;
    FiniteFieldSecp256r1;
    FiniteFieldCyclicSecp256k1;
    FiniteFieldCyclicSecp256r1;
);

arith_combat!(
    EllipticCurveGroupSecp256r1,
    FiniteFieldSecp256k1;
    FiniteFieldSecp256r1;
    FiniteFieldCyclicSecp256k1;
    FiniteFieldCyclicSecp256r1;
);

arith_combat!(
    EllipticCurveCyclicSubgroupSecp256k1,
    FiniteFieldSecp256k1;
    FiniteFieldSecp256r1;
    FiniteFieldCyclicSecp256k1;
    FiniteFieldCyclicSecp256r1;
);

arith_combat!(
    EllipticCurveCyclicSubgroupSecp256r1,
    FiniteFieldSecp256k1;
    FiniteFieldSecp256r1;
    FiniteFieldCyclicSecp256k1;
    FiniteFieldCyclicSecp256r1;
);

arith_combat!(
    JacobianGroupSecp256k1,
    FiniteFieldSecp256k1;
    FiniteFieldSecp256r1;
    FiniteFieldCyclicSecp256k1;
    FiniteFieldCyclicSecp256r1;
);

arith_combat!(
    JacobianGroupSecp256r1,
    FiniteFieldSecp256k1;
    FiniteFieldSecp256r1;
    FiniteFieldCyclicSecp256k1;
    FiniteFieldCyclicSecp256r1;
);
