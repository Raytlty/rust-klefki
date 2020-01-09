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

#[cfg(test)]
mod test {
    use super::{EllipticCurveGroupSecp256k1, FiniteFieldSecp256k1, MatMul, Pow};
    use crate::types::algebra::traits::Identity;

    #[test]
    fn test_mat_mul() {
        let g1 = EllipticCurveGroupSecp256k1::default();
        let f1 = FiniteFieldSecp256k1::new("2");
        let g_f = g1.mat_mul(&f1);

        let g2 = g1.clone() + g1.clone() + EllipticCurveGroupSecp256k1::identity();
        assert_eq!(g2 == g_f, true);
    }

    #[test]
    fn test_pow() {
        let g1 = EllipticCurveGroupSecp256k1::default();
        let f1 = FiniteFieldSecp256k1::new("2");
        let g_f = g1.pow(&f1);

        let g2 = g1.clone() + g1.clone() + EllipticCurveGroupSecp256k1::identity();
        assert_eq!(g2 == g_f, true);
    }
}
