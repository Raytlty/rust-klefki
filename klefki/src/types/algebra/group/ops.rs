use crate::constrant::COMPLEX_PREC;
use crate::types::algebra::{
    field::{
        FiniteFieldCyclicSecp256k1, FiniteFieldCyclicSecp256r1, FiniteFieldSecp256k1,
        FiniteFieldSecp256r1,
    },
    group::{
        choose_field_from_version, EllipticCurveCyclicSubgroupSecp256k1,
        EllipticCurveCyclicSubgroupSecp256r1, EllipticCurveGroupSecp256k1,
        EllipticCurveGroupSecp256r1, JacobianGroupSecp256k1, JacobianGroupSecp256r1,
    },
    registers::{InCompleteField, RegisterField},
    traits::{MatMul, Pow, Xor},
};
use crate::{from_field_boxed, from_incomplete};
use rug::Complex;

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

        impl Xor<$Field> for $Group {
            type Output = $Group;
            fn xor(&self, rhs: &$Field) -> $Group {
                self.scalar(rhs)
            }
        }
    )*

        impl MatMul<RegisterField> for $Group {
            type Output = $Group;
            fn mat_mul(&self, rhs: &RegisterField) -> $Group {
                match rhs {
                    RegisterField::V1(field) => self.mat_mul(field),
                    RegisterField::V2(field) => self.mat_mul(field),
                    RegisterField::V3(field) => self.mat_mul(field),
                    RegisterField::V4(field) => self.mat_mul(field),
                }
            }
        }

        impl Pow<RegisterField> for $Group {
            type Output = $Group;
            fn pow(&self, rhs: &RegisterField) -> $Group {
                match rhs {
                    RegisterField::V1(field) => self.pow(field),
                    RegisterField::V2(field) => self.pow(field),
                    RegisterField::V3(field) => self.pow(field),
                    RegisterField::V4(field) => self.pow(field),
                }
            }
        }

        impl Xor<RegisterField> for $Group {
            type Output = $Group;
            fn xor(&self, rhs: &RegisterField) -> $Group {
                match rhs {
                    RegisterField::V1(field) => self.xor(field),
                    RegisterField::V2(field) => self.xor(field),
                    RegisterField::V3(field) => self.xor(field),
                    RegisterField::V4(field) => self.xor(field),
                }
            }
        }

    };
}

macro_rules! jcg2ecg {
    ($Jg: ty, $($Ecg: ty;)*) => { $(
        impl From<$Jg> for $Ecg {
            fn from(jg: $Jg) -> $Ecg {
                let (x, y, z) = (
                    from_field_boxed!(&jg.x),
                    from_field_boxed!(&jg.y),
                    from_field_boxed!(&jg.z),
                );
                let version = x.version();
                let rx = from_incomplete!(x * z.clone(), version).pow(2);
                let ry = from_incomplete!(y * z, version).pow(3);
                Self {
                    x: choose_field_from_version(rx.into_inner(), version),
                    y: choose_field_from_version(ry.into_inner(), version),
                }
            }
        }

        impl From<$Ecg> for $Jg {
            fn from(ecg: $Ecg) -> $Jg {
                let x = from_field_boxed!(&ecg.x);
                let versionx = x.version();
                Self {
                    x: ecg.x,
                    y: ecg.y,
                    z: choose_field_from_version(Complex::with_val(COMPLEX_PREC, (1, 0)), versionx)
                }
            }
        }

    )*
    };
}

jcg2ecg!(
    JacobianGroupSecp256k1,
    EllipticCurveGroupSecp256k1;
    EllipticCurveGroupSecp256r1;
    EllipticCurveCyclicSubgroupSecp256k1;
    EllipticCurveCyclicSubgroupSecp256r1;
);

jcg2ecg!(
    JacobianGroupSecp256r1,
    EllipticCurveGroupSecp256k1;
    EllipticCurveGroupSecp256r1;
    EllipticCurveCyclicSubgroupSecp256k1;
    EllipticCurveCyclicSubgroupSecp256r1;
);

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
