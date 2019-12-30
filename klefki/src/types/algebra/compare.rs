use crate::constrant::COMPLEX_PREC;
use crate::types::algebra::{
    field::{
        FiniteFieldCyclicSecp256k1, FiniteFieldCyclicSecp256r1, FiniteFieldSecp256k1,
        FiniteFieldSecp256r1,
    },
    traits::{Field, Identity, MatMul, Pow as FieldPow, SecIdentity},
};
use rug::{Complex, Float, Integer};
use std::ops::{Add, Div, Mul, Neg, Sub};

macro_rules! eq_re{
    ($Field1: ty, $Field2: ty) => {
        impl PartialEq<$Field1> for $Field2 {
            #[inline]
            fn eq(&self, other: &$Field1) -> bool {
                self.value.imag().eq(other.value.imag()) && self.value.real().eq(other.value.real())
            }
        }

        impl PartialEq<$Field2> for $Field1 {
            #[inline]
            fn eq(&self, other: &$Field2) -> bool {
                self.value.imag().eq(other.value.imag()) && self.value.real().eq(other.value.real())
            }
        }
    };
    ($St: ident; $($Re: ty)*) => { $(
        impl PartialEq<$Re> for $St {
            #[inline]
            fn eq(&self, other: &$Re) -> bool {
                self.value.imag().is_zero() && self.value.real().eq(other)
            }
        }

        impl PartialEq<$St> for $Re {
            #[inline]
            fn eq(&self, other: &$St) -> bool {
                other.value.imag().is_zero() && other.value.real().eq(self)
            }
        }

    )* };
}

macro_rules! primitive_cal {
    ($Field1: ty; $Field2: ty; $structName: ident) => {
        impl Add<$Field2> for $Field1 {
            type Output = Self;
            fn add(self, other: $Field2) -> Self::Output {
                self.op(&other.value)
            }
        }

        impl Sub<$Field2> for $Field1 {
            type Output = Self;
            fn sub(self, other: $Field2) -> Self::Output {
                let other = other.inverse();
                self.op(&other.value)
            }
        }

        impl Mul<$Field2> for $Field1 {
            type Output = Self;
            fn mul(self, other: $Field2) -> Self::Output {
                self.sec_op(&other.value)
            }
        }

        impl Div<$Field2> for $Field1 {
            type Output = Self;
            fn div(self, other: $Field2) -> Self::Output {
                let other = other.sec_inverse();
                self.sec_op(&other.value)
            }
        }

        impl FieldPow<$Field2> for $Field1 {
            type Output = Self;
            fn pow(&self, rhs: $Field2) -> Self::Output {
                let (real, _) = rhs.value.into_real_imag();
                let (identity, _) = $structName::identity().value.into_real_imag();
                let times = match real.to_integer() {
                    Some(i) => i,
                    None => unreachable!(),
                };
                let init = match identity.to_integer() {
                    Some(i) => i,
                    None => unreachable!(),
                };

                $structName {
                    value: Integer::from(init * times) + Complex::new(COMPLEX_PREC),
                }
            }
        }

        impl MatMul<$Field2> for $Field1 {
            type Output = Self;
            fn mat_mul(&self, rhs: $Field2) -> Self::Output {
                let (real, _) = rhs.value.into_real_imag();
                let (identity, _) = $structName::identity().value.into_real_imag();
                let times = match real.to_integer() {
                    Some(i) => i,
                    None => unreachable!(),
                };
                let init = match identity.to_integer() {
                    Some(i) => i,
                    None => unreachable!(),
                };

                $structName {
                    value: Integer::from(init * times) + Complex::new(COMPLEX_PREC),
                }
            }
        }
    };
}

eq_re!(
    FiniteFieldSecp256k1;
    i8 i16 i32 i128 isize
    u8 u16 u32 u128 usize
    f32 f64
);

eq_re!(
    FiniteFieldSecp256r1;
    i8 i16 i32 i128 isize
    u8 u16 u32 u128 usize
    f32 f64
);

eq_re!(
    FiniteFieldCyclicSecp256k1;
    i8 i16 i32 i128 isize
    u8 u16 u32 u128 usize
    f32 f64
);

eq_re!(
    FiniteFieldCyclicSecp256r1;
    i8 i16 i32 i128 isize
    u8 u16 u32 u128 usize
    f32 f64
);

eq_re!(FiniteFieldSecp256k1, FiniteFieldSecp256r1);
eq_re!(FiniteFieldSecp256k1, FiniteFieldCyclicSecp256k1);
eq_re!(FiniteFieldSecp256k1, FiniteFieldCyclicSecp256r1);
eq_re!(FiniteFieldSecp256r1, FiniteFieldCyclicSecp256k1);
eq_re!(FiniteFieldCyclicSecp256k1, FiniteFieldCyclicSecp256r1);

primitive_cal!(FiniteFieldSecp256k1; FiniteFieldSecp256r1; FiniteFieldSecp256k1);
primitive_cal!(FiniteFieldSecp256r1; FiniteFieldSecp256k1; FiniteFieldSecp256r1);

primitive_cal!(FiniteFieldSecp256k1; FiniteFieldCyclicSecp256k1; FiniteFieldSecp256k1);
primitive_cal!(FiniteFieldCyclicSecp256k1; FiniteFieldSecp256k1; FiniteFieldCyclicSecp256k1);

primitive_cal!(FiniteFieldSecp256k1; FiniteFieldCyclicSecp256r1; FiniteFieldSecp256k1);
primitive_cal!(FiniteFieldCyclicSecp256r1; FiniteFieldSecp256k1; FiniteFieldCyclicSecp256r1);

primitive_cal!(FiniteFieldSecp256r1; FiniteFieldCyclicSecp256k1; FiniteFieldSecp256r1);
primitive_cal!(FiniteFieldCyclicSecp256k1; FiniteFieldSecp256r1; FiniteFieldCyclicSecp256k1);

primitive_cal!(FiniteFieldSecp256r1; FiniteFieldCyclicSecp256r1; FiniteFieldSecp256r1);
primitive_cal!(FiniteFieldCyclicSecp256r1; FiniteFieldSecp256r1; FiniteFieldCyclicSecp256r1);

primitive_cal!(FiniteFieldCyclicSecp256k1; FiniteFieldCyclicSecp256r1; FiniteFieldCyclicSecp256k1);
primitive_cal!(FiniteFieldCyclicSecp256r1; FiniteFieldCyclicSecp256k1; FiniteFieldCyclicSecp256r1);

#[cfg(test)]
mod test {
    use super::{
        FiniteFieldCyclicSecp256k1, FiniteFieldCyclicSecp256r1, FiniteFieldSecp256k1,
        FiniteFieldSecp256r1,
    };

    #[test]
    fn compare0x001() {
        let f1 = FiniteFieldSecp256k1::default();
        let f2 = FiniteFieldSecp256r1::default();
        assert_eq!(f1 == f2, false);
    }

    #[test]
    fn compare0x002() {
        use crate::constrant::SECP256K1_P;
        let f1 = FiniteFieldSecp256k1::default();
        let f2 = FiniteFieldSecp256r1::new(SECP256K1_P);
        assert_eq!(f1 == f2, true);
    }
}
