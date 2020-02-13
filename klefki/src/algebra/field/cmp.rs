use crate::algebra::{
    field::{
        FiniteFieldCyclicSecp256k1, FiniteFieldCyclicSecp256r1, FiniteFieldSecp256k1,
        FiniteFieldSecp256r1,
    },
    traits::{Field, Identity, SecIdentity},
};
use crate::constrant::COMPLEX_PREC;
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
    ($St:ident; $($Re: ty)*) => { $(
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
