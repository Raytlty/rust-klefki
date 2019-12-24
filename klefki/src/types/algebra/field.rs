use crate::constrant::{IntPrimitive, COMPLEX_PREC, SECP256K1_P};
use crate::types::algebra::{ConstP, Field, Group, Identity};
use rug::{ops::Pow, Assign, Complex, Float, Integer};
use std::any::{Any, TypeId};
use std::cmp::{Ord, PartialEq, PartialOrd};
use std::ops::{Add, Div, Mul, Neg, Sub};

pub struct FiniteFieldSecp256k1 {
    pub value: Complex,
}

pub struct FiniteFieldCyclicSecp256k1 {
    pub value: Complex,
}

impl<'a> ConstP<'a> for FiniteFieldSecp256k1 {
    const P: &'a str = SECP256K1_P;
}

impl<'a> ConstP<'a> for FiniteFieldCyclicSecp256k1 {
    const P: &'a str = SECP256K1_P;
}

impl Field for FiniteFieldSecp256k1 {}
impl Field for FiniteFieldCyclicSecp256k1 {}
impl Group for FiniteFieldSecp256k1 {}
impl Group for FiniteFieldCyclicSecp256k1 {}

impl FiniteFieldSecp256k1 {
    pub fn new(input: &str) -> Self {
        FiniteFieldSecp256k1 {
            value: Integer::from_str_radix(input, 16).expect("Cannot parse from string")
                + Complex::new(COMPLEX_PREC),
        }
    }
}

impl FiniteFieldCyclicSecp256k1 {
    pub fn new(input: &str) -> Self {
        FiniteFieldCyclicSecp256k1 {
            value: Integer::from_str_radix(input, 16).expect("Cannot parse from string")
                + Complex::new(COMPLEX_PREC),
        }
    }
}

macro_rules! identity_finitefield {
    ($structName: ident) => {
        impl Identity for $structName {
            #[inline]
            fn identity() -> Self {
                $structName {
                    value: Integer::from(0)
                        % Integer::from_str_radix($structName::P, 16)
                            .expect("Cannot parse from string")
                        + Complex::new(COMPLEX_PREC),
                }
            }
        }
    };
}

macro_rules! sec_identity_finitefield {
    ($structName: ident) => {
        impl $structName {
            #[inline]
            fn sec_identity() -> Self {
                $structName {
                    value: Integer::from(1)
                        % Integer::from_str_radix($structName::P, 16)
                            .expect("Cannot parse from string")
                        + Complex::new(COMPLEX_PREC),
                }
            }
        }
    };
}

macro_rules! inverse_finitefield {
    ($structName: ident) => {
        impl $structName {
            #[inline]
            fn inverse(&self) -> Self {
                $structName {
                    value: Integer::from_str_radix($structName::P, 16)
                        .expect("Cannot parse from string")
                        - self.value.clone()
                        + Complex::new(COMPLEX_PREC),
                }
            }
        }
    };
}

macro_rules! sec_inverse_finitefield {
    ($structName: ident) => {
        impl $structName {
            #[inline]
            fn sec_inverse(&self) -> Self {
                let base1 = Integer::from(1) + Complex::new(COMPLEX_PREC);
                let temp = self.value.clone();
                let (ref a, ref b) = base1.into_real_imag();
                let (ref c, ref d) = temp.into_real_imag();
                let real = (Float::with_val(COMPLEX_PREC, a * c)
                    + Float::with_val(COMPLEX_PREC, b * d))
                    / (Float::with_val(COMPLEX_PREC, c.pow(2))
                        + Float::with_val(COMPLEX_PREC, d.pow(2)));
                let imag = (Float::with_val(COMPLEX_PREC, b * c)
                    - Float::with_val(COMPLEX_PREC, a * d))
                    / (Float::with_val(COMPLEX_PREC, c.pow(2))
                        + Float::with_val(COMPLEX_PREC, d.pow(2)));
                $structName {
                    value: Complex::with_val(COMPLEX_PREC, (real, imag)),
                }
            }
        }
    };
}

macro_rules! mod_finitefield {
    ($structName: ident) => {
        impl $structName {
            #[inline]
            fn do_mod(&self, a: &dyn Any, b: &Integer) -> Complex {
                if TypeId::of::<Complex>() == a.type_id() {
                    let a = a
                        .downcast_ref::<Complex>()
                        .expect("do_mod downcast_ref to Complex Failed")
                        .clone();
                    let (ref real, ref imag) = a.into_real_imag();
                    let real = Float::with_val(
                        COMPLEX_PREC,
                        (real - Float::with_val(COMPLEX_PREC, real / b)),
                    );
                    let imag = Float::with_val(
                        COMPLEX_PREC,
                        (imag - Float::with_val(COMPLEX_PREC, imag / b)),
                    );
                    Complex::with_val(COMPLEX_PREC, (real, imag))
                } else if TypeId::of::<Integer>() == a.type_id() {
                    let a = a
                        .downcast_ref::<Integer>()
                        .expect("do_mod downcast_ref to Integer Failed");
                    Complex::new(COMPLEX_PREC) + Integer::from(a % b)
                } else {
                    unreachable!();
                }
            }
        }
    };
}

macro_rules! op_finitefield {
    ($structName: ident) => {
        impl $structName {
            fn do_op(&self, g: &dyn Any) -> Complex {
                let ng: $structName = if g.type_id() == TypeId::of::<IntPrimitive>() {
                    let g = g.downcast_ref::<IntPrimitive>().expect("Parse Error");
                    let c = Complex::new(COMPLEX_PREC) + g.to_integer();
                    $structName { value: c }
                } else if g.type_id() == TypeId::of::<Complex>() {
                    let g = g.downcast_ref::<Complex>().expect("Parse Error");
                    $structName { value: g.clone() }
                } else {
                    unreachable!();
                };
                let a = self.value.clone() + ng.value;
                let b =
                    Integer::from_str_radix($structName::P, 16).expect("Cannot parse from string");
                self.do_mod(&a, &b)
            }
        }
    };
}

macro_rules! sec_op_finitefield {
    ($structName: ident) => {
        impl $structName {
            fn sec_op(&self, g: &dyn Any) -> Complex {
                let ng: $structName = if g.type_id() == TypeId::of::<IntPrimitive>() {
                    let g = g.downcast_ref::<IntPrimitive>().expect("Parse Error");
                    let c = Complex::new(COMPLEX_PREC) + g.to_integer();
                    $structName { value: c }
                } else if g.type_id() == TypeId::of::<Complex>() {
                    let g = g.downcast_ref::<Complex>().expect("Parse Error");
                    $structName { value: g.clone() }
                } else {
                    unreachable!();
                };
                let a = self.value.clone() * ng.value;
                let b =
                    Integer::from_str_radix($structName::P, 16).expect("Cannot parse from string");
                self.do_mod(&a, &b)
            }
        }
    };
}

identity_finitefield!(FiniteFieldSecp256k1);
identity_finitefield!(FiniteFieldCyclicSecp256k1);
sec_identity_finitefield!(FiniteFieldSecp256k1);
sec_identity_finitefield!(FiniteFieldCyclicSecp256k1);
inverse_finitefield!(FiniteFieldSecp256k1);
inverse_finitefield!(FiniteFieldCyclicSecp256k1);
sec_inverse_finitefield!(FiniteFieldSecp256k1);
sec_inverse_finitefield!(FiniteFieldCyclicSecp256k1);
mod_finitefield!(FiniteFieldSecp256k1);
mod_finitefield!(FiniteFieldCyclicSecp256k1);
op_finitefield!(FiniteFieldSecp256k1);
op_finitefield!(FiniteFieldCyclicSecp256k1);
sec_op_finitefield!(FiniteFieldSecp256k1);
sec_op_finitefield!(FiniteFieldCyclicSecp256k1);
