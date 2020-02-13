use crate::constrant::{
    IntPrimitive, COMPLEX_PREC, SECP256K1_N, SECP256K1_P, SECP256R1_N, SECP256R1_P,
};
use crate::algebra::registers::{InCompleteField, RegisterField};
use crate::algebra::traits::{ConstP, Field, Identity, Not, SecIdentity};
use rug::{ops::Pow, Assign, Complex, Float, Integer};
use std::any::{Any, TypeId};
use std::ops::{Add, AddAssign, Div, Mul, Neg, Sub, SubAssign, MulAssign, DivAssign};

#[derive(Debug, Clone, PartialEq)]
pub struct FiniteFieldSecp256k1 {
    pub value: Complex,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FiniteFieldCyclicSecp256k1 {
    pub value: Complex,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FiniteFieldSecp256r1 {
    pub value: Complex,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FiniteFieldCyclicSecp256r1 {
    pub value: Complex,
}

impl<'a> ConstP<'a> for FiniteFieldSecp256k1 {
    const P: &'a str = SECP256K1_P;
}

impl<'a> ConstP<'a> for FiniteFieldCyclicSecp256k1 {
    const P: &'a str = SECP256K1_N;
}

impl<'a> ConstP<'a> for FiniteFieldSecp256r1 {
    const P: &'a str = SECP256R1_P;
}

impl<'a> ConstP<'a> for FiniteFieldCyclicSecp256r1 {
    const P: &'a str = SECP256R1_N;
}

macro_rules! field_trait_implement {
    ($Struct: ident) => {

        impl Default for $Struct {
            fn default() -> Self {
                let p = $Struct::P;
                $Struct::new(p)
            }
        }

        impl From<$Struct> for Integer {
            fn from(field: $Struct) -> Integer {
                match field.value.real().to_integer() {
                    Some(i) => i,
                    None => unreachable!()
                }
            }
        }

        impl From<Integer> for $Struct {
            fn from(int: Integer) -> $Struct {
                $Struct {
                    value: Complex::new(COMPLEX_PREC) + int
                }
            }
        }

        impl $Struct {
            #[inline]
            pub fn new(input: &str) -> Self {
                $Struct {
                    value: Integer::from_str_radix(input, 16).expect("Cannot parse from string")
                            + Complex::new(COMPLEX_PREC),
                }
            }

            pub fn scalar(&self, field: &dyn Field) -> Self {
                let value = field.value();
                let time = match value.real().to_integer() {
                    Some(i) => i,
                    None => unreachable!(),
                };
                let time: usize = time.to_usize().expect("Unwrap to usize failed");
                if time == 0 {
                    Self::identity()
                } else {
                    double_and_add!(time, self.clone(), Self::identity())
                }
            }

            pub fn mat_mul<T>(&self, x: T) -> Self
            where
                T: Into<Self>,
            {
                self.scalar(&x.into())
            }

            pub fn pow<T>(&self, x: T) -> Self
            where
            T: Into<Self>,
            {
                self.scalar(&x.into())
            }

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
                        real - Float::with_val(COMPLEX_PREC, real / b),
                    );
                    let imag = Float::with_val(
                        COMPLEX_PREC,
                        imag - Float::with_val(COMPLEX_PREC, imag / b),
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

            #[inline]
            pub fn true_div(&self) -> InCompleteField<Complex> {
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
                InCompleteField::new(Complex::with_val(COMPLEX_PREC, (real, imag)))
            }

            #[inline]
            pub fn type_name<T>(_: &T) -> String {
                let name = std::any::type_name::<T>()
                    .split("::")
                    .collect::<Vec<&str>>();
                format!("{}", name[name.len() - 1])
            }
        }

        impl Identity for $Struct {
            #[inline]
            fn identity() -> Self {
                $Struct {
                    value: Integer::from(0)
                        % Integer::from_str_radix($Struct::P, 16)
                            .expect("Cannot parse from string")
                        + Complex::new(COMPLEX_PREC),
                }
            }
        }

        impl SecIdentity for $Struct {
            #[inline]
            fn sec_identity() -> Self {
                $Struct {
                    value: Integer::from(1)
                        % Integer::from_str_radix($Struct::P, 16)
                            .expect("Cannot parse from string")
                        + Complex::new(COMPLEX_PREC),
                }
            }
        }

        impl Field for $Struct {
            #[inline]
            fn name(&self) -> String {
                let names = std::any::type_name::<$Struct>()
                    .split("::")
                    .collect::<Vec<&str>>();
                format!("{}", names[names.len() - 1])
            }

            #[inline]
            fn value(&self) -> Complex {
                self.value.clone()
            }

            #[inline]
            fn inverse(&self) -> InCompleteField<Complex> {
                let value = Integer::from_str_radix($Struct::P, 16)
                    .expect("Cannot parse from string")
                    - self.value.clone()
                    + Complex::new(COMPLEX_PREC);
                InCompleteField::new(value)
            }

            #[inline]
            fn sec_inverse(&self) -> InCompleteField<Complex> {
                if $Struct::type_name(&self.value) == String::from("Complex") {
                    self.true_div()
                } else {
                    unreachable!();
                }
            }

            #[inline]
            fn op(&self, g: &dyn Any) -> InCompleteField<Complex> {
                let ng: $Struct = if g.type_id() == TypeId::of::<IntPrimitive>() {
                    let g = g.downcast_ref::<IntPrimitive>().expect("Parse Error");
                    let c = Complex::new(COMPLEX_PREC) + g.to_integer();
                    $Struct { value: c }
                } else if g.type_id() == TypeId::of::<Complex>() {
                    let g = g.downcast_ref::<Complex>().expect("Parse Error");
                    $Struct { value: g.clone() }
                } else {
                    unreachable!();
                };
                let a = self.value.clone() + ng.value;
                let b =
                    Integer::from_str_radix($Struct::P, 16).expect("Cannot parse from string");
                let v: Complex = self.do_mod(&a, &b);
                InCompleteField::new(v)
            }

            #[inline]
            fn sec_op(&self, g: &dyn Any) -> InCompleteField<Complex> {
                let ng: $Struct = if g.type_id() == TypeId::of::<IntPrimitive>() {
                    let g = g.downcast_ref::<IntPrimitive>().expect("Parse Error");
                    let c = Complex::new(COMPLEX_PREC) + g.to_integer();
                    $Struct { value: c }
                } else if g.type_id() == TypeId::of::<Complex>() {
                    let g = g.downcast_ref::<Complex>().expect("Parse Error");
                    $Struct { value: g.clone() }
                } else {
                    unreachable!();
                };
                let a = self.value.clone() * ng.value;
                let b =
                    Integer::from_str_radix($Struct::P, 16).expect("Cannot parse from string");
                let v: Complex = self.do_mod(&a, &b);
                InCompleteField::new(v)
            }
        }

        //impl Not for $Struct {
        //fn not(&self) -> bool {
        //self != &$Struct::identity()
        //}
        //}
    };
}

field_trait_implement!(FiniteFieldSecp256k1);
field_trait_implement!(FiniteFieldCyclicSecp256k1);
field_trait_implement!(FiniteFieldSecp256r1);
field_trait_implement!(FiniteFieldCyclicSecp256r1);

arith_binary_self!(
    FiniteFieldSecp256k1,FiniteFieldSecp256k1;
    Add {
        add, 
        |lhs: FiniteFieldSecp256k1, rhs: FiniteFieldSecp256k1| {
            lhs.op(&rhs.value)
        }
    };
    AddAssign {add_assign};
    Sub {
        sub,
        |lhs: FiniteFieldSecp256k1, rhs: FiniteFieldSecp256k1| {
            let other = FiniteFieldSecp256k1::from(rhs.inverse());
            lhs.op(&other.value)
        }
    };
    SubAssign {sub_assign};
    Mul {
        mul,
        |lhs: FiniteFieldSecp256k1, rhs: FiniteFieldSecp256k1| {
            lhs.sec_op(&rhs.value)
        }
    };
    MulAssign {mul_assign};
    Div {
        div,
        |lhs: FiniteFieldSecp256k1, rhs: FiniteFieldSecp256k1| {
            let other = FiniteFieldSecp256k1::from(rhs.sec_inverse());
            lhs.sec_op(&other.value)
        }
    };
    DivAssign {div_assign};
);

arith_binary_self!(
    FiniteFieldSecp256r1,FiniteFieldSecp256r1;
    Add {
        add, 
        |lhs: FiniteFieldSecp256r1, rhs: FiniteFieldSecp256r1| {
            lhs.op(&rhs.value)
        }
    };
    AddAssign {add_assign};
    Sub {
        sub,
        |lhs: FiniteFieldSecp256r1, rhs: FiniteFieldSecp256r1| {
            let other = FiniteFieldSecp256r1::from(rhs.inverse());
            lhs.op(&other.value)
        }
    };
    SubAssign {sub_assign};
    Mul {
        mul,
        |lhs: FiniteFieldSecp256r1, rhs: FiniteFieldSecp256r1| {
            lhs.sec_op(&rhs.value)
        }
    };
    MulAssign {mul_assign};
    Div {
        div,
        |lhs: FiniteFieldSecp256r1, rhs: FiniteFieldSecp256r1| {
            let other = FiniteFieldSecp256r1::from(rhs.sec_inverse());
            lhs.sec_op(&other.value)
        }
    };
    DivAssign {div_assign};
);

arith_binary_self!(
    FiniteFieldCyclicSecp256k1,FiniteFieldCyclicSecp256k1;
    Add {
        add, 
        |lhs: FiniteFieldCyclicSecp256k1, rhs: FiniteFieldCyclicSecp256k1| {
            lhs.op(&rhs.value)
        }
    };
    AddAssign {add_assign};
    Sub {
        sub,
        |lhs: FiniteFieldCyclicSecp256k1, rhs: FiniteFieldCyclicSecp256k1| {
            let other = FiniteFieldCyclicSecp256k1::from(rhs.inverse());
            lhs.op(&other.value)
        }
    };
    SubAssign {sub_assign};
    Mul {
        mul,
        |lhs: FiniteFieldCyclicSecp256k1, rhs: FiniteFieldCyclicSecp256k1| {
            lhs.sec_op(&rhs.value)
        }
    };
    MulAssign {mul_assign};
    Div {
        div,
        |lhs: FiniteFieldCyclicSecp256k1, rhs: FiniteFieldCyclicSecp256k1| {
            let other = FiniteFieldCyclicSecp256k1::from(rhs.sec_inverse());
            lhs.sec_op(&other.value)
        }
    };
    DivAssign {div_assign};
);

arith_binary_self!(
    FiniteFieldCyclicSecp256r1,FiniteFieldCyclicSecp256r1;
    Add {
        add, 
        |lhs: FiniteFieldCyclicSecp256r1, rhs: FiniteFieldCyclicSecp256r1| {
            lhs.op(&rhs.value)
        }
    };
    AddAssign {add_assign};
    Sub {
        sub,
        |lhs: FiniteFieldCyclicSecp256r1, rhs: FiniteFieldCyclicSecp256r1| {
            let other = FiniteFieldCyclicSecp256r1::from(rhs.inverse());
            lhs.op(&other.value)
        }
    };
    SubAssign {sub_assign};
    Mul {
        mul,
        |lhs: FiniteFieldCyclicSecp256r1, rhs: FiniteFieldCyclicSecp256r1| {
            lhs.sec_op(&rhs.value)
        }
    };
    MulAssign {mul_assign};
    Div {
        div,
        |lhs: FiniteFieldCyclicSecp256r1, rhs: FiniteFieldCyclicSecp256r1| {
            let other = FiniteFieldCyclicSecp256r1::from(rhs.sec_inverse());
            lhs.sec_op(&other.value)
        }
    };
    DivAssign {div_assign};
);

arith_unary!(
    FiniteFieldSecp256k1, FiniteFieldSecp256k1;
    Neg {
        neg,
        |x: FiniteFieldSecp256k1| {
            x.inverse()
        }
    };
);

arith_unary!(
    FiniteFieldSecp256r1, FiniteFieldSecp256r1;
    Neg {
        neg,
        |x: FiniteFieldSecp256r1| {
            x.inverse()
        }
    };
);

arith_unary!(
    FiniteFieldCyclicSecp256k1, FiniteFieldCyclicSecp256k1;
    Neg {
        neg,
        |x: FiniteFieldCyclicSecp256k1| {
            x.inverse()
        }
    };
);

arith_unary!(
    FiniteFieldCyclicSecp256r1, FiniteFieldCyclicSecp256r1;
    Neg {
        neg,
        |x: FiniteFieldCyclicSecp256r1| {
            x.inverse()
        }
    };
);

#[cfg(test)]
mod test {
    use super::FiniteFieldSecp256k1;

    #[test]
    fn test_add() {
        let f1 = FiniteFieldSecp256k1::default();
        let f2 = FiniteFieldSecp256k1::default();
        let f3 = f1.clone() + &f2;
        let mut f1 = f1.clone();
        f1 += f2;
        assert_eq!(f3.value, f1.value);
    }

    #[test]
    fn test_sub() {
        let f1 = FiniteFieldSecp256k1::default();
        let f2 = FiniteFieldSecp256k1::default();
        let f3 = f1.clone() - &f2;
        let mut f1 = f1.clone();
        f1 -= f2;
        assert_eq!(f3.value, f1.value);
    }
}
