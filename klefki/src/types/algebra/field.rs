use crate::constrant::{
    IntPrimitive, COMPLEX_PREC, SECP256K1_N, SECP256K1_P, SECP256R1_N, SECP256R1_P,
};
use crate::types::algebra::traits::{ConstP, Field, Identity, Not, SecIdentity};
use rug::{ops::Pow, Assign, Complex, Float, Integer};
use std::any::{Any, TypeId};
use std::ops::{Add, Div, Mul, Neg, Sub};

#[derive(Debug)]
pub struct InCompleteField<T> {
    value: T,
}

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

impl FiniteFieldSecp256r1 {
    pub fn new(input: &str) -> Self {
        FiniteFieldSecp256r1 {
            value: Integer::from_str_radix(input, 16).expect("Cannot parse from string")
                + Complex::new(COMPLEX_PREC),
        }
    }
}

impl FiniteFieldCyclicSecp256r1 {
    pub fn new(input: &str) -> Self {
        FiniteFieldCyclicSecp256r1 {
            value: Integer::from_str_radix(input, 16).expect("Cannot parse from string")
                + Complex::new(COMPLEX_PREC),
        }
    }
}

impl Default for FiniteFieldSecp256k1 {
    fn default() -> Self {
        let p = FiniteFieldSecp256k1::P;
        FiniteFieldSecp256k1::new(p)
    }
}

impl Default for FiniteFieldCyclicSecp256k1 {
    fn default() -> Self {
        let p = FiniteFieldCyclicSecp256k1::P;
        FiniteFieldCyclicSecp256k1::new(p)
    }
}

impl Default for FiniteFieldSecp256r1 {
    fn default() -> Self {
        let p = FiniteFieldSecp256r1::P;
        FiniteFieldSecp256r1::new(p)
    }
}

impl Default for FiniteFieldCyclicSecp256r1 {
    fn default() -> Self {
        let p = FiniteFieldCyclicSecp256r1::P;
        FiniteFieldCyclicSecp256r1::new(p)
    }
}

macro_rules! field_trait_implement {
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
        }

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

        impl SecIdentity for $structName {
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

        impl Field for $structName {
            #[inline]
            fn name() -> String {
                let names = std::any::type_name::<$structName>()
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
                InCompleteField {
                    value: Integer::from_str_radix($structName::P, 16)
                        .expect("Cannot parse from string")
                        - self.value.clone()
                        + Complex::new(COMPLEX_PREC),
                }
            }

            #[inline]
            fn sec_inverse(&self) -> InCompleteField<Complex> {
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
                InCompleteField {
                    value: Complex::with_val(COMPLEX_PREC, (real, imag)),
                }
            }

            #[inline]
            fn op(&self, g: &dyn Any) -> InCompleteField<Complex> {
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
                let v: Complex = self.do_mod(&a, &b);
                InCompleteField { value: v }
            }

            #[inline]
            fn sec_op(&self, g: &dyn Any) -> InCompleteField<Complex> {
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
                let v: Complex = self.do_mod(&a, &b);
                InCompleteField { value: v }
            }
        }

        impl Add for $structName {
            type Output = InCompleteField<Complex>;
            fn add(self, other: Self) -> Self::Output {
                self.op(&other.value)
            }
        }

        impl Sub for $structName {
            type Output = InCompleteField<Complex>;
            fn sub(self, other: Self) -> Self::Output {
                let other = $structName::from(other.inverse());
                self.op(&other.value)
            }
        }

        impl Neg for $structName {
            type Output = InCompleteField<Complex>;
            fn neg(self) -> Self::Output {
                self.inverse()
            }
        }

        impl Mul for $structName {
            type Output = InCompleteField<Complex>;
            fn mul(self, other: Self) -> Self::Output {
                self.sec_op(&other.value)
            }
        }

        impl Div for $structName {
            type Output = InCompleteField<Complex>;
            fn div(self, other: Self) -> Self::Output {
                let other = $structName::from(other.sec_inverse());
                self.sec_op(&other.value)
            }
        }

        impl Not for $structName {
            fn not(&self) -> bool {
                self != &$structName::identity()
            }
        }
    };
}

pub(crate) mod cast_to_field {
    use super::{
        Complex, Field, FiniteFieldCyclicSecp256k1, FiniteFieldCyclicSecp256r1,
        FiniteFieldSecp256k1, FiniteFieldSecp256r1, InCompleteField,
    };
    use crate::types::algebra::traits::Identity;
    use std::any::{Any, TypeId};
    use std::ops::{Add, Div, Mul, Sub};

    macro_rules! from_incomplete_to_field {
        ($structName: ident) => {
            impl From<InCompleteField<Complex>> for $structName {
                fn from(item: InCompleteField<Complex>) -> $structName {
                    $structName { value: item.value }
                }
            }
        };
    }

    from_incomplete_to_field!(FiniteFieldSecp256k1);
    from_incomplete_to_field!(FiniteFieldSecp256r1);
    from_incomplete_to_field!(FiniteFieldCyclicSecp256k1);
    from_incomplete_to_field!(FiniteFieldCyclicSecp256r1);

    #[derive(Debug, Clone)]
    pub enum RegisterField {
        V1(FiniteFieldSecp256k1),
        V2(FiniteFieldSecp256r1),
        V3(FiniteFieldCyclicSecp256k1),
        V4(FiniteFieldCyclicSecp256r1),
    }

    impl PartialEq for RegisterField {
        fn eq(&self, other: &RegisterField) -> bool {
            let lhs = self.into_inner();
            let rhs = other.into_inner();
            lhs == rhs
        }
    }

    impl Add for RegisterField {
        type Output = InCompleteField<Complex>;
        fn add(self, other: Self) -> Self::Output {
            let v = self.into_inner() + other.into_inner();
            InCompleteField { value: v }
        }
    }

    impl Div for RegisterField {
        type Output = InCompleteField<Complex>;
        fn div(self, other: Self) -> Self::Output {
            let v = self.into_inner() / other.into_inner();
            InCompleteField { value: v }
        }
    }

    impl Sub for RegisterField {
        type Output = InCompleteField<Complex>;
        fn sub(self, other: Self) -> Self::Output {
            let v = self.into_inner() - other.into_inner();
            InCompleteField { value: v }
        }
    }

    impl Mul for RegisterField {
        type Output = InCompleteField<Complex>;
        fn mul(self, other: Self) -> Self::Output {
            let v = self.into_inner() * other.into_inner();
            InCompleteField { value: v }
        }
    }

    impl RegisterField {
        pub fn into_inner(&self) -> Complex {
            match self {
                RegisterField::V1(f) => f.value.clone(),
                RegisterField::V2(f) => f.value.clone(),
                RegisterField::V3(f) => f.value.clone(),
                RegisterField::V4(f) => f.value.clone(),
            }
        }

        pub fn identity_value(&self) -> Complex {
            match self {
                RegisterField::V1(_) => FiniteFieldSecp256k1::identity().value,
                RegisterField::V2(_) => FiniteFieldSecp256r1::identity().value,
                RegisterField::V3(_) => FiniteFieldCyclicSecp256k1::identity().value,
                RegisterField::V4(_) => FiniteFieldCyclicSecp256r1::identity().value,
            }
        }

        pub fn from_any(x: Box<dyn Any>) -> Self {
            unsafe {
                let ptr = Box::into_raw(x);
                if let Some(r) = ptr.as_ref() {
                    let x = r as &dyn Any;
                    if TypeId::of::<FiniteFieldSecp256k1>() == x.type_id() {
                        let _field = x
                            .downcast_ref::<FiniteFieldSecp256k1>()
                            .expect("RegisterField downcast_ref from FiniteFieldSecp256k1 Failed")
                            .clone();
                        RegisterField::V1(_field)
                    } else if TypeId::of::<FiniteFieldSecp256r1>() == x.type_id() {
                        let _field = x
                            .downcast_ref::<FiniteFieldSecp256r1>()
                            .expect("RegisterField downcast_ref from FiniteFieldSecp256r1 Failed")
                            .clone();
                        RegisterField::V2(_field)
                    } else if TypeId::of::<FiniteFieldCyclicSecp256k1>() == x.type_id() {
                        let _field = x
                            .downcast_ref::<FiniteFieldCyclicSecp256k1>()
                            .expect(
                                "RegisterField downcast_ref from FiniteFieldCyclicSecp256k1 Failed",
                            )
                            .clone();
                        RegisterField::V3(_field)
                    } else {
                        let _field = x
                            .downcast_ref::<FiniteFieldCyclicSecp256r1>()
                            .expect(
                                "RegisterField downcast_ref from FiniteFieldCyclicSecp256r1 Failed",
                            )
                            .clone();
                        RegisterField::V4(_field)
                    }
                } else {
                    unreachable!();
                }
            }
        }

        pub fn is_v1(&self) -> bool {
            match self {
                RegisterField::V1(_) => true,
                _ => false,
            }
        }

        pub fn is_v2(&self) -> bool {
            match self {
                RegisterField::V2(_) => true,
                _ => false,
            }
        }

        pub fn is_v3(&self) -> bool {
            match self {
                RegisterField::V3(_) => true,
                _ => false,
            }
        }

        pub fn is_v4(&self) -> bool {
            match self {
                RegisterField::V4(_) => true,
                _ => false,
            }
        }
    }
}

field_trait_implement!(FiniteFieldSecp256k1);
field_trait_implement!(FiniteFieldCyclicSecp256k1);
field_trait_implement!(FiniteFieldSecp256r1);
field_trait_implement!(FiniteFieldCyclicSecp256r1);
