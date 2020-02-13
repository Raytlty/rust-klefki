use crate::algebra::{
    field::{
        FiniteFieldCyclicSecp256k1, FiniteFieldCyclicSecp256r1, FiniteFieldSecp256k1,
        FiniteFieldSecp256r1,
    },
    group::{
        EllipticCurveCyclicSubgroupSecp256k1, EllipticCurveCyclicSubgroupSecp256r1,
        EllipticCurveGroupSecp256k1, EllipticCurveGroupSecp256r1, JacobianGroupSecp256k1,
        JacobianGroupSecp256r1,
    },
    traits::{Field, Identity},
};
use rug::{Complex, Integer};
use std::any::{Any, TypeId};
use std::ops::{Add, Div, Mul, Neg, Sub};

#[derive(Debug)]
pub struct InCompleteField<T> {
    value: T,
}

impl<T> InCompleteField<T> {
    pub fn new(x: T) -> Self {
        InCompleteField { value: x }
    }
}

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

macro_rules! register_field_partialeq {
    ($Big:ty; $($Re: ty)*) => {
        impl PartialEq<$Big> for $Big {
            #[inline]
            fn eq(&self, other: &$Big) -> bool {
                let lhs = self.into_inner();
                let rhs = other.into_inner();
                lhs == rhs
            }
        }

        $(
            impl PartialEq<$Big> for $Re {
                fn eq(&self, other: &$Big) -> bool {
                    let inner = other.into_inner();
                    inner.imag().is_zero() && inner.real().eq(self)
                }
            }

            impl PartialEq<$Re> for $Big {
                fn eq(&self, other: &$Re) -> bool {
                    let inner = self.into_inner();
                    inner.imag().is_zero() && inner.real().eq(other)
                }
            }
        )*
    };
}

register_field_partialeq!(
    RegisterField;
    i8 i16 i32 i128 isize
    u8 u16 u32 u128 usize
    f32 f64
);

impl Add for RegisterField {
    type Output = InCompleteField<Complex>;
    fn add(self, other: Self) -> Self::Output {
        let v: Complex = match other {
            RegisterField::V1(f) => f.value(),
            RegisterField::V2(f) => f.value(),
            RegisterField::V3(f) => f.value(),
            RegisterField::V4(f) => f.value(),
        };
        match self {
            RegisterField::V1(f) => f.op(&v),
            RegisterField::V2(f) => f.op(&v),
            RegisterField::V3(f) => f.op(&v),
            RegisterField::V4(f) => f.op(&v),
        }
    }
}

impl Div for RegisterField {
    type Output = InCompleteField<Complex>;
    fn div(self, other: Self) -> Self::Output {
        let signed = match other {
            RegisterField::V1(f) => {
                FiniteFieldSecp256k1::type_name(&f.value) == String::from("Complex")
            }
            RegisterField::V2(f) => {
                FiniteFieldSecp256r1::type_name(&f.value) == String::from("Complex")
            }
            RegisterField::V3(f) => {
                FiniteFieldCyclicSecp256k1::type_name(&f.value) == String::from("Complex")
            }
            RegisterField::V4(f) => {
                FiniteFieldCyclicSecp256r1::type_name(&f.value) == String::from("Complex")
            }
        };
        if signed {
            match self {
                RegisterField::V1(f) => f.true_div(),
                RegisterField::V2(f) => f.true_div(),
                RegisterField::V3(f) => f.true_div(),
                RegisterField::V4(f) => f.true_div(),
            }
        } else {
            unreachable!();
        }
    }
}

impl Sub for RegisterField {
    type Output = InCompleteField<Complex>;
    fn sub(self, other: Self) -> Self::Output {
        let version = other.version();
        let inverse = match other {
            RegisterField::V1(f) => f.inverse(),
            RegisterField::V2(f) => f.inverse(),
            RegisterField::V3(f) => f.inverse(),
            RegisterField::V4(f) => f.inverse(),
        };
        let inverse: Complex = RegisterField::from_incomplete(inverse, Some(version)).into_inner();
        match self {
            RegisterField::V1(f) => f.op(&inverse),
            RegisterField::V2(f) => f.op(&inverse),
            RegisterField::V3(f) => f.op(&inverse),
            RegisterField::V4(f) => f.op(&inverse),
        }
    }
}

impl Mul for RegisterField {
    type Output = InCompleteField<Complex>;
    fn mul(self, other: Self) -> Self::Output {
        self.add(other)
    }
}

impl Neg for RegisterField {
    type Output = InCompleteField<Complex>;
    fn neg(self) -> Self::Output {
        match self {
            RegisterField::V1(field) => field.inverse(),
            RegisterField::V2(field) => field.inverse(),
            RegisterField::V3(field) => field.inverse(),
            RegisterField::V4(field) => field.inverse(),
        }
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

    pub fn mat_mul<T>(&self, x: T) -> Self
    where
        T: Into<Integer>,
    {
        match self {
            RegisterField::V1(field) => RegisterField::V1(field.mat_mul(x.into())),
            RegisterField::V2(field) => RegisterField::V2(field.mat_mul(x.into())),
            RegisterField::V3(field) => RegisterField::V3(field.mat_mul(x.into())),
            RegisterField::V4(field) => RegisterField::V4(field.mat_mul(x.into())),
        }
    }

    pub fn pow<T>(&self, x: T) -> Self
    where
        T: Into<Integer>,
    {
        match self {
            RegisterField::V1(field) => RegisterField::V1(field.pow(x.into())),
            RegisterField::V2(field) => RegisterField::V2(field.pow(x.into())),
            RegisterField::V3(field) => RegisterField::V3(field.pow(x.into())),
            RegisterField::V4(field) => RegisterField::V4(field.pow(x.into())),
        }
    }

    pub fn from_incomplete(item: InCompleteField<Complex>, version: Option<i8>) -> Self {
        let version = version.unwrap_or(1);
        if version == 1 {
            RegisterField::V1(FiniteFieldSecp256k1::from(item))
        } else if version == 2 {
            RegisterField::V2(FiniteFieldSecp256r1::from(item))
        } else if version == 3 {
            RegisterField::V3(FiniteFieldCyclicSecp256k1::from(item))
        } else {
            RegisterField::V4(FiniteFieldCyclicSecp256r1::from(item))
        }
    }

    pub fn version(&self) -> i8 {
        match self {
            RegisterField::V1(_) => 1,
            RegisterField::V2(_) => 2,
            RegisterField::V3(_) => 3,
            RegisterField::V4(_) => 4,
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
                        .expect("RegisterField downcast_ref from FiniteFieldCyclicSecp256k1 Failed")
                        .clone();
                    RegisterField::V3(_field)
                } else {
                    let _field = x
                        .downcast_ref::<FiniteFieldCyclicSecp256r1>()
                        .expect("RegisterField downcast_ref from FiniteFieldCyclicSecp256r1 Failed")
                        .clone();
                    RegisterField::V4(_field)
                }
            } else {
                unreachable!();
            }
        }
    }

    pub fn from_field_boxed(x: &Box<dyn Field>) -> Self {
        if x.name() == String::from("FiniteFieldSecp256k1") {
            RegisterField::V1(FiniteFieldSecp256k1 { value: x.value() })
        } else if x.name() == String::from("FiniteFieldSecp256r1") {
            RegisterField::V2(FiniteFieldSecp256r1 { value: x.value() })
        } else if x.name() == String::from("FiniteFieldCyclicSecp256k1") {
            RegisterField::V3(FiniteFieldCyclicSecp256k1 { value: x.value() })
        } else {
            RegisterField::V4(FiniteFieldCyclicSecp256r1 { value: x.value() })
        }
    }
}

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
            _ => unreachable!(),
        }
    }

    pub fn into_field2(&self) -> (RegisterField, RegisterField, RegisterField) {
        match self {
            RegisterGroup::V5(group) => (
                RegisterField::from_field_boxed(&group.x),
                RegisterField::from_field_boxed(&group.y),
                RegisterField::from_field_boxed(&group.z),
            ),
            RegisterGroup::V6(group) => (
                RegisterField::from_field_boxed(&group.x),
                RegisterField::from_field_boxed(&group.y),
                RegisterField::from_field_boxed(&group.z),
            ),
            _ => unreachable!(),
        }
    }

    pub fn version(&self) -> i8 {
        match self {
            RegisterGroup::V1(_) => 1,
            RegisterGroup::V2(_) => 2,
            RegisterGroup::V3(_) => 3,
            RegisterGroup::V4(_) => 4,
            RegisterGroup::V5(_) => 5,
            RegisterGroup::V6(_) => 6,
        }
    }

    pub fn from_any(x: &dyn Any) -> RegisterGroup {
        if TypeId::of::<EllipticCurveGroupSecp256k1>() == x.type_id() {
            RegisterGroup::V1(
                x.downcast_ref::<EllipticCurveGroupSecp256k1>()
                    .expect("RegisterGroup downcast_ref from EllipticCurveGroupSecp256k1 Failed")
                    .clone(),
            )
        } else if TypeId::of::<EllipticCurveGroupSecp256r1>() == x.type_id() {
            RegisterGroup::V2(
                x.downcast_ref::<EllipticCurveGroupSecp256r1>()
                    .expect("RegisterGroup downcast_ref from EllipticCurveGroupSecp256r1 Failed")
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

impl PartialEq<RegisterGroup> for RegisterGroup {
    #[inline]
    fn eq(&self, other: &RegisterGroup) -> bool {
        let version1 = self.version();
        let version2 = other.version();
        if (version1 >= 5 && version2 < 4) || (version1 < 4 && version2 >= 5) {
            false
        } else if version1 < 4 && version2 < 4 {
            let (sx, sy) = self.into_field();
            let (gx, gy) = other.into_field();
            sx == gx && sy == gy
        } else {
            let (sx, sy, sz) = self.into_field2();
            let (gx, gy, gz) = other.into_field2();
            sx == gx && sy == gy && sz == gz
        }
    }
}
