use crate::constrant::{
    IntPrimitive, COMPLEX_PREC, SECP256K1_A, SECP256K1_B, SECP256K1_GX, SECP256K1_GY, SECP256K1_N,
    SECP256K1_P, SECP256R1_A, SECP256R1_B, SECP256R1_GX, SECP256R1_GY, SECP256R1_N, SECP256R1_P,
};
use crate::types::algebra::field::{
    cast_to_field::RegisterField, FiniteFieldCyclicSecp256k1, FiniteFieldCyclicSecp256r1,
    FiniteFieldSecp256k1, FiniteFieldSecp256r1, InCompleteField,
};
use crate::types::algebra::traits::{
    ConstA, ConstB, ConstN, ConstP, Field, Group, Identity, SecGroup, SecIdentity,
};
use rug::{ops::Pow, Assign, Complex, Float, Integer};
use std::any::{Any, TypeId};
use std::marker::PhantomData;
use std::ops::{Add, Div, Mul, Neg, Sub};

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
    z: Box<dyn Field>,
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
    z: Box<dyn Field>,
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

impl EllipticCurveGroupSecp256k1 {
    pub fn new(x: Box<dyn Field>, y: Option<Box<dyn Field>>) -> Self {
        let y = y.unwrap_or(Box::new(FiniteFieldSecp256k1::new("0")));
        EllipticCurveGroupSecp256k1 { x, y }
    }
}

impl Default for EllipticCurveGroupSecp256k1 {
    fn default() -> Self {
        let x = Box::new(FiniteFieldSecp256k1::new("0"));
        let y = Box::new(FiniteFieldSecp256k1::new("0"));
        EllipticCurveGroupSecp256k1 { x, y }
    }
}

impl_const!(
    EllipticCurveCyclicSubgroupSecp256k1
    'a
    ConstA, A, SECP256K1_A;
    ConstB, B, SECP256K1_B;
    ConstN, N, SECP256K1_N;
);

impl EllipticCurveCyclicSubgroupSecp256k1 {
    pub fn new(x: Box<dyn Field>, y: Option<Box<dyn Field>>) -> Self {
        let y = y.unwrap_or(Box::new(FiniteFieldSecp256k1::new("0")));
        EllipticCurveCyclicSubgroupSecp256k1 { x, y }
    }
}

impl Default for EllipticCurveCyclicSubgroupSecp256k1 {
    fn default() -> Self {
        let x = Box::new(FiniteFieldSecp256k1::new("0"));
        let y = Box::new(FiniteFieldSecp256k1::new("0"));
        EllipticCurveCyclicSubgroupSecp256k1 { x, y }
    }
}

impl_const!(
    JacobianGroupSecp256k1
    'a
    ConstA, A, SECP256K1_A;
    ConstB, B, SECP256K1_B;
);

impl JacobianGroupSecp256k1 {
    pub fn new(x: Box<dyn Field>, y: Option<Box<dyn Field>>, z: Option<Box<dyn Field>>) -> Self {
        let y = y.unwrap_or(Box::new(FiniteFieldSecp256k1::new("0")));
        let z = z.unwrap_or(Box::new(FiniteFieldSecp256k1::new("0")));
        JacobianGroupSecp256k1 { x, y, z }
    }
}

impl Default for JacobianGroupSecp256k1 {
    fn default() -> Self {
        let x = Box::new(FiniteFieldSecp256k1::new("0"));
        let y = Box::new(FiniteFieldSecp256k1::new("0"));
        let z = Box::new(FiniteFieldSecp256k1::new("0"));
        JacobianGroupSecp256k1 { x, y, z }
    }
}

impl_const!(
    EllipticCurveGroupSecp256r1
    'a
    ConstA, A, SECP256K1_A;
    ConstB, B, SECP256K1_B;
);

impl EllipticCurveGroupSecp256r1 {
    pub fn new(x: Box<dyn Field>, y: Option<Box<dyn Field>>) -> Self {
        let y = y.unwrap_or(Box::new(FiniteFieldSecp256k1::new("0")));
        EllipticCurveGroupSecp256r1 { x, y }
    }
}

impl Default for EllipticCurveGroupSecp256r1 {
    fn default() -> Self {
        let x = Box::new(FiniteFieldSecp256k1::new("0"));
        let y = Box::new(FiniteFieldSecp256k1::new("0"));
        EllipticCurveGroupSecp256r1 { x, y }
    }
}

impl_const!(
    JacobianGroupSecp256r1
    'a
    ConstA, A, SECP256R1_A;
    ConstB, B, SECP256R1_B;
);

impl JacobianGroupSecp256r1 {
    pub fn new(x: Box<dyn Field>, y: Option<Box<dyn Field>>, z: Option<Box<dyn Field>>) -> Self {
        let y = y.unwrap_or(Box::new(FiniteFieldSecp256k1::new("0")));
        let z = z.unwrap_or(Box::new(FiniteFieldSecp256k1::new("0")));
        JacobianGroupSecp256r1 { x, y, z }
    }
}

impl Default for JacobianGroupSecp256r1 {
    fn default() -> Self {
        let x = Box::new(FiniteFieldSecp256k1::new("0"));
        let y = Box::new(FiniteFieldSecp256k1::new("0"));
        let z = Box::new(FiniteFieldSecp256k1::new("0"));
        JacobianGroupSecp256r1 { x, y, z }
    }
}

impl_const!(
    EllipticCurveCyclicSubgroupSecp256r1
    'a
    ConstA, A, SECP256R1_A;
    ConstB, B, SECP256R1_B;
    ConstN, N, SECP256R1_N;
);

impl EllipticCurveCyclicSubgroupSecp256r1 {
    pub fn new(x: Box<dyn Field>, y: Option<Box<dyn Field>>) -> Self {
        let y = y.unwrap_or(Box::new(FiniteFieldSecp256k1::new("0")));
        EllipticCurveCyclicSubgroupSecp256r1 { x, y }
    }
}

impl Default for EllipticCurveCyclicSubgroupSecp256r1 {
    fn default() -> Self {
        let x = Box::new(FiniteFieldSecp256k1::new("0"));
        let y = Box::new(FiniteFieldSecp256k1::new("0"));
        EllipticCurveCyclicSubgroupSecp256r1 { x, y }
    }
}

impl EllipticCurveGroupSecp256k1 {
    fn G_p() -> EllipticCurveCyclicSubgroupSecp256k1 {
        EllipticCurveCyclicSubgroupSecp256k1 {
            x: Box::new(SECP256k1X.clone()),
            y: Box::new(SECP256k1Y.clone()),
        }
    }
}

impl EllipticCurveCyclicSubgroupSecp256k1 {
    fn G_p() -> EllipticCurveCyclicSubgroupSecp256k1 {
        EllipticCurveCyclicSubgroupSecp256k1 {
            x: Box::new(SECP256k1X.clone()),
            y: Box::new(SECP256k1Y.clone()),
        }
    }
}

impl EllipticCurveGroupSecp256r1 {
    fn G_p() -> EllipticCurveCyclicSubgroupSecp256r1 {
        EllipticCurveCyclicSubgroupSecp256r1 {
            x: Box::new(SECP256r1X.clone()),
            y: Box::new(SECP256r1Y.clone()),
        }
    }
}

impl EllipticCurveCyclicSubgroupSecp256r1 {
    fn G_p() -> EllipticCurveCyclicSubgroupSecp256r1 {
        EllipticCurveCyclicSubgroupSecp256r1 {
            x: Box::new(SECP256r1X.clone()),
            y: Box::new(SECP256r1Y.clone()),
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
use cast_to_group::RegisterGroup;

fn choose_field_from_version(v: Complex, version: i8) -> Box<dyn Field> {
    if version == 1 {
        Box::new(FiniteFieldSecp256k1 { value: v })
    } else if version == 2 {
        Box::new(FiniteFieldSecp256r1 { value: v })
    } else if version == 3 {
        Box::new(FiniteFieldCyclicSecp256k1 { value: v })
    } else {
        Box::new(FiniteFieldCyclicSecp256r1 { value: v })
    }
}

macro_rules! elliptic_curve_group {
    ($structName: ident) => {
        impl Identity for $structName {
            fn identity() -> Self {
                $structName::default()
            }
        }

        impl PartialEq for $structName {
            fn eq(&self, other: &Self) -> bool {
                self.x.value() == other.x.value() && self.y.value() == other.y.value()
            }
        }

        impl Group for $structName {
            fn inverse(&self) -> Self {
                let x = RegisterField::from_field_boxed(&self.x);
                let y = RegisterField::from_field_boxed(&self.y);
                let versionx = x.version();
                let versiony = y.version();
                let y = RegisterField::from_incomplete(-y, Some(versiony));
                $structName {
                    x: choose_field_from_version(x.into_inner(), versionx),
                    y: choose_field_from_version(y.into_inner(), versiony),
                }
            }

            fn op(&self, g: &dyn Any) -> Self {
                let group = RegisterGroup::from_any(g);
                let x1 = RegisterField::from_field_boxed(&self.x);
                let y1 = RegisterField::from_field_boxed(&self.y);
                let (x2, y2) = group.into_field();

                let versionx = x1.version();
                let versiony = y1.version();

                // Next do the calculate
                let m: InCompleteField<Complex> = if x1 != x2 {
                    RegisterField::from_incomplete(y1.clone() - y2.clone(), Some(versiony))
                        / RegisterField::from_incomplete(x1.clone() - x2.clone(), Some(versionx))
                } else {
                    if y1 == RegisterField::from_incomplete(-y2, Some(versiony)) {
                        return $structName::identity();
                    }
                    let A = Integer::from_str_radix($structName::A, 16)
                        .expect("Parse ConstA Failed")
                        + Complex::new(COMPLEX_PREC);
                    let field3 = choose_field_from_version(
                        Complex::with_val(COMPLEX_PREC, (3, 0)),
                        versionx,
                    );
                    let field2 = choose_field_from_version(
                        Complex::with_val(COMPLEX_PREC, (2, 0)),
                        versionx,
                    );
                    let A = choose_field_from_version(A, versionx);

                    let field3 = RegisterField::from_field_boxed(&field3);
                    let field2 = RegisterField::from_field_boxed(&field2);
                    let A = RegisterField::from_field_boxed(&A);

                    let v1 = RegisterField::from_incomplete(field3 * x1.clone(), Some(versionx));
                    let v2 = RegisterField::from_incomplete(v1 * x1.clone(), Some(versionx));
                    let v3 = RegisterField::from_incomplete(v2 + A, Some(versionx));
                    let v4 = RegisterField::from_incomplete(field2 * y1.clone(), Some(versionx));
                    v3 / v4
                };

                let m = RegisterField::from_incomplete(m, Some(versionx));
                let rx: RegisterField = {
                    let v1 = RegisterField::from_incomplete(m.clone() * m.clone(), Some(versionx));
                    let v2 = RegisterField::from_incomplete(v1 - x1.clone(), Some(versionx));
                    let v3 = RegisterField::from_incomplete(v2 - x2.clone(), Some(versionx));
                    v3
                };
                let ry: RegisterField = {
                    let v1 =
                        RegisterField::from_incomplete(rx.clone() - x1.clone(), Some(versionx));
                    let v2 = RegisterField::from_incomplete(m.clone() * v1, Some(versionx));
                    let v3 = RegisterField::from_incomplete(y1.clone() + v2, Some(versionx));
                    v3
                };
                let ry = RegisterField::from_incomplete(-ry, Some(versionx));
                let rx_boxed = choose_field_from_version(rx.into_inner(), versionx);
                let ry_boxed = choose_field_from_version(ry.into_inner(), versiony);
                $structName {
                    x: rx_boxed,
                    y: ry_boxed,
                }
            }
        }

        impl Add for $structName {
            type Output = Self;
            fn add(self, other: Self) -> Self::Output {
                self.op(&other)
            }
        }

        impl Mul for $structName {
            type Output = Self;
            fn mul(self, other: Self) -> Self::Output {
                self + other
            }
        }

        impl Sub for $structName {
            type Output = Self;
            fn sub(self, other: Self) -> Self::Output {
                self.op(&other.inverse())
            }
        }

        impl Neg for $structName {
            type Output = Self;
            fn neg(self) -> Self::Output {
                self.inverse()
            }
        }
    };
}

macro_rules! cyclic_add_group {
    ($structName: ident) => {
        impl Identity for $structName {
            fn identity() -> Self {
                $structName::default()
            }
        }

        impl Group for $structName {
            fn inverse(&self) -> Self {
                let a: Complex = Integer::from(0)
                    % Integer::from_str_radix($structName::N, 16)
                        .expect("Cannot parse from string")
                    + Complex::new(COMPLEX_PREC);

                let rf: RegisterField = RegisterField::from_field_boxed(self.x);
                let version = rf.version();
                let b: Complex = rf.into_inner();

                let v = a * b;
                let rx_boxed = choose_field_from_version(v, version);

                $structName::new(rx_boxed, None)
            }

            fn op(&self, g: &dyn Any) -> Self {
                let group = RegisterGroup::from_any(g);
                let (x1, _) = group.into_field();
                let (x2, _) = RegisterField::from(self.x);

                let version = x2.version();
                let x1 = match x1.into_inner().real().to_integer() {
                    Some(i) => i,
                    None => unreachable!();
                };
                let x2 = match x2.into_inner().real().to_integer() {
                    Some(i) => i,
                    None => unreachable!();
                };
                let N = Integer::from_str_radix($structName::N, 16).expect("Parse from string failed");
                let (_, result) = (x1 + x2).div_rem(N);
                let rx_boxed = choose_field_from_version(result + Complex::new(COMPLEX_PREC), version);
                $structName::new(rx_boxed, None)
            }
        }

        impl $structName {
            pub fn pow(&self, item: &dyn Any) -> Self {
                let group = RegisterGroup::from_any(g);
                let (x1, _) = group.into_field();
                let (x2, _) = RegisterField::from(self.x);

                let version = x2.version();
                let x1 = match x1.into_inner().real().to_integer() {
                    Some(i) => i,
                    None => unreachable!();
                };
                let x2 = match x2.into_inner().real().to_integer() {
                    Some(i) => i,
                    None => unreachable!();
                };
                let N = Integer::from_str_radix($structName::N, 16).expect("Parse from string failed");
                let result = x2.secure_pow_mod(&x1, &N);
                let rx_boxed = choose_field_from_version(result + Complex::new(COMPLEX_PREC), version);
                $structName::new(rx_boxed, None)
            }
        }
    };
}

macro_rules! jacobian_group {
    ($structName: ident) => {
        impl Identity for $structName {
            fn identity() -> Self {
                $structName::default()
            }
        }

        impl PartialEq for $structName {
            fn eq(&self, other: &Self) -> bool {
                self.x.value() == other.x.value()
                    && self.y.value() == other.y.value()
                    && self.z.value() == other.z.value()
            }
        }

        impl $structName {
            fn double(&self, n: &dyn Any) -> Self {
                let group = RegisterGroup::from_any(n);
                let (x, y, z) = match group {
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
                };
                let version = x.version();
                let sx = RegisterField::from_field_boxed(&self.x).into_inner();
                let sy = RegisterField::from_field_boxed(&self.y).into_inner();
                let sz = RegisterField::from_field_boxed(&self.z).into_inner();

                let ysq: Complex = y.into_inner() * 2;
                let s: Complex = sx.clone() * 4 * ysq.clone();
                let A =
                    Integer::from_str_radix($structName::A, 16).expect("Parse from string failed");
                let m: Complex = (sx.clone() * 2) * 3 + (sz.clone() * 4) * A.clone();
                let nx: Complex = m.clone() * 2 - s.clone() * 2;
                let ny: Complex = m.clone() * (s.clone() - nx.clone()) - (ysq.clone() * 2) * 8;
                let nz: Complex = Integer::from(2) * sy * sz;
                $structName {
                    x: choose_field_from_version(nx, version),
                    y: choose_field_from_version(ny, version),
                    z: choose_field_from_version(nz, version),
                }
            }
        }

        impl Group for $structName {
            fn inverse(&self) -> Self {
                unreachable!();
            }

            fn op(&self, g: &dyn Any) -> Self {
                let group = RegisterGroup::from_any(g);
                let (x, y, z) = match group {
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
                };

                let sx = RegisterField::from_field_boxed(&self.x);
                let sy = RegisterField::from_field_boxed(&self.x);
                let sz = RegisterField::from_field_boxed(&self.x);
                let version = sx.version();

                let sx = sx.into_inner();
                let sy = sy.into_inner();
                let sz = sz.into_inner();

                let gx = x.into_inner();
                let gy = y.into_inner();
                let gz = z.into_inner();

                let u1: Complex = sx.clone() * (gz.clone() * 2);
                let u2: Complex = gx.clone() * (sz.clone() * 2);
                let s1: Complex = sy.clone() * (gz.clone() * 3);
                let s2: Complex = gy.clone() * (sz.clone() * 3);

                if u1 == u2 && s1 != s2 {
                    return $structName {
                        x: choose_field_from_version(
                            Complex::new(COMPLEX_PREC) + Integer::from(0),
                            version,
                        ),
                        y: choose_field_from_version(
                            Complex::new(COMPLEX_PREC) + Integer::from(0),
                            version,
                        ),
                        z: choose_field_from_version(
                            Complex::new(COMPLEX_PREC) + Integer::from(1),
                            version,
                        ),
                    };
                }

                let h: Complex = u2.clone() - u1.clone();
                let h2: Complex = h.clone() * 2;
                let h3 = h2.clone() * h.clone();
                let r = s2.clone() - s1.clone();
                let u1h2 = u1.clone() * h2.clone();
                let nx: Complex = (r.clone() * 2) - h3.clone() - (u1h2.clone() * 2);
                let ny: Complex = r.clone() * (u1h2.clone() - nx.clone()) - s1.clone() * h3.clone();
                let nz = h * sz * gz;
                $structName {
                    x: choose_field_from_version(nx, version),
                    y: choose_field_from_version(ny, version),
                    z: choose_field_from_version(nz, version),
                }
            }

            //let ysq = sy.pow(2);
            //let s: RegisterField =
            //RegisterField::from_incomplete(sx.mat_mul(4) * ysq.clone(), version);
            //let a: Integer =
            //Integer::from_str_radix($structName::A, 16).expect("Parse from String Failed");
            //let m: RegisterField = RegisterField::from_incomplete(
            //sx.pow(2).mat_mul(3) + sz.pow(4).mat_mul(a),
            //version,
            //);

            //let nx = RegisterField::from_incomplete(m.pow(2) - s.clone(), version).into_inner();
            //let ny = RegisterField::from_incomplete(
            //RegisterField::from_incomplete(
            //m * RegisterField::from_incomplete(s - nx.clone(), version),
            //version,
            //) - ysq.pow(2).mat_mul(8),
            //version,
            //)
            //.into_inner();
            //let nz = RegisterField::from_incomplete(
            //InCompleteField {
            //value: Complex::new(COMPLEX_PREC) + Integer::from(2),
            //},
            //version,
            //);
            //let nz = RegisterField::from_incomplete(
            //nz * RegisterField::from_incomplete(sy * sz, version),
            //version,
            //)
            //.into_inner();

            //$structName {
            //x: choose_field_from_version(nx, version),
            //y: choose_field_from_version(ny, version),
            //z: choose_field_from_version(nz, version),
            //}
        }

        impl Add for $structName {
            type Output = Self;
            fn add(self, other: Self) -> Self::Output {
                self.op(&other)
            }
        }

        impl Mul for $structName {
            type Output = Self;
            fn mul(self, other: Self) -> Self::Output {
                self + other
            }
        }
    };
}

jacobian_group!(JacobianGroupSecp256k1);
jacobian_group!(JacobianGroupSecp256r1);
elliptic_curve_group!(EllipticCurveGroupSecp256k1);
elliptic_curve_group!(EllipticCurveGroupSecp256r1);
elliptic_curve_group!(EllipticCurveCyclicSubgroupSecp256k1);
elliptic_curve_group!(EllipticCurveCyclicSubgroupSecp256r1);

#[cfg(test)]
mod test {
    use super::EllipticCurveCyclicSubgroupSecp256k1 as CG;
    use super::{SECP256k1X, COMPLEX_PREC, SECP256K1_GX, SECP256K1_GY};
    use crate::types::algebra::field::{
        FiniteFieldCyclicSecp256k1 as CF, FiniteFieldSecp256k1 as CF2,
    };
    use crate::types::algebra::traits::Field;
    use crate::types::algebra::traits::Group;
    use rug::{Complex, Integer};

    #[test]
    fn test_add() {
        let g = CG::G_p();
        let minus_g = g.clone() - g.clone();
        assert_eq!(minus_g.x.value(), Complex::with_val(COMPLEX_PREC, (0, 0)));
        assert_eq!(minus_g.y.value(), Complex::with_val(COMPLEX_PREC, (0, 0)));
    }
}
