use crate::constrant::{
    IntPrimitive, COMPLEX_PREC, SECP256K1_A, SECP256K1_B, SECP256K1_GX, SECP256K1_GY, SECP256K1_N,
    SECP256K1_P, SECP256R1_A, SECP256R1_B, SECP256R1_GX, SECP256R1_GY, SECP256R1_N, SECP256R1_P,
};
use crate::types::algebra::field::{
    FiniteFieldCyclicSecp256k1, FiniteFieldCyclicSecp256r1, FiniteFieldSecp256k1,
    FiniteFieldSecp256r1,
};
use crate::types::algebra::registers::{InCompleteField, RegisterField, RegisterGroup};
use crate::types::algebra::traits::{
    ConstA, ConstB, ConstN, ConstP, Field, Group, Identity, SecGroup, SecIdentity,
};
use rug::{ops::Pow, Assign, Complex, Float, Integer};
use std::any::{Any, TypeId};
use std::marker::PhantomData;
use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign};

lazy_static! {
    static ref SECP256k1X: FiniteFieldSecp256k1 = FiniteFieldSecp256k1::new(SECP256K1_GX);
    static ref SECP256k1Y: FiniteFieldSecp256k1 = FiniteFieldSecp256k1::new(SECP256K1_GY);
    static ref SECP256r1X: FiniteFieldSecp256r1 = FiniteFieldSecp256r1::new(SECP256R1_GX);
    static ref SECP256r1Y: FiniteFieldSecp256r1 = FiniteFieldSecp256r1::new(SECP256R1_GY);
}

macro_rules! from_incomplete {
    ($Param: expr, $Version: expr) => {
        RegisterField::from_incomplete($Param, Some($Version))
    };
}

macro_rules! from_field_boxed {
    ($Param: expr) => {
        RegisterField::from_field_boxed($Param)
    };
}

#[derive(Clone)]
pub struct EllipticCurveCyclicSubgroupSecp256k1 {
    pub x: Box<dyn Field>,
    pub y: Box<dyn Field>,
}

#[derive(Clone)]
pub struct EllipticCurveGroupSecp256k1 {
    pub x: Box<dyn Field>,
    pub y: Box<dyn Field>,
}

#[derive(Clone)]
pub struct JacobianGroupSecp256k1 {
    pub x: Box<dyn Field>,
    pub y: Box<dyn Field>,
    pub z: Box<dyn Field>,
}

#[derive(Clone)]
pub struct EllipticCurveGroupSecp256r1 {
    pub x: Box<dyn Field>,
    pub y: Box<dyn Field>,
}

#[derive(Clone)]
pub struct JacobianGroupSecp256r1 {
    pub x: Box<dyn Field>,
    pub y: Box<dyn Field>,
    pub z: Box<dyn Field>,
}

#[derive(Clone)]
pub struct EllipticCurveCyclicSubgroupSecp256r1 {
    pub x: Box<dyn Field>,
    pub y: Box<dyn Field>,
}

macro_rules! impl_const {
    () => {};
    (
        $Struct:ident
        $impl_lt:tt
        $($trait_name: ident, $variable_name:ident, $trait_input:ident;)*
    ) => {
        $(
            impl<$impl_lt> $trait_name<$impl_lt> for $Struct
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

impl_const!(
    EllipticCurveCyclicSubgroupSecp256k1
    'a
    ConstA, A, SECP256K1_A;
    ConstB, B, SECP256K1_B;
    ConstN, N, SECP256K1_N;
);

impl_const!(
    JacobianGroupSecp256k1
    'a
    ConstA, A, SECP256K1_A;
    ConstB, B, SECP256K1_B;
);

impl_const!(
    EllipticCurveGroupSecp256r1
    'a
    ConstA, A, SECP256K1_A;
    ConstB, B, SECP256K1_B;
);

impl_const!(
    JacobianGroupSecp256r1
    'a
    ConstA, A, SECP256R1_A;
    ConstB, B, SECP256R1_B;
);

impl_const!(
    EllipticCurveCyclicSubgroupSecp256r1
    'a
    ConstA, A, SECP256R1_A;
    ConstB, B, SECP256R1_B;
    ConstN, N, SECP256R1_N;
);

impl EllipticCurveGroupSecp256k1 {
    pub fn G_p() -> EllipticCurveCyclicSubgroupSecp256k1 {
        EllipticCurveCyclicSubgroupSecp256k1 {
            x: Box::new(SECP256k1X.clone()),
            y: Box::new(SECP256k1Y.clone()),
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
}

impl EllipticCurveCyclicSubgroupSecp256k1 {
    pub fn G_p() -> EllipticCurveCyclicSubgroupSecp256k1 {
        EllipticCurveCyclicSubgroupSecp256k1 {
            x: Box::new(SECP256k1X.clone()),
            y: Box::new(SECP256k1Y.clone()),
        }
    }

    pub fn scalar(&self, field: &dyn Field) -> Self {
        let value = field.value();
        let time = match value.real().to_integer() {
            Some(i) => i,
            None => unreachable!(),
        };
        let time = time.secure_pow_mod(
            &Integer::from(1),
            &Integer::from_str_radix(Self::N, 16).expect("Scalar parse from string failed"),
        );
        let time: usize = time.to_usize().expect("Unwrap to usize failed");
        if time == 0 {
            Self::identity()
        } else {
            double_and_add!(time, self.clone(), Self::identity())
        }
    }
}

impl EllipticCurveGroupSecp256r1 {
    pub fn G_p() -> EllipticCurveCyclicSubgroupSecp256r1 {
        EllipticCurveCyclicSubgroupSecp256r1 {
            x: Box::new(SECP256r1X.clone()),
            y: Box::new(SECP256r1Y.clone()),
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
}

impl EllipticCurveCyclicSubgroupSecp256r1 {
    pub fn G_p() -> EllipticCurveCyclicSubgroupSecp256r1 {
        EllipticCurveCyclicSubgroupSecp256r1 {
            x: Box::new(SECP256r1X.clone()),
            y: Box::new(SECP256r1Y.clone()),
        }
    }

    pub fn scalar(&self, field: &dyn Field) -> Self {
        let value = field.value();
        let time = match value.real().to_integer() {
            Some(i) => i,
            None => unreachable!(),
        };
        let time = time.secure_pow_mod(
            &Integer::from(1),
            &Integer::from_str_radix(Self::N, 16).expect("Scalar parse from string failed"),
        );
        let time: usize = time.to_usize().expect("Unwrap to usize failed");
        double_and_add!(time, self.clone(), Self::identity())
    }
}

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
    ($Struct: ident) => {
        impl $Struct {
            pub fn new(x: Box<dyn Field>, y: Option<Box<dyn Field>>) -> Self {
                let y = y.unwrap_or(Box::new(FiniteFieldSecp256k1::new("0")));
                $Struct { x, y }
            }
        }

        impl Default for $Struct {
            fn default() -> Self {
                let x = Box::new(FiniteFieldSecp256k1::new("0"));
                let y = Box::new(FiniteFieldSecp256k1::new("0"));
                $Struct { x, y }
            }
        }

        impl Identity for $Struct {
            fn identity() -> Self {
                $Struct::default()
            }
        }

        impl PartialEq for $Struct {
            fn eq(&self, other: &Self) -> bool {
                self.x.value() == other.x.value() && self.y.value() == other.y.value()
            }
        }

        impl Group for $Struct {
            fn inverse(&self) -> Self {
                let x = from_field_boxed!(&self.x);
                let y = from_field_boxed!(&self.y);
                let versionx = x.version();
                let versiony = y.version();
                let y = from_incomplete!(-y, versiony);
                $Struct {
                    x: choose_field_from_version(x.into_inner(), versionx),
                    y: choose_field_from_version(y.into_inner(), versiony),
                }
            }

            fn op(&self, g: &dyn Any) -> Self {
                let group = RegisterGroup::from_any(g);
                let x1 = from_field_boxed!(&self.x);
                let y1 = from_field_boxed!(&self.y);
                let (x2, y2) = group.into_field();

                let versionx = x1.version();
                let versiony = y1.version();

                // Next do the calculate
                let m: InCompleteField<Complex> = if x1 != x2 {
                    from_incomplete!(y1.clone() - y2.clone(), versiony)
                        / from_incomplete!(x1.clone() - x2.clone(), versionx)
                } else {
                    if y1 == from_incomplete!(-y2, versiony) {
                        return $Struct::identity();
                    }
                    let A = Integer::from_str_radix($Struct::A, 16).expect("Parse ConstA Failed")
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

                    let field3 = from_field_boxed!(&field3);
                    let field2 = from_field_boxed!(&field2);
                    let A = from_field_boxed!(&A);

                    let v1 = from_incomplete!(field3 * x1.clone(), versionx);
                    let v2 = from_incomplete!(v1 * x1.clone(), versionx);
                    let v3 = from_incomplete!(v2 + A, versionx);
                    let v4 = from_incomplete!(field2 * y1.clone(), versionx);
                    v3 / v4
                };

                let m = from_incomplete!(m, versionx);
                let rx: RegisterField = {
                    let v1 = from_incomplete!(m.clone() * m.clone(), versionx);
                    let v2 = from_incomplete!(v1 - x1.clone(), versionx);
                    let v3 = from_incomplete!(v2 - x2.clone(), versionx);
                    v3
                };
                let ry: RegisterField = {
                    let v1 = from_incomplete!(rx.clone() - x1.clone(), versionx);
                    let v2 = from_incomplete!(m.clone() * v1, versionx);
                    let v3 = from_incomplete!(y1.clone() + v2, versionx);
                    v3
                };
                let ry = from_incomplete!(-ry, versionx);
                let rx_boxed = choose_field_from_version(rx.into_inner(), versionx);
                let ry_boxed = choose_field_from_version(ry.into_inner(), versiony);
                $Struct {
                    x: rx_boxed,
                    y: ry_boxed,
                }
            }
        }

        impl Neg for $Struct {
            type Output = Self;
            fn neg(self) -> Self::Output {
                self.inverse()
            }
        }
    };
}

macro_rules! cyclic_add_group {
    ($Struct: ident) => {
        impl Identity for $Struct {
            fn identity() -> Self {
                $Struct::default()
            }
        }

        impl Group for $Struct {
            fn inverse(&self) -> Self {
                let a: Complex = Integer::from(0)
                    % Integer::from_str_radix($Struct::N, 16).expect("Cannot parse from string")
                    + Complex::new(COMPLEX_PREC);

                let rf: RegisterField = from_field_boxed!(self.x);
                let version = rf.version();
                let b: Complex = rf.into_inner();

                let v = a * b;
                let rx_boxed = choose_field_from_version(v, version);

                $Struct::new(rx_boxed, None)
            }

            fn op(&self, g: &dyn Any) -> Self {
                let group = RegisterGroup::from_any(g);
                let (x1, _) = group.into_field();
                let (x2, _) = RegisterField::from(self.x);

                let version = x2.version();
                let x1 = match x1.into_inner().real().to_integer() {
                    Some(i) => i,
                    None => unreachable!(),
                };
                let x2 = match x2.into_inner().real().to_integer() {
                    Some(i) => i,
                    None => unreachable!(),
                };
                let N = Integer::from_str_radix($Struct::N, 16).expect("Parse from string failed");
                let (_, result) = (x1 + x2).div_rem(N);
                let rx_boxed =
                    choose_field_from_version(result + Complex::new(COMPLEX_PREC), version);
                $Struct::new(rx_boxed, None)
            }
        }

        impl $Struct {
            pub fn pow(&self, item: &dyn Any) -> Self {
                let group = RegisterGroup::from_any(g);
                let (x1, _) = group.into_field();
                let (x2, _) = RegisterField::from(self.x);

                let version = x2.version();
                let x1 = match x1.into_inner().real().to_integer() {
                    Some(i) => i,
                    None => unreachable!(),
                };
                let x2 = match x2.into_inner().real().to_integer() {
                    Some(i) => i,
                    None => unreachable!(),
                };
                let N = Integer::from_str_radix($Struct::N, 16).expect("Parse from string failed");
                let result = x2.secure_pow_mod(&x1, &N);
                let rx_boxed =
                    choose_field_from_version(result + Complex::new(COMPLEX_PREC), version);
                $Struct::new(rx_boxed, None)
            }
        }
    };
}

macro_rules! jacobian_group {
    ($Struct: ident) => {
        impl $Struct {
            pub fn new(
                x: Box<dyn Field>,
                y: Option<Box<dyn Field>>,
                z: Option<Box<dyn Field>>,
            ) -> Self {
                let y = y.unwrap_or(Box::new(FiniteFieldSecp256k1::new("0")));
                let z = z.unwrap_or(Box::new(FiniteFieldSecp256k1::new("0")));
                $Struct { x, y, z }
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
        }

        impl Default for $Struct {
            fn default() -> Self {
                let x = Box::new(FiniteFieldSecp256k1::new("0"));
                let y = Box::new(FiniteFieldSecp256k1::new("0"));
                let z = Box::new(FiniteFieldSecp256k1::new("0"));
                $Struct { x, y, z }
            }
        }

        impl Identity for $Struct {
            fn identity() -> Self {
                $Struct::default()
            }
        }

        impl PartialEq for $Struct {
            fn eq(&self, other: &Self) -> bool {
                self.x.value() == other.x.value()
                    && self.y.value() == other.y.value()
                    && self.z.value() == other.z.value()
            }
        }

        impl $Struct {
            fn double(&self, n: &dyn Any) -> Self {
                let group = RegisterGroup::from_any(n);
                let (x, y, z) = group.into_field2();
                let version = x.version();
                let sx = from_field_boxed!(&self.x);
                let sy = from_field_boxed!(&self.y);
                let sz = from_field_boxed!(&self.z);

                let version = sx.version();

                let A = Integer::from_str_radix($Struct::A, 16).expect("Parse String Failed");
                let ysq = sy.pow(2);
                let s = from_incomplete!(sx.mat_mul(4) * ysq.clone(), version);
                let m = from_incomplete!(sx.pow(2).mat_mul(3) + sz.pow(4).mat_mul(A), version);
                let nx = from_incomplete!(m.pow(2) - s.mat_mul(2), version);
                let ny = {
                    let v1 = from_incomplete!(s - nx.clone(), version);
                    let v2 = from_incomplete!(m * v1, version);
                    let v3 = ysq.pow(2).mat_mul(8);
                    v3
                };
                let nz = {
                    let field2 = from_incomplete!(
                        InCompleteField::new(Complex::with_val(COMPLEX_PREC, (2, 0))),
                        version
                    );
                    let v1 = from_incomplete!(field2 * sy, version);
                    let v2 = from_incomplete!(sz * v1, version);
                    v2
                };

                $Struct {
                    x: choose_field_from_version(nx.into_inner(), version),
                    y: choose_field_from_version(ny.into_inner(), version),
                    z: choose_field_from_version(nz.into_inner(), version),
                }
            }
        }

        impl Group for $Struct {
            fn inverse(&self) -> Self {
                unreachable!();
            }

            fn op(&self, g: &dyn Any) -> Self {
                let group = RegisterGroup::from_any(g);
                let (gx, gy, gz) = match group {
                    RegisterGroup::V5(group) => (
                        from_field_boxed!(&group.x),
                        from_field_boxed!(&group.y),
                        from_field_boxed!(&group.z),
                    ),
                    RegisterGroup::V6(group) => (
                        from_field_boxed!(&group.x),
                        from_field_boxed!(&group.y),
                        from_field_boxed!(&group.z),
                    ),
                    _ => unreachable!(),
                };

                let sx = from_field_boxed!(&self.x);
                let sy = from_field_boxed!(&self.y);
                let sz = from_field_boxed!(&self.z);
                let version = sx.version();

                let u1 = from_incomplete!(sx.clone() * gz.pow(2), version);
                let u2 = from_incomplete!(gx.clone() * sz.pow(2), version);
                let s1 = from_incomplete!(sy.clone() * gz.pow(3), version);
                let s2 = from_incomplete!(gy.clone() * sz.pow(3), version);

                if u1 == u2 && s1 != s2 {
                    return $Struct {
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

                let h = from_incomplete!(
                    InCompleteField::new(u2.into_inner() - u1.into_inner()),
                    version
                );
                let r = from_incomplete!(
                    InCompleteField::new(s2.into_inner() - s1.into_inner()),
                    version
                );
                let h2 = from_incomplete!(h.clone() * h.clone(), version);
                let h3 = from_incomplete!(h2.clone() * h.clone(), version);
                let u1h2 = from_incomplete!(u1.clone() * h2.clone(), version);

                let nx = {
                    let v1 = from_incomplete!(r.pow(2) - h3.clone(), version);
                    let v2 = from_incomplete!(v1 - u1h2.mat_mul(2), version);
                    v2
                };
                let ny = {
                    let v1 = from_incomplete!(u1h2 - nx.clone(), version);
                    let v2 = from_incomplete!(s1 * h3, version);
                    let v3 = from_incomplete!(r * v1, version);
                    let v4 = from_incomplete!(v3 - v2, version);
                    v4
                };
                let nz = {
                    let v1 = from_incomplete!(h * sz, version);
                    let v2 = from_incomplete!(gz * v1, version);
                    v2
                };
                $Struct {
                    x: choose_field_from_version(nx.into_inner(), version),
                    y: choose_field_from_version(ny.into_inner(), version),
                    z: choose_field_from_version(nz.into_inner(), version),
                }
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

arith_binary_self!(
    EllipticCurveGroupSecp256k1, EllipticCurveGroupSecp256k1;
    Add {
        add,
        |lhs: EllipticCurveGroupSecp256k1, rhs: EllipticCurveGroupSecp256k1| {
            lhs.op(&rhs)
        }
    };
    AddAssign {
        add_assign
    };
    Mul {
        mul,
        |lhs: EllipticCurveGroupSecp256k1, rhs: EllipticCurveGroupSecp256k1| {
            lhs + rhs
        }
    };
    MulAssign {
        mul_assign
    };
    Sub {
        sub,
        |lhs: EllipticCurveGroupSecp256k1, rhs: EllipticCurveGroupSecp256k1| {
            lhs.op(&rhs.inverse())
        }
    };
    SubAssign {
        sub_assign
    };
);

arith_binary_self!(
    EllipticCurveGroupSecp256r1, EllipticCurveGroupSecp256r1;
    Add {
        add,
        |lhs: EllipticCurveGroupSecp256r1, rhs: EllipticCurveGroupSecp256r1| {
            lhs.op(&rhs)
        }
    };
    AddAssign {
        add_assign
    };
    Mul {
        mul,
        |lhs: EllipticCurveGroupSecp256r1, rhs: EllipticCurveGroupSecp256r1| {
            lhs + rhs
        }
    };
    MulAssign {
        mul_assign
    };
    Sub {
        sub,
        |lhs: EllipticCurveGroupSecp256r1, rhs: EllipticCurveGroupSecp256r1| {
            lhs.op(&rhs.inverse())
        }
    };
    SubAssign {
        sub_assign
    };
);

arith_binary_self!(
    EllipticCurveCyclicSubgroupSecp256k1, EllipticCurveCyclicSubgroupSecp256k1;
    Add {
        add,
        |lhs: EllipticCurveCyclicSubgroupSecp256k1, rhs: EllipticCurveCyclicSubgroupSecp256k1| {
            lhs.op(&rhs)
        }
    };
    AddAssign {
        add_assign
    };
    Mul {
        mul,
        |lhs: EllipticCurveCyclicSubgroupSecp256k1, rhs: EllipticCurveCyclicSubgroupSecp256k1| {
            lhs + rhs
        }
    };
    MulAssign {
        mul_assign
    };
    Sub {
        sub,
        |lhs: EllipticCurveCyclicSubgroupSecp256k1, rhs: EllipticCurveCyclicSubgroupSecp256k1| {
            lhs.op(&rhs.inverse())
        }
    };
    SubAssign {
        sub_assign
    };
);

arith_binary_self!(
    EllipticCurveCyclicSubgroupSecp256r1, EllipticCurveCyclicSubgroupSecp256r1;
    Add {
        add,
        |lhs: EllipticCurveCyclicSubgroupSecp256r1, rhs: EllipticCurveCyclicSubgroupSecp256r1| {
            lhs.op(&rhs)
        }
    };
    AddAssign {
        add_assign
    };
    Mul {
        mul,
        |lhs: EllipticCurveCyclicSubgroupSecp256r1, rhs: EllipticCurveCyclicSubgroupSecp256r1| {
            lhs + rhs
        }
    };
    MulAssign {
        mul_assign
    };
    Sub {
        sub,
        |lhs: EllipticCurveCyclicSubgroupSecp256r1, rhs: EllipticCurveCyclicSubgroupSecp256r1| {
            lhs.op(&rhs.inverse())
        }
    };
    SubAssign {
        sub_assign
    };
);

arith_binary_self!(
    JacobianGroupSecp256k1, JacobianGroupSecp256k1;
    Add {
        add,
        |lhs: JacobianGroupSecp256k1, rhs: JacobianGroupSecp256k1| {
            lhs.op(&rhs)
        }
    };
    AddAssign {
        add_assign
    };
    Mul {
        mul,
        |lhs: JacobianGroupSecp256k1, rhs: JacobianGroupSecp256k1| {
            lhs + rhs
        }
    };
    MulAssign {
        mul_assign
    };
);

arith_binary_self!(
    JacobianGroupSecp256r1, JacobianGroupSecp256r1;
    Add {
        add,
        |lhs: JacobianGroupSecp256r1, rhs: JacobianGroupSecp256r1| {
            lhs.op(&rhs)
        }
    };
    AddAssign {
        add_assign
    };
    Mul {
        mul,
        |lhs: JacobianGroupSecp256r1, rhs: JacobianGroupSecp256r1| {
            lhs + rhs
        }
    };
    MulAssign {
        mul_assign
    };
);

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
