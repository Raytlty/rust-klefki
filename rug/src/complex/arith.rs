// Copyright © 2016–2019 University of Malta

// This program is free software: you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation, either version 3 of
// the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
// General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public
// License and a copy of the GNU General Public License along with
// this program. If not, see <https://www.gnu.org/licenses/>.

#[cfg(feature = "integer")]
use crate::Integer;
#[cfg(feature = "rational")]
use crate::Rational;
use crate::{
    complex::SmallComplex,
    ext::xmpc::{self, ordering2, raw_round2, Ordering2, Round2, NEAREST2},
    float::SmallFloat,
    ops::{
        AddAssignRound, AddFrom, AddFromRound, AssignRound, DivAssignRound, DivFrom, DivFromRound,
        MulAssignRound, MulFrom, MulFromRound, NegAssign, Pow, PowAssign, PowAssignRound, PowFrom,
        PowFromRound, SubAssignRound, SubFrom, SubFromRound,
    },
    Complex, Float,
};
use az::{CheckedAs, CheckedCast};
use gmp_mpfr_sys::mpc::{self, mpc_t, rnd_t};
use std::{
    ops::{
        Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Shl, ShlAssign, Shr, ShrAssign, Sub,
        SubAssign,
    },
    os::raw::{c_int, c_long, c_ulong},
};

impl Neg for Complex {
    type Output = Complex;
    #[inline]
    fn neg(mut self) -> Complex {
        self.neg_assign();
        self
    }
}

impl NegAssign for Complex {
    #[inline]
    fn neg_assign(&mut self) {
        xmpc::neg(self, None, NEAREST2);
    }
}

impl<'a> Neg for &'a Complex {
    type Output = NegIncomplete<'a>;
    #[inline]
    fn neg(self) -> NegIncomplete<'a> {
        NegIncomplete { val: self }
    }
}

#[derive(Debug)]
pub struct NegIncomplete<'a> {
    val: &'a Complex,
}

impl AssignRound<NegIncomplete<'_>> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, src: NegIncomplete<'_>, round: Round2) -> Ordering2 {
        xmpc::neg(self, Some(src.val), round)
    }
}

macro_rules! arith_binary_self_complex {
    (
        $func:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpAssignRound:ident { $method_assign_round:ident }
        $ImpFrom:ident { $method_from:ident }
        $ImpFromRound:ident { $method_from_round:ident }
        $Incomplete:ident
    ) => {
        arith_binary_self_round! {
            Complex, Round2, NEAREST2 => Ordering2;
            $func, raw_round2 => ordering2;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $ImpAssignRound { $method_assign_round }
            $ImpFrom { $method_from }
            $ImpFromRound { $method_from_round }
            $Incomplete
        }
    };
}

macro_rules! arith_forward_complex {
    (
        $func:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpAssignRound:ident { $method_assign_round:ident }
        $T:ty;
        $Incomplete:ident,
        $OwnedIncomplete:ident
    ) => {
        arith_forward_round! {
            Complex, Round2, NEAREST2 => Ordering2;
            $func, raw_round2 => ordering2;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $ImpAssignRound { $method_assign_round }
            $T;
            $Incomplete, $OwnedIncomplete
        }
    };
}

macro_rules! arith_commut_complex {
    (
        $func:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpAssignRound:ident { $method_assign_round:ident }
        $ImpFrom:ident { $method_from:ident }
        $ImpFromRound:ident { $method_from_round:ident }
        $T:ty;
        $Incomplete:ident,
        $OwnedIncomplete:ident
    ) => {
        arith_commut_round! {
            Complex, Round2, NEAREST2 => Ordering2;
            $func, raw_round2 => ordering2;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $ImpAssignRound { $method_assign_round }
            $ImpFrom { $method_from }
            $ImpFromRound { $method_from_round }
            $T;
            $Incomplete, $OwnedIncomplete
        }
    };
}

macro_rules! arith_noncommut_complex {
    (
        $func:path,
        $func_from:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpAssignRound:ident { $method_assign_round:ident }
        $ImpFrom:ident { $method_from:ident }
        $ImpFromRound:ident { $method_from_round:ident }
        $T:ty;
        $Incomplete:ident, $OwnedIncomplete:ident;
        $FromIncomplete:ident, $FromOwnedIncomplete:ident
    ) => {
        arith_noncommut_round! {
            Complex, Round2, NEAREST2 => Ordering2;
            $func, $func_from, raw_round2 => ordering2;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $ImpAssignRound { $method_assign_round }
            $ImpFrom { $method_from }
            $ImpFromRound { $method_from_round }
            $T;
            $Incomplete, $OwnedIncomplete;
            $FromIncomplete, $FromOwnedIncomplete
        }
    };
}

arith_binary_self_complex! {
    mpc::add;
    Add { add }
    AddAssign { add_assign }
    AddAssignRound { add_assign_round }
    AddFrom { add_from }
    AddFromRound { add_from_round }
    AddIncomplete
}
arith_binary_self_complex! {
    mpc::sub;
    Sub { sub }
    SubAssign { sub_assign }
    SubAssignRound { sub_assign_round }
    SubFrom { sub_from }
    SubFromRound { sub_from_round }
    SubIncomplete
}
arith_binary_self_complex! {
    mpc::mul;
    Mul { mul }
    MulAssign { mul_assign }
    MulAssignRound { mul_assign_round }
    MulFrom { mul_from }
    MulFromRound { mul_from_round }
    MulIncomplete
}
arith_binary_self_complex! {
    mpc::div;
    Div { div }
    DivAssign { div_assign }
    DivAssignRound { div_assign_round }
    DivFrom { div_from }
    DivFromRound { div_from_round }
    DivIncomplete
}
arith_binary_self_complex! {
    mpc::pow;
    Pow { pow }
    PowAssign { pow_assign }
    PowAssignRound { pow_assign_round }
    PowFrom { pow_from }
    PowFromRound { pow_from_round }
    PowIncomplete
}

arith_commut_complex! {
    mpc::add_fr;
    Add { add }
    AddAssign { add_assign }
    AddAssignRound { add_assign_round }
    AddFrom { add_from }
    AddFromRound { add_from_round }
    Float;
    AddFloatIncomplete, AddOwnedFloatIncomplete
}
arith_noncommut_complex! {
    mpc::sub_fr, mpc::fr_sub;
    Sub { sub }
    SubAssign { sub_assign }
    SubAssignRound { sub_assign_round }
    SubFrom { sub_from }
    SubFromRound { sub_from_round }
    Float;
    SubFloatIncomplete, SubOwnedFloatIncomplete;
    SubFromFloatIncomplete, SubFromOwnedFloatIncomplete
}
arith_commut_complex! {
    mpc::mul_fr;
    Mul { mul }
    MulAssign { mul_assign }
    MulAssignRound { mul_assign_round }
    MulFrom { mul_from }
    MulFromRound { mul_from_round }
    Float;
    MulFloatIncomplete, MulOwnedFloatIncomplete
}
arith_noncommut_complex! {
    mpc::div_fr, mpc::fr_div;
    Div { div }
    DivAssign { div_assign }
    DivAssignRound { div_assign_round }
    DivFrom { div_from }
    DivFromRound { div_from_round }
    Float;
    DivFloatIncomplete, DivOwnedFloatIncomplete;
    DivFromFloatIncomplete, DivFromOwnedFloatIncomplete
}
arith_forward_complex! {
    mpc::pow_fr;
    Pow { pow }
    PowAssign { pow_assign }
    PowAssignRound { pow_assign_round }
    Float;
    PowFloatIncomplete, PowOwnedFloatIncomplete
}
#[cfg(feature = "integer")]
arith_forward_complex! {
    mpc::pow_z;
    Pow { pow }
    PowAssign { pow_assign }
    PowAssignRound { pow_assign_round }
    Integer;
    PowIntegerIncomplete, PowOwnedIntegerIncomplete
}

macro_rules! arith_prim_exact_complex {
    (
        $func:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $($T:ty, $Incomplete:ident;)*
    ) => {
        arith_prim_exact_round! {
            Complex, Round2, NEAREST2 => Ordering2;
            $func, raw_round2 => ordering2;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $($T, $Incomplete;)*
        }
    };
}

macro_rules! arith_prim_commut_complex {
    (
        $func:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpAssignRound:ident { $method_assign_round:ident }
        $ImpFrom:ident { $method_from:ident }
        $ImpFromRound:ident { $method_from_round:ident }
        $($T:ty, $Incomplete:ident;)*
    ) => {
        arith_prim_commut_round! {
            Complex, Round2, NEAREST2 => Ordering2;
            $func, raw_round2 => ordering2;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $ImpAssignRound { $method_assign_round }
            $ImpFrom { $method_from }
            $ImpFromRound { $method_from_round }
            $($T, $Incomplete;)*
        }
    };
}

macro_rules! arith_prim_noncommut_complex {
    (
        $func:path,
        $func_from:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpAssignRound:ident { $method_assign_round:ident }
        $ImpFrom:ident { $method_from:ident }
        $ImpFromRound:ident { $method_from_round:ident }
        $($T:ty, $Incomplete:ident, $FromIncomplete:ident;)*
    ) => {
        arith_prim_noncommut_round! {
            Complex, Round2, NEAREST2 => Ordering2;
            $func, $func_from, raw_round2 => ordering2;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $ImpAssignRound { $method_assign_round }
            $ImpFrom { $method_from }
            $ImpFromRound { $method_from_round }
            $($T, $Incomplete, $FromIncomplete;)*
        }
    };
}

arith_prim_commut_complex! {
    PrimOps::add;
    Add { add }
    AddAssign { add_assign }
    AddAssignRound { add_assign_round }
    AddFrom { add_from }
    AddFromRound { add_from_round }
    i8, AddI8Incomplete;
    i16, AddI16Incomplete;
    i32, AddI32Incomplete;
    i64, AddI64Incomplete;
    i128, AddI128Incomplete;
    u8, AddU8Incomplete;
    u16, AddU16Incomplete;
    u32, AddU32Incomplete;
    u64, AddU64Incomplete;
    u128, AddU128Incomplete;
    f32, AddF32Incomplete;
    f64, AddF64Incomplete;
}
arith_prim_noncommut_complex! {
    PrimOps::sub, PrimOps::sub_from;
    Sub { sub }
    SubAssign { sub_assign }
    SubAssignRound { sub_assign_round }
    SubFrom { sub_from }
    SubFromRound { sub_from_round }
    i8, SubI8Incomplete, SubFromI8Incomplete;
    i16, SubI16Incomplete, SubFromI16Incomplete;
    i32, SubI32Incomplete, SubFromI32Incomplete;
    i64, SubI64Incomplete, SubFromI64Incomplete;
    i128, SubI128Incomplete, SubFromI128Incomplete;
    u8, SubU8Incomplete, SubFromU8Incomplete;
    u16, SubU16Incomplete, SubFromU16Incomplete;
    u32, SubU32Incomplete, SubFromU32Incomplete;
    u64, SubU64Incomplete, SubFromU64Incomplete;
    u128, SubU128Incomplete, SubFromU128Incomplete;
    f32, SubF32Incomplete, SubFromF32Incomplete;
    f64, SubF64Incomplete, SubFromF64Incomplete;
}
arith_prim_commut_complex! {
    PrimOps::mul;
    Mul { mul }
    MulAssign { mul_assign }
    MulAssignRound { mul_assign_round }
    MulFrom { mul_from }
    MulFromRound { mul_from_round }
    i8, MulI8Incomplete;
    i16, MulI16Incomplete;
    i32, MulI32Incomplete;
    i64, MulI64Incomplete;
    i128, MulI128Incomplete;
    u8, MulU8Incomplete;
    u16, MulU16Incomplete;
    u32, MulU32Incomplete;
    u64, MulU64Incomplete;
    u128, MulU128Incomplete;
    f32, MulF32Incomplete;
    f64, MulF64Incomplete;
}
arith_prim_noncommut_complex! {
    PrimOps::div, PrimOps::div_from;
    Div { div }
    DivAssign { div_assign }
    DivAssignRound { div_assign_round }
    DivFrom { div_from }
    DivFromRound { div_from_round }
    i8, DivI8Incomplete, DivFromI8Incomplete;
    i16, DivI16Incomplete, DivFromI16Incomplete;
    i32, DivI32Incomplete, DivFromI32Incomplete;
    i64, DivI64Incomplete, DivFromI64Incomplete;
    i128, DivI128Incomplete, DivFromI128Incomplete;
    u8, DivU8Incomplete, DivFromU8Incomplete;
    u16, DivU16Incomplete, DivFromU16Incomplete;
    u32, DivU32Incomplete, DivFromU32Incomplete;
    u64, DivU64Incomplete, DivFromU64Incomplete;
    u128, DivU128Incomplete, DivFromU128Incomplete;
    f32, DivF32Incomplete, DivFromF32Incomplete;
    f64, DivF64Incomplete, DivFromF64Incomplete;
}
arith_prim_noncommut_complex! {
    PrimOps::pow, PrimOps::pow_from;
    Pow { pow }
    PowAssign { pow_assign }
    PowAssignRound { pow_assign_round }
    PowFrom { pow_from }
    PowFromRound { pow_from_round }
    i8, PowI8Incomplete, PowFromI8Incomplete;
    i16, PowI16Incomplete, PowFromI16Incomplete;
    i32, PowI32Incomplete, PowFromI32Incomplete;
    i64, PowI64Incomplete, PowFromI64Incomplete;
    i128, PowI128Incomplete, PowFromI128Incomplete;
    u8, PowU8Incomplete, PowFromU8Incomplete;
    u16, PowU16Incomplete, PowFromU16Incomplete;
    u32, PowU32Incomplete, PowFromU32Incomplete;
    u64, PowU64Incomplete, PowFromU64Incomplete;
    u128, PowU128Incomplete, PowFromU128Incomplete;
    f32, PowF32Incomplete, PowFromF32Incomplete;
    f64, PowF64Incomplete, PowFromF64Incomplete;
}

#[cfg(feature = "integer")]
arith_commut_complex! {
    xmpc::add_z;
    Add { add }
    AddAssign { add_assign }
    AddAssignRound { add_assign_round }
    AddFrom { add_from }
    AddFromRound { add_from_round }
    Integer;
    AddIntegerIncomplete, AddOwnedIntegerIncomplete
}
#[cfg(feature = "integer")]
arith_noncommut_complex! {
    xmpc::sub_z, xmpc::z_sub;
    Sub { sub }
    SubAssign { sub_assign }
    SubAssignRound { sub_assign_round }
    SubFrom { sub_from }
    SubFromRound { sub_from_round }
    Integer;
    SubIntegerIncomplete, SubOwnedIntegerIncomplete;
    SubFromIntegerIncomplete, SubFromOwnedIntegerIncomplete
}
#[cfg(feature = "integer")]
arith_commut_complex! {
    xmpc::mul_z;
    Mul { mul }
    MulAssign { mul_assign }
    MulAssignRound { mul_assign_round }
    MulFrom { mul_from }
    MulFromRound { mul_from_round }
    Integer;
    MulIntegerIncomplete, MulOwnedIntegerIncomplete
}
#[cfg(feature = "integer")]
arith_forward_complex! {
    xmpc::div_z;
    Div { div }
    DivAssign { div_assign }
    DivAssignRound { div_assign_round }
    Integer;
    DivIntegerIncomplete, DivOwnedIntegerIncomplete
}
#[cfg(feature = "rational")]
arith_commut_complex! {
    xmpc::add_q;
    Add { add }
    AddAssign { add_assign }
    AddAssignRound { add_assign_round }
    AddFrom { add_from }
    AddFromRound { add_from_round }
    Rational;
    AddRationalIncomplete, AddOwnedRationalIncomplete
}
#[cfg(feature = "rational")]
arith_noncommut_complex! {
    xmpc::sub_q, xmpc::q_sub;
    Sub { sub }
    SubAssign { sub_assign }
    SubAssignRound { sub_assign_round }
    SubFrom { sub_from }
    SubFromRound { sub_from_round }
    Rational;
    SubRationalIncomplete, SubOwnedRationalIncomplete;
    SubFromRationalIncomplete, SubFromOwnedRationalIncomplete
}
#[cfg(feature = "rational")]
arith_commut_complex! {
    xmpc::mul_q;
    Mul { mul }
    MulAssign { mul_assign }
    MulAssignRound { mul_assign_round }
    MulFrom { mul_from }
    MulFromRound { mul_from_round }
    Rational;
    MulRationalIncomplete, MulOwnedRationalIncomplete
}
#[cfg(feature = "rational")]
arith_forward_complex! {
    xmpc::div_q;
    Div { div }
    DivAssign { div_assign }
    DivAssignRound { div_assign_round }
    Rational;
    DivRationalIncomplete, DivOwnedRationalIncomplete
}

arith_prim_exact_complex! {
    xmpc::shl_u32;
    Shl { shl }
    ShlAssign { shl_assign }
    u32, ShlU32Incomplete;
}
arith_prim_exact_complex! {
    xmpc::shr_u32;
    Shr { shr }
    ShrAssign { shr_assign }
    u32, ShrU32Incomplete;
}
arith_prim_exact_complex! {
    xmpc::shl_i32;
    Shl { shl }
    ShlAssign { shl_assign }
    i32, ShlI32Incomplete;
}
arith_prim_exact_complex! {
    xmpc::shr_i32;
    Shr { shr }
    ShrAssign { shr_assign }
    i32, ShrI32Incomplete;
}

mul_op_commut_round! {
    Complex, Round2, NEAREST2 => Ordering2;
    add_mul, raw_round2 => ordering2;
    Add { add }
    AddAssign { add_assign }
    AddAssignRound { add_assign_round }
    AddFrom { add_from }
    AddFromRound { add_from_round }
    MulIncomplete;
    AddMulIncomplete
}
mul_op_noncommut_round! {
    Complex, Round2, NEAREST2 => Ordering2;
    sub_mul, mul_sub, raw_round2 => ordering2;
    Sub { sub }
    SubAssign { sub_assign }
    SubAssignRound { sub_assign_round }
    SubFrom { sub_from }
    SubFromRound { sub_from_round }
    MulIncomplete;
    SubMulIncomplete, SubMulFromIncomplete
}

trait PrimOps<Long>: AsLong {
    unsafe fn add(rop: *mut mpc_t, op1: *const mpc_t, op2: Self, rnd: rnd_t) -> c_int;
    unsafe fn sub(rop: *mut mpc_t, op1: *const mpc_t, op2: Self, rnd: rnd_t) -> c_int;
    unsafe fn sub_from(rop: *mut mpc_t, op1: Self, op2: *const mpc_t, rnd: rnd_t) -> c_int;
    unsafe fn mul(rop: *mut mpc_t, op1: *const mpc_t, op2: Self, rnd: rnd_t) -> c_int;
    unsafe fn div(rop: *mut mpc_t, op1: *const mpc_t, op2: Self, rnd: rnd_t) -> c_int;
    unsafe fn div_from(rop: *mut mpc_t, op1: Self, op2: *const mpc_t, rnd: rnd_t) -> c_int;
    unsafe fn pow(rop: *mut mpc_t, op1: *const mpc_t, op2: Self, rnd: rnd_t) -> c_int;
    unsafe fn pow_from(rop: *mut mpc_t, op1: Self, op2: *const mpc_t, rnd: rnd_t) -> c_int;
}

trait AsLong: Copy {
    type Long;
}

macro_rules! as_long {
    ($Long:ty: $($Prim:ty)*) => { $(
        impl AsLong for $Prim {
            type Long = $Long;
        }
    )* }
}

as_long! { c_long: i8 i16 i32 i64 i128 isize }
as_long! { c_ulong: u8 u16 u32 u64 u128 usize }
as_long! { f64: f32 f64 }

macro_rules! forward {
    (fn $fn:ident() -> $deleg_long:path, $deleg:path) => {
        #[inline]
        unsafe fn $fn(rop: *mut mpc_t, op1: *const mpc_t, op2: Self, rnd: rnd_t) -> c_int {
            if let Some(op2) = op2.checked_as() {
                $deleg_long(rop, op1, op2, rnd)
            } else {
                let small: SmallFloat = op2.into();
                $deleg(rop, op1, small.as_raw(), rnd)
            }
        }
    };
}
macro_rules! reverse {
    (fn $fn:ident() -> $deleg_long:path, $deleg:path) => {
        #[inline]
        unsafe fn $fn(rop: *mut mpc_t, op1: Self, op2: *const mpc_t, rnd: rnd_t) -> c_int {
            if let Some(op1) = op1.checked_as() {
                $deleg_long(rop, op1, op2, rnd)
            } else {
                let small: SmallFloat = op1.into();
                $deleg(rop, small.as_raw(), op2, rnd)
            }
        }
    };
}

impl<T> PrimOps<c_long> for T
where
    T: AsLong<Long = c_long> + CheckedCast<c_long> + Into<SmallFloat> + Into<SmallComplex>,
{
    forward! { fn add() -> xmpc::add_si, mpc::add_fr }
    forward! { fn sub() -> xmpc::sub_si, mpc::sub_fr }
    reverse! { fn sub_from() -> xmpc::si_sub, mpc::fr_sub }
    forward! { fn mul() -> xmpc::mul_si, mpc::mul_fr }
    forward! { fn div() -> xmpc::div_si, mpc::div_fr }
    reverse! { fn div_from() -> xmpc::si_div, mpc::fr_div }

    #[inline]
    unsafe fn pow(rop: *mut mpc_t, op1: *const mpc_t, op2: Self, rnd: rnd_t) -> c_int {
        let small: SmallFloat = op2.into();
        mpc::pow_fr(rop, op1, small.as_raw(), rnd)
    }

    #[inline]
    unsafe fn pow_from(rop: *mut mpc_t, op1: Self, op2: *const mpc_t, rnd: rnd_t) -> c_int {
        let small: SmallComplex = op1.into();
        mpc::pow(rop, small.as_raw(), op2, rnd)
    }
}

impl<T> PrimOps<c_ulong> for T
where
    T: AsLong<Long = c_ulong> + CheckedCast<c_ulong> + Into<SmallFloat> + Into<SmallComplex>,
{
    forward! { fn add() -> xmpc::add_ui, mpc::add_fr }
    forward! { fn sub() -> xmpc::sub_ui, mpc::sub_fr }
    reverse! { fn sub_from() -> xmpc::ui_sub, mpc::fr_sub }
    forward! { fn mul() -> xmpc::mul_ui, mpc::mul_fr }
    forward! { fn div() -> xmpc::div_ui, mpc::div_fr }
    reverse! { fn div_from() -> xmpc::ui_div, mpc::fr_div }

    #[inline]
    unsafe fn pow(rop: *mut mpc_t, op1: *const mpc_t, op2: Self, rnd: rnd_t) -> c_int {
        let small: SmallFloat = op2.into();
        mpc::pow_fr(rop, op1, small.as_raw(), rnd)
    }

    #[inline]
    unsafe fn pow_from(rop: *mut mpc_t, op1: Self, op2: *const mpc_t, rnd: rnd_t) -> c_int {
        let small: SmallComplex = op1.into();
        mpc::pow(rop, small.as_raw(), op2, rnd)
    }
}

impl<T> PrimOps<f64> for T
where
    T: AsLong<Long = f64> + CheckedCast<f64> + Into<SmallFloat> + Into<SmallComplex>,
{
    forward! { fn add() -> xmpc::add_d, mpc::add_fr }
    forward! { fn sub() -> xmpc::sub_d, mpc::sub_fr }
    reverse! { fn sub_from() -> xmpc::d_sub, mpc::fr_sub }
    forward! { fn mul() -> xmpc::mul_d, mpc::mul_fr }
    forward! { fn div() -> xmpc::div_d, mpc::div_fr }
    reverse! { fn div_from() -> xmpc::d_div, mpc::fr_div }

    #[inline]
    unsafe fn pow(rop: *mut mpc_t, op1: *const mpc_t, op2: Self, rnd: rnd_t) -> c_int {
        let small: SmallFloat = op2.into();
        mpc::pow_fr(rop, op1, small.as_raw(), rnd)
    }

    #[inline]
    unsafe fn pow_from(rop: *mut mpc_t, op1: Self, op2: *const mpc_t, rnd: rnd_t) -> c_int {
        let small: SmallComplex = op1.into();
        mpc::pow(rop, small.as_raw(), op2, rnd)
    }
}

#[inline]
unsafe fn add_mul(rop: *mut mpc_t, add: *const mpc_t, mul: MulIncomplete<'_>, rnd: rnd_t) -> c_int {
    mpc::fma(rop, mul.lhs.as_raw(), mul.rhs.as_raw(), add, rnd)
}

#[inline]
unsafe fn sub_mul(rop: *mut mpc_t, add: *const mpc_t, mul: MulIncomplete<'_>, rnd: rnd_t) -> c_int {
    xmpc::submul(rop, add, (mul.lhs.as_raw(), mul.rhs.as_raw()), rnd)
}

#[inline]
unsafe fn mul_sub(rop: *mut mpc_t, mul: MulIncomplete<'_>, sub: *const mpc_t, rnd: rnd_t) -> c_int {
    xmpc::mulsub(rop, (mul.lhs.as_raw(), mul.rhs.as_raw()), sub, rnd)
}

#[cfg(test)]
#[allow(clippy::cognitive_complexity)]
mod tests {
    #[cfg(feature = "rational")]
    use crate::Rational;
    use crate::{
        float::{self, arith::tests as float_tests, FreeCache, Special},
        ops::{NegAssign, Pow},
        Complex, Float,
    };
    #[cfg(feature = "integer")]
    use {crate::Integer, std::str::FromStr};

    #[test]
    fn check_neg() {
        let mut a = Complex::with_val(53, (Special::Zero, Special::NegZero));
        assert!(a.real().is_sign_positive() && a.imag().is_sign_negative());
        a.neg_assign();
        assert!(a.real().is_sign_negative() && a.imag().is_sign_positive());
        let a = -a;
        assert!(a.real().is_sign_positive() && a.imag().is_sign_negative());
        let a = Complex::with_val(53, -&a);
        assert!(a.real().is_sign_negative() && a.imag().is_sign_positive());

        float::free_cache(FreeCache::All);
    }

    fn same(a: Complex, b: Complex) -> bool {
        let (re_a, im_a) = a.into_real_imag();
        let (re_b, im_b) = b.into_real_imag();
        float_tests::same(re_a, re_b) && float_tests::same(im_a, im_b)
    }

    macro_rules! test_ref_op {
        ($first:expr, $second:expr) => {
            assert_eq!(
                Complex::with_val(53, $first),
                $second,
                "({}) != ({})",
                stringify!($first),
                stringify!($second)
            );
        };
    }

    #[test]
    fn check_ref_op() {
        let lhs = Complex::with_val(53, (12.25, -1.375));
        let rhs = Complex::with_val(53, (-1.375, 13));
        let pu = 30_u32;
        let pi = -15_i32;
        let ps = 31.625_f32;
        let pd = -1.5_f64;
        test_ref_op!(-&lhs, -lhs.clone());
        test_ref_op!(&lhs + &rhs, lhs.clone() + &rhs);
        test_ref_op!(&lhs - &rhs, lhs.clone() - &rhs);
        test_ref_op!(&lhs * &rhs, lhs.clone() * &rhs);
        test_ref_op!(&lhs / &rhs, lhs.clone() / &rhs);
        test_ref_op!((&lhs).pow(&rhs), lhs.clone().pow(&rhs));

        test_ref_op!(&lhs + pu, lhs.clone() + pu);
        test_ref_op!(&lhs - pu, lhs.clone() - pu);
        test_ref_op!(&lhs * pu, lhs.clone() * pu);
        test_ref_op!(&lhs / pu, lhs.clone() / pu);
        test_ref_op!(&lhs << pu, lhs.clone() << pu);
        test_ref_op!(&lhs >> pu, lhs.clone() >> pu);
        test_ref_op!((&lhs).pow(pu), lhs.clone().pow(pu));

        test_ref_op!(pu + &lhs, pu + lhs.clone());
        test_ref_op!(pu - &lhs, pu - lhs.clone());
        test_ref_op!(pu * &lhs, pu * lhs.clone());
        test_ref_op!(pu / &lhs, pu / lhs.clone());

        test_ref_op!(&lhs + pi, lhs.clone() + pi);
        test_ref_op!(&lhs - pi, lhs.clone() - pi);
        test_ref_op!(&lhs * pi, lhs.clone() * pi);
        test_ref_op!(&lhs / pi, lhs.clone() / pi);
        test_ref_op!(&lhs << pi, lhs.clone() << pi);
        test_ref_op!(&lhs >> pi, lhs.clone() >> pi);
        test_ref_op!((&lhs).pow(pi), lhs.clone().pow(pi));

        test_ref_op!(pi + &lhs, pi + lhs.clone());
        test_ref_op!(pi - &lhs, pi - lhs.clone());
        test_ref_op!(pi * &lhs, pi * lhs.clone());
        test_ref_op!(pi / &lhs, pi / lhs.clone());

        test_ref_op!((&lhs).pow(ps), lhs.clone().pow(ps));
        test_ref_op!((&lhs).pow(pd), lhs.clone().pow(pd));

        float::free_cache(FreeCache::All);
    }

    macro_rules! check_others {
        (&$list:expr, $against:expr) => {
            for op in &$list {
                let cop = Complex::with_val(150, op);
                for b in &$against {
                    assert!(same(b.clone() + op, b.clone() + &cop));
                    assert!(same(op + b.clone(), cop.clone() + b));
                    assert!(same(b.clone() - op, b.clone() - &cop));
                    assert!(same(op - b.clone(), cop.clone() - b));
                    if b.real().is_finite() && b.imag().is_finite() {
                        assert!(same(b.clone() * op, b.clone() * &cop));
                        assert!(same(op * b.clone(), cop.clone() * b));
                        if *op != 0 {
                            assert!(same(b.clone() / op, b.clone() / &cop));
                        }
                    }
                }
            }
        };
        ($list:expr, $against:expr, $zero:expr) => {
            for op in $list {
                let cop = Complex::with_val(150, *op);
                for b in &$against {
                    assert!(same(b.clone() + *op, b.clone() + &cop));
                    assert!(same(*op + b.clone(), cop.clone() + b));
                    assert!(same(b.clone() - *op, b.clone() - &cop));
                    assert!(same(*op - b.clone(), cop.clone() - b));
                    if b.real().is_finite() && b.imag().is_finite() {
                        assert!(same(b.clone() * *op, b.clone() * &cop));
                        assert!(same(*op * b.clone(), cop.clone() * b));
                        if *op != $zero {
                            assert!(same(b.clone() / *op, b.clone() / &cop));
                        }
                        if *b != 0i32 {
                            assert!(same(*op / b.clone(), cop.clone() / b));
                        }
                    }
                }
            }
        };
    }

    #[test]
    fn check_arith_others() {
        use crate::tests::{F32, F64, I128, I16, I32, I64, I8, U128, U16, U32, U64, U8};
        let large = [
            Complex::with_val(20, (Special::Zero, 1.0)),
            Complex::with_val(20, (Special::NegZero, 1.0)),
            Complex::with_val(20, (Special::Infinity, 1.0)),
            Complex::with_val(20, (Special::NegInfinity, 1.0)),
            Complex::with_val(20, (Special::Nan, 1.0)),
            Complex::with_val(20, (1, 1.0)),
            Complex::with_val(20, (-1, 1.0)),
            Complex::with_val(20, (999_999e100, 1.0)),
            Complex::with_val(20, (999_999e-100, 1.0)),
            Complex::with_val(20, (-999_999e100, 1.0)),
            Complex::with_val(20, (-999_999e-100, 1.0)),
        ];
        #[cfg(feature = "integer")]
        let z = [
            Integer::from(0),
            Integer::from(1),
            Integer::from(-1),
            Integer::from_str("-1000000000000").unwrap(),
            Integer::from_str("1000000000000").unwrap(),
        ];
        #[cfg(feature = "rational")]
        let q = [
            Rational::from(0),
            Rational::from(1),
            Rational::from(-1),
            Rational::from_str("-1000000000000/33333333333").unwrap(),
            Rational::from_str("1000000000000/33333333333").unwrap(),
        ];
        let f = [
            Float::with_val(20, 0.0),
            Float::with_val(20, 1.0),
            Float::with_val(20, -1.0),
            Float::with_val(20, 12.5),
            Float::with_val(20, 12.5) << 10000,
            Float::with_val(20, Special::Infinity),
        ];

        let mut against = large
            .iter()
            .cloned()
            .chain(U32.iter().map(|&x| Complex::with_val(20, x)))
            .chain(I32.iter().map(|&x| Complex::with_val(20, x)))
            .chain(U64.iter().map(|&x| Complex::with_val(20, x)))
            .chain(I64.iter().map(|&x| Complex::with_val(20, x)))
            .chain(U128.iter().map(|&x| Complex::with_val(20, x)))
            .chain(I128.iter().map(|&x| Complex::with_val(20, x)))
            .chain(F32.iter().map(|&x| Complex::with_val(20, x)))
            .chain(F64.iter().map(|&x| Complex::with_val(20, x)))
            .collect::<Vec<Complex>>();
        #[cfg(feature = "integer")]
        against.extend(z.iter().map(|x| Complex::with_val(20, x)));
        #[cfg(feature = "rational")]
        against.extend(q.iter().map(|x| Complex::with_val(20, x)));
        against.extend(f.iter().map(|x| Complex::with_val(20, x)));

        check_others!(I8, against, 0);
        check_others!(I16, against, 0);
        check_others!(I32, against, 0);
        check_others!(I64, against, 0);
        check_others!(I128, against, 0);
        check_others!(U8, against, 0);
        check_others!(U16, against, 0);
        check_others!(U32, against, 0);
        check_others!(U64, against, 0);
        check_others!(U128, against, 0);
        check_others!(F32, against, 0.0);
        check_others!(F64, against, 0.0);
        #[cfg(feature = "integer")]
        check_others!(&z, against);
        #[cfg(feature = "rational")]
        check_others!(&q, against);
        check_others!(&f, against);

        float::free_cache(FreeCache::All);
    }

    macro_rules! check_pow {
        ($list:expr, $against:expr) => {
            for op in $list {
                let cop = Complex::with_val(150, *op);
                for b in &$against {
                    assert!(same(b.clone().pow(*op), b.clone().pow(&cop)));
                    assert!(same(op.pow(b.clone()), cop.clone().pow(b)));
                }
            }
        };
    }

    #[test]
    fn check_pow() {
        use crate::tests::{F32, I32};
        use std::f64;
        let large = [
            Complex::with_val(20, (Special::Zero, 1.0)),
            Complex::with_val(20, (Special::NegZero, 1.0)),
            Complex::with_val(20, (Special::Infinity, 1.0)),
            Complex::with_val(20, (Special::NegInfinity, 1.0)),
            Complex::with_val(20, (Special::Nan, 1.0)),
            Complex::with_val(20, (1, 1.0)),
            Complex::with_val(20, (-1, 1.0)),
            Complex::with_val(20, (999_999e100, 1.0)),
            Complex::with_val(20, (999_999e-100, 1.0)),
            Complex::with_val(20, (-999_999e100, 1.0)),
            Complex::with_val(20, (-999_999e-100, 1.0)),
        ];
        let f = [
            Float::with_val(20, 0.0),
            Float::with_val(20, 1.0),
            Float::with_val(20, -1.0),
            Float::with_val(20, 12.5),
            Float::with_val(20, 12.5) << 10000,
            Float::with_val(20, Special::Infinity),
        ];

        let against = large
            .iter()
            .cloned()
            .chain(I32.iter().map(|&x| Complex::with_val(20, x)))
            .chain(F32.iter().map(|&x| Complex::with_val(20, x)))
            .chain(f.iter().map(|x| Complex::with_val(20, x)))
            .collect::<Vec<Complex>>();

        check_pow!(&[-1001i32, -1, 0, 1, 1001], against);
        check_pow!(&[0u32, 1, 1001], against);
        check_pow!(
            &[
                0.0,
                1.0,
                -1.0,
                1000.5,
                f64::NAN,
                f64::INFINITY,
                f64::NEG_INFINITY
            ],
            against
        );

        float::free_cache(FreeCache::All);
    }
}
