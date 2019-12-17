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
    ext::xmpfr::{self, ordering1, raw_round},
    float::{Round, SmallFloat},
    ops::{
        AddAssignRound, AddFrom, AddFromRound, AssignRound, DivAssignRound, DivFrom, DivFromRound,
        MulAssignRound, MulFrom, MulFromRound, NegAssign, Pow, PowAssign, PowAssignRound, PowFrom,
        PowFromRound, SubAssignRound, SubFrom, SubFromRound,
    },
    Float,
};
use az::{CheckedAs, CheckedCast};
use gmp_mpfr_sys::mpfr::{self, mpfr_t, rnd_t};
use std::{
    cmp::Ordering,
    ops::{
        Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Shl, ShlAssign, Shr, ShrAssign, Sub,
        SubAssign,
    },
    os::raw::{c_int, c_long, c_ulong},
};

impl Neg for Float {
    type Output = Float;
    #[inline]
    fn neg(mut self) -> Float {
        self.neg_assign();
        self
    }
}

impl NegAssign for Float {
    #[inline]
    fn neg_assign(&mut self) {
        xmpfr::neg(self, None, Round::Nearest);
    }
}

impl<'a> Neg for &'a Float {
    type Output = NegIncomplete<'a>;
    #[inline]
    fn neg(self) -> NegIncomplete<'a> {
        NegIncomplete { val: self }
    }
}

#[derive(Debug)]
pub struct NegIncomplete<'a> {
    val: &'a Float,
}

impl AssignRound<NegIncomplete<'_>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, src: NegIncomplete<'_>, round: Round) -> Ordering {
        xmpfr::neg(self, Some(src.val), round)
    }
}

macro_rules! arith_binary_self_float {
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
            Float, Round, Round::Nearest => Ordering;
            $func, raw_round => ordering1;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $ImpAssignRound { $method_assign_round }
            $ImpFrom { $method_from }
            $ImpFromRound { $method_from_round }
            $Incomplete
        }
    };
}

#[cfg(feature = "integer")]
macro_rules! arith_forward_float {
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
            Float, Round, Round::Nearest => Ordering;
            $func, raw_round => ordering1;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $ImpAssignRound { $method_assign_round }
            $T;
            $Incomplete, $OwnedIncomplete
        }
    };
}

#[cfg(feature = "integer")]
macro_rules! arith_commut_float {
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
            Float, Round, Round::Nearest => Ordering;
            $func, raw_round => ordering1;
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

#[cfg(feature = "integer")]
macro_rules! arith_noncommut_float {
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
            Float, Round, Round::Nearest => Ordering;
            $func, $func_from, raw_round => ordering1;
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

arith_binary_self_float! {
    mpfr::add;
    Add { add }
    AddAssign { add_assign }
    AddAssignRound { add_assign_round }
    AddFrom { add_from }
    AddFromRound { add_from_round }
    AddIncomplete
}
arith_binary_self_float! {
    mpfr::sub;
    Sub { sub }
    SubAssign { sub_assign }
    SubAssignRound { sub_assign_round }
    SubFrom { sub_from }
    SubFromRound { sub_from_round }
    SubIncomplete
}
arith_binary_self_float! {
    mpfr::mul;
    Mul { mul }
    MulAssign { mul_assign }
    MulAssignRound { mul_assign_round }
    MulFrom { mul_from }
    MulFromRound { mul_from_round }
    MulIncomplete
}
arith_binary_self_float! {
    mpfr::div;
    Div { div }
    DivAssign { div_assign }
    DivAssignRound { div_assign_round }
    DivFrom { div_from }
    DivFromRound { div_from_round }
    DivIncomplete
}
arith_binary_self_float! {
    mpfr::pow;
    Pow { pow }
    PowAssign { pow_assign }
    PowAssignRound { pow_assign_round }
    PowFrom { pow_from }
    PowFromRound { pow_from_round }
    PowIncomplete
}

#[cfg(feature = "integer")]
arith_commut_float! {
    mpfr::add_z;
    Add { add }
    AddAssign { add_assign }
    AddAssignRound { add_assign_round }
    AddFrom { add_from }
    AddFromRound { add_from_round }
    Integer;
    AddIntegerIncomplete, AddOwnedIntegerIncomplete
}
#[cfg(feature = "integer")]
arith_noncommut_float! {
    mpfr::sub_z, mpfr::z_sub;
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
arith_commut_float! {
    mpfr::mul_z;
    Mul { mul }
    MulAssign { mul_assign }
    MulAssignRound { mul_assign_round }
    MulFrom { mul_from }
    MulFromRound { mul_from_round }
    Integer;
    MulIntegerIncomplete, MulOwnedIntegerIncomplete
}
#[cfg(feature = "integer")]
arith_noncommut_float! {
    mpfr::div_z, xmpfr::z_div;
    Div { div }
    DivAssign { div_assign }
    DivAssignRound { div_assign_round }
    DivFrom { div_from }
    DivFromRound { div_from_round }
    Integer;
    DivIntegerIncomplete, DivOwnedIntegerIncomplete;
    DivFromIntegerIncomplete, DivFromOwnedIntegerIncomplete
}
#[cfg(feature = "integer")]
arith_forward_float! {
    mpfr::pow_z;
    Pow { pow }
    PowAssign { pow_assign }
    PowAssignRound { pow_assign_round }
    Integer;
    PowIntegerIncomplete, PowOwnedIntegerIncomplete
}

#[cfg(feature = "rational")]
arith_commut_float! {
    mpfr::add_q;
    Add { add }
    AddAssign { add_assign }
    AddAssignRound { add_assign_round }
    AddFrom { add_from }
    AddFromRound { add_from_round }
    Rational;
    AddRationalIncomplete, AddOwnedRationalIncomplete
}
#[cfg(feature = "rational")]
arith_noncommut_float! {
    mpfr::sub_q, xmpfr::q_sub;
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
arith_commut_float! {
    mpfr::mul_q;
    Mul { mul }
    MulAssign { mul_assign }
    MulAssignRound { mul_assign_round }
    MulFrom { mul_from }
    MulFromRound { mul_from_round }
    Rational;
    MulRationalIncomplete, MulOwnedRationalIncomplete
}
#[cfg(feature = "rational")]
arith_noncommut_float! {
    mpfr::div_q, xmpfr::q_div;
    Div { div }
    DivAssign { div_assign }
    DivAssignRound { div_assign_round }
    DivFrom { div_from }
    DivFromRound { div_from_round }
    Rational;
    DivRationalIncomplete, DivOwnedRationalIncomplete;
    DivFromRationalIncomplete, DivFromOwnedRationalIncomplete
}

macro_rules! arith_prim_exact_float {
    (
        $func:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $($T:ty, $Incomplete:ident;)*
    ) => {
        arith_prim_exact_round! {
            Float, Round, Round::Nearest => Ordering;
            $func, raw_round => ordering1;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $($T, $Incomplete;)*
        }
    };
}

macro_rules! arith_prim_commut_float {
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
            Float, Round, Round::Nearest => Ordering;
            $func, raw_round => ordering1;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $ImpAssignRound { $method_assign_round }
            $ImpFrom { $method_from }
            $ImpFromRound { $method_from_round }
            $($T, $Incomplete;)*
        }
    };
}

macro_rules! arith_prim_noncommut_float {
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
            Float, Round, Round::Nearest => Ordering;
            $func, $func_from, raw_round => ordering1;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $ImpAssignRound { $method_assign_round }
            $ImpFrom { $method_from }
            $ImpFromRound { $method_from_round }
            $($T, $Incomplete, $FromIncomplete;)*
        }
    };
}

arith_prim_commut_float! {
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
arith_prim_noncommut_float! {
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
arith_prim_commut_float! {
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
arith_prim_noncommut_float! {
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
arith_prim_noncommut_float! {
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

arith_prim_exact_float! {
    xmpfr::shl_u32;
    Shl { shl }
    ShlAssign { shl_assign }
    u32, ShlU32Incomplete;
}
arith_prim_exact_float! {
    xmpfr::shr_u32;
    Shr { shr }
    ShrAssign { shr_assign }
    u32, ShrU32Incomplete;
}
arith_prim_exact_float! {
    xmpfr::shl_i32;
    Shl { shl }
    ShlAssign { shl_assign }
    i32, ShlI32Incomplete;
}
arith_prim_exact_float! {
    xmpfr::shr_i32;
    Shr { shr }
    ShrAssign { shr_assign }
    i32, ShrI32Incomplete;
}
mul_op_commut_round! {
    Float, Round, Round::Nearest => Ordering;
    add_mul, raw_round => ordering1;
    Add { add }
    AddAssign { add_assign }
    AddAssignRound { add_assign_round }
    AddFrom { add_from }
    AddFromRound { add_from_round }
    MulIncomplete;
    AddMulIncomplete
}
mul_op_noncommut_round! {
    Float, Round, Round::Nearest => Ordering;
    sub_mul, mul_sub, raw_round => ordering1;
    Sub { sub }
    SubAssign { sub_assign }
    SubAssignRound { sub_assign_round }
    SubFrom { sub_from }
    SubFromRound { sub_from_round }
    MulIncomplete;
    SubMulIncomplete, SubMulFromIncomplete
}

trait PrimOps<Long>: AsLong {
    unsafe fn add(rop: *mut mpfr_t, op1: *const mpfr_t, op2: Self, rnd: rnd_t) -> c_int;
    unsafe fn sub(rop: *mut mpfr_t, op1: *const mpfr_t, op2: Self, rnd: rnd_t) -> c_int;
    unsafe fn sub_from(rop: *mut mpfr_t, op1: Self, op2: *const mpfr_t, rnd: rnd_t) -> c_int;
    unsafe fn mul(rop: *mut mpfr_t, op1: *const mpfr_t, op2: Self, rnd: rnd_t) -> c_int;
    unsafe fn div(rop: *mut mpfr_t, op1: *const mpfr_t, op2: Self, rnd: rnd_t) -> c_int;
    unsafe fn div_from(rop: *mut mpfr_t, op1: Self, op2: *const mpfr_t, rnd: rnd_t) -> c_int;
    unsafe fn pow(rop: *mut mpfr_t, op1: *const mpfr_t, op2: Self, rnd: rnd_t) -> c_int;
    unsafe fn pow_from(rop: *mut mpfr_t, op1: Self, op2: *const mpfr_t, rnd: rnd_t) -> c_int;
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
        unsafe fn $fn(rop: *mut mpfr_t, op1: *const mpfr_t, op2: Self, rnd: rnd_t) -> c_int {
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
        unsafe fn $fn(rop: *mut mpfr_t, op1: Self, op2: *const mpfr_t, rnd: rnd_t) -> c_int {
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
    T: AsLong<Long = c_long> + CheckedCast<c_long> + Into<SmallFloat>,
{
    forward! { fn add() -> mpfr::add_si, mpfr::add }
    forward! { fn sub() -> mpfr::sub_si, mpfr::sub }
    reverse! { fn sub_from() -> mpfr::si_sub, mpfr::sub }
    forward! { fn mul() -> mpfr::mul_si, mpfr::mul }
    forward! { fn div() -> mpfr::div_si, mpfr::div }
    reverse! { fn div_from() -> mpfr::si_div, mpfr::div }
    forward! { fn pow() -> mpfr::pow_si, mpfr::pow }

    #[inline]
    unsafe fn pow_from(rop: *mut mpfr_t, op1: Self, op2: *const mpfr_t, rnd: rnd_t) -> c_int {
        let small: SmallFloat = op1.into();
        mpfr::pow(rop, small.as_raw(), op2, rnd)
    }
}

impl<T> PrimOps<c_ulong> for T
where
    T: AsLong<Long = c_ulong> + CheckedCast<c_ulong> + Into<SmallFloat>,
{
    forward! { fn add() -> mpfr::add_ui, mpfr::add }
    forward! { fn sub() -> mpfr::sub_ui, mpfr::sub }
    reverse! { fn sub_from() -> mpfr::ui_sub, mpfr::sub }
    forward! { fn mul() -> mpfr::mul_ui, mpfr::mul }
    forward! { fn div() -> mpfr::div_ui, mpfr::div }
    reverse! { fn div_from() -> mpfr::ui_div, mpfr::div }
    forward! { fn pow() -> mpfr::pow_ui, mpfr::pow }
    reverse! { fn pow_from() -> mpfr::ui_pow, mpfr::pow }
}

impl<T> PrimOps<f64> for T
where
    T: AsLong<Long = f64> + CheckedCast<f64> + Into<SmallFloat>,
{
    forward! { fn add() -> mpfr::add_d, mpfr::add }
    forward! { fn sub() -> mpfr::sub_d, mpfr::sub }
    reverse! { fn sub_from() -> mpfr::d_sub, mpfr::sub }
    forward! { fn mul() -> mpfr::mul_d, mpfr::mul }
    forward! { fn div() -> mpfr::div_d, mpfr::div }
    reverse! { fn div_from() -> mpfr::d_div, mpfr::div }

    #[inline]
    unsafe fn pow(rop: *mut mpfr_t, op1: *const mpfr_t, op2: Self, rnd: rnd_t) -> c_int {
        let small: SmallFloat = op2.into();
        mpfr::pow(rop, op1, small.as_raw(), rnd)
    }

    #[inline]
    unsafe fn pow_from(rop: *mut mpfr_t, op1: Self, op2: *const mpfr_t, rnd: rnd_t) -> c_int {
        let small: SmallFloat = op1.into();
        mpfr::pow(rop, small.as_raw(), op2, rnd)
    }
}

impl<'a> Add for MulIncomplete<'a> {
    type Output = MulAddMulIncomplete<'a>;
    #[inline]
    fn add(self, rhs: MulIncomplete<'a>) -> MulAddMulIncomplete<'_> {
        MulAddMulIncomplete { lhs: self, rhs }
    }
}

#[derive(Debug)]
pub struct MulAddMulIncomplete<'a> {
    lhs: MulIncomplete<'a>,
    rhs: MulIncomplete<'a>,
}

impl AssignRound<MulAddMulIncomplete<'_>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, src: MulAddMulIncomplete<'_>, round: Round) -> Ordering {
        let ret = unsafe {
            mpfr::fmma(
                self.as_raw_mut(),
                src.lhs.lhs.as_raw(),
                src.lhs.rhs.as_raw(),
                src.rhs.lhs.as_raw(),
                src.rhs.rhs.as_raw(),
                raw_round(round),
            )
        };
        ordering1(ret)
    }
}

impl<'a> Sub for MulIncomplete<'a> {
    type Output = MulSubMulIncomplete<'a>;
    #[inline]
    fn sub(self, rhs: MulIncomplete<'a>) -> MulSubMulIncomplete<'_> {
        MulSubMulIncomplete { lhs: self, rhs }
    }
}

#[derive(Debug)]
pub struct MulSubMulIncomplete<'a> {
    lhs: MulIncomplete<'a>,
    rhs: MulIncomplete<'a>,
}

impl AssignRound<MulSubMulIncomplete<'_>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, src: MulSubMulIncomplete<'_>, round: Round) -> Ordering {
        let ret = unsafe {
            mpfr::fmms(
                self.as_raw_mut(),
                src.lhs.lhs.as_raw(),
                src.lhs.rhs.as_raw(),
                src.rhs.lhs.as_raw(),
                src.rhs.rhs.as_raw(),
                raw_round(round),
            )
        };
        ordering1(ret)
    }
}

#[inline]
unsafe fn add_mul(
    rop: *mut mpfr_t,
    add: *const mpfr_t,
    mul: MulIncomplete<'_>,
    rnd: rnd_t,
) -> c_int {
    mpfr::fma(rop, mul.lhs.as_raw(), mul.rhs.as_raw(), add, rnd)
}

#[inline]
unsafe fn sub_mul(
    rop: *mut mpfr_t,
    add: *const mpfr_t,
    mul: MulIncomplete<'_>,
    rnd: rnd_t,
) -> c_int {
    xmpfr::submul(rop, add, (mul.lhs.as_raw(), mul.rhs.as_raw()), rnd)
}

#[inline]
unsafe fn mul_sub(
    rop: *mut mpfr_t,
    mul: MulIncomplete<'_>,
    sub: *const mpfr_t,
    rnd: rnd_t,
) -> c_int {
    mpfr::fms(rop, mul.lhs.as_raw(), mul.rhs.as_raw(), sub, rnd)
}

#[cfg(test)]
#[allow(clippy::cognitive_complexity)]
pub(crate) mod tests {
    #[cfg(feature = "rational")]
    use crate::Rational;
    use crate::{
        float::{self, FreeCache, Special},
        ops::Pow,
        Float,
    };
    #[cfg(feature = "integer")]
    use {crate::Integer, std::str::FromStr};

    pub fn same(a: Float, b: Float) -> bool {
        if a.is_nan() && b.is_nan() {
            return true;
        }
        if a == b {
            return true;
        }
        if a.prec() == b.prec() {
            return false;
        }
        a == Float::with_val(a.prec(), b)
    }

    macro_rules! test_ref_op {
        ($first:expr, $second:expr) => {
            assert_eq!(
                Float::with_val(53, $first),
                $second,
                "({}) != ({})",
                stringify!($first),
                stringify!($second)
            );
        };
    }

    #[test]
    fn check_ref_op() {
        let lhs = Float::with_val(53, 12.25);
        let rhs = Float::with_val(53, -1.375);
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
        test_ref_op!(Pow::pow(pu, &lhs), Pow::pow(pu, lhs.clone()));

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

        test_ref_op!(&lhs + ps, lhs.clone() + ps);
        test_ref_op!(&lhs - ps, lhs.clone() - ps);
        test_ref_op!(&lhs * ps, lhs.clone() * ps);
        test_ref_op!(&lhs / ps, lhs.clone() / ps);

        test_ref_op!(ps + &lhs, ps + lhs.clone());
        test_ref_op!(ps - &lhs, ps - lhs.clone());
        test_ref_op!(ps * &lhs, ps * lhs.clone());
        test_ref_op!(ps / &lhs, ps / lhs.clone());

        test_ref_op!(&lhs + pd, lhs.clone() + pd);
        test_ref_op!(&lhs - pd, lhs.clone() - pd);
        test_ref_op!(&lhs * pd, lhs.clone() * pd);
        test_ref_op!(&lhs / pd, lhs.clone() / pd);

        test_ref_op!(pd + &lhs, pd + lhs.clone());
        test_ref_op!(pd - &lhs, pd - lhs.clone());
        test_ref_op!(pd * &lhs, pd * lhs.clone());
        test_ref_op!(pd / &lhs, pd / lhs.clone());

        float::free_cache(FreeCache::All);
    }

    macro_rules! check_others {
        (&$list:expr, $against:expr) => {
            for op in &$list {
                let fop = Float::with_val(150, op);
                for b in &$against {
                    assert!(same(b.clone() + op, b.clone() + &fop));
                    assert!(same(b.clone() - op, b.clone() - &fop));
                    assert!(same(b.clone() * op, b.clone() * &fop));
                    assert!(same(b.clone() / op, b.clone() / &fop));
                    assert!(same(op + b.clone(), fop.clone() + b));
                    assert!(same(op - b.clone(), fop.clone() - b));
                    assert!(same(op * b.clone(), fop.clone() * b));
                    assert!(same(op / b.clone(), fop.clone() / b));
                }
            }
        };
        ($list:expr, $against:expr) => {
            for op in $list {
                let fop = Float::with_val(150, *op);
                for b in &$against {
                    assert!(same(b.clone() + *op, b.clone() + &fop));
                    assert!(same(b.clone() - *op, b.clone() - &fop));
                    assert!(same(b.clone() * *op, b.clone() * &fop));
                    assert!(same(b.clone() / *op, b.clone() / &fop));
                    assert!(same(*op + b.clone(), fop.clone() + b));
                    assert!(same(*op - b.clone(), fop.clone() - b));
                    assert!(same(*op * b.clone(), fop.clone() * b));
                    assert!(same(*op / b.clone(), fop.clone() / b));
                    assert!(same(b.clone().pow(*op), b.clone().pow(&fop)));
                    assert!(same(op.pow(b.clone()), fop.clone().pow(b)));
                }
            }
        };
    }

    #[test]
    fn check_arith_others() {
        use crate::tests::{F32, F64, I128, I16, I32, I64, I8, U128, U16, U32, U64, U8};
        let large = [
            Float::with_val(20, Special::Zero),
            Float::with_val(20, Special::NegZero),
            Float::with_val(20, Special::Infinity),
            Float::with_val(20, Special::NegInfinity),
            Float::with_val(20, Special::Nan),
            Float::with_val(20, 1),
            Float::with_val(20, -1),
            Float::with_val(20, 999_999e100),
            Float::with_val(20, 999_999e-100),
            Float::with_val(20, -999_999e100),
            Float::with_val(20, -999_999e-100),
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

        let against = large
            .iter()
            .cloned()
            .chain(U32.iter().map(|&x| Float::with_val(20, x)))
            .chain(I32.iter().map(|&x| Float::with_val(20, x)))
            .chain(U64.iter().map(|&x| Float::with_val(20, x)))
            .chain(I64.iter().map(|&x| Float::with_val(20, x)))
            .chain(U128.iter().map(|&x| Float::with_val(20, x)))
            .chain(I128.iter().map(|&x| Float::with_val(20, x)))
            .chain(F32.iter().map(|&x| Float::with_val(20, x)))
            .chain(F64.iter().map(|&x| Float::with_val(20, x)))
            .collect::<Vec<Float>>();
        #[cfg(feature = "integer")]
        let mut against = against;
        #[cfg(feature = "integer")]
        against.extend(z.iter().map(|x| Float::with_val(20, x)));
        #[cfg(feature = "rational")]
        against.extend(q.iter().map(|x| Float::with_val(20, x)));

        check_others!(I8, against);
        check_others!(I16, against);
        check_others!(I32, against);
        check_others!(I64, against);
        check_others!(I128, against);
        check_others!(U8, against);
        check_others!(U16, against);
        check_others!(U32, against);
        check_others!(U64, against);
        check_others!(U128, against);
        check_others!(F32, against);
        check_others!(F64, against);
        #[cfg(feature = "integer")]
        check_others!(&z, against);
        #[cfg(feature = "rational")]
        check_others!(&q, against);

        float::free_cache(FreeCache::All);
    }
}
