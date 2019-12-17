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

use crate::{complex::SmallComplex, ext::xmpfr, float::Round, Complex};
#[cfg(feature = "rational")]
use gmp_mpfr_sys::gmp::mpq_t;
#[cfg(feature = "integer")]
use gmp_mpfr_sys::gmp::mpz_t;
use gmp_mpfr_sys::{
    mpc::{self, mpc_t, rnd_t},
    mpfr::{self, rnd_t as mpfr_rnd_t},
};
use std::{
    cmp::Ordering,
    os::raw::{c_int, c_long, c_ulong},
};

pub type Round2 = (Round, Round);
pub const NEAREST2: Round2 = (Round::Nearest, Round::Nearest);

pub type Ordering2 = (Ordering, Ordering);

#[inline]
pub fn raw_round2(round: Round2) -> rnd_t {
    match (round.0, round.1) {
        (Round::Nearest, Round::Nearest) => mpc::RNDNN,
        (Round::Nearest, Round::Zero) => mpc::RNDNZ,
        (Round::Nearest, Round::Up) => mpc::RNDNU,
        (Round::Nearest, Round::Down) => mpc::RNDND,
        (Round::Zero, Round::Nearest) => mpc::RNDZN,
        (Round::Zero, Round::Zero) => mpc::RNDZZ,
        (Round::Zero, Round::Up) => mpc::RNDZU,
        (Round::Zero, Round::Down) => mpc::RNDZD,
        (Round::Up, Round::Nearest) => mpc::RNDUN,
        (Round::Up, Round::Zero) => mpc::RNDUZ,
        (Round::Up, Round::Up) => mpc::RNDUU,
        (Round::Up, Round::Down) => mpc::RNDUD,
        (Round::Down, Round::Nearest) => mpc::RNDDN,
        (Round::Down, Round::Zero) => mpc::RNDDZ,
        (Round::Down, Round::Up) => mpc::RNDDU,
        (Round::Down, Round::Down) => mpc::RNDDD,
        _ => unreachable!(),
    }
}

#[inline]
pub fn ordering2(ord: c_int) -> Ordering2 {
    // ord == first + 4 * second
    let first = mpc::INEX_RE(ord).cmp(&0);
    let second = mpc::INEX_IM(ord).cmp(&0);
    (first, second)
}

#[inline]
fn ordering4(ord: c_int) -> (Ordering2, Ordering2) {
    (ordering2(mpc::INEX1(ord)), ordering2(mpc::INEX2(ord)))
}

macro_rules! wrap {
    (fn $fn:ident($($op:ident),* $(; $param:ident: $T:ty)*) -> $deleg:path) => {
        #[inline]
        pub fn $fn(
            rop: &mut Complex,
            $($op: Option<&Complex>,)*
            $($param: $T,)*
            rnd: Round2,
        ) -> Ordering2 {
            ordering2(unsafe {
                $deleg(
                    rop.as_raw_mut(),
                    $($op.unwrap_or(rop).as_raw(),)*
                    $($param.into(),)*
                    raw_round2(rnd),
                )
            })
        }
    };
}

// do not use mpc::neg to avoid function call when op is None
#[inline]
pub fn neg(rop: &mut Complex, op: Option<&Complex>, rnd: Round2) -> Ordering2 {
    (
        xmpfr::neg(rop.mut_real(), op.map(Complex::real), rnd.0),
        xmpfr::neg(rop.mut_imag(), op.map(Complex::imag), rnd.1),
    )
}

#[inline]
pub fn mul_i(rop: &mut Complex, op: Option<&Complex>, neg: bool, rnd: Round2) -> Ordering2 {
    ordering2(unsafe {
        mpc::mul_i(
            rop.as_raw_mut(),
            op.unwrap_or(rop).as_raw(),
            if neg { -1 } else { 0 },
            raw_round2(rnd),
        )
    })
}

#[inline]
pub fn recip(rop: &mut Complex, op: Option<&Complex>, rnd: Round2) -> Ordering2 {
    let rop_ptr = rop.as_raw_mut();
    let op_ptr = op.unwrap_or(rop).as_raw();
    let rnd = raw_round2(rnd);
    ordering2(unsafe { ui_div(rop_ptr, 1, op_ptr, rnd) })
}

#[inline]
pub fn rootofunity(rop: &mut Complex, n: u32, k: u32, rnd: Round2) -> Ordering2 {
    ordering2(unsafe { mpc::rootofunity(rop.as_raw_mut(), n.into(), k.into(), raw_round2(rnd)) })
}

#[inline]
pub fn sin_cos(
    rop_sin: &mut Complex,
    rop_cos: &mut Complex,
    op: Option<&Complex>,
    rnd: Round2,
) -> (Ordering2, Ordering2) {
    ordering4(unsafe {
        mpc::sin_cos(
            rop_sin.as_raw_mut(),
            rop_cos.as_raw_mut(),
            op.unwrap_or(rop_sin).as_raw(),
            raw_round2(rnd),
            raw_round2(rnd),
        )
    })
}

wrap! { fn fma(op1, op2, op3) -> mpc::fma }

wrap! { fn proj(op) -> mpc::proj }
wrap! { fn sqr(op) -> mpc::sqr }
wrap! { fn sqrt(op) -> mpc::sqrt }
wrap! { fn conj(op) -> mpc::conj }
wrap! { fn log(op) -> mpc::log }
wrap! { fn log10(op) -> mpc::log10 }
wrap! { fn exp(op) -> mpc::exp }
wrap! { fn sin(op) -> mpc::sin }
wrap! { fn cos(op) -> mpc::cos }
wrap! { fn tan(op) -> mpc::tan }
wrap! { fn sinh(op) -> mpc::sinh }
wrap! { fn cosh(op) -> mpc::cosh }
wrap! { fn tanh(op) -> mpc::tanh }
wrap! { fn asin(op) -> mpc::asin }
wrap! { fn acos(op) -> mpc::acos }
wrap! { fn atan(op) -> mpc::atan }
wrap! { fn asinh(op) -> mpc::asinh }
wrap! { fn acosh(op) -> mpc::acosh }
wrap! { fn atanh(op) -> mpc::atanh }

macro_rules! sum_forward {
    (fn $name:ident($T:ty) -> $func:path) => {
        #[inline]
        pub unsafe fn $name(rop: *mut mpc_t, op1: *const mpc_t, op2: $T, rnd: rnd_t) -> c_int {
            let (rnd_re, rnd_im) = rnd_re_im(rnd);
            ord_ord(
                $func(mpc::realref(rop), mpc::realref_const(op1), op2, rnd_re),
                mpfr::set(mpc::imagref(rop), mpc::imagref_const(op1), rnd_im),
            )
        }
    };
}

macro_rules! sub_reverse {
    (fn $name:ident($T:ty) -> $func:path) => {
        #[inline]
        pub unsafe fn $name(rop: *mut mpc_t, op1: $T, op2: *const mpc_t, rnd: rnd_t) -> c_int {
            let (rnd_re, rnd_im) = rnd_re_im(rnd);
            ord_ord(
                $func(mpc::realref(rop), op1, mpc::realref_const(op2), rnd_re),
                mpfr::neg(mpc::imagref(rop), mpc::imagref_const(op2), rnd_im),
            )
        }
    };
}

macro_rules! prod_forward {
    (fn $name:ident($T:ty) -> $func:path) => {
        #[inline]
        pub unsafe fn $name(rop: *mut mpc_t, op1: *const mpc_t, op2: $T, rnd: rnd_t) -> c_int {
            let (rnd_re, rnd_im) = rnd_re_im(rnd);
            ord_ord(
                $func(mpc::realref(rop), mpc::realref_const(op1), op2, rnd_re),
                $func(mpc::imagref(rop), mpc::imagref_const(op1), op2, rnd_im),
            )
        }
    };
}

macro_rules! div_reverse {
    (fn $name:ident($T:ty) -> $func:path) => {
        #[inline]
        pub unsafe fn $name(rop: *mut mpc_t, op1: $T, op2: *const mpc_t, rnd: rnd_t) -> c_int {
            let op1 = SmallComplex::from(op1);
            mpc::div(rop, op1.as_raw(), op2, rnd)
        }
    };
}

sum_forward! { fn add_ui(c_ulong) -> mpfr::add_ui }
sum_forward! { fn add_si(c_long) -> mpfr::add_si }
sum_forward! { fn add_d(f64) -> mpfr::add_d }
#[cfg(feature = "integer")]
sum_forward! { fn add_z(*const mpz_t) -> mpfr::add_z }
#[cfg(feature = "rational")]
sum_forward! { fn add_q(*const mpq_t) -> mpfr::add_q }

sum_forward! { fn sub_ui(c_ulong) -> mpfr::sub_ui }
sum_forward! { fn sub_si(c_long) -> mpfr::sub_si }
sum_forward! { fn sub_d(f64) -> mpfr::sub_d }
#[cfg(feature = "integer")]
sum_forward! { fn sub_z(*const mpz_t) -> mpfr::sub_z }
#[cfg(feature = "rational")]
sum_forward! { fn sub_q(*const mpq_t) -> mpfr::sub_q }

sub_reverse! { fn ui_sub(c_ulong) -> mpfr::ui_sub }
sub_reverse! { fn si_sub(c_long) -> mpfr::si_sub }
sub_reverse! { fn d_sub(f64) -> mpfr::d_sub }
#[cfg(feature = "integer")]
sub_reverse! { fn z_sub(*const mpz_t) -> mpfr::z_sub }
#[cfg(feature = "rational")]
sub_reverse! { fn q_sub(*const mpq_t) -> xmpfr::q_sub }

prod_forward! { fn mul_ui(c_ulong) -> mpfr::mul_ui }
prod_forward! { fn mul_si(c_long) -> mpfr::mul_si }
prod_forward! { fn mul_d(f64) -> mpfr::mul_d }
#[cfg(feature = "integer")]
prod_forward! { fn mul_z(*const mpz_t) -> mpfr::mul_z }
#[cfg(feature = "rational")]
prod_forward! { fn mul_q(*const mpq_t) -> mpfr::mul_q }

prod_forward! { fn div_ui(c_ulong) -> mpfr::div_ui }
prod_forward! { fn div_si(c_long) -> mpfr::div_si }
prod_forward! { fn div_d(f64) -> mpfr::div_d }
#[cfg(feature = "integer")]
prod_forward! { fn div_z(*const mpz_t) -> mpfr::div_z }
#[cfg(feature = "rational")]
prod_forward! { fn div_q(*const mpq_t) -> mpfr::div_q }

div_reverse! { fn ui_div(c_ulong) -> mpfr::ui_div }
div_reverse! { fn si_div(c_long) -> mpfr::si_div }
div_reverse! { fn d_div(f64) -> mpfr::d_div }

#[inline]
pub unsafe fn mulsub(
    rop: *mut mpc_t,
    (m1, m2): (*const mpc_t, *const mpc_t),
    sub: *const mpc_t,
    rnd: rnd_t,
) -> c_int {
    let sub_complex = &*cast_ptr!(sub, Complex);
    let add = sub_complex.as_neg();
    mpc::fma(rop, m1, m2, add.as_raw(), rnd)
}

#[inline]
pub unsafe fn submul(
    rop: *mut mpc_t,
    add: *const mpc_t,
    (m1, m2): (*const mpc_t, *const mpc_t),
    rnd: rnd_t,
) -> c_int {
    let m1_complex = &*cast_ptr!(m1, Complex);
    let neg_m1 = m1_complex.as_neg();
    mpc::fma(rop, neg_m1.as_raw(), m2, add, rnd)
}

#[inline]
fn rnd_re_im(r: rnd_t) -> (mpfr_rnd_t, mpfr_rnd_t) {
    let re = match r & 0x0f {
        0 => mpfr_rnd_t::RNDN,
        1 => mpfr_rnd_t::RNDZ,
        2 => mpfr_rnd_t::RNDU,
        3 => mpfr_rnd_t::RNDD,
        _ => unreachable!(),
    };
    let im = match r >> 4 {
        0 => mpfr_rnd_t::RNDN,
        1 => mpfr_rnd_t::RNDZ,
        2 => mpfr_rnd_t::RNDU,
        3 => mpfr_rnd_t::RNDD,
        _ => unreachable!(),
    };
    (re, im)
}

#[inline]
fn ord_ord(re: c_int, im: c_int) -> c_int {
    let r = match re.cmp(&0) {
        Ordering::Less => 2,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    };
    let i = match im.cmp(&0) {
        Ordering::Less => 8,
        Ordering::Equal => 0,
        Ordering::Greater => 4,
    };
    r | i
}

#[inline]
pub unsafe fn shl_u32(rop: *mut mpc_t, op1: *const mpc_t, op2: u32, rnd: rnd_t) -> c_int {
    mpc::mul_2ui(rop, op1, op2.into(), rnd)
}

#[inline]
pub unsafe fn shr_u32(rop: *mut mpc_t, op1: *const mpc_t, op2: u32, rnd: rnd_t) -> c_int {
    mpc::div_2ui(rop, op1, op2.into(), rnd)
}

#[inline]
pub unsafe fn shl_i32(rop: *mut mpc_t, op1: *const mpc_t, op2: i32, rnd: rnd_t) -> c_int {
    mpc::mul_2si(rop, op1, op2.into(), rnd)
}

#[inline]
pub unsafe fn shr_i32(rop: *mut mpc_t, op1: *const mpc_t, op2: i32, rnd: rnd_t) -> c_int {
    mpc::div_2si(rop, op1, op2.into(), rnd)
}
