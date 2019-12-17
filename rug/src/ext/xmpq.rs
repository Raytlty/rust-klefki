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

use crate::{
    ext::xmpz,
    misc::{AsOrPanic, NegAbs},
    ops::{NegAssign, SubFrom},
    rational::SmallRational,
    Assign, Integer, Rational,
};
use az::{Az, CheckedAs};
use gmp_mpfr_sys::gmp::{self, mpq_t};
use std::{
    cmp::Ordering,
    mem,
    os::raw::{c_int, c_long, c_ulong},
};

macro_rules! wrap {
    (fn $fn:ident($($op:ident),* $(; $param:ident: $T:ty)*) -> $deleg:path) => {
        #[inline]
        pub fn $fn(
            rop: &mut Rational,
            $($op: Option<&Rational>,)*
            $($param: $T,)*
        ) {
            unsafe {
                $deleg(
                    rop.as_raw_mut(),
                    $($op.unwrap_or(rop).as_raw(),)*
                    $($param.into(),)*
                );
            }
        }
    };
}

#[inline]
pub fn set(rop: &mut Rational, op: Option<&Rational>) {
    if let Some(op) = op {
        unsafe {
            gmp::mpq_set(rop.as_raw_mut(), op.as_raw());
        }
    }
}

#[inline]
pub unsafe fn clear(rop: &mut Rational) {
    gmp::mpq_clear(rop.as_raw_mut());
}

#[inline]
fn process_int_rat<F>(
    rint: Option<&mut Integer>,
    rrat: Option<&mut Rational>,
    op: Option<&Rational>,
    f: F,
) where
    F: FnOnce(&mut Integer, Option<&Integer>, &Integer),
{
    let (onum, oden) = match op {
        Some(r) => (Some(r.numer()), Some(r.denom())),
        None => (None, None),
    };
    if let Some(rrat) = rrat {
        let (rn, rd) = unsafe { rrat.as_mut_numer_denom_no_canonicalization() };
        f(rn, onum, oden.unwrap_or(rd));
        xmpz::set_1(rd);
    } else if let Some(rint) = rint {
        f(rint, onum, oden.expect("no denominator"));
    } else {
        panic!("no numerator");
    }
}

#[inline]
pub unsafe fn init_set(rop: *mut Rational, op: &Rational) {
    let rop = cast_ptr_mut!(rop, mpq_t);
    let num = cast_ptr_mut!(gmp::mpq_numref(rop), Integer);
    let den = cast_ptr_mut!(gmp::mpq_denref(rop), Integer);
    xmpz::init_set(num, op.numer());
    xmpz::init_set(den, op.denom());
}

#[inline]
pub fn signum(rint: Option<&mut Integer>, rrat: Option<&mut Rational>, op: Option<&Rational>) {
    process_int_rat(rint, rrat, op, |r, n, _| xmpz::signum(r, n))
}

#[inline]
pub fn trunc(rint: Option<&mut Integer>, rrat: Option<&mut Rational>, op: Option<&Rational>) {
    process_int_rat(rint, rrat, op, |r, n, d| xmpz::tdiv_q(r, n, Some(d)));
}

#[inline]
pub fn ceil(rint: Option<&mut Integer>, rrat: Option<&mut Rational>, op: Option<&Rational>) {
    process_int_rat(rint, rrat, op, |r, n, d| {
        // use tdiv_q rather than cdiv_q to let GMP not keep remainder
        if xmpz::is_1(d) {
            xmpz::set(r, n);
        } else {
            let neg = n.unwrap_or(r).cmp0() == Ordering::Less;
            xmpz::tdiv_q(r, n, Some(d));
            if !neg {
                xmpz::add_ui(r, None, 1);
            }
        }
    });
}

#[inline]
pub fn floor(rint: Option<&mut Integer>, rrat: Option<&mut Rational>, op: Option<&Rational>) {
    process_int_rat(rint, rrat, op, |r, n, d| {
        // use tdiv_q rather than fdiv_q to let GMP not keep remainder
        if xmpz::is_1(d) {
            xmpz::set(r, n);
        } else {
            let neg = n.unwrap_or(r).cmp0() == Ordering::Less;
            xmpz::tdiv_q(r, n, Some(d));
            if neg {
                xmpz::sub_ui(r, None, 1);
            }
        }
    });
}

pub fn round(rint: Option<&mut Integer>, rrat: Option<&mut Rational>, op: Option<&Rational>) {
    process_int_rat(rint, rrat, op, |r, n, d| {
        // The remainder cannot be larger than the divisor, but we
        // allocate an extra limb because the GMP docs suggest we should.
        let limbs = d.inner().size.abs().as_or_panic::<usize>() + 1;
        let bits = limbs
            .checked_mul(gmp::LIMB_BITS.az::<usize>())
            .expect("overflow");
        let mut rem = Integer::with_capacity(bits);
        xmpz::tdiv_qr(r, &mut rem, n, Some(d));
        if xmpz::round_away(&rem, d) {
            if rem.cmp0() == Ordering::Less {
                // negative number
                xmpz::sub_ui(r, None, 1);
            } else {
                // positive number
                xmpz::add_ui(r, None, 1);
            }
        }
    });
}

#[inline]
pub fn inv(rop: &mut Rational, op: Option<&Rational>) {
    assert_ne!(
        op.unwrap_or(rop).cmp0(),
        Ordering::Equal,
        "division by zero"
    );
    unsafe {
        gmp::mpq_inv(rop.as_raw_mut(), op.unwrap_or(rop).as_raw());
    }
}

#[inline]
pub fn trunc_fract(fract: &mut Rational, op: Option<&Rational>) {
    let op_num = op.map(Rational::numer);
    let op_den = op.map(Rational::denom);
    let (fract_num, fract_den) = unsafe { fract.as_mut_numer_denom_no_canonicalization() };
    xmpz::set(fract_den, op_den);
    xmpz::tdiv_r(fract_num, op_num, Some(fract_den));
}

#[inline]
pub fn ceil_fract(fract: &mut Rational, op: Option<&Rational>) {
    let op_num = op.map(Rational::numer);
    let op_den = op.map(Rational::denom);
    let (fract_num, fract_den) = unsafe { fract.as_mut_numer_denom_no_canonicalization() };
    xmpz::set(fract_den, op_den);
    xmpz::cdiv_r(fract_num, op_num, Some(fract_den));
}

#[inline]
pub fn floor_fract(fract: &mut Rational, op: Option<&Rational>) {
    let op_num = op.map(Rational::numer);
    let op_den = op.map(Rational::denom);
    let (fract_num, fract_den) = unsafe { fract.as_mut_numer_denom_no_canonicalization() };
    xmpz::set(fract_den, op_den);
    xmpz::fdiv_r(fract_num, op_num, Some(fract_den));
}

pub fn round_fract(fract: &mut Rational, op: Option<&Rational>) {
    let op_num = op.map(Rational::numer);
    let op_den = op.map(Rational::denom);
    let (fract_num, fract_den) = unsafe { fract.as_mut_numer_denom_no_canonicalization() };
    xmpz::set(fract_den, op_den);
    xmpz::tdiv_r(fract_num, op_num, Some(fract_den));
    if xmpz::round_away(fract_num, fract_den) {
        if fract_num.cmp0() == Ordering::Less {
            // negative number
            xmpz::add(fract_num, None, Some(fract_den));
        } else {
            // positive number
            xmpz::sub(fract_num, None, Some(fract_den));
        }
    }
}

#[inline]
pub fn square(rop: &mut Rational, op: Option<&Rational>) {
    unsafe {
        let (rop_num, rop_den) = rop.as_mut_numer_denom_no_canonicalization();
        let op_num = op.map(Rational::numer);
        let op_den = op.map(Rational::denom);
        xmpz::square(rop_num, op_num);
        xmpz::square(rop_den, op_den);
    }
}

wrap! { fn neg(op) -> gmp::mpq_neg }
wrap! { fn abs(op) -> gmp::mpq_abs }
wrap! { fn add(op1, op2) -> gmp::mpq_add }
wrap! { fn sub(op1, op2) -> gmp::mpq_sub }
wrap! { fn mul(op1, op2) -> gmp::mpq_mul }
wrap! { fn div(op1, op2) -> gmp::mpq_div }
wrap! { fn mul_2exp(op1; op2: u32) -> gmp::mpq_mul_2exp }
wrap! { fn div_2exp(op1; op2: u32) -> gmp::mpq_div_2exp }

#[inline]
pub fn set_0(rop: &mut Rational) {
    unsafe {
        let (num, den) = rop.as_mut_numer_denom_no_canonicalization();
        xmpz::set_0(num);
        xmpz::set_1(den);
    }
}

#[inline]
pub fn lshift_i32(rop: &mut Rational, op1: Option<&Rational>, op2: i32) {
    let (op2_neg, op2_abs) = op2.neg_abs();
    if !op2_neg {
        mul_2exp(rop, op1, op2_abs);
    } else {
        div_2exp(rop, op1, op2_abs);
    }
}

#[inline]
pub fn rshift_i32(rop: &mut Rational, op1: Option<&Rational>, op2: i32) {
    let (op2_neg, op2_abs) = op2.neg_abs();
    if !op2_neg {
        div_2exp(rop, op1, op2_abs);
    } else {
        mul_2exp(rop, op1, op2_abs);
    }
}

#[inline]
pub fn pow_u32(rop: &mut Rational, op1: Option<&Rational>, op2: u32) {
    unsafe {
        let (rop_num, rop_den) = rop.as_mut_numer_denom_no_canonicalization();
        let op1_num = op1.map(Rational::numer);
        let op1_den = op1.map(Rational::denom);
        xmpz::pow_u32(rop_num, op1_num, op2);
        xmpz::pow_u32(rop_den, op1_den, op2);
    }
}

#[inline]
pub fn pow_i32(rop: &mut Rational, op1: Option<&Rational>, op2: i32) {
    let (op2_neg, op2_abs) = op2.neg_abs();
    pow_u32(rop, op1, op2_abs);
    if op2_neg {
        inv(rop, None);
    }
}

#[inline]
pub fn trunc_fract_whole(fract: &mut Rational, trunc: &mut Integer, op: Option<&Rational>) {
    let op_num = op.map(Rational::numer);
    let op_den = op.map(Rational::denom);
    let (fract_num, fract_den) = unsafe { fract.as_mut_numer_denom_no_canonicalization() };
    xmpz::set(fract_den, op_den);
    unsafe {
        gmp::mpz_tdiv_qr(
            trunc.as_raw_mut(),
            fract_num.as_raw_mut(),
            op_num.unwrap_or(fract_num).as_raw(),
            fract_den.as_raw(),
        );
    }
}

#[inline]
pub fn ceil_fract_whole(fract: &mut Rational, ceil: &mut Integer, op: Option<&Rational>) {
    let op_num = op.map(Rational::numer);
    let op_den = op.map(Rational::denom);
    let (fract_num, fract_den) = unsafe { fract.as_mut_numer_denom_no_canonicalization() };
    xmpz::set(fract_den, op_den);
    unsafe {
        gmp::mpz_cdiv_qr(
            ceil.as_raw_mut(),
            fract_num.as_raw_mut(),
            op_num.unwrap_or(fract_num).as_raw(),
            fract_den.as_raw(),
        );
    }
}

#[inline]
pub fn floor_fract_whole(fract: &mut Rational, floor: &mut Integer, op: Option<&Rational>) {
    let op_num = op.map(Rational::numer);
    let op_den = op.map(Rational::denom);
    let (fract_num, fract_den) = unsafe { fract.as_mut_numer_denom_no_canonicalization() };
    xmpz::set(fract_den, op_den);
    unsafe {
        gmp::mpz_fdiv_qr(
            floor.as_raw_mut(),
            fract_num.as_raw_mut(),
            op_num.unwrap_or(fract_num).as_raw(),
            fract_den.as_raw(),
        );
    }
}

pub fn round_fract_whole(fract: &mut Rational, round: &mut Integer, op: Option<&Rational>) {
    let op_num = op.map(Rational::numer);
    let op_den = op.map(Rational::denom);
    let (fract_num, fract_den) = unsafe { fract.as_mut_numer_denom_no_canonicalization() };
    xmpz::set(fract_den, op_den);
    unsafe {
        gmp::mpz_tdiv_qr(
            round.as_raw_mut(),
            fract_num.as_raw_mut(),
            op_num.unwrap_or(fract_num).as_raw(),
            fract_den.as_raw(),
        );
    }
    if xmpz::round_away(fract_num, fract_den) {
        if fract_num.cmp0() == Ordering::Less {
            // negative number
            xmpz::sub_ui(round, None, 1);
            xmpz::add(fract_num, None, Some(fract_den));
        } else {
            // positive number
            xmpz::add_ui(round, None, 1);
            xmpz::sub(fract_num, None, Some(fract_den));
        }
    }
}

#[inline]
fn ord(o: c_int) -> Ordering {
    o.cmp(&0)
}

#[inline]
pub fn cmp(op1: &Rational, op2: &Rational) -> Ordering {
    ord(unsafe { gmp::mpq_cmp(op1.as_raw(), op2.as_raw()) })
}

#[inline]
pub fn equal(op1: &Rational, op2: &Rational) -> bool {
    (unsafe { gmp::mpq_equal(op1.as_raw(), op2.as_raw()) }) != 0
}

#[inline]
pub fn cmp_z(op1: &Rational, op2: &Integer) -> Ordering {
    ord(unsafe { gmp::mpq_cmp_z(op1.as_raw(), op2.as_raw()) })
}

#[inline]
pub fn cmp_u32(op1: &Rational, n2: u32, d2: u32) -> Ordering {
    ord(unsafe { gmp::mpq_cmp_ui(op1.as_raw(), n2.into(), d2.into()) })
}

#[inline]
pub fn cmp_i32(op1: &Rational, n2: i32, d2: u32) -> Ordering {
    ord(unsafe { gmp::mpq_cmp_si(op1.as_raw(), n2.into(), d2.into()) })
}

#[inline]
pub fn cmp_u64(op1: &Rational, n2: u64, d2: u64) -> Ordering {
    if let Some(n2) = n2.checked_as() {
        if let Some(d2) = d2.checked_as() {
            return ord(unsafe { gmp::mpq_cmp_ui(op1.as_raw(), n2, d2) });
        }
    }
    let small = SmallRational::from((n2, d2));
    ord(unsafe { gmp::mpq_cmp(op1.as_raw(), small.as_raw()) })
}

#[inline]
pub fn cmp_i64(op1: &Rational, n2: i64, d2: u64) -> Ordering {
    if let Some(n2) = n2.checked_as() {
        if let Some(d2) = d2.checked_as() {
            return ord(unsafe { gmp::mpq_cmp_si(op1.as_raw(), n2, d2) });
        }
    }
    let small = SmallRational::from((n2, d2));
    ord(unsafe { gmp::mpq_cmp(op1.as_raw(), small.as_raw()) })
}

#[inline]
pub fn cmp_u128(op1: &Rational, n2: u128, d2: u128) -> Ordering {
    if let Some(n2) = n2.checked_as() {
        if let Some(d2) = d2.checked_as() {
            return ord(unsafe { gmp::mpq_cmp_ui(op1.as_raw(), n2, d2) });
        }
    }
    let small = SmallRational::from((n2, d2));
    ord(unsafe { gmp::mpq_cmp(op1.as_raw(), small.as_raw()) })
}

#[inline]
pub fn cmp_i128(op1: &Rational, n2: i128, d2: u128) -> Ordering {
    if let Some(n2) = n2.checked_as() {
        if let Some(d2) = d2.checked_as() {
            return ord(unsafe { gmp::mpq_cmp_si(op1.as_raw(), n2, d2) });
        }
    }
    let small = SmallRational::from((n2, d2));
    ord(unsafe { gmp::mpq_cmp(op1.as_raw(), small.as_raw()) })
}

pub fn cmp_finite_d(op1: &Rational, op2: f64) -> Ordering {
    let num1 = op1.numer();
    let den1 = op1.denom();
    let den1_bits = den1.significant_bits();
    // cmp(num1, op2 * den1)
    let cmp;
    unsafe {
        let_uninit_ptr!(op2_f, op2_ptr);
        gmp::mpf_init2(op2_ptr, 53);
        let mut op2_f = assume_init!(op2_f);
        gmp::mpf_set_d(&mut op2_f, op2);
        let_uninit_ptr!(rhs, rhs_ptr);
        gmp::mpf_init2(rhs_ptr, (den1_bits + 53).as_or_panic());
        let mut rhs = assume_init!(rhs);
        gmp::mpf_set_z(&mut rhs, den1.as_raw());
        gmp::mpf_mul(&mut rhs, &rhs, &op2_f);
        cmp = -gmp::mpf_cmp_z(&rhs, num1.as_raw());
        gmp::mpf_clear(&mut rhs);
        gmp::mpf_clear(&mut op2_f);
    }
    ord(cmp)
}

pub fn add_z(rop: &mut Rational, lhs: Option<&Rational>, rhs: &Integer) {
    if let Some(lhs) = lhs {
        rop.assign(lhs);
    }
    // No canonicalization is necessary, as (numer + rhs * denom) is
    // not divisible by denom when numer is not divisible by denom.
    let (numer, denom) = unsafe { rop.as_mut_numer_denom_no_canonicalization() };
    *numer += rhs * &*denom;
}

pub fn sub_z(rop: &mut Rational, lhs: Option<&Rational>, rhs: &Integer) {
    if let Some(lhs) = lhs {
        rop.assign(lhs);
    }
    // No canonicalization is necessary, as (numer - rhs * denom) is
    // not divisible by denom when numer is not divisible by denom.
    let (numer, denom) = unsafe { rop.as_mut_numer_denom_no_canonicalization() };
    *numer -= rhs * &*denom;
}

pub fn z_sub(rop: &mut Rational, lhs: &Integer, rhs: Option<&Rational>) {
    if let Some(rhs) = rhs {
        rop.assign(rhs);
    }
    // No canonicalization is necessary, as (lhs * denom - numer) is
    // not divisible by denom when numer is not divisible by denom.
    let (numer, denom) = unsafe { rop.as_mut_numer_denom_no_canonicalization() };
    numer.sub_from(lhs * &*denom);
}

pub fn mul_z(rop: &mut Rational, lhs: Option<&Rational>, rhs: &Integer) {
    if rhs.cmp0() == Ordering::Equal {
        set_0(rop);
        return;
    }
    // Canonicalization is done in this function.
    //     gcd = gcd(lhs.denom, rhs)
    //     (numer, denom) = (rhs / gcd * lhs.numer, lhs.denom / gcd)
    let (numer, denom) = unsafe { rop.as_mut_numer_denom_no_canonicalization() };
    if let Some(lhs) = lhs {
        // store gcd temporarily in numer
        numer.assign(lhs.denom().gcd_ref(rhs));
        if !xmpz::is_1(numer) {
            denom.assign(lhs.denom().div_exact_ref(numer));
            numer.div_exact_from(rhs);
            *numer *= lhs.numer();
        } else {
            numer.assign(lhs.numer() * rhs);
            denom.assign(lhs.denom());
        }
    } else {
        let mut gcd = Integer::from(denom.gcd_ref(rhs));
        if !xmpz::is_1(&gcd) {
            denom.div_exact_mut(&gcd);
            gcd.div_exact_from(rhs);
            *numer *= gcd;
        } else {
            *numer *= rhs;
        }
    }
}

pub fn div_z(rop: &mut Rational, lhs: Option<&Rational>, rhs: &Integer) {
    xmpz::check_div0(rhs);
    // Canonicalization is done in this function.
    //     gcd = gcd(lhs.numer, rhs)
    //     (numer, denom) = (lhs.numer / gcd, rhs / gcd * lhs.denom)
    let (numer, denom) = unsafe { rop.as_mut_numer_denom_no_canonicalization() };
    if let Some(lhs) = lhs {
        // store gcd temporarily in numer
        numer.assign(lhs.numer().gcd_ref(rhs));
        if !xmpz::is_1(numer) {
            denom.assign(rhs.div_exact_ref(numer));
            *denom *= lhs.denom();
            numer.div_exact_from(lhs.numer());
        } else {
            numer.assign(lhs.numer());
            denom.assign(lhs.denom() * rhs);
        }
    } else {
        let mut gcd = Integer::from(numer.gcd_ref(rhs));
        if !xmpz::is_1(&gcd) {
            numer.div_exact_mut(&gcd);
            gcd.div_exact_from(rhs);
            *denom *= gcd;
        } else {
            *denom *= rhs;
        }
    }
    if denom.cmp0() == Ordering::Less {
        numer.neg_assign();
        denom.neg_assign();
    }
}

pub fn z_div(rop: &mut Rational, lhs: &Integer, rhs: Option<&Rational>) {
    xmpz::check_div0(rhs.unwrap_or(rop).numer());
    // Canonicalization is done in this function.
    //     gcd = gcd(lhs, rhs.numer)
    //     (numer, denom) = (lhs / gcd * rhs.denom, rhs.numer / gcd)
    let (numer, denom) = unsafe { rop.as_mut_numer_denom_no_canonicalization() };
    if let Some(rhs) = rhs {
        // store gcd temporarily in numer
        numer.assign(rhs.numer().gcd_ref(lhs));
        if !xmpz::is_1(numer) {
            denom.assign(rhs.numer().div_exact_ref(numer));
            numer.div_exact_from(lhs);
            *numer *= rhs.denom();
        } else {
            numer.assign(lhs * rhs.denom());
            denom.assign(rhs.numer());
        }
    } else {
        let mut gcd = Integer::from(numer.gcd_ref(lhs));
        mem::swap(numer, denom);
        if !xmpz::is_1(&gcd) {
            denom.div_exact_mut(&gcd);
            gcd.div_exact_from(lhs);
            *numer *= gcd;
        } else {
            *numer *= lhs;
        }
    }
    if denom.cmp0() == Ordering::Less {
        numer.neg_assign();
        denom.neg_assign();
    }
}

pub fn add_ui(rop: &mut Rational, lhs: Option<&Rational>, rhs: c_ulong) {
    if let Some(lhs) = lhs {
        rop.assign(lhs);
    }
    // No canonicalization is necessary, as (numer + rhs * denom) is
    // not divisible by denom when numer is not divisible by denom.
    let (numer, denom) = unsafe { rop.as_mut_numer_denom_no_canonicalization() };
    *numer += rhs * &*denom;
}

pub fn sub_ui(rop: &mut Rational, lhs: Option<&Rational>, rhs: c_ulong) {
    if let Some(lhs) = lhs {
        rop.assign(lhs);
    }
    // No canonicalization is necessary, as (numer + rhs * denom) is
    // not divisible by denom when numer is not divisible by denom.
    let (numer, denom) = unsafe { rop.as_mut_numer_denom_no_canonicalization() };
    *numer -= rhs * &*denom;
}

pub fn ui_sub(rop: &mut Rational, lhs: c_ulong, rhs: Option<&Rational>) {
    if let Some(rhs) = rhs {
        rop.assign(rhs);
    }
    // No canonicalization is necessary, as (numer + rhs * denom) is
    // not divisible by denom when numer is not divisible by denom.
    let (numer, denom) = unsafe { rop.as_mut_numer_denom_no_canonicalization() };
    numer.sub_from(lhs * &*denom);
}

#[inline]
pub fn add_si(rop: &mut Rational, op1: Option<&Rational>, op2: c_long) {
    match op2.neg_abs() {
        (false, op2_abs) => {
            add_ui(rop, op1, op2_abs);
        }
        (true, op2_abs) => {
            sub_ui(rop, op1, op2_abs);
        }
    }
}

#[inline]
pub fn sub_si(rop: &mut Rational, lhs: Option<&Rational>, rhs: c_long) {
    match rhs.neg_abs() {
        (false, rhs_abs) => {
            sub_ui(rop, lhs, rhs_abs);
        }
        (true, rhs_abs) => {
            add_ui(rop, lhs, rhs_abs);
        }
    }
}

#[inline]
pub fn si_sub(rop: &mut Rational, lhs: c_long, rhs: Option<&Rational>) {
    match lhs.neg_abs() {
        (false, lhs_abs) => {
            ui_sub(rop, lhs_abs, rhs);
        }
        (true, lhs_abs) => {
            add_ui(rop, rhs, lhs_abs);
            neg(rop, None);
        }
    }
}

pub fn mul_ui(rop: &mut Rational, lhs: Option<&Rational>, rhs: c_ulong) {
    if rhs == 0 {
        set_0(rop);
        return;
    }
    // Canonicalization is done in this function.
    //     gcd = gcd(lhs.denom, rhs), cannot be zero because rhs ≠ 0
    //     (numer, denom) = (rhs / gcd * lhs.numer, lhs.denom / gcd)
    let (numer, denom) = unsafe { rop.as_mut_numer_denom_no_canonicalization() };
    if let Some(lhs) = lhs {
        let gcd = xmpz::gcd_ui(None, Some(lhs.denom()), rhs);
        if gcd != 1 {
            numer.assign(rhs / gcd * lhs.numer());
            xmpz::divexact_ui(denom, Some(lhs.denom()), gcd);
        } else {
            numer.assign(rhs * lhs.numer());
            denom.assign(lhs.denom());
        }
    } else {
        let gcd = xmpz::gcd_ui(None, Some(denom), rhs);
        if gcd != 1 {
            *numer *= rhs / gcd;
            xmpz::divexact_ui(denom, None, gcd);
        } else {
            *numer *= rhs;
        }
    }
}

pub fn div_ui(rop: &mut Rational, lhs: Option<&Rational>, rhs: c_ulong) {
    assert_ne!(rhs, 0, "division by zero");
    // Canonicalization is done in this function.
    //     gcd = gcd(lhs.numer, rhs), cannot be zero because rhs ≠ 0
    //     (numer, denom) = (lhs.numer / gcd, rhs / gcd * lhs.denom)
    let (numer, denom) = unsafe { rop.as_mut_numer_denom_no_canonicalization() };
    if let Some(lhs) = lhs {
        let gcd = xmpz::gcd_ui(None, Some(lhs.numer()), rhs);
        if gcd != 1 {
            xmpz::divexact_ui(numer, Some(lhs.numer()), gcd);
            denom.assign(rhs / gcd * lhs.denom());
        } else {
            numer.assign(lhs.numer());
            denom.assign(rhs * lhs.denom());
        }
    } else {
        let gcd = xmpz::gcd_ui(None, Some(numer), rhs);
        if gcd != 1 {
            xmpz::divexact_ui(numer, None, gcd);
            *denom *= rhs / gcd;
        } else {
            *denom *= rhs;
        }
    }
    // since rhs is positive, denom is positive
}

pub fn ui_div(rop: &mut Rational, lhs: c_ulong, rhs: Option<&Rational>) {
    xmpz::check_div0(rhs.unwrap_or(rop).numer());
    if lhs == 0 {
        set_0(rop);
        return;
    }
    // Canonicalization is done in this function.
    //     gcd = gcd(lhs, rhs.numer), cannot be zero because lhs ≠ 0
    //     (numer, denom) = (lhs / gcd * rhs.denom, rhs.numer / gcd)
    let (numer, denom) = unsafe { rop.as_mut_numer_denom_no_canonicalization() };
    if let Some(rhs) = rhs {
        let gcd = xmpz::gcd_ui(None, Some(rhs.numer()), lhs);
        if gcd != 1 {
            numer.assign(lhs / gcd * rhs.denom());
            xmpz::divexact_ui(denom, Some(rhs.numer()), gcd);
        } else {
            numer.assign(lhs * rhs.denom());
            denom.assign(rhs.numer());
        }
    } else {
        let gcd = xmpz::gcd_ui(None, Some(numer), lhs);
        mem::swap(numer, denom);
        if gcd != 1 {
            *numer *= lhs / gcd;
            xmpz::divexact_ui(denom, None, gcd);
        } else {
            *numer *= lhs;
        }
    }
    if denom.cmp0() == Ordering::Less {
        numer.neg_assign();
        denom.neg_assign();
    }
}

#[inline]
pub fn mul_si(rop: &mut Rational, lhs: Option<&Rational>, rhs: c_long) {
    let (rhs_neg, rhs_abs) = rhs.neg_abs();
    mul_ui(rop, lhs, rhs_abs);
    if rhs_neg {
        neg(rop, None);
    }
}

#[inline]
pub fn div_si(rop: &mut Rational, lhs: Option<&Rational>, rhs: c_long) {
    let (rhs_neg, rhs_abs) = rhs.neg_abs();
    div_ui(rop, lhs, rhs_abs);
    if rhs_neg {
        neg(rop, None);
    }
}

#[inline]
pub fn si_div(rop: &mut Rational, lhs: c_long, rhs: Option<&Rational>) {
    let (lhs_neg, lhs_abs) = lhs.neg_abs();
    ui_div(rop, lhs_abs, rhs);
    if lhs_neg {
        neg(rop, None);
    }
}

#[cfg(test)]
mod tests {
    use crate::{ext::xmpq, Assign, Integer, Rational};

    #[test]
    fn check_add_sub_z() {
        let mut r = Rational::from((13, 7));
        let i = Integer::from(-5);

        // 13/7 + -5 = -22/7
        xmpq::add_z(&mut r, None, &i);
        assert_eq!(*r.numer(), -22);
        assert_eq!(*r.denom(), 7);

        // -22/7 - -5 = 13/7
        xmpq::sub_z(&mut r, None, &i);
        assert_eq!(*r.numer(), 13);
        assert_eq!(*r.denom(), 7);

        // -5 - 13/7 = -48/7
        xmpq::z_sub(&mut r, &i, None);
        assert_eq!(*r.numer(), -48);
        assert_eq!(*r.denom(), 7);
    }

    #[test]
    fn check_mul_z() {
        let mut r = Rational::from((13, 10));
        let mut rr = Rational::new();
        let mut i = Integer::from(-6);

        // 13/10 * -6 = -39/5
        xmpq::mul_z(&mut rr, Some(&r), &i);
        assert_eq!(*rr.numer(), -39);
        assert_eq!(*rr.denom(), 5);
        // 13/10 * 6 = 39/5
        xmpq::mul_z(&mut r, None, &i.as_neg());
        assert_eq!(*r.numer(), 39);
        assert_eq!(*r.denom(), 5);

        rr.assign(0);

        // 39/5 * -6 = -234/5
        xmpq::mul_z(&mut rr, Some(&r), &i);
        assert_eq!(*rr.numer(), -234);
        assert_eq!(*rr.denom(), 5);
        // 39/5 * 6 = 234/5
        xmpq::mul_z(&mut r, None, &i.as_neg());
        assert_eq!(*r.numer(), 234);
        assert_eq!(*r.denom(), 5);

        i.assign(0);
        xmpq::mul_z(&mut r, None, &i);
        assert_eq!(*r.numer(), 0);
        assert_eq!(*r.denom(), 1);
    }

    #[test]
    fn check_div_z() {
        let mut r = Rational::from((10, 13));
        let mut rr = Rational::new();
        let i = Integer::from(-6);

        // 10/13 / -6 = -5/39
        xmpq::div_z(&mut rr, Some(&r), &i);
        assert_eq!(*rr.numer(), -5);
        assert_eq!(*rr.denom(), 39);
        // 10/13 / 6 = 5/39
        xmpq::div_z(&mut r, None, &i.as_neg());
        assert_eq!(*r.numer(), 5);
        assert_eq!(*r.denom(), 39);

        rr.assign(0);

        // 5/39 / -6 = -5/234
        xmpq::div_z(&mut rr, Some(&r), &i);
        assert_eq!(*rr.numer(), -5);
        assert_eq!(*rr.denom(), 234);
        // 5/39 / 6 = 5/234
        xmpq::div_z(&mut r, None, &i.as_neg());
        assert_eq!(*r.numer(), 5);
        assert_eq!(*r.denom(), 234);
    }

    #[test]
    fn check_z_div() {
        let mut r = Rational::from((10, 13));
        let mut rr = Rational::new();
        let i = Integer::from(-6);

        // -6 / 10/13 = -39/5
        xmpq::z_div(&mut rr, &i, Some(&r));
        assert_eq!(*rr.numer(), -39);
        assert_eq!(*rr.denom(), 5);
        // 6 / 10/13 / 6 = 39/5
        xmpq::z_div(&mut r, &i.as_neg(), None);
        assert_eq!(*r.numer(), 39);
        assert_eq!(*r.denom(), 5);

        rr.assign(0);
        r.recip_mut();

        // -6 / 39/5 = -234/5
        xmpq::z_div(&mut rr, &i, Some(&r));
        assert_eq!(*rr.numer(), -234);
        assert_eq!(*rr.denom(), 5);
        // 6 / 39/5 = 234/5
        xmpq::z_div(&mut r, &i.as_neg(), None);
        assert_eq!(*r.numer(), 234);
        assert_eq!(*r.denom(), 5);
    }

    #[test]
    fn check_add_sub_ui_si() {
        let mut r = Rational::from((13, 7));
        let mut rr = Rational::new();

        // 13/7 + -5 = -22/7
        xmpq::add_si(&mut rr, Some(&r), -5);
        assert_eq!(*rr.numer(), -22);
        assert_eq!(*rr.denom(), 7);
        // 13/7 + 5 = 48/7
        xmpq::add_si(&mut rr, Some(&r), 5);
        assert_eq!(*rr.numer(), 48);
        assert_eq!(*rr.denom(), 7);
        xmpq::add_ui(&mut r, None, 5);
        assert_eq!(*r.numer(), 48);
        assert_eq!(*r.denom(), 7);

        rr.assign(0);

        // 48/7 - -5 = 83/7
        xmpq::sub_si(&mut rr, Some(&r), -5);
        assert_eq!(*rr.numer(), 83);
        assert_eq!(*rr.denom(), 7);
        // 48/7 - 5 = 13/7
        xmpq::sub_si(&mut rr, Some(&r), 5);
        assert_eq!(*rr.numer(), 13);
        assert_eq!(*rr.denom(), 7);
        xmpq::sub_ui(&mut r, None, 5);
        assert_eq!(*r.numer(), 13);
        assert_eq!(*r.denom(), 7);

        rr.assign(0);

        // -5 - 13/7 = -48/7
        xmpq::si_sub(&mut rr, -5, Some(&r));
        assert_eq!(*rr.numer(), -48);
        assert_eq!(*rr.denom(), 7);
        // 5 - 13/7 = 22/7
        xmpq::si_sub(&mut rr, 5, Some(&r));
        assert_eq!(*rr.numer(), 22);
        assert_eq!(*rr.denom(), 7);
        xmpq::ui_sub(&mut r, 5, None);
        assert_eq!(*r.numer(), 22);
        assert_eq!(*r.denom(), 7);
    }

    #[test]
    fn check_mul_ui_si() {
        let mut r = Rational::from((13, 10));
        let mut rr = Rational::new();

        // 13/10 * -6 = -39/5
        xmpq::mul_si(&mut rr, Some(&r), -6);
        assert_eq!(*rr.numer(), -39);
        assert_eq!(*rr.denom(), 5);
        // 13/10 * 6 = 39/5
        xmpq::mul_si(&mut rr, Some(&r), 6);
        assert_eq!(*rr.numer(), 39);
        assert_eq!(*rr.denom(), 5);
        xmpq::mul_ui(&mut r, None, 6);
        assert_eq!(*r.numer(), 39);
        assert_eq!(*r.denom(), 5);

        rr.assign(0);

        // 39/5 * -6 = -234/5
        xmpq::mul_si(&mut rr, Some(&r), -6);
        assert_eq!(*rr.numer(), -234);
        assert_eq!(*rr.denom(), 5);
        // 39/5 * 6 = 234/5
        xmpq::mul_si(&mut rr, Some(&r), 6);
        assert_eq!(*rr.numer(), 234);
        assert_eq!(*rr.denom(), 5);
        xmpq::mul_ui(&mut r, None, 6);
        assert_eq!(*r.numer(), 234);
        assert_eq!(*r.denom(), 5);

        xmpq::mul_si(&mut rr, Some(&r), 0);
        assert_eq!(*rr.numer(), 0);
        assert_eq!(*rr.denom(), 1);
        xmpq::mul_ui(&mut r, None, 0);
        assert_eq!(*r.numer(), 0);
        assert_eq!(*r.denom(), 1);
    }

    #[test]
    fn check_div_ui_si() {
        let mut r = Rational::from((10, 13));
        let mut rr = Rational::new();

        // 10/13 / -6 = -5/39
        xmpq::div_si(&mut rr, Some(&r), -6);
        assert_eq!(*rr.numer(), -5);
        assert_eq!(*rr.denom(), 39);
        // 10/13 / 6 = 5/39
        xmpq::div_si(&mut rr, Some(&r), 6);
        assert_eq!(*rr.numer(), 5);
        assert_eq!(*rr.denom(), 39);
        xmpq::div_ui(&mut r, None, 6);
        assert_eq!(*r.numer(), 5);
        assert_eq!(*r.denom(), 39);

        rr.assign(0);

        // 5/39 / -6 = -5/234
        xmpq::div_si(&mut rr, Some(&r), -6);
        assert_eq!(*rr.numer(), -5);
        assert_eq!(*rr.denom(), 234);
        // 5/39 / 6 = 5/234
        xmpq::div_si(&mut rr, Some(&r), 6);
        assert_eq!(*rr.numer(), 5);
        assert_eq!(*rr.denom(), 234);
        xmpq::div_ui(&mut r, None, 6);
        assert_eq!(*r.numer(), 5);
        assert_eq!(*r.denom(), 234);
    }

    #[test]
    fn check_ui_si_div() {
        let mut r = Rational::from((10, 13));
        let mut rr = Rational::new();

        // -6 / 10/13 = -39/5
        xmpq::si_div(&mut rr, -6, Some(&r));
        assert_eq!(*rr.numer(), -39);
        assert_eq!(*rr.denom(), 5);
        // 6 / 10/13 / 6 = 39/5
        xmpq::si_div(&mut rr, 6, Some(&r));
        assert_eq!(*rr.numer(), 39);
        assert_eq!(*rr.denom(), 5);
        xmpq::ui_div(&mut r, 6, None);
        assert_eq!(*r.numer(), 39);
        assert_eq!(*r.denom(), 5);

        rr.assign(0);
        r.recip_mut();

        // -6 / 39/5 = -234/5
        xmpq::si_div(&mut rr, -6, Some(&r));
        assert_eq!(*rr.numer(), -234);
        assert_eq!(*rr.denom(), 5);
        // 6 / 39/5 = 234/5
        xmpq::si_div(&mut rr, 6, Some(&r));
        assert_eq!(*rr.numer(), 234);
        assert_eq!(*rr.denom(), 5);
        xmpq::ui_div(&mut r, 6, None);
        assert_eq!(*r.numer(), 234);
        assert_eq!(*r.denom(), 5);
    }
}
