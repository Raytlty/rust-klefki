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
    ext::{xmpq, xmpz},
    rational::{big, ParseRationalError},
    Assign, Integer, Rational,
};
use gmp_mpfr_sys::gmp::{self, mpq_t};
use std::{
    cmp::Ordering,
    fmt::{Binary, Debug, Display, Formatter, LowerHex, Octal, Result as FmtResult, UpperHex},
    hash::{Hash, Hasher},
    mem,
    str::FromStr,
};
#[cfg(try_from)]
use {
    crate::rational::TryFromFloatError,
    std::{convert::TryFrom, error::Error},
};

impl Default for Rational {
    #[inline]
    fn default() -> Rational {
        Rational::new()
    }
}

impl Clone for Rational {
    #[inline]
    fn clone(&self) -> Rational {
        unsafe {
            let_uninit_ptr!(dst: Rational, dst_ptr);
            let inner_ptr = cast_ptr_mut!(dst_ptr, mpq_t);
            let num = cast_ptr_mut!(gmp::mpq_numref(inner_ptr), Integer);
            xmpz::init_set(num, self.numer());
            let den = cast_ptr_mut!(gmp::mpq_denref(inner_ptr), Integer);
            xmpz::init_set(den, self.denom());
            assume_init!(dst)
        }
    }

    #[inline]
    fn clone_from(&mut self, src: &Rational) {
        self.assign(src);
    }
}

impl Drop for Rational {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            xmpq::clear(self);
        }
    }
}

impl Hash for Rational {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.numer().hash(state);
        self.denom().hash(state);
    }
}

impl FromStr for Rational {
    type Err = ParseRationalError;
    #[inline]
    fn from_str(src: &str) -> Result<Rational, ParseRationalError> {
        Ok(Rational::from(Rational::parse(src)?))
    }
}

impl Display for Rational {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        fmt_radix(self, f, 10, false, "")
    }
}

impl Debug for Rational {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        fmt_radix(self, f, 10, false, "")
    }
}

impl Binary for Rational {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        fmt_radix(self, f, 2, false, "0b")
    }
}

impl Octal for Rational {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        fmt_radix(self, f, 8, false, "0o")
    }
}

impl LowerHex for Rational {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        fmt_radix(self, f, 16, false, "0x")
    }
}

impl UpperHex for Rational {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        fmt_radix(self, f, 16, true, "0x")
    }
}

impl Assign for Rational {
    #[inline]
    fn assign(&mut self, src: Rational) {
        drop(mem::replace(self, src));
    }
}

impl Assign<&Rational> for Rational {
    #[inline]
    fn assign(&mut self, src: &Rational) {
        xmpq::set(self, Some(src));
    }
}

impl From<&Rational> for Rational {
    #[inline]
    fn from(src: &Rational) -> Self {
        unsafe {
            let_uninit_ptr!(dst, dst_ptr);
            xmpq::init_set(dst_ptr, src);
            assume_init!(dst)
        }
    }
}

impl<Num> Assign<Num> for Rational
where
    Integer: Assign<Num>,
{
    #[inline]
    fn assign(&mut self, src: Num) {
        // no need to canonicalize, as denominator will be 1.
        let num_den = unsafe { self.as_mut_numer_denom_no_canonicalization() };
        num_den.0.assign(src);
        xmpz::set_1(num_den.1);
    }
}

impl<Num> From<Num> for Rational
where
    Integer: From<Num>,
{
    #[inline]
    fn from(src: Num) -> Self {
        unsafe {
            let_uninit_ptr!(dst: Rational, dst_ptr);
            let inner_ptr = cast_ptr_mut!(dst_ptr, mpq_t);
            let num = cast_ptr_mut!(gmp::mpq_numref(inner_ptr), Integer);
            num.write(Integer::from(src));
            let den = cast_ptr_mut!(gmp::mpq_denref(inner_ptr), Integer);
            xmpz::init_set_u32(den, 1);
            assume_init!(dst)
        }
    }
}

impl<Num, Den> Assign<(Num, Den)> for Rational
where
    Integer: Assign<Num> + Assign<Den>,
{
    #[inline]
    fn assign(&mut self, src: (Num, Den)) {
        self.mutate_numer_denom(move |num, den| {
            num.assign(src.0);
            den.assign(src.1);
        })
    }
}

impl<Num, Den> From<(Num, Den)> for Rational
where
    Integer: From<Num> + From<Den>,
{
    #[inline]
    fn from(src: (Num, Den)) -> Self {
        unsafe {
            let_uninit_ptr!(dst: Rational, dst_ptr);
            let inner_ptr = cast_ptr_mut!(dst_ptr, mpq_t);
            let num = cast_ptr_mut!(gmp::mpq_numref(inner_ptr), Integer);
            num.write(Integer::from(src.0));
            let den = cast_ptr_mut!(gmp::mpq_denref(inner_ptr), Integer);
            den.write(Integer::from(src.1));
            assert_ne!((*den).cmp0(), Ordering::Equal, "division by zero");
            gmp::mpq_canonicalize(inner_ptr);
            assume_init!(dst)
        }
    }
}

impl<'a, Num, Den> Assign<&'a (Num, Den)> for Rational
where
    Integer: Assign<&'a Num> + Assign<&'a Den>,
{
    #[inline]
    fn assign(&mut self, src: &'a (Num, Den)) {
        self.mutate_numer_denom(|num, den| {
            num.assign(&src.0);
            den.assign(&src.1);
        });
    }
}

impl<'a, Num, Den> From<&'a (Num, Den)> for Rational
where
    Integer: From<&'a Num> + From<&'a Den>,
{
    #[inline]
    fn from(src: &'a (Num, Den)) -> Self {
        unsafe {
            let_uninit_ptr!(dst: Rational, dst_ptr);
            let inner_ptr = cast_ptr_mut!(dst_ptr, mpq_t);
            let num = cast_ptr_mut!(gmp::mpq_numref(inner_ptr), Integer);
            num.write(Integer::from(&src.0));
            let den = cast_ptr_mut!(gmp::mpq_denref(inner_ptr), Integer);
            den.write(Integer::from(&src.1));
            assert_ne!((*den).cmp0(), Ordering::Equal, "division by zero");
            gmp::mpq_canonicalize(inner_ptr);
            assume_init!(dst)
        }
    }
}

#[cfg(try_from)]
impl TryFrom<f32> for Rational {
    type Error = TryFromFloatError;
    #[inline]
    fn try_from(value: f32) -> Result<Self, TryFromFloatError> {
        Rational::from_f32(value).ok_or(TryFromFloatError { _unused: () })
    }
}

#[cfg(try_from)]
impl TryFrom<f64> for Rational {
    type Error = TryFromFloatError;
    #[inline]
    fn try_from(value: f64) -> Result<Self, TryFromFloatError> {
        Rational::from_f64(value).ok_or(TryFromFloatError { _unused: () })
    }
}

fn fmt_radix(
    r: &Rational,
    f: &mut Formatter<'_>,
    radix: i32,
    to_upper: bool,
    prefix: &str,
) -> FmtResult {
    let mut s = String::new();
    big::append_to_string(&mut s, r, radix, to_upper);
    let neg = s.starts_with('-');
    let buf = if neg { &s[1..] } else { &s[..] };
    f.pad_integral(!neg, prefix, buf)
}

#[cfg(try_from)]
impl Error for TryFromFloatError {
    fn description(&self) -> &str {
        "conversion of infinite or NaN value attempted"
    }
}

#[cfg(try_from)]
impl Display for TryFromFloatError {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        Display::fmt(self.description(), f)
    }
}

unsafe impl Send for Rational {}
unsafe impl Sync for Rational {}

#[cfg(test)]
#[allow(clippy::float_cmp)]
mod tests {
    use crate::{Assign, Rational};
    #[cfg(try_from)]
    use std::convert::TryFrom;

    #[test]
    fn check_assign() {
        let mut r = Rational::from((1, 2));
        assert_eq!(r, (1, 2));
        let other = Rational::from((-2, 3));
        r.assign(&other);
        assert_eq!(r, (-2, 3));
        r.assign(-other);
        assert_eq!(r, (2, 3));
    }

    #[cfg(try_from)]
    #[test]
    fn check_fallible_conversions() {
        use crate::tests::{F32, F64};
        for &f in F32 {
            let r = Rational::try_from(f);
            assert_eq!(r.is_ok(), f.is_finite());
            #[cfg(feature = "float")]
            {
                if let Ok(r) = r {
                    assert_eq!(r, f);
                }
            }
        }
        for &f in F64 {
            let r = Rational::try_from(f);
            assert_eq!(r.is_ok(), f.is_finite());
            #[cfg(feature = "float")]
            {
                if let Ok(r) = r {
                    assert_eq!(r, f);
                }
            }
        }
    }
}
