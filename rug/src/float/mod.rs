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

/*!
Multi-precision floating-point numbers with correct rounding.

This module provides support for floating-point numbers of type
[`Float`].

[`Float`]: ../struct.Float.html
*/

pub(crate) mod arith;
pub(crate) mod big;
mod cmp;
mod ord;
#[cfg(feature = "serde")]
mod serde;
pub(crate) mod small;
mod traits;

pub use crate::float::{
    big::ParseFloatError,
    ord::OrdFloat,
    small::{SmallFloat, ToSmall},
};
use gmp_mpfr_sys::mpfr::{self, exp_t, prec_t};
use std::{i32, u32};

/**
Returns the minimum value for the exponent.

# Examples

```rust
use rug::float;
println!("Minimum exponent is {}", float::exp_min());
```
*/
#[inline]
pub fn exp_min() -> i32 {
    let min = unsafe { mpfr::get_emin() };
    if min > exp_t::from(i32::MIN) {
        min as i32
    } else {
        i32::MIN
    }
}

/**
Returns the maximum value for the exponent.

# Examples

```rust
use rug::float;
println!("Maximum exponent is {}", float::exp_max());
```
*/
#[inline]
pub fn exp_max() -> i32 {
    let max = unsafe { mpfr::get_emax() };
    if max < exp_t::from(i32::MAX) {
        max as i32
    } else {
        i32::MAX
    }
}

/**
Returns the minimum value for the precision.

# Examples

```rust
use rug::float;
println!("Minimum precision is {}", float::prec_min());
```
*/
#[inline]
pub const fn prec_min() -> u32 {
    mpfr::PREC_MIN as u32
}

/**
Returns the maximum value for the precision.

# Examples

```rust
use rug::float;
println!("Maximum precision is {}", float::prec_max());
```
*/
#[inline]
pub const fn prec_max() -> u32 {
    const MAX_FITS: bool = mpfr::PREC_MAX < u32::MAX as prec_t;
    const VALUES: [u32; 2] = [u32::MAX, mpfr::PREC_MAX as u32];
    VALUES[MAX_FITS as usize]
}

/**
The rounding methods for floating-point values.

When rounding to the nearest, if the number to be rounded is exactly
between two representable numbers, it is rounded to the even one, that
is, the one with the least significant bit set to zero.

# Examples

```rust
use rug::{float::Round, ops::AssignRound, Float};
let mut f4 = Float::new(4);
f4.assign_round(10.4, Round::Nearest);
assert_eq!(f4, 10);
f4.assign_round(10.6, Round::Nearest);
assert_eq!(f4, 11);
f4.assign_round(-10.7, Round::Zero);
assert_eq!(f4, -10);
f4.assign_round(10.3, Round::Up);
assert_eq!(f4, 11);
```

Rounding to the nearest will round numbers exactly between two
representable numbers to the even one.

```rust
use rug::{float::Round, ops::AssignRound, Float};
// 24 is 11000 in binary
// 25 is 11001 in binary
// 26 is 11010 in binary
// 27 is 11011 in binary
// 28 is 11100 in binary
let mut f4 = Float::new(4);
f4.assign_round(25, Round::Nearest);
assert_eq!(f4, 24);
f4.assign_round(27, Round::Nearest);
assert_eq!(f4, 28);
```
*/
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Round {
    /// Round towards the nearest.
    Nearest,
    /// Round towards zero.
    Zero,
    /// Round towards plus infinity.
    Up,
    /// Round towards minus infinity.
    Down,
    #[doc(hidden)]
    __Nonexhaustive,
}

impl Default for Round {
    #[inline]
    fn default() -> Round {
        Round::Nearest
    }
}

/**
The available floating-point constants.

# Examples

```rust
use rug::{float::Constant, Float};

let log2 = Float::with_val(53, Constant::Log2);
let pi = Float::with_val(53, Constant::Pi);
let euler = Float::with_val(53, Constant::Euler);
let catalan = Float::with_val(53, Constant::Catalan);

assert_eq!(log2.to_string_radix(10, Some(5)), "6.9315e-1");
assert_eq!(pi.to_string_radix(10, Some(5)), "3.1416");
assert_eq!(euler.to_string_radix(10, Some(5)), "5.7722e-1");
assert_eq!(catalan.to_string_radix(10, Some(5)), "9.1597e-1");
```
*/
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Constant {
    /// The logarithm of two, 0.693...
    Log2,
    /// The value of pi, 3.141...
    Pi,
    /// Euler’s constant, 0.577...
    Euler,
    /// Catalan’s constant, 0.915...
    Catalan,
    #[doc(hidden)]
    __Nonexhaustive,
}

/**
Special floating-point values.

# Examples

```rust
use rug::{float::Special, Float};

let zero = Float::with_val(53, Special::Zero);
let neg_zero = Float::with_val(53, Special::NegZero);
let infinity = Float::with_val(53, Special::Infinity);
let neg_infinity = Float::with_val(53, Special::NegInfinity);
let nan = Float::with_val(53, Special::Nan);

assert_eq!(zero, 0);
assert!(zero.is_sign_positive());
assert_eq!(neg_zero, 0);
assert!(neg_zero.is_sign_negative());
assert!(infinity.is_infinite());
assert!(infinity.is_sign_positive());
assert!(neg_infinity.is_infinite());
assert!(neg_infinity.is_sign_negative());
assert!(nan.is_nan());
```
*/
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Special {
    /// Positive zero.
    Zero,
    /// Negative zero.
    NegZero,
    /// Positive infinity.
    Infinity,
    /// Negative infinity.
    NegInfinity,
    /// Not a number.
    Nan,
    #[doc(hidden)]
    __Nonexhaustive,
}

/**
Specifies which cache to free.

# Examples

```rust
use rug::float::{self, FreeCache};
use std::thread;

fn main() {
    let child = thread::spawn(move || {
        // some work here that uses Float
        float::free_cache(FreeCache::Local);
    });
    // some work here
    child.join().expect("couldn't join thread");
    float::free_cache(FreeCache::All);
}
```
*/
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FreeCache {
    /// Free caches local to the current thread.
    Local,
    /// Free caches shared by all threads.
    Global,
    /// Free both local and global caches.
    All,
    #[doc(hidden)]
    __Nonexhaustive,
}

/**
Frees various caches and memory pools that are used internally.

To avoid memory leaks being reported when using tools like [Valgrind],
it is advisable to free thread-local caches before terminating a
thread and all caches before exiting.

# Examples

```rust
use rug::float::{self, FreeCache};
use std::thread;

fn main() {
    let child = thread::spawn(move || {
        // some work here that uses Float
        float::free_cache(FreeCache::Local);
    });
    // some work here
    child.join().expect("couldn't join thread");
    float::free_cache(FreeCache::All);
}
```

[Valgrind]: http://www.valgrind.org/
*/
#[inline]
pub fn free_cache(which: FreeCache) {
    let way = match which {
        FreeCache::Local => mpfr::FREE_LOCAL_CACHE,
        FreeCache::Global => mpfr::FREE_GLOBAL_CACHE,
        FreeCache::All => mpfr::FREE_LOCAL_CACHE | mpfr::FREE_GLOBAL_CACHE,
        _ => unreachable!(),
    };
    unsafe {
        mpfr::free_cache2(way);
    }
}

#[cfg(test)]
#[allow(clippy::cognitive_complexity, clippy::float_cmp)]
pub(crate) mod tests {
    #[cfg(feature = "rand")]
    use crate::rand::{RandGen, RandState};
    use crate::{
        float::{self, FreeCache, Round, Special},
        Assign, Float,
    };
    use gmp_mpfr_sys::{gmp, mpfr};
    use std::{
        cmp::Ordering,
        f64,
        fmt::{Debug, Error as FmtError, Formatter},
    };

    #[derive(Clone, Copy)]
    pub enum Cmp {
        F64(f64),
        Nan(bool),
    }

    impl Cmp {
        pub fn inf(neg: bool) -> Cmp {
            Cmp::F64(if neg {
                f64::NEG_INFINITY
            } else {
                f64::INFINITY
            })
        }
    }

    impl Debug for Cmp {
        fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
            match *self {
                Cmp::F64(ref val) => val.fmt(f),
                Cmp::Nan(negative) => {
                    let s = if negative { "-NaN" } else { "NaN" };
                    s.fmt(f)
                }
            }
        }
    }

    impl PartialEq<Cmp> for Float {
        fn eq(&self, other: &Cmp) -> bool {
            match *other {
                Cmp::F64(ref f) => self.eq(f),
                Cmp::Nan(negative) => self.is_nan() && self.is_sign_negative() == negative,
            }
        }
    }

    #[test]
    fn check_from_str() {
        assert!(Float::with_val(53, Float::parse("-0").unwrap()).is_sign_negative());
        assert!(Float::with_val(53, Float::parse("+0").unwrap()).is_sign_positive());
        assert!(Float::with_val(53, Float::parse("1e1000").unwrap()).is_finite());
        let huge_hex = "1@99999999999999999999999999999999";
        assert!(Float::with_val(53, Float::parse_radix(huge_hex, 16).unwrap()).is_infinite());

        let bad_strings = [
            ("", 10),
            ("-", 10),
            ("+", 10),
            (".", 10),
            ("inf", 11),
            ("@ nan @", 10),
            ("inf", 16),
            ("1.1.", 10),
            ("1e", 10),
            ("e10", 10),
            (".e10", 10),
            ("1e1.", 10),
            ("1e1e1", 10),
            ("1e+-1", 10),
            ("1e-+1", 10),
            ("+-1", 10),
            ("-+1", 10),
            ("infinit", 10),
            ("1@1a", 16),
            ("9", 9),
            ("nan(20) x", 10),
        ];
        for &(s, radix) in bad_strings.iter() {
            assert!(
                Float::parse_radix(s, radix).is_err(),
                "{} parsed correctly",
                s
            );
        }
        let good_strings = [
            ("INF", 10, Cmp::inf(false)),
            ("- @iNf@", 16, Cmp::inf(true)),
            ("+0e99", 2, Cmp::F64(0.0)),
            ("-9.9e1", 10, Cmp::F64(-99.0)),
            ("-.99e+2", 10, Cmp::F64(-99.0)),
            ("+99.e+0", 10, Cmp::F64(99.0)),
            ("-99@-1", 10, Cmp::F64(-9.9f64)),
            ("-a_b__.C_d_E_@3", 16, Cmp::F64(f64::from(-0xabcde))),
            ("1e1023", 2, Cmp::F64(2.0f64.powi(1023))),
            (" NaN() ", 10, Cmp::Nan(false)),
            (" + NaN (20 Number_Is) ", 10, Cmp::Nan(false)),
            (" - @nan@", 2, Cmp::Nan(true)),
        ];
        for &(s, radix, f) in good_strings.iter() {
            match Float::parse_radix(s, radix) {
                Ok(ok) => assert_eq!(Float::with_val(53, ok), f),
                Err(_err) => panic!("could not parse {}", s),
            }
        }

        float::free_cache(FreeCache::All);
    }

    #[test]
    fn check_clamping() {
        let mut f = Float::new(4);

        // Both 1.00002 and 1.00001 are rounded to 1.0 with the same
        // rounding direction, so these work even though min > max.

        f.assign(-1);
        let dir = f.clamp_round(&1.00002, &1.00001, Round::Down);
        assert_eq!(f, 1.0);
        assert_eq!(dir, Ordering::Less);

        f.assign(-1);
        let dir = f.clamp_round(&1.00002, &1.00001, Round::Up);
        assert_eq!(f, 1.125);
        assert_eq!(dir, Ordering::Greater);

        f.assign(2);
        let dir = f.clamp_round(&1.00002, &1.00001, Round::Down);
        assert_eq!(f, 1.0);
        assert_eq!(dir, Ordering::Less);

        f.assign(2);
        let dir = f.clamp_round(&1.00002, &1.00001, Round::Up);
        assert_eq!(f, 1.125);
        assert_eq!(dir, Ordering::Greater);

        float::free_cache(FreeCache::All);
    }

    #[test]
    #[should_panic(expected = "minimum larger than maximum")]
    fn check_clamping_panic() {
        let mut f = Float::new(4);
        f.assign(-1);
        // Both 1.00001 and 0.99999 would be rounded to 1.0, but one
        // would be larger and the other would be smaller.
        f.clamp(&1.00001, &0.99999);
    }

    #[test]
    fn check_formatting() {
        let mut f = Float::with_val(53, Special::Zero);
        assert_eq!(format!("{}", f), "0.0");
        assert_eq!(format!("{:?}", f), "0.0");
        assert_eq!(format!("{:+?}", f), "+0.0");
        f.assign(Special::NegZero);
        assert_eq!(format!("{}", f), "-0.0");
        assert_eq!(format!("{:?}", f), "-0.0");
        assert_eq!(format!("{:+?}", f), "-0.0");
        f.assign(Special::Infinity);
        assert_eq!(format!("{}", f), "inf");
        assert_eq!(format!("{:+}", f), "+inf");
        assert_eq!(format!("{:x}", f), "@inf@");
        f.assign(Special::NegInfinity);
        assert_eq!(format!("{}", f), "-inf");
        assert_eq!(format!("{:x}", f), "-@inf@");
        f.assign(Special::Nan);
        assert_eq!(format!("{}", f), "NaN");
        assert_eq!(format!("{:+}", f), "+NaN");
        assert_eq!(format!("{:x}", f), "@NaN@");
        f = -f;
        assert_eq!(format!("{}", f), "-NaN");
        assert_eq!(format!("{:x}", f), "-@NaN@");
        f.assign(-27);
        assert_eq!(format!("{:.2}", f), "-2.7e1");
        assert_eq!(format!("{:.4?}", f), "-2.700e1");
        assert_eq!(format!("{:.4e}", f), "-2.700e1");
        assert_eq!(format!("{:.4E}", f), "-2.700E1");
        assert_eq!(format!("{:.8b}", f), "-1.1011000e4");
        assert_eq!(format!("{:.3b}", f), "-1.11e4");
        assert_eq!(format!("{:#.8b}", f), "-0b1.1011000e4");
        assert_eq!(format!("{:.2o}", f), "-3.3e1");
        assert_eq!(format!("{:#.2o}", f), "-0o3.3e1");
        assert_eq!(format!("{:.2x}", f), "-1.b@1");
        assert_eq!(format!("{:.2X}", f), "-1.B@1");
        assert_eq!(format!("{:12.1x}", f), "      -1.b@1");
        assert_eq!(format!("{:012.3X}", f), "-000001.B0@1");
        assert_eq!(format!("{:#012.2x}", f), "-0x00001.b@1");
        assert_eq!(format!("{:#12.2X}", f), "    -0x1.B@1");

        float::free_cache(FreeCache::All);
    }

    #[test]
    fn check_assumptions() {
        assert_eq!(unsafe { mpfr::custom_get_size(64) }, 8);
        assert!(unsafe { mpfr::custom_get_size(32) } <= gmp::NUMB_BITS as usize);

        float::free_cache(FreeCache::All);
    }

    #[cfg(feature = "rand")]
    struct OnesZerosRand {
        one_words: u32,
    }

    #[cfg(feature = "rand")]
    impl RandGen for OnesZerosRand {
        fn gen(&mut self) -> u32 {
            if self.one_words > 0 {
                self.one_words -= 1;
                !0
            } else {
                0
            }
        }
    }

    #[cfg(feature = "rand")]
    #[test]
    fn check_nan_random_bits() {
        // Least significant 64 bits (two 32-bit words) of mantissa
        // will be ones, all others will be zeros. With 256 bits of
        // precision, the "random" number will be 0.0{192}1{64}. This
        // will be normalized to 0.1{64} * 2^-192.
        for i in 0..2 {
            let mut zeros_ones = OnesZerosRand { one_words: 2 };
            let mut rand = RandState::new_custom(&mut zeros_ones);
            let save_emin;
            unsafe {
                save_emin = mpfr::get_emin();
                mpfr::set_emin(-192 + i);
            }
            let f = Float::with_val(256, Float::random_bits(&mut rand));
            if i == 0 {
                assert_eq!(f, Float::with_val(64, !0u64) >> 256);
            } else {
                assert!(f.is_nan());
            }
            unsafe {
                mpfr::set_emin(save_emin);
            }
        }

        float::free_cache(FreeCache::All);
    }
}
