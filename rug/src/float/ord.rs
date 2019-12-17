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

use crate::Float;
use gmp_mpfr_sys::mpfr;
use std::{
    cmp::Ordering,
    hash::{Hash, Hasher},
};

/**
A float that supports total ordering and hashing.

Negative zero is ordered as less than positive zero. Negative NaN is
ordered as less than negative infinity, while positive NaN is ordered
as greater than positive infinity. Comparing two negative NaNs or two
positive NaNs produces equality.

# Examples

```rust
use rug::{
    float::{OrdFloat, Special},
    Float,
};
use std::cmp::Ordering;

let pos_nan_f = Float::with_val(53, Special::Nan);
let pos_inf_f = Float::with_val(53, Special::Infinity);
let pos_zero_f = Float::with_val(53, Special::Zero);
let neg_zero_f = Float::with_val(53, Special::NegZero);
let neg_inf_f = Float::with_val(53, Special::NegInfinity);
let neg_nan_f = Float::with_val(53, -&pos_nan_f);
let pos_nan = OrdFloat::from(pos_nan_f);
let pos_inf = OrdFloat::from(pos_inf_f);
let pos_zero = OrdFloat::from(pos_zero_f);
let neg_zero = OrdFloat::from(neg_zero_f);
let neg_inf = OrdFloat::from(neg_inf_f);
let neg_nan = OrdFloat::from(neg_nan_f);

assert_eq!(pos_nan.cmp(&pos_nan), Ordering::Equal);
assert_eq!(neg_nan.cmp(&neg_nan), Ordering::Equal);
assert_eq!(neg_nan.cmp(&pos_nan), Ordering::Less);

assert_eq!(pos_nan.cmp(&pos_inf), Ordering::Greater);
assert_eq!(neg_nan.cmp(&neg_inf), Ordering::Less);

assert_eq!(pos_zero.cmp(&neg_zero), Ordering::Greater);
```
*/
#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct OrdFloat {
    inner: Float,
}

fn _static_assertions() {
    static_assert_same_layout!(OrdFloat, Float);
}

impl OrdFloat {
    /// Extracts the underlying [`Float`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{float::OrdFloat, Float};
    /// let f = Float::with_val(53, 1.5);
    /// let ord = OrdFloat::from(f);
    /// let f_ref = ord.as_float();
    /// assert_eq!(f_ref.to_f64(), 1.5);
    /// ```
    ///
    /// [`Float`]: ../struct.Float.html
    #[inline]
    pub fn as_float(&self) -> &Float {
        &self.inner
    }

    /// Extracts the underlying [`Float`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{float::OrdFloat, Float};
    /// let f = Float::with_val(53, -1.5);
    /// let mut ord = OrdFloat::from(f);
    /// ord.as_float_mut().abs_mut();
    /// assert_eq!(ord.as_float().to_f64(), 1.5);
    /// ```
    ///
    /// [`Float`]: ../struct.Float.html
    #[inline]
    pub fn as_float_mut(&mut self) -> &mut Float {
        &mut self.inner
    }
}

impl Hash for OrdFloat {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let float = &self.inner;
        float.inner().sign.hash(state);
        float.inner().exp.hash(state);
        if float.is_normal() {
            let slice = float.inner_data();
            //   * Do not hash the least significant zero limbs, as
            //     equal numbers with different precisions must have
            //     equal hashes.
            //   * MPFR keeps unused bits set to zero, so there is no
            //     need to mask least significant limb.
            if let Some(first) = slice.iter().position(|&limb| limb != 0) {
                slice[first..].hash(state);
            }
        }
    }
}

impl Eq for OrdFloat {}

impl Ord for OrdFloat {
    #[inline]
    fn cmp(&self, other: &OrdFloat) -> Ordering {
        let s = &self.inner;
        let o = &other.inner;
        if s.is_zero() && o.is_zero() {
            s.is_sign_positive().cmp(&o.is_sign_positive())
        } else {
            match (s.is_nan(), o.is_nan()) {
                (false, true) => {
                    if o.is_sign_negative() {
                        Ordering::Greater
                    } else {
                        Ordering::Less
                    }
                }
                (true, false) => {
                    if o.is_sign_negative() {
                        Ordering::Less
                    } else {
                        Ordering::Greater
                    }
                }
                (true, true) => s.is_sign_positive().cmp(&o.is_sign_positive()),
                (false, false) => unsafe { mpfr::cmp(s.as_raw(), o.as_raw()).cmp(&0) },
            }
        }
    }
}

impl PartialEq for OrdFloat {
    #[inline]
    fn eq(&self, other: &OrdFloat) -> bool {
        let s = &self.inner;
        let o = &other.inner;
        if s.is_nan() {
            o.is_nan() && s.is_sign_negative() == o.is_sign_negative()
        } else if s.is_zero() {
            o.is_zero() && s.is_sign_negative() == o.is_sign_negative()
        } else {
            s.eq(o)
        }
    }
}

impl PartialOrd for OrdFloat {
    #[inline]
    fn partial_cmp(&self, other: &OrdFloat) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl From<Float> for OrdFloat {
    #[inline]
    fn from(src: Float) -> Self {
        OrdFloat { inner: src }
    }
}

impl From<OrdFloat> for Float {
    #[inline]
    fn from(src: OrdFloat) -> Self {
        src.inner
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        float::{self, FreeCache, Special},
        Float,
    };
    use std::{
        collections::hash_map::DefaultHasher,
        hash::{Hash, Hasher},
    };

    fn calculate_hash<T: Hash>(t: &T) -> u64 {
        let mut s = DefaultHasher::new();
        t.hash(&mut s);
        s.finish()
    }

    #[test]
    fn check_zero() {
        let p = Float::with_val(53, Special::Zero);
        let n = Float::with_val(53, Special::NegZero);
        assert_eq!(p, n);
        let ord_p = p.as_ord();
        let ord_n = n.as_ord();
        assert_eq!(ord_p, ord_p);
        assert_eq!(ord_n, ord_n);
        assert_eq!(calculate_hash(ord_p), calculate_hash(ord_p));
        assert_eq!(calculate_hash(ord_n), calculate_hash(ord_n));
        assert_ne!(ord_p, ord_n);
        assert_ne!(calculate_hash(ord_p), calculate_hash(ord_n));

        float::free_cache(FreeCache::All);
    }

    #[test]
    fn check_hash_different_prec() {
        let f = Float::with_val(53, 23.5);
        let g = Float::with_val(5301, 23.5);
        assert_eq!(f, g);
        let ord_f = f.as_ord();
        let ord_g = g.as_ord();
        assert_eq!(ord_f, ord_g);
        let mut hasher_f = DefaultHasher::new();
        ord_f.hash(&mut hasher_f);
        let hash_f = hasher_f.finish();
        let mut hasher_g = DefaultHasher::new();
        ord_g.hash(&mut hasher_g);
        let hash_g = hasher_g.finish();
        assert_eq!(hash_f, hash_g);
    }
}
