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
    integer::{small::Mpz, ToSmall},
    misc::{Limbs, MaybeLimb, LIMBS_IN_SMALL},
    Assign, Rational,
};
use az::Az;
use gmp_mpfr_sys::gmp::{self, limb_t, mpq_t};
use std::{mem, ops::Deref, sync::atomic::Ordering};

/**
A small rational number that does not require any memory allocation.

This can be useful when you have a numerator and denominator that are
primitive integer-types such as [`i64`] or [`u8`], and you need a
reference to a [`Rational`].

Although no allocation is required, setting the value of a
`SmallRational` does require some computation, as the numerator and
denominator need to be canonicalized.

The `SmallRational` type can be coerced to a [`Rational`], as it
implements
<code>[Deref]&lt;[Target] = [Rational][`Rational`]&gt;</code>.

# Examples

```rust
use rug::{rational::SmallRational, Rational};
// `a` requires a heap allocation
let mut a = Rational::from((100, 13));
// `b` can reside on the stack
let b = SmallRational::from((-100, 21));
a /= &*b;
assert_eq!(*a.numer(), -21);
assert_eq!(*a.denom(), 13);
```

[Deref]: https://doc.rust-lang.org/nightly/core/ops/trait.Deref.html
[Target]: https://doc.rust-lang.org/nightly/core/ops/trait.Deref.html#associatedtype.Target
[`Rational`]: ../struct.Rational.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
*/
#[repr(C)]
pub struct SmallRational {
    inner: Mpq,
    // numerator is first in limbs if inner.num.d <= inner.den.d
    first_limbs: Limbs,
    last_limbs: Limbs,
}

impl Clone for SmallRational {
    #[inline]
    fn clone(&self) -> SmallRational {
        let (first_limbs, last_limbs) = if self.num_is_first() {
            (&self.first_limbs, &self.last_limbs)
        } else {
            (&self.last_limbs, &self.first_limbs)
        };
        SmallRational {
            inner: self.inner.clone(),
            first_limbs: *first_limbs,
            last_limbs: *last_limbs,
        }
    }
}

#[derive(Clone)]
#[repr(C)]
struct Mpq {
    num: Mpz,
    den: Mpz,
}

fn _static_assertions() {
    static_assert_same_layout!(Mpq, mpq_t);
}

impl Default for SmallRational {
    #[inline]
    fn default() -> Self {
        SmallRational::new()
    }
}

impl SmallRational {
    /// Creates a [`SmallRational`] with value 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rational::SmallRational;
    /// let r = SmallRational::new();
    /// // Use r as if it were Rational.
    /// assert_eq!(*r.numer(), 0);
    /// assert_eq!(*r.denom(), 1);
    /// ```
    ///
    /// [`SmallRational`]: struct.SmallRational.html
    #[inline]
    pub fn new() -> Self {
        SmallRational {
            inner: Mpq {
                num: Mpz {
                    alloc: LIMBS_IN_SMALL.az(),
                    size: 0,
                    d: Default::default(),
                },
                den: Mpz {
                    alloc: LIMBS_IN_SMALL.az(),
                    size: 1,
                    d: Default::default(),
                },
            },
            first_limbs: small_limbs![0],
            last_limbs: small_limbs![1],
        }
    }

    /// Returns a mutable reference to a [`Rational`] number for
    /// simple operations that do not need to allocate more space for
    /// the numerator or denominator.
    ///
    /// # Safety
    ///
    /// It is undefined behaviour to perform operations that
    /// reallocate the internal data of the referenced [`Rational`]
    /// number or to swap it with another number, although it is
    /// allowed to swap the numerator and denominator allocations,
    /// such as in the reciprocal operation [`recip_mut`].
    ///
    /// Some GMP functions swap the allocations of their target
    /// operands; calling such functions with the mutable reference
    /// returned by this method can lead to undefined behaviour.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rational::SmallRational;
    /// let mut r = SmallRational::from((-15i32, 47i32));
    /// let num_capacity = r.numer().capacity();
    /// let den_capacity = r.denom().capacity();
    /// // reciprocating this will not require reallocations
    /// unsafe {
    ///     r.as_nonreallocating_rational().recip_mut();
    /// }
    /// assert_eq!(*r, (-47, 15));
    /// assert_eq!(r.numer().capacity(), num_capacity);
    /// assert_eq!(r.denom().capacity(), den_capacity);
    /// ```
    ///
    /// [`Rational`]: ../struct.Rational.html
    /// [`recip_mut`]: ../struct.Rational.html#method.recip_mut
    #[inline]
    pub unsafe fn as_nonreallocating_rational(&mut self) -> &mut Rational {
        self.update_d();
        let ptr = cast_ptr_mut!(&mut self.inner, Rational);
        &mut *ptr
    }

    /// Creates a [`SmallRational`] from a numerator and denominator,
    /// assuming they are in canonical form.
    ///
    /// # Safety
    ///
    /// This method leads to undefined behaviour if `den` is zero or
    /// if `num` and `den` have common factors.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rational::SmallRational;
    /// let from_unsafe = unsafe { SmallRational::from_canonical(-13, 10) };
    /// // from_safe is canonicalized to the same form as from_unsafe
    /// let from_safe = SmallRational::from((130, -100));
    /// assert_eq!(from_unsafe.numer(), from_safe.numer());
    /// assert_eq!(from_unsafe.denom(), from_safe.denom());
    /// ```
    ///
    /// [`SmallRational`]: struct.SmallRational.html
    pub unsafe fn from_canonical<Num: ToSmall, Den: ToSmall>(num: Num, den: Den) -> Self {
        let mut dst = SmallRational::default();
        dst.assign_canonical(num, den);
        dst
    }

    /// Assigns a numerator and denominator to a [`SmallRational`],
    /// assuming they are in canonical form.
    ///
    /// # Safety
    ///
    /// This method leads to undefined behaviour if `den` is zero or
    /// negative, or if `num` and `den` have common factors.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{rational::SmallRational, Assign};
    /// let mut a = SmallRational::new();
    /// unsafe {
    ///     a.assign_canonical(-13, 10);
    /// }
    /// // b is canonicalized to the same form as a
    /// let mut b = SmallRational::new();
    /// b.assign((130, -100));
    /// assert_eq!(a.numer(), b.numer());
    /// assert_eq!(a.denom(), b.denom());
    /// ```
    ///
    /// [`SmallRational`]: struct.SmallRational.html
    pub unsafe fn assign_canonical<Num: ToSmall, Den: ToSmall>(&mut self, num: Num, den: Den) {
        let (num_limbs, den_limbs) = if self.num_is_first() {
            (&mut self.first_limbs, &mut self.last_limbs)
        } else {
            (&mut self.last_limbs, &mut self.first_limbs)
        };
        num.copy(&mut self.inner.num.size, num_limbs);
        den.copy(&mut self.inner.den.size, den_limbs);
    }

    #[inline]
    fn num_is_first(&self) -> bool {
        (self.inner.num.d.load(Ordering::Relaxed) as usize)
            <= (self.inner.den.d.load(Ordering::Relaxed) as usize)
    }

    // To be used when offsetting num and den in case the struct has
    // been displaced in memory; if currently num.d <= den.d then
    // num.d points to first_limbs and den.d points to last_limbs,
    // otherwise num.d points to last_limbs and den.d points to
    // first_limbs.
    #[inline]
    fn update_d(&self) {
        // Since this is borrowed, the limbs won't move around, and we
        // can set the d fields.
        let first = self.first_limbs[0].as_ptr() as *mut limb_t;
        let last = self.last_limbs[0].as_ptr() as *mut limb_t;
        let (num_d, den_d) = if self.num_is_first() {
            (first, last)
        } else {
            (last, first)
        };
        self.inner.num.d.store(num_d, Ordering::Relaxed);
        self.inner.den.d.store(den_d, Ordering::Relaxed);
    }
}

impl Deref for SmallRational {
    type Target = Rational;
    #[inline]
    fn deref(&self) -> &Rational {
        self.update_d();
        let ptr = cast_ptr!(&self.inner, Rational);
        unsafe { &*ptr }
    }
}

impl<Num: ToSmall> Assign<Num> for SmallRational {
    #[inline]
    fn assign(&mut self, src: Num) {
        let (num_limbs, den_limbs) = if self.num_is_first() {
            (&mut self.first_limbs, &mut self.last_limbs)
        } else {
            (&mut self.last_limbs, &mut self.first_limbs)
        };
        src.copy(&mut self.inner.num.size, num_limbs);
        self.inner.den.size = 1;
        den_limbs[0] = MaybeLimb::new(1);
    }
}

impl<Num: ToSmall> From<Num> for SmallRational {
    fn from(src: Num) -> Self {
        let mut dst = SmallRational::default();
        src.copy(&mut dst.inner.num.size, &mut dst.first_limbs);
        dst.inner.den.size = 1;
        dst.last_limbs[0] = MaybeLimb::new(1);
        dst
    }
}

impl<Num: ToSmall, Den: ToSmall> Assign<(Num, Den)> for SmallRational {
    fn assign(&mut self, src: (Num, Den)) {
        assert!(!src.1.is_zero(), "division by zero");
        {
            let (num_limbs, den_limbs) = if self.num_is_first() {
                (&mut self.first_limbs, &mut self.last_limbs)
            } else {
                (&mut self.last_limbs, &mut self.first_limbs)
            };
            src.0.copy(&mut self.inner.num.size, num_limbs);
            src.1.copy(&mut self.inner.den.size, den_limbs);
        }
        unsafe {
            gmp::mpq_canonicalize(self.as_nonreallocating_rational().as_raw_mut());
        }
    }
}

impl<Num: ToSmall, Den: ToSmall> From<(Num, Den)> for SmallRational {
    fn from(src: (Num, Den)) -> Self {
        let mut dst = SmallRational::default();
        dst.assign(src);
        dst
    }
}

impl Assign<&Self> for SmallRational {
    #[inline]
    fn assign(&mut self, other: &Self) {
        self.clone_from(other);
    }
}

impl Assign for SmallRational {
    #[inline]
    fn assign(&mut self, other: Self) {
        drop(mem::replace(self, other));
    }
}

#[cfg(test)]
mod tests {
    use crate::{rational::SmallRational, Assign};

    #[test]
    fn check_assign() {
        let mut r = SmallRational::from((1, 2));
        assert_eq!(*r, (1, 2));
        r.assign(3);
        assert_eq!(*r, 3);
        let other = SmallRational::from((4, 5));
        r.assign(&other);
        assert_eq!(*r, (4, 5));
        r.assign((6, 7));
        assert_eq!(*r, (6, 7));
        r.assign(other);
        assert_eq!(*r, (4, 5));
    }
}
