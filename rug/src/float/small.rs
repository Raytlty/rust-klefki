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
    ext::xmpfr::{self, raw_round},
    float::Round,
    misc::{AsOrPanic, Limbs, MaybeLimb, NegAbs},
    Assign, Float,
};
use az::Az;
use gmp_mpfr_sys::{
    gmp::{self, limb_t},
    mpfr::{self, exp_t, mpfr_t, prec_t},
};
use std::{
    mem,
    ops::Deref,
    os::raw::c_int,
    sync::atomic::{AtomicPtr, Ordering},
};

/**
A small float that does not require any memory allocation.

This can be useful when you have a primitive number type but need a
reference to a [`Float`]. The `SmallFloat` will have a precision
according to the type of the primitive used to set its value.

  * [`i8`], [`u8`]: the `SmallFloat` will have eight bits of
    precision.
  * [`i16`], [`u16`]: the `SmallFloat` will have 16 bits of precision.
  * [`i32`], [`u32`]: the `SmallFloat` will have 32 bits of precision.
  * [`i64`], [`u64`]: the `SmallFloat` will have 64 bits of precision.
  * [`i128`], [`u128`]: the `SmallFloat` will have 128 bits of
    precision.
  * [`isize`], [`usize`]: the `SmallFloat` will have 32 or 64 bits of
    precision, depending on the platform.
  * [`f32`]: the `SmallFloat` will have 24 bits of precision.
  * [`f64`]: the `SmallFloat` will have 53 bits of precision.

The `SmallFloat` type can be coerced to a [`Float`], as it implements
<code>[Deref]&lt;[Target] = [Float][`Float`]&gt;</code>.

# Examples

```rust
use rug::{float::SmallFloat, Float};
// `a` requires a heap allocation, has 53-bit precision
let mut a = Float::with_val(53, 250);
// `b` can reside on the stack
let b = SmallFloat::from(-100f64);
a += &*b;
assert_eq!(a, 150);
// another computation:
a *= &*b;
assert_eq!(a, -15000);
```

[Deref]: https://doc.rust-lang.org/nightly/core/ops/trait.Deref.html
[Target]: https://doc.rust-lang.org/nightly/core/ops/trait.Deref.html#associatedtype.Target
[`Float`]: ../struct.Float.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
*/
#[derive(Clone)]
#[repr(C)]
pub struct SmallFloat {
    inner: Mpfr,
    limbs: Limbs,
}

#[repr(C)]
pub struct Mpfr {
    pub prec: prec_t,
    pub sign: c_int,
    pub exp: exp_t,
    pub d: AtomicPtr<limb_t>,
}

fn _static_assertions() {
    static_assert!(mem::size_of::<Limbs>() == 16);
    static_assert_same_layout!(Mpfr, mpfr_t);
}

// Mpfr is only used inside SmallFloat and SmallComplex. The d field
// does not need to be copied from self. SmallComplex::clone is
// responsible to keep real and imag parts ordered.
impl Clone for Mpfr {
    #[inline]
    fn clone(&self) -> Mpfr {
        Mpfr {
            prec: self.prec,
            sign: self.sign,
            exp: self.exp,
            d: Default::default(),
        }
    }
}

impl SmallFloat {
    /// Returns a mutable reference to a [`Float`] for simple
    /// operations that do not need to change the precision of the
    /// number.
    ///
    /// # Safety
    ///
    /// It is undefined behaviour to modify the precision of the
    /// referenced [`Float`] or to swap it with
    /// another number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::float::SmallFloat;
    /// let mut f = SmallFloat::from(1.0f32);
    /// // addition does not change the precision
    /// unsafe {
    ///     *f.as_nonreallocating_float() += 2.0;
    /// }
    /// assert_eq!(*f, 3.0);
    /// ```
    ///
    /// [`Float`]: ../struct.Float.html
    #[inline]
    pub unsafe fn as_nonreallocating_float(&mut self) -> &mut Float {
        self.update_d();
        let ptr = cast_ptr_mut!(&mut self.inner, Float);
        &mut *ptr
    }

    #[inline]
    fn update_d(&self) {
        // Since this is borrowed, the limb won't move around, and we
        // can set the d field.
        let d = self.limbs[0].as_ptr() as *mut limb_t;
        self.inner.d.store(d, Ordering::Relaxed);
    }
}

impl Deref for SmallFloat {
    type Target = Float;
    #[inline]
    fn deref(&self) -> &Float {
        self.update_d();
        let ptr = cast_ptr!(&self.inner, Float);
        unsafe { &*ptr }
    }
}

/// Types implementing this trait can be converted to [`SmallFloat`].
///
/// The following are implemented when `T` implements `ToSmall`:
///   * <code>[Assign][`Assign`]&lt;T&gt; for [SmallFloat][`SmallFloat`]</code>
///   * <code>[From][`From`]&lt;T&gt; for [SmallFloat][`SmallFloat`]</code>
///
/// This trait is sealed and cannot be implemented for more types; it
/// is implemented for the integer types [`i8`], [`i16`], [`i32`],
/// [`i64`], [`i128`], [`isize`], [`u8`], [`u16`], [`u32`], [`u64`],
/// [`u128`] and [`usize`], and for the floating-point types [`f32`]
/// and [`f64`].
///
/// [`Assign`]: ../trait.Assign.html
/// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
/// [`SmallFloat`]: struct.SmallFloat.html
/// [`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
/// [`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
/// [`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
/// [`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
/// [`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
/// [`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
/// [`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
/// [`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
/// [`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
/// [`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
/// [`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
/// [`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
pub trait ToSmall: SealedToSmall {}

pub trait SealedToSmall: Copy {
    unsafe fn copy(self, inner: *mut Mpfr, limbs: &mut Limbs);
}

macro_rules! signed {
    ($($I:ty)*) => { $(
        impl ToSmall for $I {}
        impl SealedToSmall for $I {
            #[inline]
            unsafe fn copy(self, inner: *mut Mpfr, limbs: &mut Limbs) {
                let (neg, abs) = self.neg_abs();
                abs.copy(inner, limbs);
                if neg {
                    (*inner).sign = -1;
                }
            }
        }
    )* };
}

macro_rules! unsigned_32 {
    ($U:ty, $bits:expr) => {
        impl ToSmall for $U {}
        impl SealedToSmall for $U {
            #[inline]
            unsafe fn copy(self, inner: *mut Mpfr, limbs: &mut Limbs) {
                let ptr = cast_ptr_mut!(inner, mpfr_t);
                let limbs_ptr = limbs[0].as_mut_ptr();
                if self == 0 {
                    xmpfr::custom_zero(ptr, limbs_ptr, $bits);
                } else {
                    let leading = self.leading_zeros();
                    let limb_leading = leading + gmp::LIMB_BITS.az::<u32>() - $bits;
                    limbs[0] = MaybeLimb::new(limb_t::from(self) << limb_leading);
                    let exp = $bits - leading;
                    xmpfr::custom_regular(ptr, limbs_ptr, exp.as_or_panic(), $bits);
                }
            }
        }
    };
}

signed! { i8 i16 i32 i64 i128 isize }

unsigned_32! { u8, 8 }
unsigned_32! { u16, 16 }
unsigned_32! { u32, 32 }

impl ToSmall for u64 {}
impl SealedToSmall for u64 {
    #[inline]
    unsafe fn copy(self, inner: *mut Mpfr, limbs: &mut Limbs) {
        let ptr = cast_ptr_mut!(inner, mpfr_t);
        let limbs_ptr = limbs[0].as_mut_ptr();
        if self == 0 {
            xmpfr::custom_zero(ptr, limbs_ptr, 64);
        } else {
            let leading = self.leading_zeros();
            let sval = self << leading;
            #[cfg(gmp_limb_bits_64)]
            {
                limbs[0] = MaybeLimb::new(sval);
            }
            #[cfg(gmp_limb_bits_32)]
            {
                limbs[0] = MaybeLimb::new(sval as u32);
                limbs[1] = MaybeLimb::new((sval >> 32) as u32);
            }
            xmpfr::custom_regular(ptr, limbs_ptr, (64 - leading).as_or_panic(), 64);
        }
    }
}

impl ToSmall for u128 {}
impl SealedToSmall for u128 {
    #[inline]
    unsafe fn copy(self, inner: *mut Mpfr, limbs: &mut Limbs) {
        let ptr = cast_ptr_mut!(inner, mpfr_t);
        let limbs_ptr = limbs[0].as_mut_ptr();
        if self == 0 {
            xmpfr::custom_zero(ptr, limbs_ptr, 128);
        } else {
            let leading = self.leading_zeros();
            let sval = self << leading;
            #[cfg(gmp_limb_bits_64)]
            {
                limbs[0] = MaybeLimb::new(sval as u64);
                limbs[1] = MaybeLimb::new((sval >> 64) as u64);
            }
            #[cfg(gmp_limb_bits_32)]
            {
                limbs[0] = MaybeLimb::new(sval as u32);
                limbs[1] = MaybeLimb::new((sval >> 32) as u32);
                limbs[2] = MaybeLimb::new((sval >> 64) as u32);
                limbs[3] = MaybeLimb::new((sval >> 96) as u32);
            }
            xmpfr::custom_regular(ptr, limbs_ptr, (128 - leading).as_or_panic(), 128);
        }
    }
}

impl ToSmall for usize {}
impl SealedToSmall for usize {
    #[inline]
    unsafe fn copy(self, inner: *mut Mpfr, limbs: &mut Limbs) {
        #[cfg(target_pointer_width = "32")]
        {
            (self as u32).copy(inner, limbs);
        }
        #[cfg(target_pointer_width = "64")]
        {
            (self as u64).copy(inner, limbs);
        }
    }
}

impl ToSmall for f32 {}
impl SealedToSmall for f32 {
    #[inline]
    unsafe fn copy(self, inner: *mut Mpfr, limbs: &mut Limbs) {
        let ptr = cast_ptr_mut!(inner, mpfr_t);
        let limbs_ptr = limbs[0].as_mut_ptr();
        xmpfr::custom_zero(ptr, limbs_ptr, 24);
        mpfr::set_d(ptr, self.into(), raw_round(Round::Nearest));
        // retain sign in case of NaN
        if self.is_sign_negative() {
            (*inner).sign = -1;
        }
    }
}

impl ToSmall for f64 {}
impl SealedToSmall for f64 {
    #[inline]
    unsafe fn copy(self, inner: *mut Mpfr, limbs: &mut Limbs) {
        let ptr = cast_ptr_mut!(inner, mpfr_t);
        let limbs_ptr = limbs[0].as_mut_ptr();
        xmpfr::custom_zero(ptr, limbs_ptr, 53);
        mpfr::set_d(ptr, self, raw_round(Round::Nearest));
        // retain sign in case of NaN
        if self.is_sign_negative() {
            (*inner).sign = -1;
        }
    }
}

impl<T: ToSmall> Assign<T> for SmallFloat {
    #[inline]
    fn assign(&mut self, src: T) {
        unsafe {
            src.copy(&mut self.inner, &mut self.limbs);
        }
    }
}

impl<T: ToSmall> From<T> for SmallFloat {
    #[inline]
    fn from(src: T) -> Self {
        let mut dst = SmallFloat {
            inner: Mpfr {
                prec: 0,
                sign: 0,
                exp: 0,
                d: Default::default(),
            },
            limbs: small_limbs![],
        };
        unsafe {
            src.copy(&mut dst.inner, &mut dst.limbs);
        }
        dst
    }
}

impl Assign<&Self> for SmallFloat {
    #[inline]
    fn assign(&mut self, other: &Self) {
        self.clone_from(other);
    }
}

impl Assign for SmallFloat {
    #[inline]
    fn assign(&mut self, other: Self) {
        drop(mem::replace(self, other));
    }
}

#[cfg(test)]
#[allow(clippy::float_cmp)]
mod tests {
    use crate::{
        float::{self, FreeCache, SmallFloat},
        Assign,
    };

    #[test]
    fn check_assign() {
        let mut f = SmallFloat::from(-1.0f32);
        assert_eq!(*f, -1.0);
        f.assign(-2.0f64);
        assert_eq!(*f, -2.0);
        let other = SmallFloat::from(4u8);
        f.assign(&other);
        assert_eq!(*f, 4);
        f.assign(5i8);
        assert_eq!(*f, 5);
        f.assign(other);
        assert_eq!(*f, 4);
        f.assign(6u16);
        assert_eq!(*f, 6);
        f.assign(-6i16);
        assert_eq!(*f, -6);
        f.assign(6u32);
        assert_eq!(*f, 6);
        f.assign(-6i32);
        assert_eq!(*f, -6);
        f.assign(6u64);
        assert_eq!(*f, 6);
        f.assign(-6i64);
        assert_eq!(*f, -6);
        f.assign(6u128);
        assert_eq!(*f, 6);
        f.assign(-6i128);
        assert_eq!(*f, -6);
        f.assign(6usize);
        assert_eq!(*f, 6);
        f.assign(-6isize);
        assert_eq!(*f, -6);
        f.assign(0u32);
        assert_eq!(*f, 0);

        float::free_cache(FreeCache::All);
    }
}
