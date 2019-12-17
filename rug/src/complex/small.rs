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
    ext::xmpfr,
    float::{small::Mpfr, ToSmall},
    misc::Limbs,
    Assign, Complex,
};
use gmp_mpfr_sys::{gmp::limb_t, mpc::mpc_t, mpfr::mpfr_t};
use std::{mem, ops::Deref, sync::atomic::Ordering};

/**
A small complex number that does not require any memory allocation.

This can be useful when you have real and imaginary numbers that are
primitive integers or floats and you need a reference to a
[`Complex`].

The `SmallComplex` will have a precision according to the types of the
primitives used to set its real and imaginary parts. Note that if
different types are used to set the parts, the parts can have
different precisions.

  * [`i8`], [`u8`]: the part will have eight bits of precision.
  * [`i16`], [`u16`]: the part will have 16 bits of precision.
  * [`i32`], [`u32`]: the part will have 32 bits of precision.
  * [`i64`], [`u64`]: the part will have 64 bits of precision.
  * [`i128`], [`u128`]: the part will have 128 bits of precision.
  * [`isize`], [`usize`]: the part will have 32 or 64 bits of
    precision, depending on the platform.
  * [`f32`]: the part will have 24 bits of precision.
  * [`f64`]: the part will have 53 bits of precision.

The `SmallComplex` type can be coerced to a [`Complex`], as it
implements
<code>[Deref]&lt;[Target] = [Complex][`Complex`]&gt;</code>.

# Examples

```rust
use rug::{complex::SmallComplex, Complex};
// `a` requires a heap allocation
let mut a = Complex::with_val(53, (1, 2));
// `b` can reside on the stack
let b = SmallComplex::from((-10f64, -20.5f64));
a += &*b;
assert_eq!(*a.real(), -9);
assert_eq!(*a.imag(), -18.5);
```

[Deref]: https://doc.rust-lang.org/nightly/core/ops/trait.Deref.html
[Target]: https://doc.rust-lang.org/nightly/core/ops/trait.Deref.html#associatedtype.Target
[`Complex`]: ../struct.Complex.html
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
#[repr(C)]
pub struct SmallComplex {
    inner: Mpc,
    // real part is first in limbs if inner.re.d <= inner.im.d
    first_limbs: Limbs,
    last_limbs: Limbs,
}

impl Clone for SmallComplex {
    #[inline]
    fn clone(&self) -> SmallComplex {
        let (first_limbs, last_limbs) = if self.re_is_first() {
            (&self.first_limbs, &self.last_limbs)
        } else {
            (&self.last_limbs, &self.first_limbs)
        };
        SmallComplex {
            inner: self.inner.clone(),
            first_limbs: *first_limbs,
            last_limbs: *last_limbs,
        }
    }
}

#[derive(Clone)]
#[repr(C)]
struct Mpc {
    re: Mpfr,
    im: Mpfr,
}

fn _static_assertions() {
    static_assert_same_layout!(Mpc, mpc_t);
}

impl SmallComplex {
    /// Returns a mutable reference to a [`Complex`] number for simple
    /// operations that do not need to change the precision of the
    /// real or imaginary part.
    ///
    /// # Safety
    ///
    /// It is undefined behaviour to modify the precision of the
    /// referenced [`Complex`] number or to swap it with another
    /// number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::complex::SmallComplex;
    /// let mut c = SmallComplex::from((1.0f32, 3.0f32));
    /// // rotation does not change the precision
    /// unsafe {
    ///     c.as_nonreallocating_complex().mul_i_mut(false);
    /// }
    /// assert_eq!(*c, (-3.0, 1.0));
    /// ```
    ///
    /// [`Complex`]: ../struct.Complex.html
    #[inline]
    pub unsafe fn as_nonreallocating_complex(&mut self) -> &mut Complex {
        self.update_d();
        let ptr = cast_ptr_mut!(&mut self.inner, Complex);
        &mut *ptr
    }

    #[inline]
    fn re_is_first(&self) -> bool {
        (self.inner.re.d.load(Ordering::Relaxed) as usize)
            <= (self.inner.im.d.load(Ordering::Relaxed) as usize)
    }

    // To be used when offsetting re and im in case the struct has
    // been displaced in memory; if currently re.d <= im.d then re.d
    // points to first_limbs and im.d points to last_limbs, otherwise
    // re.d points to last_limbs and im.d points to first_limbs.
    #[inline]
    fn update_d(&self) {
        // Since this is borrowed, the limbs won't move around, and we
        // can set the d fields.
        let first = self.first_limbs[0].as_ptr() as *mut limb_t;
        let last = self.last_limbs[0].as_ptr() as *mut limb_t;
        let (re_d, im_d) = if self.re_is_first() {
            (first, last)
        } else {
            (last, first)
        };
        self.inner.re.d.store(re_d, Ordering::Relaxed);
        self.inner.im.d.store(im_d, Ordering::Relaxed);
    }
}

impl Deref for SmallComplex {
    type Target = Complex;
    #[inline]
    fn deref(&self) -> &Complex {
        self.update_d();
        let ptr = cast_ptr!(&self.inner, Complex);
        unsafe { &*ptr }
    }
}

impl<Re: ToSmall> Assign<Re> for SmallComplex {
    fn assign(&mut self, src: Re) {
        unsafe {
            src.copy(&mut self.inner.re, &mut self.first_limbs);
            xmpfr::custom_zero(
                cast_ptr_mut!(&mut self.inner.im, mpfr_t),
                self.last_limbs[0].as_mut_ptr(),
                self.inner.re.prec,
            );
        }
    }
}

impl<Re: ToSmall> From<Re> for SmallComplex {
    fn from(src: Re) -> Self {
        let mut dst = SmallComplex {
            inner: Mpc {
                re: Mpfr {
                    prec: 0,
                    sign: 0,
                    exp: 0,
                    d: Default::default(),
                },
                im: Mpfr {
                    prec: 0,
                    sign: 0,
                    exp: 0,
                    d: Default::default(),
                },
            },
            first_limbs: small_limbs![],
            last_limbs: small_limbs![],
        };
        unsafe {
            src.copy(&mut dst.inner.re, &mut dst.first_limbs);
            xmpfr::custom_zero(
                cast_ptr_mut!(&mut dst.inner.im, mpfr_t),
                dst.last_limbs[0].as_mut_ptr(),
                dst.inner.re.prec,
            );
        }
        dst
    }
}

impl<Re: ToSmall, Im: ToSmall> Assign<(Re, Im)> for SmallComplex {
    fn assign(&mut self, src: (Re, Im)) {
        unsafe {
            src.0.copy(&mut self.inner.re, &mut self.first_limbs);
            src.1.copy(&mut self.inner.im, &mut self.last_limbs);
        }
    }
}

impl<Re: ToSmall, Im: ToSmall> From<(Re, Im)> for SmallComplex {
    fn from(src: (Re, Im)) -> Self {
        let mut dst = SmallComplex {
            inner: Mpc {
                re: Mpfr {
                    prec: 0,
                    sign: 0,
                    exp: 0,
                    d: Default::default(),
                },
                im: Mpfr {
                    prec: 0,
                    sign: 0,
                    exp: 0,
                    d: Default::default(),
                },
            },
            first_limbs: small_limbs![],
            last_limbs: small_limbs![],
        };
        unsafe {
            src.0.copy(&mut dst.inner.re, &mut dst.first_limbs);
            src.1.copy(&mut dst.inner.im, &mut dst.last_limbs);
        }
        dst
    }
}

impl Assign<&Self> for SmallComplex {
    #[inline]
    fn assign(&mut self, other: &Self) {
        self.clone_from(other);
    }
}

impl Assign for SmallComplex {
    #[inline]
    fn assign(&mut self, other: Self) {
        drop(mem::replace(self, other));
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        complex::SmallComplex,
        float::{self, FreeCache},
        Assign,
    };

    #[test]
    fn check_assign() {
        let mut c = SmallComplex::from((1.0, 2.0));
        assert_eq!(*c, (1.0, 2.0));
        c.assign(3.0);
        assert_eq!(*c, (3.0, 0.0));
        let other = SmallComplex::from((4.0, 5.0));
        c.assign(&other);
        assert_eq!(*c, (4.0, 5.0));
        c.assign((6.0, 7.0));
        assert_eq!(*c, (6.0, 7.0));
        c.assign(other);
        assert_eq!(*c, (4.0, 5.0));

        float::free_cache(FreeCache::All);
    }
}
