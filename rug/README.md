<!-- Copyright © 2016–2019 University of Malta -->

<!-- Copying and distribution of this file, with or without
modification, are permitted in any medium without royalty provided the
copyright notice and this notice are preserved. This file is offered
as-is, without any warranty. -->

# Arbitrary-precision numbers

Rug provides integers and floating-point numbers with arbitrary
precision and correct rounding:

  * [`Integer`] is a bignum integer with arbitrary precision,
  * [`Rational`] is a bignum rational number with arbitrary precision,
  * [`Float`] is a multi-precision floating-point number with correct
    rounding, and
  * [`Complex`] is a multi-precision complex number with correct
    rounding.

Rug is a high-level interface to the following [GNU] libraries:

  * [GMP] for integers and rational numbers,
  * [MPFR] for floating-point numbers, and
  * [MPC] for complex numbers.

Rug is free software: you can redistribute it and/or modify it under
the terms of the GNU Lesser General Public License as published by the
Free Software Foundation, either version 3 of the License, or (at your
option) any later version. See the full text of the [GNU LGPL] and
[GNU GPL] for details.

## What’s new

### Version 1.7.0 news (unreleased)

  * Arithmetic operations with one [`Integer`] or integer primitive
    operand and one [`Rational`] operand were added.
  * The method
    <code>[Integer][`Integer`]::[div_exact_from][`div_exact_from`]</code>
    was added.
  * The methods <code>[Integer][`Integer`]::[gcd_u][`gcd_u`]</code>,
    <code>[Integer][`Integer`]::[gcd_u_mut][`gcd_u_mut`]</code> and
    <code>[Integer][`Integer`]::[gcd_u_ref][`gcd_u_ref`]</code> were
    added.
  * The methods <code>[Integer][`Integer`]::[lcm_u][`lcm_u`]</code>,
    <code>[Integer][`Integer`]::[lcm_u_mut][`lcm_u_mut`]</code> and
    <code>[Integer][`Integer`]::[lcm_u_ref][`lcm_u_ref`]</code> were
    added.

[`div_exact_from`]: https://docs.rs/rug/~1.6/rug/struct.Integer.html#method.div_exact_from
[`gcd_u_mut`]: https://docs.rs/rug/~1.6/rug/struct.Integer.html#method.gcd_u_mut
[`gcd_u_ref`]: https://docs.rs/rug/~1.6/rug/struct.Integer.html#method.gcd_u_ref
[`gcd_u`]: https://docs.rs/rug/~1.6/rug/struct.Integer.html#method.gcd_u
[`lcm_u_mut`]: https://docs.rs/rug/~1.6/rug/struct.Integer.html#method.lcm_u_mut
[`lcm_u_ref`]: https://docs.rs/rug/~1.6/rug/struct.Integer.html#method.lcm_u_ref
[`lcm_u`]: https://docs.rs/rug/~1.6/rug/struct.Integer.html#method.lcm_u

### Version 1.6.0 news (2019-09-03)

  * Arithmetic operator implementations for [`i8`], [`i16`], [`i64`],
    [`i128`], [`u8`], [`u16`], [`u64`] and [`u128`] were added to the
    existing implementations for [`i32`] and [`u32`].
  * The function
    <code>[float][`float`]::[free_cache][`free_cache`]</code> was
    added.
  * The method
    <code>[RandState][`RandState`]::[into_custom_boxed][`into_custom_boxed`]</code>
    was added.
  * [`ThreadRandState`] and [`ThreadRandGen`] were added to the
    [`rand`] module to enable the use of custom random generators that
    are not [`Send`] and [`Sync`].
  * Numeric type methods which take [`RandState`] now can also take
    [`ThreadRandState`].

#### Compatibility note

  * The numeric type methods which took
    <code>&mut [RandState][`RandState`]</code> were changed to take
    <code>&mut dyn [MutRandState][`MutRandState`]</code> instead.
    Under normal use, this does not have any affect apart from
    allowing the use of
	<code>&mut [ThreadRandState][`ThreadRandState`]</code> as well.
    With function inlining and optimization, the generated code should
    have the same performance.

[`MutRandState`]: https://docs.rs/rug/~1.6/rug/rand/trait.MutRandState.html
[`RandState`]: https://docs.rs/rug/~1.6/rug/rand/struct.RandState.html
[`Send`]: https://doc.rust-lang.org/nightly/core/marker/trait.Send.html
[`Sync`]: https://doc.rust-lang.org/nightly/core/marker/trait.Sync.html
[`ThreadRandGen`]: https://docs.rs/rug/~1.6/rug/rand/trait.ThreadRandGen.html
[`ThreadRandState`]: https://docs.rs/rug/~1.6/rug/rand/struct.ThreadRandState.html
[`float`]: https://docs.rs/rug/~1.6/rug/float/index.html
[`free_cache`]: https://docs.rs/rug/~1.6/rug/float/fn.free_cache.html
[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`into_custom_boxed`]: https://docs.rs/rug/~1.6/rug/rand/struct.RandState.html#method.into_custom_boxed
[`rand`]: https://docs.rs/rug/~1.6/rug/rand/index.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html

### Other releases

Details on other releases can be found in [*RELEASES.md*].

## Quick example

```rust
use rug::{Assign, Integer};
let mut int = Integer::new();
assert_eq!(int, 0);
int.assign(14);
assert_eq!(int, 14);

let decimal = "98_765_432_109_876_543_210";
int.assign(Integer::parse(decimal).unwrap());
assert!(int > 100_000_000);

let hex_160 = "ffff0000ffff0000ffff0000ffff0000ffff0000";
int.assign(Integer::parse_radix(hex_160, 16).unwrap());
assert_eq!(int.significant_bits(), 160);
int = (int >> 128) - 1;
assert_eq!(int, 0xfffe_ffff_u32);
```

  * <code>[Integer][`Integer`]::[new][`new`]</code> creates a new
    [`Integer`] intialized to zero.
  * To assign values to Rug types, we use the [`Assign`] trait and its
    method [`Assign::assign`]. We do not use the
    [assignment operator `=`][assignment] as that would drop the
    left-hand-side operand and replace it with a right-hand-side
    operand of the same type, which is not what we want here.
  * Arbitrary precision numbers can hold numbers that are too large to
    fit in a primitive type. To assign such a number to the large
    types, we use strings rather than primitives; in the example this
    is done using <code>[Integer][`Integer`]::[parse][`parse`]</code>
    and
    <code>[Integer][`Integer`]::[parse_radix][`parse_radix`]</code>.
  * We can compare Rug types to primitive types or to other Rug types
    using the normal comparison operators, for example
    `int > 100_000_000`.
  * Most arithmetic operations are supported with Rug types and
    primitive types on either side of the operator, for example
    `int >> 128`.

## Using with primitive types

With Rust primitive types, arithmetic operators usually operate on two
values of the same type, for example `12i32 + 5i32`. Unlike primitive
types, conversion to and from Rug types can be expensive, so the
arithmetic operators are overloaded to work on many combinations of
Rug types and primitives. More details are available in the
[documentation][primitive types].

## Operators

Operators are overloaded to work on Rug types alone or on a
combination of Rug types and Rust primitives. When at least one
operand is an owned value of a Rug type, the operation will consume
that value and return a value of the Rug type. For example

```rust
use rug::Integer;
let a = Integer::from(10);
let b = 5 - a;
assert_eq!(b, 5 - 10);
```

Here `a` is consumed by the subtraction, and `b` is an owned
[`Integer`].

If on the other hand there are no owned Rug types and there are
references instead, the returned value is not the final value, but an
incomplete-computation value. For example

```rust
use rug::Integer;
let (a, b) = (Integer::from(10), Integer::from(20));
let incomplete = &a - &b;
// This would fail to compile: assert_eq!(incomplete, -10);
let sub = Integer::from(incomplete);
assert_eq!(sub, -10);
```

Here `a` and `b` are not consumed, and `incomplete` is not the final
value. It still needs to be converted or assigned into an [`Integer`].
This is covered in more detail in the documentation’s
[*Incomplete-computation values*] section.

More details on operators are available in the
[documentation][operators].

## Using Rug

Rug is available on [crates.io][rug crate]. To use Rug in your crate,
add it as a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
rug = "1.6"
```

Rug requires rustc version 1.31.0 or later.

Rug also depends on the [GMP], [MPFR] and [MPC] libraries through the
low-level FFI bindings in the [gmp-mpfr-sys crate][sys crate], which
needs some setup to build; the [gmp-mpfr-sys documentation][sys] has
some details on usage under [GNU/Linux][sys gnu], [macOS][sys mac] and
[Windows][sys win].

## Optional features

The Rug crate has six optional features:

 1. `integer`, enabled by default. Required for the [`Integer`] type
    and its supporting features.
 2. `rational`, enabled by default. Required for the [`Rational`]
    number type and its supporting features. This feature requires the
    `integer` feature.
 3. `float`, enabled by default. Required for the [`Float`] type and
    its supporting features.
 4. `complex`, enabled by default. Required for the [`Complex`] number
    type and its supporting features. This feature requires the
    `float` feature.
 5. `rand`, enabled by default. Required for the [`RandState`] type
    and its supporting features. This feature requires the `integer`
    feature.
 6. `serde`, disabled by default. This provides serialization support
    for the [`Integer`], [`Rational`], [`Float`] and [`Complex`]
    number types, providing that they are enabled. This feature
    requires the [serde crate].

The first five optional features are enabled by default; to use
features selectively, you can add the dependency like this to
[*Cargo.toml*]:

```toml
[dependencies.rug]
version = "1.6"
default-features = false
features = ["integer", "float", "rand"]
```

Here only the `integer`, `float` and `rand` features are enabled. If
none of the features are selected, the [gmp-mpfr-sys crate][sys crate]
is not required and thus not enabled. In that case, only the
[`Assign`] trait and the traits that are in the [`ops`] module are
provided by the crate.

[*Cargo.toml*]: https://doc.rust-lang.org/cargo/guide/dependencies.html
[*Incomplete-computation values*]: https://docs.rs/rug/~1.6/rug/index.html#incomplete-computation-values
[*RELEASES.md*]: https://gitlab.com/tspiteri/rug/blob/master/RELEASES.md
[GMP]: https://gmplib.org/
[GNU GPL]: https://www.gnu.org/licenses/gpl-3.0.html
[GNU LGPL]: https://www.gnu.org/licenses/lgpl-3.0.en.html
[GNU]: https://www.gnu.org/
[MPC]: http://www.multiprecision.org/mpc/
[MPFR]: https://www.mpfr.org/
[`Assign::assign`]: https://docs.rs/rug/~1.6/rug/trait.Assign.html#tymethod.assign
[`Assign`]: https://docs.rs/rug/~1.6/rug/trait.Assign.html
[`Complex`]: https://docs.rs/rug/~1.6/rug/struct.Complex.html
[`Float`]: https://docs.rs/rug/~1.6/rug/struct.Float.html
[`Integer`]: https://docs.rs/rug/~1.6/rug/struct.Integer.html
[`RandState`]: https://docs.rs/rug/~1.6/rug/rand/struct.RandState.html
[`Rational`]: https://docs.rs/rug/~1.6/rug/struct.Rational.html
[`new`]: https://docs.rs/rug/~1.6/rug/struct.Integer.html#method.new
[`ops`]: https://docs.rs/rug/~1.6/rug/ops/index.html
[`parse_radix`]: https://docs.rs/rug/~1.6/rug/struct.Integer.html#method.parse_radix
[`parse`]: https://docs.rs/rug/~1.6/rug/struct.Integer.html#method.parse
[assignment]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#assignment-expressions
[operators]: https://docs.rs/rug/~1.6/rug/index.html#operators
[primitive types]: https://docs.rs/rug/~1.6/rug/index.html#using-with-primitive-types
[rug crate]: https://crates.io/crates/rug
[serde crate]: https://crates.io/crates/serde
[sys crate]: https://crates.io/crates/gmp-mpfr-sys
[sys gnu]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/index.html#building-on-gnulinux
[sys mac]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/index.html#building-on-macos
[sys win]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/index.html#building-on-windows
[sys]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/index.html
