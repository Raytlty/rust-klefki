//! A field is any set of elements that satisfies the field axioms for both addition and multiplication and is a commutative division algebra.
//!
//! Field Axioms:nbsphinx-math: *cite{FieldAxioms}* are generally written in additive and multiplication pairs:
//!
//! $$
//! (a + b) + c = a + (b + c); (ab)c = a(bc); (Associativity)
//! \tag{1}
//! $$
//!
//! $$
//! a + b = b + a; ab = ba; (Commutativity)
//! \tag{2}
//! $$
//!
//! $$
//! a(b + c) = ab + ac; (a + b)c = ac + bc; (Distributivity)
//! \tag{3}
//! $$
//!
//! $$
//! a + 0 = a = 0 + 1; a . 1 = a = 1 . a; (Identity)
//! \tag{4}
//! $$
//!
//! $$
//! a + (-a) = 0 = (-a) + a; aa^{-1} = 1 = a^{-1}a; (Inverse)
//! \tag{5}
//! $$
//!
//! # The Finite Field
//!
//! A finite field is, A set with a finite number of elements.
//! An example of inite field is the set of integers modulo P, where P is a prime number,
//! which can be generally note as $\mathbb{Z}/P$, 𝐺𝐹(P) or $\mathbb{F}_P$.

mod arith;
mod cmp;
mod ops;

pub use arith::{
    FiniteFieldCyclicSecp256k1, FiniteFieldCyclicSecp256r1, FiniteFieldSecp256k1,
    FiniteFieldSecp256r1,
};

/*
2. (a+b)+c=a+(b+c); $ a b = b a$ (Commutativity)
3. a(b+c) = ab + ac; \((a+b)c=ac+bc\) (distributivity)
4. a + 0 = a = 0 + 1 \((a.1=a=1.a)\)  (identity)
5. a+(-a)=0=(-a)+a; \(aa^{-1}=1=a^{-1}a if a \neq 0\) (inverses)
 * */
