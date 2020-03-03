//! A set $\mathbb{G}$ = a, b, c... is called a group.
//!
//! If there exists a group addition(+) connection the elements in ($\mathbb{G}$, $\mathbb{+}$) in the
//! following ways：
//!
//! $$
//! a, b \in \mathbb{G}: c = a + b \in \mathbb{G}; (Closure)
//! \tag{1}
//! $$
//!
//! $$
//! a, b, c, \in \mathbb{G}: (a + b)c = a(b + c); (Associativity)
//! \tag{2}
//! $$
//!
//! $$
//! \exists e \in \mathbb{G}: a + e = e, \forall a \in \mathbb{G}; (Identity / Neutral Element)
//! \tag{3}
//! $$
//!
//! $$
//! \forall a \in \mathbb{G}, \exists b \in \mathbb{G}: a + b = e, b \equiv -a; (Inverse)
//! \tag{4}
//! $$
//!
//! If a group obey axiom (1,2), it is a SemiGroup;
//!
//! If a group obey axiom (1,2,3), it is a monadid;
//!
//! If a group obey axiom (1,2,3,4) and the axiom of commutatativity(a + b = b + a), it is a Abelian Group;

mod arith;
//mod cmp;
//mod ops;

pub use arith::{
    choose_field_from_version, EllipticCurveCyclicSubgroupSecp256k1,
    EllipticCurveCyclicSubgroupSecp256r1, EllipticCurveGroupSecp256k1, EllipticCurveGroupSecp256r1,
    JacobianGroupSecp256k1, JacobianGroupSecp256r1,
};
