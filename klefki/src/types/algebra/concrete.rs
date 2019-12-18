use crate::constrant;

pub trait FiniteFieldSecp256k1 {
    const P: &'static str = constrant::SECP256K1_P;
}

pub trait FiniteFieldCyclicSecp256k1 {
    const P: &'static str = constrant::SECP256K1_N;
}
