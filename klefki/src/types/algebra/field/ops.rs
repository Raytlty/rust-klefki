macro_rules! arith_prim {
    (
        $Big:ty, $BigName:ident;
        $Imp: ident {$method: ident};
        $ImpAssign: ident {$method_assign: ident};
        $($T: ty;)*
    ) => {$(
        impl $Imp<$T> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(self, rhs: $T) -> $Big {
                $BigName {
                    value: self.value.$method(rhs)
                }
            }
        }

        impl $Imp<&$T> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(self, rhs: &$T) -> $Big {
                $BigName {
                    value: self.value.$method(rhs)
                }
            }
        }

        impl $ImpAssign<$T> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: $T) {
                *self = {
                    let cloned = self.clone();
                    cloned.$method(rhs)
                };
            }
        }

        impl $ImpAssign<&$T> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: &$T) {
                self.$method_assign(*rhs);
            }
        }
    )*};
}

//macro_rules! arith_group {
    //(
        //$Big: ty, $BigName: ident;
        //$Imp: ident {$method: ident, $func: expr};
        //$ImpAssign: ident {$method_assign: ident};
        //$G: ty, $GName: ident;
    //) => {

    //};
//}

use crate::types::algebra::field::{
    FiniteFieldCyclicSecp256k1, FiniteFieldCyclicSecp256r1, FiniteFieldSecp256k1,
    FiniteFieldSecp256r1,
};
use rug::{Complex, Integer};
use std::ops::{Add, AddAssign, Sub, SubAssign, Mul, MulAssign, Div, DivAssign};

arith_prim!(
    FiniteFieldSecp256k1, FiniteFieldSecp256k1;
    Add {add};
    AddAssign {add_assign};
    i8; i16; i32; i64; i128; 
    u8; u16; u32; u64; u128;
    f32; f64;
);

arith_prim!(
    FiniteFieldSecp256k1, FiniteFieldSecp256k1;
    Sub {sub};
    SubAssign {sub_assign};
    i8; i16; i32; i64; i128; 
    u8; u16; u32; u64; u128;
    f32; f64;
);

arith_prim!(
    FiniteFieldSecp256k1, FiniteFieldSecp256k1;
    Mul {mul};
    MulAssign {mul_assign};
    i8; i16; i32; i64; i128; 
    u8; u16; u32; u64; u128;
    f32; f64;
);

arith_prim!(
    FiniteFieldSecp256k1, FiniteFieldSecp256k1;
    Div {div};
    DivAssign {div_assign};
    i8; i16; i32; i64; i128; 
    u8; u16; u32; u64; u128;
    f32; f64;
);

arith_prim!(
    FiniteFieldSecp256r1, FiniteFieldSecp256r1;
    Add {add};
    AddAssign {add_assign};
    i8; i16; i32; i64; i128; 
    u8; u16; u32; u64; u128;
    f32; f64;
);

arith_prim!(
    FiniteFieldSecp256r1, FiniteFieldSecp256r1;
    Sub {sub};
    SubAssign {sub_assign};
    i8; i16; i32; i64; i128; 
    u8; u16; u32; u64; u128;
    f32; f64;
);

arith_prim!(
    FiniteFieldSecp256r1, FiniteFieldSecp256r1;
    Mul {mul};
    MulAssign {mul_assign};
    i8; i16; i32; i64; i128; 
    u8; u16; u32; u64; u128;
    f32; f64;
);

arith_prim!(
    FiniteFieldSecp256r1, FiniteFieldSecp256r1;
    Div {div};
    DivAssign {div_assign};
    i8; i16; i32; i64; i128; 
    u8; u16; u32; u64; u128;
    f32; f64;
);


arith_prim!(
    FiniteFieldCyclicSecp256k1, FiniteFieldCyclicSecp256k1;
    Add {add};
    AddAssign {add_assign};
    i8; i16; i32; i64; i128; 
    u8; u16; u32; u64; u128;
    f32; f64;
);

arith_prim!(
    FiniteFieldCyclicSecp256k1, FiniteFieldCyclicSecp256k1;
    Sub {sub};
    SubAssign {sub_assign};
    i8; i16; i32; i64; i128; 
    u8; u16; u32; u64; u128;
    f32; f64;
);

arith_prim!(
    FiniteFieldCyclicSecp256k1, FiniteFieldCyclicSecp256k1;
    Mul {mul};
    MulAssign {mul_assign};
    i8; i16; i32; i64; i128; 
    u8; u16; u32; u64; u128;
    f32; f64;
);

arith_prim!(
    FiniteFieldCyclicSecp256k1, FiniteFieldCyclicSecp256k1;
    Div {div};
    DivAssign {div_assign};
    i8; i16; i32; i64; i128; 
    u8; u16; u32; u64; u128;
    f32; f64;
);

arith_prim!(
    FiniteFieldCyclicSecp256r1, FiniteFieldCyclicSecp256r1;
    Add {add};
    AddAssign {add_assign};
    i8; i16; i32; i64; i128; 
    u8; u16; u32; u64; u128;
    f32; f64;
);

arith_prim!(
    FiniteFieldCyclicSecp256r1, FiniteFieldCyclicSecp256r1;
    Sub {sub};
    SubAssign {sub_assign};
    i8; i16; i32; i64; i128; 
    u8; u16; u32; u64; u128;
    f32; f64;
);

arith_prim!(
    FiniteFieldCyclicSecp256r1, FiniteFieldCyclicSecp256r1;
    Mul {mul};
    MulAssign {mul_assign};
    i8; i16; i32; i64; i128; 
    u8; u16; u32; u64; u128;
    f32; f64;
);

arith_prim!(
    FiniteFieldCyclicSecp256r1, FiniteFieldCyclicSecp256r1;
    Div {div};
    DivAssign {div_assign};
    i8; i16; i32; i64; i128; 
    u8; u16; u32; u64; u128;
    f32; f64;
);

#[cfg(test)]
mod test {

    use super::FiniteFieldSecp256k1;

    #[test]
    fn test_add() {
        let s = FiniteFieldSecp256k1::new("1");
        let t = FiniteFieldSecp256k1::new("2");
        assert_eq!(s + 1, t);
    }
}
