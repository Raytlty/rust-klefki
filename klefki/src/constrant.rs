use rug::Integer;

pub const SECP256K1_P: &'static str =
    "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F";
pub const SECP256K1_N: &'static str =
    "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141";
pub const SECP256K1_GX: &'static str =
    "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798";
pub const SECP256K1_GY: &'static str =
    "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8";
pub const SECP256K1_A: &'static str = "0";
pub const SECP256K1_B: &'static str = "7";

pub const SECP256R1_P: &'static str =
    "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff";
pub const SECP256R1_A: &'static str =
    "ffffffff00000001000000000000000000000000fffffffffffffffffffffffc";
pub const SECP256R1_B: &'static str =
    "5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b";
pub const SECP256R1_N: &'static str =
    "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551";
pub const SECP256R1_GX: &'static str =
    "6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296";
pub const SECP256R1_GY: &'static str =
    "4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5";
pub const COMPLEX_PREC: u32 = 256;

#[derive(Debug, Clone, Copy)]
pub enum IntPrimitive {
    I32(i32),
    U32(u32),
    I64(i64),
    U64(u64),
    I128(i128),
    U128(u128),
    Isize(isize),
    Usize(usize),
}

macro_rules! to_primitive {
    ($Imp: ident, $method: ident, $method_ref: ident, $match: ident, $ret: ty) => {
        pub trait $Imp {
            fn $method(self) -> $ret;
            fn $method_ref(&self) -> $ret;
        }

        impl $Imp for IntPrimitive {
            #[inline(always)]
            fn $method(self) -> $ret {
                match self {
                    IntPrimitive::$match(v) => v,
                    _ => unreachable!(),
                }
            }

            #[inline(always)]
            fn $method_ref(&self) -> $ret {
                match self {
                    &IntPrimitive::$match(v) => v,
                    _ => unreachable!(),
                }
            }
        }
    };
}

to_primitive!(ToI32, to_i32, to_i32_ref, I32, i32);
to_primitive!(ToU32, to_u32, to_u32_ref, U32, u32);
to_primitive!(ToI64, to_i64, to_i64_ref, I64, i64);
to_primitive!(ToU64, to_u64, to_u64_ref, U64, u64);
to_primitive!(ToI128, to_i128, to_i128_ref, I128, i128);
to_primitive!(ToU128, to_u128, to_u128_ref, U128, u128);
to_primitive!(ToIsize, to_isize, to_isize_ref, Isize, isize);
to_primitive!(ToUsize, to_usize, to_usize_ref, Usize, usize);

impl IntPrimitive {
    pub fn to_integer(&self) -> Integer {
        match self {
            &IntPrimitive::I32(v) => Integer::from(v),
            &IntPrimitive::U32(v) => Integer::from(v),
            &IntPrimitive::I64(v) => Integer::from(v),
            &IntPrimitive::U64(v) => Integer::from(v),
            &IntPrimitive::I128(v) => Integer::from(v),
            &IntPrimitive::U128(v) => Integer::from(v),
            &IntPrimitive::Isize(v) => Integer::from(v),
            &IntPrimitive::Usize(v) => Integer::from(v),
        }
    }
}
