use rug::ops::Pow;
use rug::Complex;
use rug::Float;
use rug::Integer;
use std::any::{Any, TypeId};

fn is_integer(s: &dyn Any) -> bool {
    TypeId::of::<Integer>() == s.type_id()
}
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

fn downcast_ref_u32(s: &dyn Any) {
    let s = s.downcast_ref::<Integer>();
    //println!("{:?}", s.type_id());
    //println!("{:?}", TypeId::of::<u32>());
    //println!("{:?}", TypeId::of::<i32>());
    //println!("{:?}", TypeId::of::<u64>());
    //println!("{}", TypeId::of::<u32>() == s.type_id());
    //let s = s.downcast_ref::<String>();
    //let s = Integer::from(s);
    println!("{:?}", s);
}

macro_rules! identity_finitefield {
    ($structName: ident) => {
        impl Identity for $structName {
            #[inline]
            fn identity(&self) -> Self {
                $structName {
                    value: Integer::from(0)
                        % Integer::from_str_radix($structName::P, 16)
                            .expect("Cannot parse from string"),
                }
            }
        }
    };
}

macro_rules! mod_finitefield {
    ($structName: ident) => {
        impl $structName {
            #[inline]
            fn do_mod(&self, a: &dyn Any, b: &Integer) -> Complex {
                if TypeId::of::<Complex>() == a.type_id() {
                    let a = a.downcast_ref::<Complex>().unwrap();
                    let (ref real, ref imag) = a.clone().into_real_imag();
                    let real = real - Float::with_val(256, real / b);
                    let imag = imag - Float::with_val(256, imag / b);
                    Complex::with_val(256, (real, imag))
                } else {
                    let a = a.downcast_ref::<Integer>().unwrap();
                    let a = Integer::from(a - b) + Complex::new(256);
                    a
                }
            }
        }
    };
}

const SECP: &'static str = "ffffffff00000001000000000000000000000000fffffffffffffffffffffffc";

trait Identity {
    fn identity(&self) -> Self;
}

trait constP {
    const P: &'static str;
}

#[derive(Debug)]
struct identity_t {
    pub value: Integer,
}

impl constP for identity_t {
    const P: &'static str = SECP;
}

identity_finitefield!(identity_t);
mod_finitefield!(identity_t);

fn main() {
    let s = "0";
    let s2 = "7";
    let s3 = "ffffffff00000001000000000000000000000000fffffffffffffffffffffffc";
    println!(
        "{:?}",
        Integer::from(Integer::from_str_radix(s, 16).expect("Cannot parse from string"))
    );
    println!(
        "{:?}",
        Integer::from(Integer::from_str_radix(s2, 16).expect("Cannot parse from string"))
    );
    println!(
        "{:?}",
        Integer::from(Integer::from_str_radix(s3, 16).expect("Cannot parse from string"))
    );

    let i4 = Integer::from(0);
    println!("{:?}", is_integer(&i4));

    let id = identity_t {
        value: Integer::from(100),
    };
    println!("{:?}", id.identity());

    let ident = identity_t {
        value: id.value - Integer::from(1),
    };

    println!(
        "{:?}",
        Integer::from_str_radix(identity_t::P, 16).expect("Cannot parse from string")
    );
    //let a = Complex::with_val(256, (10, 10));
    //let b = Integer::from(2);
    //println!("{:?}", ident.do_mod(&a, &b));

    //let p = IntPrimitive::I32(2i32);
    //fn t(p: &IntPrimitive) {
    //println!("{:?}", p.to_i32_ref());
    //}
    //println!("{:?}", p.to_i32());
    //println!("{:?}", b);
    //
    //let kkex = Integer::from_str_radix(s3, 16).expect("") + Complex::new(256);
    //println!("{:?}", kkex.real().to_integer());
    //let kkex2 = kkex.clone();

    //let kkex = Complex::with_val(256, (30, 40));
    //let kkex2 = Complex::with_val(256, (50, 60));

    //let (ref a, ref b) = kkex.into_real_imag();
    //let (ref c, ref d) = kkex2.into_real_imag();

    /*let t1 = (Float::with_val(256, a * c) + Float::with_val(256, b * d))
    / (Float::with_val(256, c.pow(2)) + Float::with_val(256, d.pow(2)));
    let t2 = (Float::with_val(256, b * c) - Float::with_val(256, a * d))
    / (Float::with_val(256, c.pow(2)) + Float::with_val(256, d.pow(2)));
    println!("{:?}, {:?}", t1, t2);
    let c = Complex::with_val(256, (t1, t2));
    println!("{:?}", c);*/
}
