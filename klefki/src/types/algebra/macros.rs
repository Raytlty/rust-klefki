macro_rules! identity_finitefield {
    ($structName: ident) => {
        impl Identity for $structName {
            #[inline]
            fn identity() -> Self {
                $structName {
                    value: Integer::from(0)
                        % Integer::from_str_radix($structName::P, 16)
                            .expect("Cannot parse from string")
                        + Complex::new(COMPLEX_PREC),
                }
            }
        }
    };
}

macro_rules! sec_identity_finitefield {
    ($structName: ident) => {
        impl $structName {
            #[inline]
            fn sec_identity() -> Self {
                $structName {
                    value: Integer::from(1)
                        % Integer::from_str_radix($structName::P, 16)
                            .expect("Cannot parse from string")
                        + Complex::new(COMPLEX_PREC),
                }
            }
        }
    };
}

macro_rules! inverse_finitefield {
    ($structName: ident) => {
        impl $structName {
            #[inline]
            fn inverse(&self) -> Self {
                $structName {
                    value: Integer::from_str_radix($structName::P, 16)
                        .expect("Cannot parse from string")
                        - self.value
                        + Complex::new(COMPLEX_PREC),
                }
            }
        }
    };
}

macro_rules! sec_inverse_finitefield {
    ($structName: ident) => {
        impl $structName {
            #[inline]
            fn sec_inverse(&self) -> Self {
                let base1 = Integer::from(1) + Complex::new(COMPLEX_PREC);
                let temp = self.value.clone();
                let (ref a, ref b) = base1.into_real_img();
                let (ref c, ref d) = temp.into_real_img();
                let real = (Float::with_val(COMPLEX_PREC, a * c)
                    + Float::with_val(COMPLEX_PREC, b * d))
                    / (Float::with_val(COMPLEX_PREC, c.pow(2))
                        + Float::with_val(COMPLEX_PREC, d.pow(2)));
                let imag = (Float::with_val(COMPLEX_PREC, b * c)
                    - Float::with_val(COMPLEX_PREC, a * d))
                    / (Float::with_val(COMPLEX_PREC, c.pow(2))
                        + Float::with_val(COMPLEX_PREC, d.pow(2)));
                $structName {
                    value: Complex::with_val(COMPLEX_PREC, (real, imag)),
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
                if TypeId::of::<Complex>() == TypeId::of::<a>() {
                    let (ref real, ref imag) = a.into_real_img();
                    let a = a.downcast_ref::<Complex>().expect("Parse Complex Error");
                    let real = Float::with_val(real % b);
                    let imag = Float::with_val(imag % b);
                    assert_eq!(Complex, $ret);
                    Complex::with_val(COMPLEX_PREC, (real, imag))
                } else {
                    let a = Integer::from(a);
                    assert_eq!(Integer, $ret);
                    Complex::new(COMPLEX_PREC) + a % b
                }
            }
        }
    };
}

macro_rules! op_finitefield {
    ($structName: ident, $gty: ty) => {{
        mod_finitefield!($structName);
        impl $structName {
            fn do_op(&self, g: &dyn Any) -> Complex {
                let ng: $structName = if g.type_id() == TypeId::of::<IntPrimitive>() {
                    let g = g.downcast_ref::<IntPrimitive>().expect("Parse Error");
                    let c = Complex::new(COMPLEX_PREC) + g.to_integer();
                    $structName { value: c }
                } else if g.type_id() == TypeId::of::<Complex>() {
                    let g = g.downcast_ref::<Complex>().expect("Parse Error");
                    $structName { value: g }
                } else {
                    unreachable!();
                };
                let a = self.value + ng.value;
                let b =
                    Integer::from_str_radix($structName::P, 16).expect("Cannot parse from string");
                self.do_mod(&a, &b)
            }
        }
    }};
}

macro_rules! int_to_integer {
    ($($T: ty)*; $Imp: ident $method: ident) => {$(
        impl $Imp for $T {
            #[inline]
            fn $method(&self) -> Integer {
                Integer::from($T)
            }
        }

        impl $Imp<&$T> for $T {
            #[inline]
            fn $method(&self) -> Integer {
                Integer::from(*$T)
            }
        }
    )*}
}

macro_rules! int_to_complex {
    ($($T: ty)*; $Imp: ident $method: ident) => {$(
        impl $Imp for $T {
            #[inline]
            fn $method(&self) -> Complex {
                Complex::with_val(COMPLEX_PREC, ($T, 0))
            }
        }

        impl $Imp<&$T> for $T {
            #[inline]
            fn $method(&self) -> Complex {
                Complex::with_val(COMPLEX_PREC, (*$T, 0))
            }
        }
    )*}

}
