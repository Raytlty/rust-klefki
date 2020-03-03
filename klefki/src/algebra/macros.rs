//macro_rules! double_and_add {
//($time: expr, $addend: expr, $init: expr) => {{
//let mut result = $init;
//let mut time = $time;
//let mut addend = $addend;
//while time > 0 {
//if time & 1 == 1 {
//result += &addend;
//}
//addend = addend.clone() + addend;
//time >>= 1;
//}
//result
//}};
//}

macro_rules! from_incomplete {
    ($Param: expr, $Version: expr) => {
        RegisterField::from_incomplete($Param, Some($Version))
    };
}

macro_rules! from_field_boxed {
    ($Param: expr) => {
        RegisterField::from_field_boxed($Param)
    };
}

macro_rules! double_and_add {
    ($time: expr, $addend: expr, $init: expr) => {{
        let mut result = $init;
        for i in 0..$time {
            result *= &$addend;
        }
        result
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

macro_rules! arith_binary_self {
    (
        $Big:ty, $BigName:ident;
        $($Imp:ident { $method:ident, $func:expr };
        $ImpAssign:ident {$method_assign:ident};)*
    ) => {
        $(impl $Imp<$Big> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(self, other: $Big) -> $Big {
                let incomplete = $func(self, other);
                $BigName::from(incomplete)
            }
        }

        impl $ImpAssign<$Big> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: $Big) {
                *self = {
                    let cloned = self.clone();
                    cloned.$method(rhs)
                };
            }
        }

        impl $Imp<&$Big> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(self, other: &$Big) -> $Big {
                let other = other.clone();
                self.$method(other)
            }
        }

        impl $ImpAssign<&$Big> for $Big {
            #[inline]
            fn $method_assign(&mut self, other: &$Big) {
                let other = other.clone();
                self.$method_assign(other);
            }
        }
        )*
    };
}

macro_rules! arith_unary {
    (
        $Big:ty, $BigName:ident;
        $Imp:ident {$method: ident, $func: expr};
    ) => {
        impl $Imp for $Big {
            type Output = $Big;
            fn $method(self) -> $Big {
                let incomplete = $func(self);
                $BigName::from(incomplete)
            }
        }

        impl<'a> $Imp for &'a $Big {
            type Output = $Big;
            fn $method(self) -> $Big {
                let other = self.clone();
                other.$method()
            }
        }
    };
}
