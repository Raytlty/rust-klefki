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
