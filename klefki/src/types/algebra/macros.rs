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
