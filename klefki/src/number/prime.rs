//! This is a prime tools about generate a big prime number, which use for RSA and other algorithm.

use rug::{integer::IsPrime, rand::RandState, Assign, Integer};

/// Choose random algorithm to generate prime number
///
/// DefaultAlgor is usinng [`NewMerSenneTwister`] algorithm.
///
/// [`NewMerSenneTwister`] is fast and has good randomness properties.
///
/// [`NewLinearCongruential`]  creates a new random generator with a linear congruential
/// algorithm <i>X</i> = (<i>a</i> × <i>X</i> + <i>c</i>) mod 2<sup><i>m</i></sup>.
///
/// [`NewLinearCongruentialSize`] creates a new random generator with a linear congruential
/// algorithm like the [`NewLinearCongruential`] method.
/// For the linear congruential algorithm
/// <i>X</i> = (<i>a</i> × <i>X</i> + <i>c</i>) mod 2<sup><i>m</i></sup>,
/// <i>a</i>, <i>c</i> and <i>m</i> are selected from a table
/// such that at least <i>size</i> bits of each <i>X</i> will be
/// used, that is <i>m</i>/2 ≥ <i>size</i>. The table only has
/// values for <i>size</i> ≤ 128; [`None`] will be returned if the
/// requested size is larger.
///
/// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
/// [`NewMerSenneTwister`]: https://docs.rs/rug/1.6.0/rug/rand/struct.RandState.html#method.new_mersenne_twister
/// [`NewLinearCongruential`]: https://docs.rs/rug/1.6.0/rug/rand/struct.RandState.html#method.new_linear_congruential
/// [`NewLinearCongruentialSize`]: https://docs.rs/rug/1.6.0/rug/rand/struct.RandState.html#method.new_linear_congruential_size
pub enum RandomAlgor<'a> {
    DefaultAlgor,
    NewMerSenneTwister,
    NewLinearCongruential(&'a Integer, u32, u32),
    NewLinearCongruentialSize(u32),
}

impl<'a> RandomAlgor<'a> {
    pub fn generate_random(&self) -> RandState {
        match self {
            RandomAlgor::DefaultAlgor | RandomAlgor::NewMerSenneTwister => {
                RandState::new_mersenne_twister()
            }
            RandomAlgor::NewLinearCongruential(a, c, m) => {
                RandState::new_linear_congruential(a, *c, *m)
            }
            RandomAlgor::NewLinearCongruentialSize(size) => {
                match RandState::new_linear_congruential_size(*size) {
                    Some(r) => r,
                    None => unreachable!(),
                }
            }
        }
    }
}

/// Create a generate prime number by givinng bits, reps and random algorithm,
/// and return a [`Integer`]
///
/// bits is [`u32`] and determine the length of prime number, and reps is [`u32`]
/// determine how much time to inspect the number is prime or not.
///
/// ## Example
///
/// ```rust
/// let possible: Integer = generate_prime(1024, 5, None);
/// println!("{:?}", possible);
/// let sign = match possible.is_probably_prime(5) {
///     IsPrime::Yes | IsPrime::Probably => true,
///     _ => false,
/// };
/// assert_eq!(sign, true);
/// ```
///
/// [`Integer`]: https://docs.rs/rug/1.6.0/rug/struct.Integer.html
/// [`u32`]: https://doc.rust-lang.org/stable/std/primitive.u32.html
pub fn generate_prime(bits: u32, reps: u32, rand: Option<RandomAlgor>) -> Integer {
    let rand_algor;
    let mut random = if rand.is_none() {
        RandState::new()
    } else {
        rand_algor = rand.unwrap();
        rand_algor.generate_random()
    };
    loop {
        let possible = Integer::from(Integer::random_bits(bits, &mut random));
        match possible.is_probably_prime(reps) {
            IsPrime::No => continue,
            IsPrime::Yes | IsPrime::Probably => return possible,
        };
    }
}

#[cfg(test)]
mod test {
    use super::{generate_prime, Integer, IsPrime, RandomAlgor};

    #[test]
    fn test0x01() {
        let possible: Integer = generate_prime(1024, 5, None);
        println!("{:?}", possible);
        let sign = match possible.is_probably_prime(5) {
            IsPrime::Yes | IsPrime::Probably => true,
            _ => false,
        };
        assert_eq!(sign, true);
    }

    #[test]
    fn test0x02() {
        let a = match Integer::from_str_radix("292787ebd3329ad7e7575e2fd", 16) {
            Ok(i) => i,
            Err(_) => unreachable!(),
        };
        let c = 1;
        let m = 100;
        let rand_algor = RandomAlgor::NewLinearCongruential(&a, c, m);
        let possible: Integer = generate_prime(256, 5, Some(rand_algor));
        println!("{:?}", possible);
        let sign = match possible.is_probably_prime(5) {
            IsPrime::Yes | IsPrime::Probably => true,
            _ => false,
        };
        assert_eq!(sign, true);
    }
}
