use rug::{integer::IsPrime, rand::RandState, Assign, Integer};
pub enum RandomAlgor<'a> {
    DefaultAlgor,       // Default as NEW_MERSENNE_TWISTER algorithm
    NewMerSenneTwister, // This algorithm is fast and has good randomness properties.
    NewLinearCongruential(&'a Integer, u32, u32), // algorithm X = (a × X + c) mod 2 ^ m.
    NewLinearCongruentialSize(u32),
}

impl<'a> RandomAlgor<'a> {
    fn generate_random(&self) -> RandState {
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
