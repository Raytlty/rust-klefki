use rug::Integer;

#[derive(Debug, Clone)]
pub struct RSA {
    pub p: Integer,
    pub q: Integer,
    pub n: Integer,
    pub d: Integer,
}

impl RSA {
    const E: u32 = 65537;

    pub fn new(p: Integer, q: Integer) -> Self {
        let n = p.clone() * q.clone();
        let rsa_mod = (p.clone() - Integer::from(1)).lcm(&(q.clone() - Integer::from(1)));
        let (gcd, a, b) = Integer::from(Self::E).gcd_cofactors(rsa_mod.clone(), Integer::new());
        let d = match a.pow_mod(&Integer::from(1), &rsa_mod) {
            Ok(i) => i,
            Err(_) => unreachable!(),
        };

        RSA { p, q, n, d }
    }

    pub fn public_key(&self) -> (Integer, Integer) {
        (self.n.clone(), Integer::from(RSA::E))
    }

    pub fn private_key(&self) -> (Integer, Integer) {
        (self.n.clone(), self.d.clone())
    }

    pub fn encrypt_with_pub_key(&self, block: Integer) -> Integer {
        block.secure_pow_mod(&Integer::from(RSA::E), &self.n)
    }

    pub fn decrypt_with_pub_key(&self, block: Integer) -> Integer {
        block.secure_pow_mod(&Integer::from(RSA::E), &self.n)
    }

    pub fn encrypt_with_priv_key(&self, block: Integer) -> Integer {
        block.secure_pow_mod(&self.d, &self.n)
    }

    pub fn decrypt_with_priv_key(&self, block: Integer) -> Integer {
        block.secure_pow_mod(&self.d, &self.n)
    }

    pub fn encrypt_string(&self, message: String) -> Vec<Integer> {
        let mut encrypted = vec![];
        for i in message.chars() {
            encrypted.push(self.encrypt_with_pub_key(Integer::from(i as u8)));
        }
        encrypted
    }

    pub fn decrypt_string(&self, encrypted: Vec<Integer>) -> String {
        let mut decrypted = vec![];
        for int in encrypted.into_iter() {
            let de = match self.decrypt_with_priv_key(int).to_u8() {
                Some(i) => i,
                None => panic!("Cannot parse into u8"),
            };
            decrypted.push(de)
        }
        String::from_utf8(decrypted).expect("Decrypt Message Failed.")
    }
}

#[cfg(test)]
mod test {
    use super::{Integer, RSA};
    use crate::constrant::{SECP256K1_N, SECP256K1_P};

    #[test]
    fn test_rsa_block_encrypt() {
        let secp1 = Integer::from_str_radix(SECP256K1_P, 16).expect("Parse from string failed.");
        let secp2 = Integer::from_str_radix(SECP256K1_N, 16).expect("Parse from string failed.");
        let rsa_instance = RSA::new(secp1, secp2);
        let encrypted = rsa_instance.encrypt_with_pub_key(Integer::from(1200));
        assert_eq!(
            rsa_instance.decrypt_with_priv_key(encrypted),
            Integer::from(1200)
        );
    }

    #[test]
    fn test_rsa_string_ecrypt() {
        let secp1 = Integer::from_str_radix(SECP256K1_P, 16).expect("Parse from string failed.");
        let secp2 = Integer::from_str_radix(SECP256K1_N, 16).expect("Parse from string failed.");
        let rsa_instance = RSA::new(secp1, secp2);
        let s = String::from("hello crypto");
        let encrypted = rsa_instance.encrypt_string(s.clone());
        assert_eq!(rsa_instance.decrypt_string(encrypted), s);
    }
}
