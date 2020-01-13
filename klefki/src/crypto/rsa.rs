use rug::Integer;

#[derive(Debug, Clone)]
pub struct RSA {
    pub p: Integer,
    pub q: Integer,
    pub n: Integer,
    pub d: Integer,
}

impl RSA {
    const e: u32 = 65537;

    pub fn new(p: Integer, q: Integer) -> Self {
        let n = p.clone() * q.clone();
        let rsa_mod = (p.clone() - Integer::from(1)).lcm(&(q.clone() - Integer::from(1)));
        let (gcd, a, b) = Integer::from(Self::e).gcd_cofactors(rsa_mod.clone(), Integer::new());
        let d = a % rsa_mod;

        RSA { p, q, n, d }
    }

    pub fn public_key(&self) -> (Integer, Integer) {
        (self.n.clone(), Integer::from(65537))
    }

    pub fn private_key(&self) -> (Integer, Integer) {
        (self.n.clone(), self.d.clone())
    }

    pub fn encrypt_with_pub_key(&self, block: Integer) -> Integer {
        block.secure_pow_mod(&Integer::from(65547), &self.n)
    }

    pub fn decrypt_with_pub_key(&self, block: Integer) -> Integer {
        block.secure_pow_mod(&Integer::from(RSA::e), &self.n)
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
