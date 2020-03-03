use crate::algebra::{Field, Group, InCompleteField, MatMul, RegisterField, Xor};
use std::fmt::Debug;
use std::ops::{BitXor, BitXorAssign, Mul, MulAssign};

pub fn v_multi<G>(g: Vec<G>, f: Vec<Box<dyn Field>>) -> G
where
    G: Group + MulAssign<G> + BitXor<RegisterField, Output = G> + Default + Debug,
{
    let mut sign = true;
    let mut result = G::default();
    for (x, y) in g.into_iter().zip(f.into_iter()) {
        println!("{:?}", result);
        if sign {
            sign = false;
            result = x ^ from_field_boxed!(&y);
        } else {
            result *= (x ^ from_field_boxed!(&y));
        }
    }
    result
}

pub fn commitment<Gp>(x: &Box<dyn Field>, r: &Box<dyn Field>, H: Gp, G: Gp) -> Gp
where
    Gp: Group + Mul<Gp, Output = Gp> + BitXor<RegisterField, Output = Gp> + Default + Debug,
{
    (G ^ from_field_boxed!(x)) * (H ^ from_field_boxed!(r))
}

pub fn vertex_commitment<Gp>(x: Vec<Box<dyn Field>>, r: &Box<dyn Field>, H: Gp, G: Vec<Gp>) -> Gp
where
    Gp: Group
        + MulAssign<Gp>
        + Mul<Gp, Output = Gp>
        + BitXor<RegisterField, Output = Gp>
        + Default
        + Debug,
{
    v_multi(G, x) * (H ^ from_field_boxed!(r))
}

//pub fn matrix_commitment<Gp>(x: Vec<Vec<Box<dyn Field>>>, r: &Box<dyn Field>, H: Gp, G: Vec<Gp>) -> Gp
//where
//Gp: Group
//+ MatMul<RegisterField, Output = Gp>
//+ AddAssign<Gp>
//+ Mul<Gp, Output = Gp>
//+ Xor<RegisterField, Output = Gp>,
//{
//fn reduce(x: Vec<Vec<Box<dyn Field>>) -> Vec<Box<dyn Field> {
//let mut result = x[0]
//}
//}

#[cfg(test)]
mod test {
    use super::*;
    use crate::algebra::field::{FiniteFieldSecp256k1, FiniteFieldSecp256r1};
    use crate::algebra::group::EllipticCurveGroupSecp256k1;

    #[test]
    fn test_v_multi() {
        let ex1 = FiniteFieldSecp256k1::new("5");
        let ex2 = FiniteFieldSecp256k1::new("6");
        let ex3 = FiniteFieldSecp256k1::new("7");
        let v1 = vec![
            EllipticCurveGroupSecp256k1::new(Box::new(ex1.clone()), Some(Box::new(ex2.clone()))),
            EllipticCurveGroupSecp256k1::new(Box::new(ex2.clone()), Some(Box::new(ex3.clone()))),
        ];
        let v2: Vec<Box<dyn Field>> = vec![
            Box::new(FiniteFieldSecp256k1::new("2")),
            Box::new(FiniteFieldSecp256r1::new("3")),
        ];
        let g = v_multi(v1, v2);
        let g2 =
            (EllipticCurveGroupSecp256k1::new(Box::new(ex1.clone()), Some(Box::new(ex2.clone())))
                ^ FiniteFieldSecp256k1::new("2"))
                * (EllipticCurveGroupSecp256k1::new(
                    Box::new(ex2.clone()),
                    Some(Box::new(ex3.clone())),
                ) ^ FiniteFieldSecp256r1::new("3"));
        assert_eq!(g == g2, true);
    }
}
