use curve25519_dalek::scalar::Scalar;
use rand::{CryptoRng, RngCore};
use rand::prelude::ThreadRng;
use crate::toolbox::secrets::{SecretSharing, Share};
use log::{debug, info};

/// A SecretSharing implementation that is based on the all-shares XOR method.  In particular, you must have every outstanding share
/// of a secret in order to reconstruct that secret.  Because it is the simplest method, it has no interesting parameters.
pub struct Xor<R: CryptoRng + RngCore> {
    rng: R,
}

impl<R> Xor<R> where R: RngCore + CryptoRng {
    /// Create a new Xor object with the provided RNG implementation.
    pub fn new(rng: R) -> Self {
        Xor {
            rng
        }
    }
}

pub struct XorShare {
    value: Scalar,
}

impl<R> XorShare where R: CryptoRng + RngCore {
    fn random(rng: R) -> Self {
        XorShare { value: Scalar::random(&mut rng) }
    }
}

impl Share for XorShare {
    fn get_value(&self) -> Scalar {
        return self.value;
    }
}

impl From<Box<dyn Share>> for XorShare {
    fn from(val: Box<dyn Share>) -> Self {
        XorShare { value: val.get_value() }
    }
}

impl Xor<ThreadRng> {
    /// Create a new Xor object with a default RNG.
    pub fn new_without_rng() -> Self {
        Xor { rng: rand::thread_rng() }
    }
}

impl<R> SecretSharing for Xor<R> where R: RngCore + CryptoRng {
    fn share(&mut self, secret: &Scalar, nr_of_shares: usize) -> Result<Vec<Box<dyn Share>>, String> {
        info!("Sharing {} pieces of {:?}", nr_of_shares, secret);
        let mut shares: Vec<Box<dyn Share>> = Vec::new();
        
        // generate n - 1 random shares; the zero-th share is the secret
        for _ in 1..nr_of_shares {
            shares.push(Box::from(XorShare::random(&mut self.rng)) as Box<dyn Share>);
        }

        // calculate the final share as a function of the random shares and the secret
        match xor_many_shares(secret, &shares) {
            Ok(value) => shares.push(Box::from(XorShare { value }) as Box<dyn Share>),
            Err(e) => return Err(e),
        }

        return Ok(shares.iter().map(|s| Box::from(*s) as Box<dyn Share>).collect());
    }

    /// For Xor, sparse_shares should include a None value for each share you want us to generate
    fn complete(&mut self, secret: &Scalar, sparse_shares: &Vec<Option<Box<dyn Share>>>) -> Result<Vec<Box<dyn Share>>, String> {
        let mut empties = 0;
        let mut shares: Vec<Box<dyn Share>> = Vec::new();
        for share in sparse_shares.iter() {
            if share.is_some() {
                shares.push(share.unwrap());
            } else {
                empties += 1;
            }
        }

        if empties < 1 {
            return Err(String::from("No empty shares in which to complete!"));
        }

        info!("Completing {} empties with {} known and secret = {:?}", empties, shares.len(), secret);

        // the "zero-th" empty will be the one we have to XOR-calculate
        for _ in 1..empties {
            shares.push(Box::from(XorShare::random(&mut self.rng)) as Box<dyn Share>);
        }
        match xor_many_shares(secret, &shares) {
            Ok(value) => shares.push(Box::from(XorShare { value }) as Box<dyn Share>),
            Err(e) => return Err(e),
        }

        return Ok(shares);
    }

    fn reconstruct(&mut self, shares: &Vec<Box<dyn Share>>) -> Result<Scalar, String> {
        if shares.len() < 1 {
            return Err(String::from("No shares provided, impossible to reconstruct!"));
        }

        info!("Reconstructing from {} shares", shares.len());

        let secret = xor_many_scalars(&(*shares[0]).get_value(), &shares[1..].iter().map(|b| (*b).get_value()).collect());
        
        debug!("Reconstructed {:?}", secret);
        return secret;
    }
}

/// Given two Scalar values, return the XOR of their constituent byte arrays
pub fn xor_scalars(a: &Scalar, b: &Scalar) -> Scalar {
    let mut the_bytes = [0 as u8; 32];
    let abytes = a.to_bytes();
    let bbytes = b.to_bytes();
    for i in 0..the_bytes.len() {
        the_bytes[i] = abytes[i] ^ bbytes[i];
    }
    Scalar::from_bits(the_bytes)
}

/// Given a list of scalars, XOR them all together.  We split out the `first` separately for efficiency's sake;
/// there are use cases where the initial value you want to XOR with isn't in your Vector, so you don't need to
/// push it.
/// 
/// TODO WARNING: the result isn't guaranteed to be modulo group order.  Is that going to be a problem?
pub fn xor_many_scalars(first: &Scalar, others: &Vec<Scalar>) -> Result<Scalar, String> {
    if others.len() < 1 {
        return Err(String::from("Vector was empty, impossible to XOR anything"));
    }
    // each Scalar is 32 bytes
    let mut the_bytes = first.clone().to_bytes();
    for scalar in others.iter() {
        let scal_bytes = scalar.to_bytes();
        for i in 0..the_bytes.len() {
            the_bytes[i] ^= scal_bytes[i];
        }
    }

    return Ok(Scalar::from_bits(the_bytes));
}

/// Given a list of scalars, XOR them all together.  We split out the `first` separately for efficiency's sake;
/// there are use cases where the initial value you want to XOR with isn't in your Vector, so you don't need to
/// push it.
/// 
/// TODO WARNING: the result isn't guaranteed to be modulo group order.  Is that going to be a problem?
pub fn xor_many_shares(first: &Scalar, others: &Vec<Box<dyn Share>>) -> Result<Scalar, String> {
    if others.len() < 1 {
        return Err(String::from("Vector was empty, impossible to XOR anything"));
    }
    // each Scalar is 32 bytes
    let mut the_bytes = first.clone().to_bytes();
    for scalar in others.iter() {
        let scal_bytes = (**scalar).get_value().to_bytes();
        for i in 0..the_bytes.len() {
            the_bytes[i] ^= scal_bytes[i];
        }
    }

    return Ok(Scalar::from_bits(the_bytes));
}


#[allow(unused_imports)]
mod tests {
    use super::*;
    use crate::toolbox::secrets::SecretSharing;

    const jenny: Scalar = Scalar::from(8675309u32);
    const bogus: Scalar = Scalar::from(5551212u32);
    const white: Scalar = Scalar::from(4561414u32);
    const jenny_share: Box<dyn Share> = Box::from(XorShare{ value: jenny });
    const bogus_share: Box<dyn Share> = Box::from(XorShare{ value: bogus });
    const white_share: Box<dyn Share> = Box::from(XorShare{ value: white });

    #[test]
    fn xor_easy() {
        let res1 = xor_scalars(&Scalar::zero(), &Scalar::zero());
        assert_eq!(Scalar::zero(), res1);

        let res2 = xor_scalars(&Scalar::zero(), &Scalar::one());
        assert_eq!(Scalar::one(), res2);
    }

    #[test]
    fn xor_medium() {
        let c = Scalar::from(13691777u32);
        assert_eq!(c, xor_scalars(&jenny, &bogus));
    }

    #[test]
    fn xor_many_easy() {
        let zeroes = vec![Scalar::zero(); 5];
        let res1 = xor_many_scalars(&Scalar::zero(), &zeroes);
        assert!(res1.is_ok());
        assert_eq!(Scalar::zero(), res1.unwrap());

        let res2 = xor_many_scalars(&Scalar::one(), &zeroes);
        assert!(res2.is_ok());
        assert_eq!(Scalar::one(), res2.unwrap());
    }

    #[test]
    fn xor_many_medium() {
        let scalars = vec![jenny, bogus, white];
        let res1 = xor_many_scalars(&Scalar::zero(), &scalars);
        assert!(res1.is_ok());
        assert_eq!(Scalar::from(9793927u32), res1.unwrap());

        let res2 = xor_many_scalars(&Scalar::from(9743901u32), &scalars);
        assert!(res2.is_ok());
        assert_eq!(Scalar::from(122778u32), res2.unwrap());
    }

    #[test]
    fn xor_share() {
        let mut xor = Xor::new_without_rng();
        let shares = xor.share(&Scalar::one(), 3);
        assert!(shares.is_ok());
        let new_shares = shares.unwrap();
        match xor.reconstruct(&new_shares) {
            Ok(val) => assert_eq!(Scalar::one(), val),
            Err(e) => assert!(false, format!("Error reconstructing secret: {}", e)),
        }
    }

    #[test]
    fn xor_reconstruct() {
        let mut xor = Xor::new_without_rng();
        let shares = vec![jenny_share, bogus_share, white_share];
        match xor.reconstruct(&shares) {
            Ok(val) => assert_eq!(Scalar::from(9793927u32), val),
            Err(e) => assert!(false, format!("Error reconstructing secret: {}", e)),
        }
    }

    #[test]
    fn xor_complete_easy() {
        let mut xor = Xor::new_without_rng();
        let sparse_shares = vec![Some(Box::from(XorShare{value:Scalar::from(123456789u32)}) as Box<dyn Share>), None];
        match xor.complete(&Scalar::one(), &sparse_shares) {
            Ok(shares) => {
                assert_eq!(Scalar::from(123456789u32), shares[0]);
                assert_eq!(Scalar::from(123456788u32), shares[1]);
            },
            Err(e) => assert!(false, format!("Error completing shares: {}", e))
        }
    }

    #[test]
    fn xor_complete_medium() {
        let mut xor = Xor::new_without_rng();
        let sparse_shares = vec![Some(jenny_share), Some(bogus_share), Some(white_share), None];
        match xor.complete(&Scalar::from(122778u32), &sparse_shares) {
            Ok(shares) => {
                assert_eq!(jenny_share, shares[0]);
                assert_eq!(bogus_share, shares[1]);
                assert_eq!(white_share, shares[2]);
                assert_eq!(Scalar::from(9743901u32), shares[3]);
            },
            Err(e) => assert!(false, format!("Error completing shares: {}", e)),
        }
    }

    #[test]
    fn xor_complete_hard() {
        let mut xor = Xor::new_without_rng();
        let sparse_shares = vec![None, None, None, None, None, Some(Box::from(XorShare { value: Scalar::from(711117u32) }) as Box<dyn Share>), None, None, None, None];
        match xor.complete(&Scalar::one(), &sparse_shares) {
            Ok(shares) => {
                assert_eq!(sparse_shares.len(), shares.len());
                let mut found = false;
                for s in shares.iter() {
                    // make sure they're all filled in
                    assert_ne!(None, *s);

                    // make sure our one original share is in there somewhere
                    if sparse_shares[5].unwrap().get_value() == (**s).get_value() {
                        found = true;
                    }
                }
                assert!(found, "Didn't find original share in the completed list");
                let val = xor.reconstruct(&shares);
                assert!(val.is_ok());
                assert_eq!(Scalar::one(), val.unwrap());
            },
            Err(e) => assert!(false, format!("Unable to complete: {}", e)),
        }
    }
}
