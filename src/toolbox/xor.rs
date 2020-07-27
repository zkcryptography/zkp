use curve25519_dalek::scalar::Scalar;
use rand::{CryptoRng, RngCore};
use rand::prelude::ThreadRng;
use crate::toolbox::secrets;
use crate::toolbox::util::random_scalar;
use log::{trace, debug, info};

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

impl Xor<ThreadRng> {
    /// Create a new Xor object with a default RNG.
    pub fn new_without_rng() -> Self {
        Xor { rng: rand::thread_rng() }
    }
}

impl<R> secrets::SecretSharing for Xor<R> where R: RngCore + CryptoRng {
    fn share(&mut self, secret: &Scalar, nr_of_shares: usize) -> Result<Vec<Scalar>, String> {
        info!("Sharing {} pieces of {:?}", nr_of_shares, secret);
        let mut shares: Vec<Scalar> = Vec::new();

        // generate n - 1 random shares; the zero-th share is the secret
        for _ in 1..nr_of_shares {
            shares.push(random_scalar(&mut self.rng));
        }

        // calculate the final share as a function of the random shares and the secret
        let val = xor_many_scalars(secret, shares.iter());
        shares.push(val);

        return Ok(shares);
    }

    /// For Xor, sparse_shares should include a None value for each share you want us to generate
    fn complete(&mut self, secret: &Scalar, sparse_shares: &Vec<Option<Scalar>>) -> Result<Vec<Scalar>, String> {
        let mut empties = 0;
        let mut shares: Vec<Scalar> = Vec::new();
        let mut new_shares: Vec<Scalar> = Vec::new();
        for share in sparse_shares.iter() {
            if share.is_some() {
                shares.push(share.unwrap());
            } else {
                if empties != 0 {     // the "zero-th" empty will be the one we have to XOR-calculate
                    trace!("Pushing a random Scalar to extra empty");
                    new_shares.push(random_scalar(&mut self.rng));
                }
                empties += 1;
            }
        }

        if empties < 1 {
            return Err(String::from("No empty shares in which to complete!"));
        }

        info!("Completing {} empties with {} known and secret = {:?}", empties, shares.len(), secret);

        let intermediate = xor_many_scalars(secret, shares.iter());
        let val = xor_many_scalars(&intermediate, new_shares.iter());

        debug!("The XOR'd share is {:?}", val);
        new_shares.push(val);

        let ret_shares: Vec<Scalar> = sparse_shares.iter().map(|x| {
            if x.is_some() {
                x.unwrap()
            } else {
                // it's OK to panic if we get a None here, since that should *never* happen
                new_shares.pop().unwrap()
            }
        }).collect();

        return Ok(ret_shares);
    }

    fn reconstruct(&mut self, shares: &Vec<Scalar>) -> Result<Scalar, String> {
        if shares.len() < 1 {
            return Err(String::from("No shares provided, impossible to reconstruct!"));
        }

        let secret = xor_many_scalars(&Scalar::zero(), shares.iter());

        if secret.is_canonical() {
            debug!("Used {} shares to reconstruct {:?}", shares.len(), secret);
            return Ok(secret);
        } else {
            debug!("Value from XOR isn't within the group! {:?}", secret);
            return Err(String::from("The reconstructed secret is outside the group"));
        }

    }
}

/// Given a list of scalars, XOR them all together.  We split out the `first` separately for efficiency's sake;
/// there are use cases where the initial value you want to XOR with isn't in your Vector, so you don't need to
/// push it.
///
/// The resulting value is **not** guaranteed to be modulo group order.  If this is important for your particular use
/// case, you'll need to do those checks after calling this function.
/// 
/// TODO is there a special way we need to write this function, to achieve some sort of SIMD benefit?
fn xor_many_scalars<'a, T>(first: &Scalar, others: T) -> Scalar
where
    T: Iterator<Item=&'a Scalar>,
{
    let mut the_bytes = first.clone().to_bytes();
    for scalar in others {
        let scal_bytes = scalar.to_bytes();
        for i in 0..the_bytes.len() {
            the_bytes[i] ^= scal_bytes[i];
        }
    }

    Scalar::from_bits(the_bytes)
}


#[allow(unused_imports)]
mod tests {
    use super::*;
    use crate::toolbox::secrets::SecretSharing;
    use curve25519_dalek::constants::BASEPOINT_ORDER;

    #[test]
    fn xor_many_easy() {
        let zeroes = vec![Scalar::zero(); 5];
        let res1 = xor_many_scalars(&Scalar::zero(), zeroes.iter());
        assert_eq!(Scalar::zero(), res1);

        let res2 = xor_many_scalars(&Scalar::one(), zeroes.iter());
        assert_eq!(Scalar::one(), res2);
    }

    #[test]
    fn xor_many_medium() {
        let scalars = vec![Scalar::from(8675309u32), Scalar::from(5551212u32), Scalar::from(4561414u32)];
        let res1 = xor_many_scalars(&Scalar::zero(), scalars.iter());
        assert_eq!(Scalar::from(9793927u32), res1);

        let res2 = xor_many_scalars(&Scalar::from(9743901u32), scalars.iter());
        assert_eq!(Scalar::from(122778u32), res2);
    }

    #[test]
    fn xor_share() {
        let mut xor = Xor::new_without_rng();
        let shares = xor.share(&Scalar::one(), 3);
        assert!(shares.is_ok());
        let new_shares = shares.unwrap().clone();
        info!("Shares: {:?}", new_shares);
        match xor.reconstruct(&new_shares) {
            Ok(val) => assert_eq!(Scalar::one(), val),
            Err(e) => assert!(false, format!("Error reconstructing secret: {}", e)),
        }
    }

    #[test]
    fn xor_reconstruct() {
        let mut xor = Xor::new_without_rng();
        let shares = vec![Scalar::from(8675309u32), Scalar::from(5551212u32), Scalar::from(4561414u32)];
        match xor.reconstruct(&shares) {
            Ok(val) => assert_eq!(Scalar::from(9793927u32), val),
            Err(e) => assert!(false, format!("Error reconstructing secret: {}", e)),
        }
    }

    #[test]
    fn xor_complete_easy() {
        let mut xor = Xor::new_without_rng();
        let sparse_shares = vec![Some(Scalar::from(123456789u32)), None];
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
        let sparse_shares = vec![Some(Scalar::from(8675309u32)), Some(Scalar::from(5551212u32)), Some(Scalar::from(4561414u32)), None];
        match xor.complete(&Scalar::from(122778u32), &sparse_shares) {
            Ok(shares) => {
                assert_eq!(Scalar::from(8675309u32), shares[0]);
                assert_eq!(Scalar::from(5551212u32), shares[1]);
                assert_eq!(Scalar::from(4561414u32), shares[2]);
                assert_eq!(Scalar::from(9743901u32), shares[3]);
            },
            Err(e) => assert!(false, format!("Error completing shares: {}", e)),
        }
    }

    #[test]
    fn xor_complete_hard() {
        let mut xor = Xor::new_without_rng();
        let sparse_shares = vec![None, None, None, None, None, Some(Scalar::from(711117u32)), None, None, None, None];
        match xor.complete(&Scalar::one(), &sparse_shares) {
            Ok(shares) => {
                assert_eq!(sparse_shares.len(), shares.len());
                let mut found = false;
                for s in shares.iter() {
                    // make sure our one original share is in there somewhere
                    if sparse_shares[5].unwrap() == *s {
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

    #[test]
    fn xor_reconstruct_out_of_group() {
        // 0x10 = 0000 1010             largest byte of \ell
        // 0x5  = 0000 0101
        //  XOR = 0000 1111

        let share1 = Scalar::from_canonical_bytes([12, 227, 105, 171, 173, 162, 96, 141, 241, 244, 32, 246, 255, 9, 210, 32, 110, 245, 179, 133, 8, 34, 83, 32, 220, 162, 102, 9, 189, 38, 231, 5]).unwrap();
        let share2 = BASEPOINT_ORDER;
        let share3 = Scalar::from(74u8);

        let mut xor = Xor::new_without_rng();
        let shares = vec![share1, share2, share3];
        assert!(xor.reconstruct(&shares).is_err(), "Shouldn't have been able to reconstruct!");
    }
}
