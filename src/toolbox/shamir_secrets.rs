use curve25519_dalek::scalar::Scalar;

#[derive(Clone)]
pub struct SecretShare {
    secret: Scalar,
    pub shares: Vec<Scalar>,
    threshold: usize,
}

impl SecretShare {
    pub fn complete(secret: Scalar, shares: &mut Vec<Option<Scalar>>) -> Result<SecretShare, String> {
        let nr_of_shares = shares.iter().filter(|&n| n.is_some()).count();

        let mut output: Vec<Scalar> = shares.iter().map(|share| {
            return match share.is_some() {
                true => share.unwrap(),
                false => secret //TODO: Shamir Secret Sharing
            };
        }).collect();
        output.insert(0, secret);
        Ok(SecretShare {
            secret,
            shares: output,
            threshold: nr_of_shares,
        })
    }

    pub fn reconstruct(shares: Vec<Scalar>) -> Result<Scalar, String> {
        return Ok(shares[0]); //TODO Shamir Secret Reconstruction
    }
}