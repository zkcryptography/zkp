use curve25519_dalek::scalar::Scalar;

/// SecretSharing is a generic interface for implementations of secret-sharing algorithms.  For more information on secret sharing, 
/// see the Handbook of Applied Cryptography, Section 12.7 (http://cacr.uwaterloo.ca/hac/about/chap12.pdf)
pub trait SecretSharing {
    /// Given a secret and the desired number of shares to calculate, create secret shares.  It should be possible to feed the output of this
    /// function immediate back to reconstruct and obtain the same secret value.
    fn share(&mut self, secret: &Scalar, nr_of_shares: usize) -> Result<Vec<Box<dyn Share>>, String>;

    /// Given a secret and a partial list of shares, calculate additional shares such that the complete list of shares will reconstruct to
    /// the provided secret.  Note that this function does NOT provide any ordering guarantees!  Specifically, any shares you provide
    /// the function may show up in a different place in the resulting Vector, as the algorithm needs.
    fn complete(&mut self, secret: &Scalar, shares: &Vec<Option<Box<dyn Share>>>) -> Result<Vec<Box<dyn Share>>, String>;

    /// Given a sufficient set of shares, return the original secret value.
    fn reconstruct(&mut self, shares: &Vec<Box<dyn Share>>) -> Result<Scalar, String>;
}

pub trait Share {
    fn get_value(&self) -> Scalar;
}
