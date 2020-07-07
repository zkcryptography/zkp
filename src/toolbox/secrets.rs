use curve25519_dalek::scalar::Scalar;

/// SecretSharing is a generic interface for implementations of secret-sharing algorithms.  For more information on 
/// secret sharing, see the Handbook of Applied Cryptography, Sec 12.7 (http://cacr.uwaterloo.ca/hac/about/chap12.pdf)
pub trait SecretSharing {
    /// Given a secret and the desired number of shares to calculate, create secret shares.  It should be possible to
    /// feed the output of this function immediate back to reconstruct() and obtain the same secret value.
    fn share(&mut self, secret: &Scalar, nr_of_shares: usize) -> Result<Vec<Scalar>, String>;

    /// Given a secret and a partial list of shares, calculate additional shares such that the complete list of shares
    /// will reconstruct to the provided secret.
    /// 
    /// IMPLEMENTORS BEWARE: your function must not alter the ordering of shares!  That is, it should only fill in the
    /// Nones, ensuring that all provided shares show up at the same indices in the resulting Vector.
    fn complete(&mut self, secret: &Scalar, shares: &Vec<Option<Scalar>>) -> Result<Vec<Scalar>, String>;

    /// Given a sufficient set of shares, return the original secret value.
    fn reconstruct(&mut self, shares: &Vec<Scalar>) -> Result<Scalar, String>;
}
