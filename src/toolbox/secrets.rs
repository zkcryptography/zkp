use curve25519_dalek::scalar::Scalar;

pub trait SecretSharing {
    fn share(&mut self, secret: &Scalar, nr_of_shares: usize) -> Vec<Option<Scalar>>;
    fn complete(&mut self, secret: &Scalar, shares: &Vec<Option<Scalar>>) -> Result<Vec<Option<Scalar>>, String>;
    fn reconstruct(&mut self, shares: &Vec<Option<Scalar>>) -> Result<Scalar, String>;
}
