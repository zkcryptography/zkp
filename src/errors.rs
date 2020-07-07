use thiserror::Error;
/// An error during proving or verification, such as a verification failure.
#[derive(Debug, Error)]
pub enum ProofError {
    /// Something is wrong with the proof, causing a verification failure.
    #[error("Verification failed.")]
    VerificationFailure,

    /// Occurs during batch verification if the batch parameters are mis-sized.
    #[error("Mismatched parameter sizes for batch verification.")]
    BatchSizeMismatch,

    /// Occurs during creation of proof if we have no completed access groups
    #[error("You have not provided enough keys to complete any of your AND groups.")]
    InsufficientKeys,

    /// Occurs during verification if the input parameters do not have the expected form
    #[error("The number of provided responses does not match the expected number.")]
    IncorrectResponseNumber,

    /// Occurs during verification if some of the proof's points are invalid
    #[error("Some points could not decompress to valid Ristretto points.")]
    DecompressionError,
}
