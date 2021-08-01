use thiserror::Error;

pub type FsDkrResult<T> = Result<T, FsDkrError>;

#[derive(Error, Debug)]
pub enum FsDkrError {
    #[error("Too many malicious parties detected! Threshold {threshold:?}, Number of Refreshed Messages: {refreshed_keys:?}, Malicious parties detected when trying to refresh: malicious_parties:?")]
    PartiesThresholdViolation {
        threshold: u16,
        refreshed_keys: usize,
        // TODO: figure out how to retrieve the malicious parties indexes and add them to the error.
        // malicious_parties: [usize]
    },

    #[error("Shares did not pass verification.")]
    PublicShareValidationError,

    #[error("SizeMismatch error for the refresh message {refresh_message_index:?} - Fairness proof length: {fairness_proof_len:?}, Points Commited Length: {points_commited_len:?}, Points Encrypted Length: {points_encrypted_len:?}")]
    SizeMismatchError {
        refresh_message_index: usize,
        fairness_proof_len: usize,
        points_commited_len: usize,
        points_encrypted_len: usize,
    },

    #[error("Fairness proof verification failed.")]
    FairnessProof,

    #[error("Duplicated refresh message found.")]
    DuplicatedRefreshMessage,

    #[error("NotImplementedYet")]
    NotImplementedYet,
}
