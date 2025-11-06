use crate::common::formal_field::{Field, FormalField};

pub trait ChallengerCtx {
    type F: FormalField;
    /// Squeezes a new challenge from a transcript.
    fn challenge(&mut self) -> Self::F;
    /// Squeezes multiple challenges from a transcript;
    fn challenge_multi(&mut self, size: usize) -> Vec<Self::F>;
}


/// Minimal context formal field (without any extension mechanics; everything is assumed to be in extension).
/// Provides field (over constants) and cryptographic sponge. This should be enough to implement sumcheck verifiers
pub trait VerifierFieldCtx : ChallengerCtx {
    /// Read value from proof and process it in transcript. Fails in prover context.
    fn read(&mut self) -> Self::F;
    /// Read multiple values from proof and process it in transcript. Fails in prover context.        
    fn read_multi(&mut self, size: usize) -> Vec<Self::F>;
    /// Read value from proof WITHOUT PROCESSING IT IN TRANSCRIPT. Fails in prover context.
    fn unconstrained_read(&mut self) -> Self::F;
    /// Read multiple values from proof WITHOUT PROCESSING IT IN TRANSCRIPT. Fails in prover context.        
    fn unconstrained_read_multi(&mut self, size: usize) -> Vec<Self::F>;
}

pub trait ProverFieldCtx : ChallengerCtx<F: Field> {
    /// Write value to proof and transcript. Fails in verifier context.
    fn write(&mut self, value: Self::F) -> ();
    /// Write multiple values from proof and process it in transcript. Might validate size for convenience. Fails in verifier context.        
    fn write_multi(&mut self, size: usize, values: &[Self::F]) -> ();
    /// Write value to proof WITHOUT ADDING IT TO TRANSCRIPT. Fails in verifier context.
    fn unconstrained_write(&mut self, value: Self::F) -> ();
    /// Write multiple values from proof WITHOUT ADDING IT TO TRANSCRIPT. Might validate size for convenience. Fails in verifier context.        
    fn unconstrained_write_multi(&mut self, size: usize, values: &[Self::F]) -> ();
}