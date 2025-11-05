/// Generic trait for arbitrary claim reduction protocols.
/// Ctx is meant to hold mutable verifier state, typically, a Fiat-Shamir challenger.
/// It can also theoretically hold a circuit builder so the same verifier implementation
/// can be used for recursion.
pub trait ProtocolVerifier<Ctx> {
    type ClaimsBefore;
    type ClaimsAfter;

    fn verify(&self, ctx: &mut Ctx, claims: Self::ClaimsBefore) -> Self::ClaimsAfter;
}

pub trait ProtocolProver<Ctx> {
    type ClaimsBefore;
    type ClaimsAfter;
    type ProverInput;
    type ProverOutput;
    
    fn prove(
        &self,
        ctx: &mut Ctx,
        claims: Self::ClaimsBefore,
        advice: Self::ProverInput
    ) -> (
        Self::ClaimsAfter,
        Self::ProverOutput
    );
}
