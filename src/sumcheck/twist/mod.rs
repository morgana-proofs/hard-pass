use crate::{common::{claims::{LinEvalClaim, SinglePointClaims, SumEvalClaim}, contexts::VerifierFieldCtx, protocol::ProtocolVerifier}, sumcheck::{generic::GenericSumcheckVerifier, glue::{TwistPPClaimBefore, TwistPostProcessing}}};

/// Protocol for passing the hard phase of Twist.
/// This is sumcheck of the form sum_{x, t} eq(rt, t) RAM(x, t) Acc(x, t) = READ(rt) 
pub struct TwistHardPhaseVerifier {
    pub x_logsize: usize,
    pub t_logsize: usize,
}

impl<Ctx: VerifierFieldCtx> ProtocolVerifier<Ctx> for TwistHardPhaseVerifier {
    type ClaimsBefore = LinEvalClaim<Ctx::F>; // evaluation of READ in point rt
    type ClaimsAfter = SinglePointClaims<Ctx::F>; // (RAM, Acc)

    fn verify(&self, ctx: &mut Ctx, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let rt = claims.point;
        let claims = SumEvalClaim {value: claims.ev, point: vec![]}; // transform into initial claim about sum
        let x_rounds = GenericSumcheckVerifier::new(2, self.x_logsize);
        let claims = x_rounds.verify(ctx, claims);
        let t_rounds = GenericSumcheckVerifier::new(3, self.t_logsize);
        let claims = t_rounds.verify(ctx, claims);
        let pp = TwistPostProcessing{ x_logsize: self.x_logsize, t_logsize: self.t_logsize };
        pp.verify(ctx, TwistPPClaimBefore{ claims, rt })
    }
}