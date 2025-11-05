use std::marker::PhantomData;

use crate::common::{algfn::AlgFnSO, claims::{SinglePointClaims, SumEvalClaim}, contexts::{ProverFieldCtx, VerifierFieldCtx}, formal_field::FormalField, math::eq_ev, protocol::{ProtocolProver, ProtocolVerifier}};
pub struct DensePostProcessing<F: FormalField, Fun: AlgFnSO<F>> {
    pub f: Fun,
    _marker: PhantomData<F>
}

impl<F: FormalField, Fun: AlgFnSO<F>> DensePostProcessing<F, Fun> {
    pub fn new(f: Fun) -> Self {
        Self {f, _marker: PhantomData}
    }
}

impl<Ctx: VerifierFieldCtx, Fun: AlgFnSO<Ctx::F>> ProtocolVerifier<Ctx> for DensePostProcessing<Ctx::F, Fun> {
    type ClaimsBefore = SumEvalClaim<Ctx::F>;
    type ClaimsAfter = SinglePointClaims<Ctx::F>;

    fn verify(&self, ctx: &mut Ctx, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let SumEvalClaim {value: ev, point} = claims;
        let poly_evs = ctx.read_multi(self.f.n_ins());
        (self.f.exec(&poly_evs) - ev).require();
        SinglePointClaims{ evs: poly_evs, point }
    }
}

impl<Ctx: ProverFieldCtx, Fun: AlgFnSO<Ctx::F>> ProtocolProver<Ctx> for DensePostProcessing<Ctx::F, Fun> {
    type ClaimsBefore = SumEvalClaim<Ctx::F>;
    type ClaimsAfter = SinglePointClaims<Ctx::F>;
    type ProverInput = Vec<Ctx::F>; // poly evs
    type ProverOutput = ();

    fn prove(
        &self,
        ctx: &mut Ctx,
        claims: Self::ClaimsBefore,
        advice: Self::ProverInput
    ) -> (
        Self::ClaimsAfter,
        Self::ProverOutput
    ) {
        let SumEvalClaim {value: ev, point} = claims;
        ctx.write_multi(self.f.n_ins(), &advice);
        // (self.f.exec(&poly_evs) - ev).require(); <-- could be debug assert
        (SinglePointClaims{ evs: advice, point }, ())
    }
}

pub struct TwistPostProcessing {
    pub x_logsize: usize,
    pub t_logsize: usize,
}

pub struct TwistPPClaimBefore<F> {
    pub claims: SumEvalClaim<F>,
    pub rt: Vec<F>,
}

impl<Ctx: VerifierFieldCtx> ProtocolVerifier<Ctx> for TwistPostProcessing {
    type ClaimsBefore = TwistPPClaimBefore<Ctx::F>;
    type ClaimsAfter = SinglePointClaims<Ctx::F>; // (RAM, Acc) in point (x|t); eq-eval should be eliminated

    fn verify(&self, ctx: &mut Ctx, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let TwistPPClaimBefore { claims: SumEvalClaim { value: ev, point }, rt} = claims;
        debug_assert!(point.len() == self.t_logsize + self.x_logsize);
        let (ut, _) = point.split_at(self.x_logsize);
        let evs = ctx.read_multi(2);
        (evs[0] * evs[1] * eq_ev(&rt, ut) - ev).require();
        SinglePointClaims { evs, point }
    }
}
