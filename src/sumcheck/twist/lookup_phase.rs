use fiat_shamir::{ProverState, VerifierState};
use p3_challenger::{FieldChallenger, GrindingChallenger};

use crate::{common::protocol::{ProtocolProver, ProtocolVerifier}, sumcheck::twist::sum_phase::TwSumPhaseClaimsAfter};

pub struct TwLookupPhase {
    pub x_logsize: usize,
    pub t_logsize: usize,
}

// This is just Acc polynomial evaluated in rx, rt
pub struct TwLookupPhaseClaimsBefore<F> {
    pub rx: Vec<F>,
    pub rt: Vec<F>,
    pub acc_ev: F,
}

impl<F: Copy> TwLookupPhaseClaimsBefore<F> {
    pub fn from_sum_phase(claims: &TwSumPhaseClaimsAfter<F>) -> Self {
        Self { rx: claims.rx.to_vec(), rt: claims.rt.to_vec() , acc_ev: claims.acc_ev }
    }
}

pub struct TwLookupPhaseClaimsAfter<F> {
    pub rt: Vec<F>,
    pub acc_indices_ev: F, // evaluated in rt

    pub rx: Vec<F>, // these points are new
    pub pushforward_ev: F, // claim about new commitment to pushforward, evaluated in rx
}


// only acc_indices are required
pub struct LookupPhaseAdvice {
    pub acc_indices: Vec<usize>,
}

// Protocol:
// 1. takes claim about Acc(rx, rt)
// 2. this is [acc_indices_* (eq_rt)](rx) claim
// 3. commit to [acc_indices_* (eq_rt)]
// 4. run logup* to obtain other claim about acc_indices_* (eq_rt)
// 5. merge claims (old claim from 2 and new one which falls out of gkr) and output

impl<F, EF, Challenger> ProtocolVerifier<VerifierState<F, EF, Challenger>> for TwLookupPhase
where
Challenger: FieldChallenger<F> + GrindingChallenger<Witness = F>,
EF: p3_field::ExtensionField<F>,
F: p3_field::Field,
{
    type ClaimsBefore = TwLookupPhaseClaimsBefore<EF>;
    type ClaimsAfter = TwLookupPhaseClaimsAfter<EF>;

    fn verify(&self, ctx: &mut VerifierState<F, EF, Challenger>, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        todo!()
    }
}

impl<F, EF, Challenger> ProtocolProver<ProverState<F, EF, Challenger>> for TwLookupPhase
where
Challenger: FieldChallenger<F> + GrindingChallenger<Witness = F>,
EF: p3_field::ExtensionField<F>,
F: p3_field::Field,
{
    type ClaimsBefore = TwLookupPhaseClaimsBefore<EF>;
    type ClaimsAfter = TwLookupPhaseClaimsAfter<EF>;

    type ProverInput = LookupPhaseAdvice;

    type ProverOutput = ();

    fn prove(
        &self,
        ctx: &mut ProverState<F, EF, Challenger>,
        claims: Self::ClaimsBefore,
        advice: Self::ProverInput
    ) -> (
        Self::ClaimsAfter,
        Self::ProverOutput
    ) {
        todo!()
    }
}