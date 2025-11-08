use fiat_shamir::{PF, ProverState, VerifierState};
use p3_challenger::{FieldChallenger, GrindingChallenger};
use p3_field::PrimeCharacteristicRing;
use p3_field::PrimeField64;
use p3_maybe_rayon::prelude::{IntoParallelRefIterator, ParallelIterator};

use crate::common::math::evaluate_multivar;
use crate::common::math::reverse_point;
use crate::common::math::reverse_variable_ordering;
use crate::logup_star::verify_pushforward_is_well_formed;
use crate::{
    common::{
        formal_field,
        math::eq_poly,
        protocol::{ProtocolProver, ProtocolVerifier},
    },
    logup_star::{compute_pushforward, prove_pushforward_is_well_formed},
    sumcheck::twist::sum_phase::TwSumPhaseClaimsAfter,
};

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
        Self {
            rx: claims.rx.to_vec(),
            rt: claims.rt.to_vec(),
            acc_ev: claims.acc_ev,
        }
    }
}

pub struct TwLookupPhaseClaimsAfter<F> {
    pub rt: Vec<F>,
    pub acc_indices_ev: F, // evaluated in rt
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

impl<EF, Challenger> ProtocolVerifier<VerifierState<PF<EF>, EF, Challenger>> for TwLookupPhase
where
    Challenger: FieldChallenger<PF<EF>>
        + GrindingChallenger<Witness = PF<EF>>
        + fiat_shamir::FSChallenger<EF>,
    EF: p3_field::ExtensionField<PF<EF>> + formal_field::Field,
    PF<EF>: PrimeField64,
{
    type ClaimsBefore = TwLookupPhaseClaimsBefore<EF>;
    type ClaimsAfter = TwLookupPhaseClaimsAfter<EF>;

    fn verify(
        &self,
        ctx: &mut VerifierState<PF<EF>, EF, Challenger>,
        claims: Self::ClaimsBefore,
    ) -> Self::ClaimsAfter {
        // 1) Receive the commitment to the pushforward
        // for now: phony commitment (we receive the full polynomial)
        let committed_pushforward = ctx
            .receive_hint_extension_scalars(1 << self.x_logsize)
            .unwrap();

        // 2) verify the committed pushforward is well-formed
        let pushforward_correctness_claims =
            verify_pushforward_is_well_formed(ctx, &claims.rt, self.x_logsize).unwrap();

        // 3) verify claims on the pushforward (TODO I din't think we should do this here)
        assert_eq!(
            evaluate_multivar(&committed_pushforward, &claims.rx),
            claims.acc_ev
        );
        assert_eq!(
            evaluate_multivar(
                &committed_pushforward,
                &reverse_point(&pushforward_correctness_claims.on_pushforward.point.0)
            ),
            pushforward_correctness_claims.on_pushforward.value
        );

        TwLookupPhaseClaimsAfter {
            rt: pushforward_correctness_claims.on_indexes.point.0,
            acc_indices_ev: pushforward_correctness_claims.on_indexes.value,
        }
    }
}

impl<EF, Challenger> ProtocolProver<ProverState<PF<EF>, EF, Challenger>> for TwLookupPhase
where
    Challenger: FieldChallenger<PF<EF>>
        + GrindingChallenger<Witness = PF<EF>>
        + fiat_shamir::FSChallenger<EF>,
    EF: p3_field::ExtensionField<PF<EF>> + formal_field::Field,
    PF<EF>: PrimeField64,
{
    type ClaimsBefore = TwLookupPhaseClaimsBefore<EF>;
    type ClaimsAfter = TwLookupPhaseClaimsAfter<EF>;

    type ProverInput = LookupPhaseAdvice;

    type ProverOutput = ();

    fn prove(
        &self,
        ctx: &mut ProverState<PF<EF>, EF, Challenger>,
        claims: Self::ClaimsBefore,
        advice: Self::ProverInput,
    ) -> (Self::ClaimsAfter, Self::ProverOutput) {
        // 1) compute the pushforward
        let eq_poly_t = eq_poly(&claims.rt);
        let pushforward = compute_pushforward(&advice.acc_indices, 1 << self.x_logsize, &eq_poly_t);

        // 2) commit the pushforward
        ctx.hint_extension_scalars(&pushforward); // for now: phony commitment (we send the full polynomial)

        // 3) verify the committed pushforward is well-formed
        let pushforward_correctness_claims = prove_pushforward_is_well_formed(
            ctx,
            &reverse_variable_ordering(&advice.acc_indices)
                .par_iter()
                .map(|&i| PF::<EF>::from_usize(i))
                .collect::<Vec<_>>(),
            &reverse_variable_ordering(&eq_poly_t),
            &pushforward,
        );

        // 4) open the committed pushforward at 2 points:
        // - claims.rx -> claims.acc_ev
        // pushforward_correctness_claims.on_pushforward.point.0 -> pushforward_correctness_claims.on_pushforward.value

        (
            TwLookupPhaseClaimsAfter {
                rt: pushforward_correctness_claims.on_indexes.point.0,
                acc_indices_ev: pushforward_correctness_claims.on_indexes.value,
            },
            (),
        )
    }
}
