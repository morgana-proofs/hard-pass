/*
Logup* (Lev Soukhanov)

https://eprint.iacr.org/2025/946.pdf

*/

use multilinear_toolkit::prelude::*;
use p3_field::{ExtensionField, PrimeField64};

use p3_field::PrimeCharacteristicRing;

use super::quotient_gkr::{prove_gkr_quotient, verify_gkr_quotient};

#[derive(Debug)]
pub struct PushforwardValidityStatements<EF> {
    pub on_indexes: Evaluation<EF>,
    pub on_pushforward: Evaluation<EF>,
}

// prove that P = pushforward(I, eq_r) is well-formed (P previously committed)
pub fn prove_pushforward_is_well_formed<EF>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    indexes: &[PF<EF>], // I
    poly_eq: &[EF],     // eq_r
    pushforward: &[EF], // already commited
) -> PushforwardValidityStatements<EF>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: PrimeField64,
{
    let c = prover_state.sample();

    let (claim_left, _, eval_c_minux_indexes) = prove_gkr_quotient(
        prover_state,
        &MleRef::Extension(poly_eq),
        (c, indexes),
        None,
    );

    let increments = (0..poly_eq.len())
        .into_par_iter()
        .map(PF::<EF>::from_usize)
        .collect::<Vec<_>>();
    let (claim_right, pushforward_final_eval, _) = prove_gkr_quotient(
        prover_state,
        &MleRef::Extension(&pushforward),
        (c, &increments),
        None,
    );

    let final_point_left = claim_left.point[1..].to_vec();
    let indexes_final_eval = c - eval_c_minux_indexes;
    prover_state.add_extension_scalar(indexes_final_eval);
    let on_indexes = Evaluation::new(final_point_left, indexes_final_eval);

    prover_state.add_extension_scalar(pushforward_final_eval);
    let on_pushforward = Evaluation::new(claim_right.point[1..].to_vec(), pushforward_final_eval);

    PushforwardValidityStatements {
        on_indexes,
        on_pushforward,
    }
}

// verify that P = pushforward(I, eq_r) is well-formed (P previously committed)
pub fn verify_pushforward_is_well_formed<EF>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    eq_point: &[EF], // r
    log_table_len: usize,
) -> Result<PushforwardValidityStatements<EF>, ProofError>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: PrimeField64,
{
    let log_indexes_len = eq_point.len();
    let c = verifier_state.sample(); // "c" in the paper

    let (quotient_left, claim_left) = verify_gkr_quotient(verifier_state, log_indexes_len + 1)?;
    let (quotient_right, claim_right) = verify_gkr_quotient(verifier_state, log_table_len + 1)?;

    if quotient_left != quotient_right {
        return Err(ProofError::InvalidProof);
    }

    let final_point_left = MultilinearPoint(claim_left.point[1..].to_vec());
    let index_openined_value = verifier_state.next_extension_scalar()?;
    let on_indexes = Evaluation::new(final_point_left.clone(), index_openined_value);
    if claim_left.value
        != final_point_left.eq_poly_outside(&MultilinearPoint(eq_point.to_vec()))
            * (EF::ONE - claim_left.point[0])
            + (c - index_openined_value) * claim_left.point[0]
    {
        return Err(ProofError::InvalidProof);
    }

    let final_point_right = claim_right.point[1..].to_vec();
    let pushforward_opening_value = verifier_state.next_extension_scalar()?;
    let on_pushforward = Evaluation::new(final_point_right.clone(), pushforward_opening_value);

    let big_endian_mle = final_point_right
        .iter()
        .rev()
        .enumerate()
        .map(|(i, &p)| p * EF::TWO.exp_u64(i as u64))
        .sum::<EF>();

    if claim_right.value
        != pushforward_opening_value * (EF::ONE - claim_right.point[0])
            + (c - big_endian_mle) * claim_right.point[0]
    {
        return Err(ProofError::InvalidProof);
    }

    Ok(PushforwardValidityStatements {
        on_indexes,
        on_pushforward,
    })
}

pub fn compute_pushforward<EF: ExtensionField<EF>>(
    indexes: &[usize],
    table_length: usize,
    poly_eq_point: &[EF],
) -> Vec<EF> {
    assert_eq!(indexes.len(), poly_eq_point.len());
    // TODO there are a lot of fun optimizations here
    let mut pushforward = EF::zero_vec(table_length);
    for (index, value) in indexes.iter().zip(poly_eq_point) {
        pushforward[*index] += *value;
    }
    pushforward
}
