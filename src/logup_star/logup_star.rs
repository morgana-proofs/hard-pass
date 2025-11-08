/*
Logup* (Lev Soukhanov)

https://eprint.iacr.org/2025/946.pdf

*/

use multilinear_toolkit::prelude::*;
use p3_field::{ExtensionField, PrimeField64};

use p3_field::PrimeCharacteristicRing;

use super::{
    MIN_VARS_FOR_PACKING,
    quotient_gkr::{prove_gkr_quotient, verify_gkr_quotient},
};

#[derive(Debug)]
pub struct LogupStarStatements<EF> {
    pub on_indexes: Evaluation<EF>,
    pub on_table: Evaluation<EF>,
    pub on_pushforward: Vec<Evaluation<EF>>,
}

pub fn prove_logup_star<EF>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    table: &MleRef<'_, EF>,
    indexes: &[PF<EF>],
    claimed_value: EF,
    poly_eq_point: &[EF],
    pushforward: &[EF], // already commited
    max_index: Option<usize>,
) -> LogupStarStatements<EF>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: PrimeField64,
{
    let table_length = table.unpacked_len();
    let indexes_length = indexes.len();
    let packing = log2_strict_usize(table_length) >= MIN_VARS_FOR_PACKING
        && log2_strict_usize(indexes_length) >= MIN_VARS_FOR_PACKING;
    let mut max_index = max_index.unwrap_or(table_length);
    if packing {
        max_index = max_index.div_ceil(packing_width::<EF>());
    }

    let (poly_eq_point_packed, pushforward_packed, table_packed) = (
        MleRef::Extension(poly_eq_point).pack_if(packing),
        MleRef::Extension(pushforward).pack_if(packing),
        table.pack_if(packing),
    );

    let (sc_point, inner_evals, prod) = {
        let (sc_point, prod, table_folded, pushforward_folded) = run_product_sumcheck(
            &table_packed.by_ref(),
            &pushforward_packed.by_ref(),
            prover_state,
            claimed_value,
            table.n_vars(),
        );
        let inner_evals = vec![
            table_folded.as_extension().unwrap()[0],
            pushforward_folded.as_extension().unwrap()[0],
        ];
        (sc_point, inner_evals, prod)
    };

    let table_eval = inner_evals[0];
    prover_state.add_extension_scalar(table_eval);
    // delayed opening
    let on_table = Evaluation::new(sc_point.clone(), table_eval);

    let pushforwardt_eval = inner_evals[1];
    prover_state.add_extension_scalar(pushforwardt_eval);
    // delayed opening
    let mut on_pushforward = vec![Evaluation::new(sc_point, pushforwardt_eval)];

    // sanity check
    assert_eq!(prod, table_eval * pushforwardt_eval);

    let c = prover_state.sample();

    let (claim_left, _, eval_c_minux_indexes) = prove_gkr_quotient(
        prover_state,
        &poly_eq_point_packed.by_ref(),
        (c, indexes),
        None,
    );

    let increments = (0..table.unpacked_len())
        .into_par_iter()
        .map(PF::<EF>::from_usize)
        .collect::<Vec<_>>();
    let (claim_right, pushforward_final_eval, _) = prove_gkr_quotient(
        prover_state,
        &pushforward_packed.by_ref(),
        (c, &increments),
        Some(max_index),
    );

    let final_point_left = claim_left.point[1..].to_vec();
    let indexes_final_eval = c - eval_c_minux_indexes;
    prover_state.add_extension_scalar(indexes_final_eval);
    let on_indexes = Evaluation::new(final_point_left, indexes_final_eval);

    prover_state.add_extension_scalar(pushforward_final_eval);
    on_pushforward.push(Evaluation::new(
        claim_right.point[1..].to_vec(),
        pushforward_final_eval,
    ));

    // These statements remained to be proven
    LogupStarStatements {
        on_indexes,
        on_table,
        on_pushforward,
    }
}

pub fn verify_logup_star<EF>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    log_table_len: usize,
    log_indexes_len: usize,
    claims: &[Evaluation<EF>],
    alpha: EF, // batching challenge
) -> Result<LogupStarStatements<EF>, ProofError>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: PrimeField64,
{
    let (sum, postponed) =
        sumcheck_verify(verifier_state, log_table_len, 2).map_err(|_| ProofError::InvalidProof)?;

    if sum
        != claims
            .iter()
            .zip(alpha.powers())
            .map(|(c, a)| c.value * a)
            .sum::<EF>()
    {
        return Err(ProofError::InvalidProof);
    }

    let table_eval = verifier_state.next_extension_scalar()?;
    let pushforward_eval = verifier_state.next_extension_scalar()?;

    let on_table = Evaluation::new(postponed.point.clone(), table_eval);
    let mut on_pushforward = vec![Evaluation::new(postponed.point, pushforward_eval)];

    if table_eval * pushforward_eval != postponed.value {
        return Err(ProofError::InvalidProof);
    }

    let random_challenge = verifier_state.sample(); // "c" in the paper

    let (quotient_left, claim_left) = verify_gkr_quotient(verifier_state, log_indexes_len + 1)?;
    let (quotient_right, claim_right) = verify_gkr_quotient(verifier_state, log_table_len + 1)?;

    if quotient_left != quotient_right {
        return Err(ProofError::InvalidProof);
    }

    let final_point_left = MultilinearPoint(claim_left.point[1..].to_vec());
    let index_openined_value = verifier_state.next_extension_scalar()?;
    let on_indexes = Evaluation::new(final_point_left.clone(), index_openined_value);
    if claim_left.value
        != claims
            .iter()
            .zip(alpha.powers())
            .map(|(claim, a)| final_point_left.eq_poly_outside(&claim.point) * a)
            .sum::<EF>()
            * (EF::ONE - claim_left.point[0])
            + (random_challenge - index_openined_value) * claim_left.point[0]
    {
        return Err(ProofError::InvalidProof);
    }

    let final_point_right = claim_right.point[1..].to_vec();
    let pushforward_opening_value = verifier_state.next_extension_scalar()?;
    on_pushforward.push(Evaluation::new(
        final_point_right.clone(),
        pushforward_opening_value,
    ));

    let big_endian_mle = final_point_right
        .iter()
        .rev()
        .enumerate()
        .map(|(i, &p)| p * EF::TWO.exp_u64(i as u64))
        .sum::<EF>();

    if claim_right.value
        != pushforward_opening_value * (EF::ONE - claim_right.point[0])
            + (random_challenge - big_endian_mle) * claim_right.point[0]
    {
        return Err(ProofError::InvalidProof);
    }

    // these statements remained to be verified
    Ok(LogupStarStatements {
        on_indexes,
        on_table,
        on_pushforward,
    })
}

pub fn compute_pushforward<F: PrimeField64, EF: ExtensionField<EF>>(
    indexes: &[F],
    table_length: usize,
    poly_eq_point: &[EF],
) -> Vec<EF> {
    assert_eq!(indexes.len(), poly_eq_point.len());
    // TODO there are a lot of fun optimizations here
    let mut pushforward = EF::zero_vec(table_length);
    for (index, value) in indexes.iter().zip(poly_eq_point) {
        let index_usize = index.as_canonical_u64() as usize;
        pushforward[index_usize] += *value;
    }
    pushforward
}
