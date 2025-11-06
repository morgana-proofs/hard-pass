use std::marker::PhantomData;


use crate::{common::{algfn::AlgFnSO, claims::{LinEvalClaim, SumEvalClaim}, contexts::{ProverFieldCtx, VerifierFieldCtx}, formal_field::{Field, FormalField}, math::{compress, decompress, evaluate_univar}, protocol::{ProtocolVerifier, ProtocolProver}}, sumcheck::sumcheckable::Sumcheckable};

/// A sumcheck with single output, without eq multiplier.
#[derive(Clone)]
pub struct GenericSumcheckVerifier<F: FormalField> {
    pub(crate) deg: usize,
    pub(crate) num_vars: usize,
    pub(crate) num_rounds: usize,
    _marker: PhantomData<F>,
}

impl<F: FormalField> GenericSumcheckVerifier<F> {
    pub fn new(deg: usize, num_vars: usize) -> Self {
        Self::new_partial(deg, num_vars, num_vars)
    }
    pub fn new_partial(deg: usize, num_vars: usize, num_rounds: usize) -> Self {
        Self { deg, num_vars, num_rounds, _marker: PhantomData }
    }
}

impl<Ctx: VerifierFieldCtx> ProtocolVerifier<Ctx> for GenericSumcheckVerifier<Ctx::F> {
    type ClaimsBefore = SumEvalClaim<Ctx::F>;
    type ClaimsAfter = SumEvalClaim<Ctx::F>;
    
    fn verify(&self, ctx: &mut Ctx, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let deg = self.deg;
        let mut sum_claim = claims.value;
        let mut rs = claims.point;
        for _ in 0..self.num_rounds {
            let compressed_poly = ctx.read_multi(deg); // read d coefficients: 0, 2, ..., d
            let poly = decompress(&sum_claim, &compressed_poly); // recover 1st coefficient
            let r = ctx.challenge(); // challenge
            rs.push(r.clone());
            sum_claim = evaluate_univar(&poly, &r);
        }
//        rs.reverse();
        SumEvalClaim{value: sum_claim, point: rs}
    }
}

pub struct GenericSumcheckProver<F: Field, S: Sumcheckable<F>> {
    pub(crate) deg: usize,
    pub(crate) num_vars: usize,
    pub(crate) num_rounds: usize,
    _marker: PhantomData<(F, S)>,
}

impl<F: Field, S: Sumcheckable<F>> GenericSumcheckProver<F, S> {
    pub fn new(deg: usize, num_vars: usize) -> Self {
        Self::new_partial(deg, num_vars, num_vars)
    }
    pub fn new_partial(deg: usize, num_vars: usize, num_rounds: usize) -> Self {
        Self { deg, num_vars, num_rounds, _marker: PhantomData }
    }
}

impl<F: Field, S: Sumcheckable<F>, Ctx: ProverFieldCtx<F = F>> ProtocolProver<Ctx> for GenericSumcheckProver<F, S> {
    type ClaimsBefore = SumEvalClaim<Ctx::F>;
    type ClaimsAfter = SumEvalClaim<Ctx::F>;
    
    type ProverInput = S;
    type ProverOutput = S;

    fn prove(
        &self,
        ctx: &mut Ctx,
        claims: Self::ClaimsBefore,
        mut sumcheckable: Self::ProverInput
    ) -> (Self::ClaimsAfter, Self::ProverOutput) {
    
        let deg = self.deg;
        let mut sum_claim = claims.value;
        let mut rs = claims.point;
        for _ in 0..self.num_rounds {
            let poly = sumcheckable.response();
            let (_sum_claim, compressed_poly) = compress(&poly);
            assert!(_sum_claim == sum_claim);
            assert!(compressed_poly.len() == deg);
            ctx.write_multi(deg, &compressed_poly);
            let r = ctx.challenge();
            rs.push(r);
            sum_claim = evaluate_univar(&poly, &r);
            sumcheckable.bind(r);
        }
        (SumEvalClaim { value: sum_claim, point: rs }, sumcheckable)
    }
}