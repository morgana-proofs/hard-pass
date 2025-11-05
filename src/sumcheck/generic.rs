use std::marker::PhantomData;


use crate::{common::{algfn::AlgFnSO, claims::{EvalClaim, SumClaim}, contexts::{ProverFieldCtx, VerifierFieldCtx}, formal_field::{Field, FormalField}, math::{compress, decompress, evaluate_univar}, protocol::{ProtocolVerifier, ProtocolProver}}, sumcheck::sumcheckable::Sumcheckable};

/// A sumcheck with single output, without eq multiplier.
#[derive(Clone)]
pub struct SumcheckProtocol<F: FormalField, Fun: AlgFnSO<F>> {
    pub(crate) f: Fun,
    pub(crate) num_vars: usize,
    pub(crate) num_rounds: usize,
    _marker: PhantomData<F>,
}

impl<F: FormalField, Fun: AlgFnSO<F>> SumcheckProtocol<F, Fun> {
    pub fn new(f: Fun, num_vars: usize) -> Self {
        Self::new_partial(f, num_vars, num_vars)
    }
    pub fn new_partial(f: Fun, num_vars: usize, num_rounds: usize) -> Self {
        Self { f, num_vars, num_rounds, _marker: PhantomData }
    }
}

impl<Ctx: VerifierFieldCtx, Fun: AlgFnSO<Ctx::F>> ProtocolVerifier<Ctx> for SumcheckProtocol<Ctx::F, Fun> {
    type ClaimsBefore = SumClaim<Ctx::F>;
    type ClaimsAfter = SumClaim<Ctx::F>;
    
    fn verify(&self, ctx: &mut Ctx, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let d = self.f.deg();
        let mut sum_claim = claims.ev;
        let mut rs = claims.point;
        for _ in 0..self.num_rounds {
            let compressed_poly = ctx.read_multi(d); // read d coefficients: 0, 2, ..., d
            let poly = decompress(&sum_claim, &compressed_poly); // recover 1st coefficient
            let r = ctx.challenge(); // challenge
            rs.push(r.clone());
            sum_claim = evaluate_univar(&poly, &r);
        }
//        rs.reverse();
        SumClaim{ev: sum_claim, point: rs}
    }
}

pub struct SumcheckGenericProverImpl<F: Field, Fun: AlgFnSO<F>, S: Sumcheckable<F>> {
    pub(crate) f: Fun,
    pub(crate) num_vars: usize,
    pub(crate) num_rounds: usize,
    _marker: PhantomData<(F, Fun, S)>,
}

impl<F: Field, Fun: AlgFnSO<F>, S: Sumcheckable<F>> SumcheckGenericProverImpl<F, Fun, S> {
    pub fn new(f: Fun, num_vars: usize) -> Self {
        Self::new_partial(f, num_vars, num_vars)
    }
    pub fn new_partial(f: Fun, num_vars: usize, num_rounds: usize) -> Self {
        Self { f, num_vars, num_rounds, _marker: PhantomData }
    }
}

pub enum SumcheckOutput<F, S> {
    Final(Vec<F>),
    Partial(S)
}

impl<F: Field, Fun: AlgFnSO<F>, S: Sumcheckable<F>, Ctx: ProverFieldCtx<F = F>> ProtocolProver<Ctx> for SumcheckGenericProverImpl<F, Fun, S> {
    type ClaimsBefore = SumClaim<Ctx::F>;
    type ClaimsAfter = SumClaim<Ctx::F>;
    
    type ProverInput = S;
    type ProverOutput = SumcheckOutput<F, S>;

    fn prove(
        &self,
        ctx: &mut Ctx,
        claims: Self::ClaimsBefore,
        mut sumcheckable: Self::ProverInput
    ) -> (Self::ClaimsAfter, Self::ProverOutput) {
    
        let d = self.f.deg();
        let mut sum_claim = claims.ev;
        let mut rs = claims.point;
        for _ in 0..self.num_rounds {
            let poly = sumcheckable.response();
            let (_sum_claim, compressed_poly) = compress(&poly);
            assert!(_sum_claim == sum_claim);
            assert!(compressed_poly.len() == d);
            ctx.write_multi(d, &compressed_poly);
            let r = ctx.challenge();
            rs.push(r);
            sum_claim = evaluate_univar(&poly, &r);
            sumcheckable.bind(r);
        }
        if self.num_rounds == self.num_vars {
            let final_evals = sumcheckable.final_evals();
            debug_assert_eq!(self.f.exec(&final_evals), sum_claim, "Final evals are passed as prover output for last round postprocess");
            (SumClaim { ev: sum_claim, point: rs }, SumcheckOutput::Final(final_evals))
        } else {
            (SumClaim { ev: sum_claim, point: rs }, SumcheckOutput::Partial(sumcheckable))
        }
    }
}