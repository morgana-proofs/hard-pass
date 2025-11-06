use std::{cmp::min, marker::PhantomData};
use p3_maybe_rayon::prelude::*;
use crate::{common::{algfn::AlgFnSO, claims::{LinEvalClaim, SinglePointClaims, SumEvalClaim}, contexts::{ProverFieldCtx, VerifierFieldCtx}, formal_field::{Field, FormalField}, math::{bind_dense_poly, evaluate_univar, from_evals}, protocol::{ProtocolProver, ProtocolVerifier}}, sumcheck::{generic::{GenericSumcheckProver, GenericSumcheckVerifier}, glue::DensePostProcessing, sumcheckable::Sumcheckable}};

pub struct DenseSumcheck<F: FormalField, Fun: AlgFnSO<F>> {
    f: Fun,
    pub num_vars: usize,
    pub num_rounds: usize,
    _pd: PhantomData<F>,
}

impl<F: FormalField, Fun: AlgFnSO<F>> DenseSumcheck<F, Fun> {
    pub fn new(f: Fun, num_vars: usize) -> Self {
        Self::new_partial(f, num_vars, num_vars)
    }
    pub fn new_partial(f: Fun, num_vars: usize, num_rounds: usize) -> Self {
        Self {f, num_vars, num_rounds, _pd: PhantomData}
    }
}

impl<F: FormalField, Fun: AlgFnSO<F>, Ctx: VerifierFieldCtx<F=F>> ProtocolVerifier<Ctx> for DenseSumcheck<F, Fun> {
    type ClaimsBefore = SumEvalClaim<F>;
    type ClaimsAfter = SinglePointClaims<F>;

    fn verify(&self, ctx: &mut Ctx, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let generic_protocol_config = GenericSumcheckVerifier::<F>::new(self.f.deg(), self.num_vars);
        let claims = generic_protocol_config.verify(ctx, claims);

        let dense_post_processing = DensePostProcessing::new(self.f.clone());
        dense_post_processing.verify(ctx, claims)
    }
}

impl<F: Field, Fun: AlgFnSO<F>, Ctx: ProverFieldCtx<F=F>> ProtocolProver<Ctx> for DenseSumcheck<F, Fun> {
    type ProverInput = Vec<Vec<F>>;
    type ProverOutput = ();
    type ClaimsBefore = SumEvalClaim<F>;
    type ClaimsAfter = SinglePointClaims<F>;

    fn prove(&self, ctx: &mut Ctx, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        let generic_protocol_config = GenericSumcheckProver::new_partial(self.f.deg(), self.num_vars, self.num_rounds);

        let so = DenseSumcheckableSO::new(advice, self.f.clone(),  self.num_vars, claims.value.clone());

        let (claims, s) = generic_protocol_config.prove(ctx, claims, so);
        let poly_evs = s.final_evals();

        let dense_post_processing = DensePostProcessing::new(self.f.clone());
        dense_post_processing.prove(ctx, claims, poly_evs)
    }
}

#[derive(Clone, Debug)]
pub struct DenseSumcheckableSO<F: Field, Fun: AlgFnSO<F>> {
    pub polys: Vec<Vec<F>>,
    rs: Vec<F>,
    f: Fun,
    num_vars: usize,
    round_idx: usize,
    cached_unipoly: Option<Vec<F>>,

    pub claim: F,
}

impl<F: Field, Fun: AlgFnSO<F>> DenseSumcheckableSO<F, Fun> {
    pub fn new(polys: Vec<Vec<F>>, f: Fun, num_vars: usize, claim_hint: F) -> Self {
        let l = polys.len();
        assert_eq!(l, f.n_ins());
        for i in 0..l {
            assert_eq!(polys[i].len(), 1 << num_vars);
        }
        Self { polys, f, num_vars, round_idx: 0, cached_unipoly: None, rs: vec![], claim: claim_hint }
    }

    pub fn final_evals(&self) -> Vec<F> {
        assert!(self.round_idx == self.num_vars, "can only call final evals after the last round");
        self.polys.iter().map(|poly| poly[0]).collect()
    }
}

impl<F: Field, Fun: AlgFnSO<F>> Sumcheckable<F> for DenseSumcheckableSO<F, Fun> {
    fn bind(&mut self, r: F) {
        assert!(self.round_idx < self.num_vars, "the protocol has already ended");
        self.rs.push(r);
        for poly in &mut self.polys {
            bind_dense_poly(poly, r);
        }
        self.round_idx += 1;
        match self.cached_unipoly.take() {
            None => {panic!("should evaluate unipoly before binding - it has an opportunity to change the state due to in-place evaluation")}
            Some(u) => {self.claim = evaluate_univar(&u, &r)}
        }
    }

    fn response(&mut self) -> Vec<F>{
        assert!(self.round_idx < self.num_vars, "the protocol has already ended");

        match self.cached_unipoly.as_ref() {
            Some(p) => {return p.clone()},
            None => {
                let half = 1 << (self.num_vars - self.round_idx - 1);
                let n_polys = self.polys.len();

                let num_tasks = 8 * current_num_threads();

                let task_size = (half + num_tasks - 1) / num_tasks;

                let acc: Vec<Vec<F>> = (0..num_tasks).into_par_iter().map(|task_idx| {
                    let mut difs = vec![F::ZERO; n_polys];
                    let mut args = vec![F::ZERO; n_polys];
                    let mut acc = vec![F::ZERO; self.f.deg()];

                    (task_idx * task_size .. min((task_idx + 1) * task_size, half)).map(|i| {
                        for j in 0..n_polys {
                            args[j] = self.polys[j][2 * i + 1];
                        }

                        acc[0] = acc[0] + self.f.exec(&args);

                        for j in 0..n_polys {
                            difs[j] = self.polys[j][2 * i + 1] - self.polys[j][2 * i]
                        }

                        for s in 1..self.f.deg() {
                            for j in 0..n_polys {
                                args[j] = args[j] + difs[j];
                            }

                            acc[s] = acc[s] + self.f.exec(&args);
                        }
                    }).count();

                    acc
                }).collect();

                let mut total_acc = vec![F::ZERO; self.f.deg() + 1];

                for i in 0..acc.len() {
                    for j in 0..self.f.deg() {
                        total_acc[j + 1] = total_acc[j + 1] + acc[i][j]
                    }
                }

                total_acc[0] = self.claim - total_acc[1];

                // // ---- debugging
                // debug_assert!( total_acc[0] == {
                //     let mut acc0 = F::ZERO;
                //     let mut args = vec![F::ZERO; n_polys];
                //     for i in 0..half {
                //         for j in 0..n_polys {
                //             args[j] = self.polys[j][2 * i];
                //         }
                //         acc0 += self.f.exec(&args);
                //     }
                //     acc0
                // });
                // // ------------------------------

                self.cached_unipoly = Some(from_evals(&total_acc));
            }
        }
        self.cached_unipoly.as_ref().unwrap().clone()

    }

    fn challenges(&self) -> &[F] {
        &self.rs
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ops::Index;
    use crate::common::{algfn::AlgFnSO, claims::SumEvalClaim, koala_passthrough::KoalaBear5 as F, math::evaluate_multivar, random::Random};
    use fiat_shamir::{ProverState, VerifierState};
    use p3_challenger::{DuplexChallenger};
    use p3_field::{PrimeCharacteristicRing};
    use p3_koala_bear::{KoalaBear, Poseidon2KoalaBear, default_koalabear_poseidon2_16};
    use rand::rngs::OsRng;
   
    type KoalaChallenger = DuplexChallenger<KoalaBear, Poseidon2KoalaBear<16>, 16, 8>;

    #[derive(Clone, Copy)]
    pub struct TestFunction {}

    impl AlgFnSO<F> for TestFunction {
        fn exec(&self, args: &impl Index<usize, Output = F>) -> F {
            args[0] * args[1] - F::ONE
        }

        fn deg(&self) -> usize {
            2
        }

        fn n_ins(&self) -> usize {
            2
        }
    }

    #[test]
    fn dense_sumcheck_with_verifier_accepts_prover() {
        let rng = &mut OsRng;
        let logsize = 6;
        let polys : Vec<Vec<F>> = (0..2).map(|_| (0 .. 1 << logsize).map(|_|F::rand(rng)).collect()).collect();

        let f = TestFunction{};

        let mut output = vec![];

        for i in 0 .. 1 << logsize {
            let args : Vec<F> = polys.iter().map(|poly| poly[i]).collect();
            output.push(f.exec(&args));
        }
        
        let permutation = default_koalabear_poseidon2_16();
        let challenger = KoalaChallenger::new(permutation);

        let mut transcript_p = ProverState::new(challenger.clone());

        let claim = SumEvalClaim{value:output.into_iter().sum(), point: vec![]};
        let sumcheck = DenseSumcheck::new(f, logsize);
        let (output_claims, _) = sumcheck.prove(&mut transcript_p, claim.clone(), polys.clone());
        let proof = transcript_p.proof_data();
        
        let mut transcript_v = VerifierState::new(proof.to_vec(), challenger.clone());

        let expected_output_claims = sumcheck.verify(&mut transcript_v, claim.clone());
        assert_eq!(output_claims, expected_output_claims);

        let SinglePointClaims { point : new_point, evs } = output_claims;
        assert_eq!(polys.iter().map(|poly| evaluate_multivar(poly, &new_point)).collect::<Vec<_>>(), evs);
    }
}