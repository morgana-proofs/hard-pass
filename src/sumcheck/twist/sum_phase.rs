use crate::{common::{
    algfn::AlgFnSO, claims::SumEvalClaim, contexts::{ChallengerCtx, ProverFieldCtx, VerifierFieldCtx}, formal_field::FormalField, math::{lte_ev, lte_poly}, protocol::{ProtocolProver, ProtocolVerifier}
}, sumcheck::{dense_sumcheck::DenseSumcheckableSO, generic::{GenericSumcheckProver, GenericSumcheckVerifier}}};
use p3_field::PrimeCharacteristicRing;

// This is protocol for the deg 3 sumcheck RAM(x, t) = init(x) + sum_t' Lte(t', t) Acc(x, t') diff(t')
// Additionally, as we already have another claim about Acc coming from read-phase, it is convenient
// to fold it with Acc(x, t) = sum_t' Acc(x, t') eq(t', t) so it will spit out a single claim.

pub struct TwSumPhase {
    pub x_logsize: usize,
    pub t_logsize: usize,
}

impl TwSumPhase {
    pub fn pp<F>(&self, gamma: F) -> TwSumPhasePP<F> {
        TwSumPhasePP { x_logsize: self.x_logsize, t_logsize: self.t_logsize, gamma }
    }
}

#[derive(Clone)]
pub struct TwSumPhaseClaimsBefore<F> {
    pub point: Vec<F>,
    pub ram_ev: F,
    pub acc_ev: F,
}

pub struct TwSumPhasePPClaimsAfter<F> {
    pub rx: Vec<F>,
    pub rt: Vec<F>,
    pub acc_ev: F, // this is in full point (rx | rt)
    pub diff_ev: F, // this is in rx = point[..x_logsize]
}

pub struct TwSumPhaseClaimsAfter<F> {
    pub rx: Vec<F>,
    pub rt: Vec<F>,
    pub init_ev: F, // this is in rt = point[x_logsize..]
    pub acc_ev: F, // this is in full point (rx | rt)
    pub diff_ev: F, // this is in rx = point[..x_logsize]
}

impl<Ctx: VerifierFieldCtx> ProtocolVerifier<Ctx> for TwSumPhase {
    type ClaimsBefore = TwSumPhaseClaimsBefore<Ctx::F>;
    type ClaimsAfter = TwSumPhaseClaimsAfter<Ctx::F>;

    fn verify(&self, ctx: &mut Ctx, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let init_ev = ctx.read();
        // start by cutting off init_ev, the remaining claim is about RAM as if it was started from 0
        let gamma = ctx.challenge();
        let (rx, rt) = claims.point.split_at(self.x_logsize);
        let folded_claim 
        = SumEvalClaim {
            point: vec![], // in theory this API would like to substitute rx here,
                           // but then they would be in wrong order, so do this manually
            value: (claims.ram_ev - init_ev) + gamma * claims.acc_ev
        };
        let sumcheck = GenericSumcheckVerifier::new(3, self.t_logsize);
        let SumEvalClaim { value, point: ut } = sumcheck.verify(ctx, folded_claim);
        let claims = TwSumPhasePPClaimsBefore { rt: rt.to_vec(), rx: rx.to_vec(), ut, value };
        let TwSumPhasePPClaimsAfter { rx, rt, acc_ev, diff_ev } = self.pp(gamma).verify(ctx, claims);
        TwSumPhaseClaimsAfter { rx, rt, init_ev, acc_ev, diff_ev }
    }
}

pub struct TwSumPhaseAdvice<F> {
    pub init_ev: F,
    pub diff: Vec<F>,
    pub acc_rx: Vec<F>,
}

impl<Ctx: ProverFieldCtx> ProtocolProver<Ctx> for TwSumPhase {
    type ClaimsBefore = TwSumPhaseClaimsBefore<Ctx::F>;
    type ClaimsAfter = TwSumPhaseClaimsAfter<Ctx::F>;

    type ProverInput = TwSumPhaseAdvice<Ctx::F>;
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
        let TwSumPhaseAdvice { init_ev, diff, acc_rx } = advice;
        ctx.write(init_ev);
        let gamma = ctx.challenge();
        let (rx, rt) = claims.point.split_at(self.x_logsize);
        let folded_claim 
        = SumEvalClaim {
            point: vec![], // in theory this API would like to substitute rx here,
                           // but then they would be in wrong order, so do this manually
            value: (claims.ram_ev - init_ev) + gamma * claims.acc_ev
        };

        let (lte, eq) = lte_poly(&rt);

        // // debugging

        // let fun = TwSumPhaseFn{ gamma, init_rx };

        // let mut expected_ram_claim = init_rx;
        // let mut expected_acc_claim = Ctx::F::ZERO;
        // let mut expected_folded_claim = init_rx;
        // for i in 0 .. (1 << self.t_logsize) {
        //     expected_ram_claim += lte[i] * diff[i] * acc_rx[i];
        //     expected_acc_claim += eq[i] * acc_rx[i];

        //     assert!(lte[i] * diff[i] * acc_rx[i] + gamma *  )

        //     expected_folded_claim += fun.exec(&[acc_rx[i], diff[i], lte[i], eq[i]]);
        // }

        // assert!(expected_acc_claim == claims.acc_ev);
        // assert!(expected_ram_claim == claims.ram_ev);
        // assert!(expected_folded_claim == folded_claim.value);

        // // debugging

        let polys = vec![
            acc_rx,
            diff,
            lte,
            eq,
        ];


        let f = TwSumPhaseFn {gamma};
        let s = DenseSumcheckableSO::new(polys, f, self.t_logsize, folded_claim.value);
        let sumcheck = GenericSumcheckProver::new(3, self.t_logsize);
        let (SumEvalClaim { value, point: ut }, s) = sumcheck.prove(ctx, folded_claim, s);
        let evals = s.final_evals();
        let pp_advice = [evals[0], evals[1]];
        let claims = TwSumPhasePPClaimsBefore { rt: rt.to_vec(), rx: rx.to_vec(), ut, value };
        let (TwSumPhasePPClaimsAfter { rx, rt, acc_ev, diff_ev }, _) = self.pp(gamma).prove(ctx, claims, pp_advice);
        (TwSumPhaseClaimsAfter{ rx, rt, init_ev, acc_ev, diff_ev }, ())
    }
}

#[derive(Clone)]
struct TwSumPhaseFn<F> {
    gamma: F,
}

impl<F: FormalField> AlgFnSO<F> for TwSumPhaseFn<F> {
    fn exec(&self, args: &impl std::ops::Index<usize, Output = F>) -> F {
        args[0] * (args[1] * args[2] + self.gamma * args[3])
    }

    fn deg(&self) -> usize {
        3
    }

    fn n_ins(&self) -> usize {
        4
    }
}

pub struct TwSumPhasePP<F> {
    pub x_logsize: usize,
    pub t_logsize: usize, 
    pub gamma: F,   
}

pub struct TwSumPhasePPClaimsBefore<F> {
    pub rt: Vec<F>,
    pub rx: Vec<F>,
    pub ut: Vec<F>,
    pub value: F,
}

// We have init(x) + sum_t' Lte(t', t) Acc(x, t') diff(t') + gamma sum_t' Acc(x, t') eq(t', t)
// Postprocessing will read claims about init, Acc and diff, and evaluate Lt and eq

impl<Ctx: VerifierFieldCtx> ProtocolVerifier<Ctx> for TwSumPhasePP<Ctx::F> {
    type ClaimsBefore = TwSumPhasePPClaimsBefore<Ctx::F>;
    type ClaimsAfter = TwSumPhasePPClaimsAfter<Ctx::F>;

    fn verify(&self, ctx: &mut Ctx, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let TwSumPhasePPClaimsBefore { value, rt, rx, ut } = claims;
        debug_assert!(rt.len() == self.t_logsize);
        debug_assert!(rx.len() == self.x_logsize);
        debug_assert!(ut.len() == self.t_logsize);
        let [acc_ev, diff_ev] = ctx.read_multi(2).try_into().unwrap();
        let (lte_term_ev, eq_term_ev) = lte_ev(&ut, &rt); // computation of lt also allows us to compute eq at the same time
        ((lte_term_ev * diff_ev + self.gamma * eq_term_ev) * acc_ev - value).require();
        TwSumPhasePPClaimsAfter{ rx, rt: ut, acc_ev, diff_ev }
    }
}

impl<Ctx: ProverFieldCtx> ProtocolProver<Ctx> for TwSumPhasePP<Ctx::F> {
    type ClaimsBefore = TwSumPhasePPClaimsBefore<Ctx::F>;
    type ClaimsAfter = TwSumPhasePPClaimsAfter<Ctx::F>;

    type ProverInput = [Ctx::F; 2];
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
        let TwSumPhasePPClaimsBefore { value, rt, rx, ut } = claims;
        debug_assert!(rt.len() == self.t_logsize);
        debug_assert!(rx.len() == self.x_logsize);
        debug_assert!(ut.len() == self.t_logsize);
        ctx.write_multi(2, &advice);
        let [acc_ev, diff_ev] = advice;
        let (lte_term_ev, eq_term_ev) = lte_ev(&ut, &rt); // computation of lt also allows us to compute eq at the same time
        debug_assert!({((lte_term_ev * diff_ev + self.gamma * eq_term_ev) * acc_ev - value).require(); true});
        (TwSumPhasePPClaimsAfter{ rx, rt: ut, acc_ev, diff_ev }, ())      
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{algfn::AlgFnSO, claims::SumEvalClaim, koala_passthrough::KoalaBear5 as F, math::{eq_poly, evaluate_multivar}, random::Random};
    use fiat_shamir::{ProverState, VerifierState};
    use itertools::Itertools;
    use p3_challenger::{DuplexChallenger};
    use p3_field::{PrimeCharacteristicRing};
    use p3_koala_bear::{KoalaBear, Poseidon2KoalaBear, default_koalabear_poseidon2_16};
    use rand::{SeedableRng, TryRngCore, rngs::{OsRng, StdRng}};
    type KoalaChallenger = DuplexChallenger<KoalaBear, Poseidon2KoalaBear<16>, 16, 8>;

    #[test]
    fn lte_makes_sense() {
        let rng = &mut StdRng::from_seed([0; 32]);
        let x = (0..3).map(|_| F::rand(rng)).collect_vec();
        let y = (0..3).map(|_| F::rand(rng)).collect_vec();
        let lte_y = lte_poly(&y);
        assert!(evaluate_multivar(&lte_y.0, &x) == lte_ev(&x, &y).0);
        assert!(evaluate_multivar(&lte_y.1, &x) == lte_ev(&x, &y).1);
    }

    #[test]
    fn twist_sum_phase_verifier_accepts_prover() {
        let x_logsize = 6;
        let t_logsize = 10; // relatively small values so we can materialize ram naively and validate everything
        
        let rng = &mut StdRng::from_seed([0; 32]);

        // generate random access pattern
        let acc = (0 .. 1 << t_logsize).map(|_| (rng.try_next_u32().unwrap() % (1 << x_logsize)) as usize).collect::<Vec<_>>();
        // generate random diffs
        let diff = (0 .. 1 << t_logsize).map(|_| F::rand(rng) ).collect::<Vec<_>>();

        let init_state = (0 .. 1 << x_logsize).map(|_| F::rand(rng) ).collect::<Vec<_>>();

        // compute ram directly:
        let mut ram = vec![];
        let mut state = init_state.clone();
        for i in 0 .. 1 << t_logsize {
            state[acc[i]] += diff[i];
            ram.push(state.clone())
        }
        
        let ram_materialized = ram.into_iter().flatten().collect::<Vec<_>>();
        let mut acc_materialized = vec![F::ZERO; 1 << (x_logsize + t_logsize)];
        for i in 0 .. (1 << t_logsize) {
            acc_materialized[(i << x_logsize) + acc[i]] = F::ONE;
        }

        let rx = (0 .. x_logsize).map(|_| F::rand(rng) ).collect::<Vec<_>>();
        let rt = (0 .. t_logsize).map(|_| F::rand(rng) ).collect::<Vec<_>>();

        let pt = rx.iter().chain(rt.iter()).map(|x| *x).collect_vec();

        let ram_ev = evaluate_multivar(&ram_materialized, &pt);
        let acc_ev = evaluate_multivar(&acc_materialized, &pt);
        let init_ev = evaluate_multivar(&init_state, &rx);
        
        let eq_rx = eq_poly(&rx);
        let acc_rx = (0 .. 1 << t_logsize).map(|i| eq_rx[acc[i]]).collect_vec();

        let permutation = default_koalabear_poseidon2_16();
        let challenger = KoalaChallenger::new(permutation);
        let mut transcript_p = ProverState::new(challenger.clone());
        let protocol = TwSumPhase{ x_logsize, t_logsize };

        let claims = TwSumPhaseClaimsBefore { point: pt, ram_ev, acc_ev };
        let advice 
        = TwSumPhaseAdvice { init_ev, diff: diff.clone(), acc_rx };

        protocol.prove(&mut transcript_p, claims.clone(), advice);

        let proof = transcript_p.proof_data();        
        let mut transcript_v = VerifierState::new(proof.to_vec(), challenger.clone());

        let TwSumPhaseClaimsAfter{
            rx: rx_,
            rt: ut,
            init_ev: init_ev_,
            acc_ev: acc_ev_,
            diff_ev: diff_ev_
        } = protocol.verify(&mut transcript_v, claims);

        // new point!!
        let pt = rx.iter().chain(ut.iter()).map(|x| *x).collect_vec();
        let acc_ev = evaluate_multivar(&acc_materialized, &pt);
        let diff_ev = evaluate_multivar(&diff, &ut);

        assert!(rx_ == rx);
        assert!(init_ev_ == init_ev);
        assert!(acc_ev_ == acc_ev);
        assert!(diff_ev_ == diff_ev);


    }
}