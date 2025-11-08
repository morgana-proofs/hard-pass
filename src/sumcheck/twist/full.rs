
#[cfg(test)]
mod tests {
    use crate::{common::{algfn::AlgFnSO, claims::{LinEvalClaim, SumEvalClaim}, koala_passthrough::KoalaBear5 as F, math::{eq_poly, evaluate_multivar}, protocol::{ProtocolProver, ProtocolVerifier}, random::Random}, sumcheck::twist::{lookup_phase::{LookupPhaseAdvice, TwLookupPhase, TwLookupPhaseClaimsBefore}, read_phase::{TwReadPhase, TwReadPhaseAdvice}, sum_phase::{TwSumPhase, TwSumPhaseClaimsAfter, TwSumPhaseClaimsBefore}}};
    use fiat_shamir::{ProverState, VerifierState};
    use itertools::Itertools;
    use p3_challenger::{DuplexChallenger};
    use p3_field::{PrimeCharacteristicRing};
    use p3_koala_bear::{KoalaBear, Poseidon2KoalaBear, default_koalabear_poseidon2_16};
    use rand::{SeedableRng, TryRngCore, rngs::{OsRng, StdRng}};
    type KoalaChallenger = DuplexChallenger<KoalaBear, Poseidon2KoalaBear<16>, 16, 8>;

    #[test]
    // check that sum phase and read phase work together
    fn integration_23() {
        let x_logsize = 6;
        let t_logsize = 10; // relatively small values so we can materialize ram naively and validate everything
        
        let n_snapshots = 12;

        let rng = &mut StdRng::from_seed([0; 32]);

        // generate random access pattern
        let acc_indices = (0 .. 1 << t_logsize).map(|_| (rng.try_next_u32().unwrap() % (1 << x_logsize)) as usize).collect::<Vec<_>>();
        // generate random diffs
        let diff = (0 .. 1 << t_logsize).map(|_| F::rand(rng) ).collect::<Vec<_>>();

        let init_state = (0 .. 1 << x_logsize).map(|_| F::rand(rng) ).collect::<Vec<_>>();

        // compute ram and read directly:
        let mut ram = vec![];
        let mut read = vec![];
        let mut state = init_state.clone();
        for i in 0 .. 1 << t_logsize {
            state[acc_indices[i]] += diff[i];
            read.push(state[acc_indices[i]]);
            ram.push(state.clone())
        }
        
        let ram_materialized = ram.into_iter().flatten().collect::<Vec<_>>();
        let mut acc_materialized = vec![F::ZERO; 1 << (x_logsize + t_logsize)];
        for i in 0 .. (1 << t_logsize) {
            acc_materialized[(i << x_logsize) + acc_indices[i]] = F::ONE;
        }

        // generate evaluation random point:
        let rt = (0 .. t_logsize).map(|_| F::rand(rng) ).collect::<Vec<_>>();

        // evaluate read in it
        let ev = evaluate_multivar(&read, &rt);
        
        let permutation = default_koalabear_poseidon2_16();
        let challenger = KoalaChallenger::new(permutation);
        
        let protocol_read = TwReadPhase{ x_logsize, t_logsize };
        let protocol_sum = TwSumPhase {x_logsize, t_logsize};

        let mut transcript_p = ProverState::new(challenger.clone());
        let init_claims = LinEvalClaim{ ev, point: rt.clone() };
        let advice 
        = TwReadPhaseAdvice {
            diff: diff.clone(),
            acc: acc_indices.clone(),
            init_state: init_state.clone(),
            n_snapshots
        };
        let (claims, advice) = protocol_read.prove(&mut transcript_p, init_claims.clone(), advice);
        
        assert!(claims.acc_ev == evaluate_multivar(&acc_materialized, &claims.point));
        assert!(claims.ram_ev == evaluate_multivar(&ram_materialized, &claims.point));
        assert!(advice.init_ev == evaluate_multivar(&init_state, &claims.point[..x_logsize]));

        let _claims = protocol_sum.prove(&mut transcript_p, claims, advice);
        let proof = transcript_p.proof_data();        

        let mut transcript_v = VerifierState::new(proof.to_vec(), challenger.clone());
        let claims = protocol_read.verify(&mut transcript_v, init_claims.clone());
        
        let rx_ = claims.point[..x_logsize].to_vec();
        let rt_ = claims.point[..t_logsize].to_vec();

        let TwSumPhaseClaimsAfter{
            rx,
            rt: ut,
            init_ev,
            acc_ev,
            diff_ev
        } = protocol_sum.verify(&mut transcript_v, claims);

        // new point!!
        let pt = rx.iter().chain(ut.iter()).map(|x| *x).collect_vec();
        let acc_ev_ = evaluate_multivar(&acc_materialized, &pt);
        let diff_ev_ = evaluate_multivar(&diff, &ut);
        let init_ev_ = evaluate_multivar(&init_state, &rx);

        assert!(rx_ == rx);
        assert!(init_ev_ == init_ev);
        assert!(acc_ev_ == acc_ev);
        assert!(diff_ev_ == diff_ev);
    }

    #[test]

    fn integration_full() {
        let x_logsize = 6;
        let t_logsize = 10; // relatively small values so we can materialize ram naively and validate everything
        
        let n_snapshots = 12;

        let rng = &mut StdRng::from_seed([0; 32]);

        // generate random access pattern
        let acc_indices = (0 .. 1 << t_logsize).map(|_| (rng.try_next_u32().unwrap() % (1 << x_logsize)) as usize).collect::<Vec<_>>();
        // generate random diffs
        let diff = (0 .. 1 << t_logsize).map(|_| F::rand(rng) ).collect::<Vec<_>>();

        let init_state = (0 .. 1 << x_logsize).map(|_| F::rand(rng) ).collect::<Vec<_>>();

        // compute ram and read directly:
        // let mut ram = vec![];
        let mut read = vec![];
        let mut state = init_state.clone();
        for i in 0 .. 1 << t_logsize {
            state[acc_indices[i]] += diff[i];
            read.push(state[acc_indices[i]]);
            // ram.push(state.clone())
        }
        
        // let ram_materialized = ram.into_iter().flatten().collect::<Vec<_>>();
        // let mut acc_materialized = vec![F::ZERO; 1 << (x_logsize + t_logsize)];
        // for i in 0 .. (1 << t_logsize) {
        //     acc_materialized[(i << x_logsize) + acc_indices[i]] = F::ONE;
        // }

        // generate evaluation random point:
        let rt = (0 .. t_logsize).map(|_| F::rand(rng) ).collect::<Vec<_>>();

        // evaluate read in it
        let ev = evaluate_multivar(&read, &rt);
        
        let permutation = default_koalabear_poseidon2_16();
        let challenger = KoalaChallenger::new(permutation);
        
        let protocol_read = TwReadPhase{ x_logsize, t_logsize };
        let protocol_sum = TwSumPhase {x_logsize, t_logsize};
        let protocol_lookup = TwLookupPhase {x_logsize, t_logsize};

        let mut transcript_p = ProverState::new(challenger.clone());
        let init_claims = LinEvalClaim{ ev, point: rt.clone() };
        let advice 
        = TwReadPhaseAdvice {
            diff: diff.clone(),
            acc: acc_indices.clone(),
            init_state: init_state.clone(),
            n_snapshots
        };
        let (claims, advice) = protocol_read.prove(&mut transcript_p, init_claims.clone(), advice);
        let claims = protocol_sum.prove(&mut transcript_p, claims, advice);
        // these do not participate in the lookup phase, so we need to propagate them further
        let _init_ev_claim = LinEvalClaim{ point: claims.0.rt.clone(), ev: claims.0.init_ev};
        let _diff_ev_claim = LinEvalClaim{ point: claims.0.rt.clone(), ev: claims.0.diff_ev};
        let claims = TwLookupPhaseClaimsBefore::from_sum_phase(&claims.0);
        let _claims = protocol_lookup.prove(&mut transcript_p, claims, LookupPhaseAdvice{acc_indices: acc_indices.clone()});
        
        let proof = transcript_p.proof_data();        

        let mut transcript_v = VerifierState::new(proof.to_vec(), challenger.clone());
        let claims = protocol_read.verify(&mut transcript_v, init_claims.clone());
        let claims = protocol_sum.verify(&mut transcript_v, claims);       
        // these do not participate in the lookup phase, so we need to propagate them further
        let rt_phase_2 = claims.rt.clone(); // memorize this for future usage, technically I could use init_ev_claim but it might be eventually optimized out
        let init_ev_claim = LinEvalClaim{ point: claims.rx.clone(), ev: claims.init_ev};
        let diff_ev_claim = LinEvalClaim{ point: claims.rt.clone(), ev: claims.diff_ev};        
        let claims = TwLookupPhaseClaimsBefore::from_sum_phase(&claims);
        let claims = protocol_lookup.verify(&mut transcript_v, claims);
        
        let acc_idx_ev_claim = LinEvalClaim {point: claims.rt.to_vec(), ev: claims.acc_indices_ev};
        let pshf_ev_claim = LinEvalClaim {point: claims.rx.to_vec(), ev: claims.pushforward_ev};
        
        // validate all claims
        assert!(init_ev_claim.ev == evaluate_multivar(&init_state, &init_ev_claim.point));
        assert!(diff_ev_claim.ev == evaluate_multivar(&diff, &diff_ev_claim.point));
        
        let acc_idx_as_field = acc_indices.iter().map(|&i| F::from_prime_subfield(KoalaBear::from_u64(i as u64))).collect_vec();

        let eqpoly_rt = eq_poly(&rt_phase_2); // easy way to recover in what point 
        let mut pshf = vec![F::ZERO; 1 << x_logsize];
        for i in 0 .. 1 << t_logsize {
            pshf[acc_indices[i]] += eqpoly_rt[i];
        }

        assert!(acc_idx_ev_claim.ev == evaluate_multivar(&acc_idx_as_field, &acc_idx_ev_claim.point));
        assert!(pshf_ev_claim.ev == evaluate_multivar(&pshf, &pshf_ev_claim.point));
    }
}