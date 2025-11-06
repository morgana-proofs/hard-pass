use std::{cmp::min, time::Instant};

use p3_maybe_rayon::prelude::*;

use crate::{
    common::{
        algfn::AlgFnSO,
        claims::{LinEvalClaim, SinglePointClaims, SumEvalClaim},
        contexts::{ProverFieldCtx, VerifierFieldCtx}, formal_field::{Field, FormalField},
        math::{bind_dense_poly_nonpar, eq_poly, eq_poly_scaled, evaluate_univar, from_evals},
        protocol::{ProtocolProver, ProtocolVerifier}},
        sumcheck::{
            dense_sumcheck::DenseSumcheckableSO,
            generic::{GenericSumcheckProver, GenericSumcheckVerifier},
            glue::{TwPPClaimBefore, TwPPInput, TwPostProcessing},
            sumcheckable::Sumcheckable
        }
    };

// This version of Twist works as follows:

// There is a diff(t) polynomial and acc(t) polynomial
// There is also init(x) polynomial, which normally = 0, but sometimes it could be not (say if we are doing continuation, idk)
// read always happens after diff, so we do |t| diffs and |t| reads and values of ram do not include init(x) but do include last state

// acc(t) is upgraded to Acc(x, t) (presumably using logup*)
// To evaluate Acc(rx, rt) we need to compute <acc_* eq[rt], eq[rx]>. The validity of acc_* eq[rt] is checked by logup* argument.
// square-decomposition is not done because we assume RAM to be relatively small (|x| << |t|)

// A polynomial RAM(x, t) = init(x) + sum[t'] Lteq(t', t) Acc(x, t') diff(t'). This sumcheck is only over t',
// so it is dense and in general only issue is actually evaluating Acc and Lt in given challenge points (which is not hard)

// A polynomial read(t) = sum[x, t'] RAM(x, t') Acc(x, t') eq(t, t')
// This is referred as "hard phase" because the sumcheck here is sparse.

// As usual, phases are happening in an order reverse to the data-flow, so hard phase goes first.
// We will refer to them as "read phase", "write phase" and "spark phase". Read phase is hard.
// Additional commitments (to acc_* eq[rt]) happen before spark phase only, the rest is pure sumchecks.

// I will for now ignore the idea that we might also need to query RAM final state for continuation; this is essentially
// trivial to achieve and is not expected to have any significant overhead.


/// Read (hard) phase of the Twist protocol.
/// This is sumcheck of the form sum_{x, t} eq(rt, t) RAM(x, t) Acc(x, t) = READ(rt) 
pub struct TwReadPhase {
    pub x_logsize: usize,
    pub t_logsize: usize,
}

impl<Ctx: VerifierFieldCtx> ProtocolVerifier<Ctx> for TwReadPhase {
    type ClaimsBefore = LinEvalClaim<Ctx::F>; // evaluation of READ in point rt
    type ClaimsAfter = SinglePointClaims<Ctx::F>; // (RAM, Acc)

    fn verify(&self, ctx: &mut Ctx, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let rt = claims.point;
        let claims = SumEvalClaim {value: claims.ev, point: vec![]}; // transform into initial claim about sum
        let x_rounds = GenericSumcheckVerifier::new(2, self.x_logsize);
        let claims = x_rounds.verify(ctx, claims);
        let t_rounds = GenericSumcheckVerifier::new(3, self.t_logsize);
        let claims = t_rounds.verify(ctx, claims);
        let pp = TwPostProcessing{ x_logsize: self.x_logsize, t_logsize: self.t_logsize };
        pp.verify(ctx, TwPPClaimBefore{ claims, rt })
    }
}

pub struct TwReadPhaseAdvice<F> {
    pub diff: Vec<F>,
    pub acc: Vec<usize>,
    pub init_state: Vec<F>,
    pub n_snapshots: usize,
}

impl<Ctx: ProverFieldCtx> ProtocolProver<Ctx> for TwReadPhase {
    type ClaimsBefore = LinEvalClaim<Ctx::F>;
    type ClaimsAfter = SinglePointClaims<Ctx::F>;
    type ProverInput = TwReadPhaseAdvice<Ctx::F>;
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
        let mut start = Instant::now();

        let TwReadPhaseAdvice { diff, acc, init_state, n_snapshots } = advice;

        let rt = claims.point;
        let claims = SumEvalClaim {value: claims.ev, point: vec![]}; // transform into initial claim about sum

        let sumcheckable_x = TwReadPhaseSumcheckableX::new(
            diff,
            acc,
            init_state,
            &rt,
            n_snapshots,
            &self,
            claims.value
        );

        let end = Instant::now();
        println!("prep: {} ms", (end - start).as_millis());
        let start = end;

        let x_rounds = GenericSumcheckProver::new(2, self.x_logsize);
        let (claims, sumcheckable_x) = x_rounds.prove(ctx, claims, sumcheckable_x);

        let end = Instant::now();
        println!("x rounds: {} ms", (end - start).as_millis());
        let start = end;

        let sumcheckable_t = sumcheckable_x.finish();
        
        let end = Instant::now();
        println!("x -> t transition: {} ms", (end - start).as_millis());
        let start = end;
        
        let t_rounds = GenericSumcheckProver::new(3, self.t_logsize);
        let (claims, sumcheckable_t) = t_rounds.prove(ctx, claims, sumcheckable_t);
        let final_evals = sumcheckable_t.final_evals();
        let pp = TwPostProcessing{ x_logsize: self.x_logsize, t_logsize: self.t_logsize };
        let ret = pp.prove(ctx, TwPPClaimBefore{ claims, rt }, TwPPInput{ram_ev: final_evals[0], acc_ev: final_evals[1]});
    
        let end = Instant::now();
        println!("t rounds: {} ms", (end - start).as_millis());
        
        ret
    }
    

    

}

// Note: this assumes that values in RAM over extension. This is relatively fair, as vectorized values will be rlc-ed to extension,
// and also these become extension after the 2nd round anyway. Gruen's skip optimizations or similar tricks can be investigated
// separately.
pub struct RAMData<F: Field> {
    pub diff: Vec<F>,
    pub acc: Vec<usize>,
    pub x_logsize: usize,
    pub t_logsize: usize,
    /// represents some collection of snapshots of RAM,
    /// taken at positions idx * ((1 << t_logsize) + 1) / snapshots.len() 
    /// --- note there is |t| + 1 states in total including initial state
    pub snapshots: Vec<Vec<F>>,
    pub n_snapshots: usize,

    /// represents coefficients attained by acc during binds
    pub multipliers: Vec<F>,
    /// saved for caching purposes
    pub eq_poly_rt: Vec<F>,
    /// saved for multiplier recovery purposes
    pub eq_poly_rt_inv: Vec<F>,
}

impl<F: Field> RAMData<F> {
    /// Constructs new RAM data. There is always a single snapshot, additional ones will be added during the sumcheck processing.
    pub fn new(diff: Vec<F>, acc: Vec<usize>, init_state: Vec<F>, rt: &[F], n_snapshots: usize, cfg: &TwReadPhase) -> Self {
        let x_logsize = cfg.x_logsize;
        let t_logsize = cfg.t_logsize;
        // In debug we will check that data is well-formed.
        debug_assert!(diff.len() == 1 << t_logsize);
        debug_assert!(acc.len() == 1 << t_logsize);
        debug_assert!(init_state.len() == 1 << x_logsize);
        debug_assert!(rt.len() == t_logsize);
        for i in 0 .. 1 << t_logsize {
            debug_assert!(acc[i] < (1 << x_logsize)); // all address accesses are correct
        }

        let eq_poly_rt = eq_poly(&rt);

        let mirror_rt = rt.into_iter().map(|&x| F::ONE - x).collect::<Vec<_>>();
        let mut total_prod = F::ONE;
        for i in 0..t_logsize {
            total_prod *= rt[i] * mirror_rt[i];
        }

        let eq_poly_rt_inv = eq_poly_scaled(total_prod.inverse(), &mirror_rt);

        Self {
            diff,
            acc,
            x_logsize,
            t_logsize,
            snapshots: vec![init_state],
            multipliers: eq_poly_rt.clone(),
            n_snapshots,
            eq_poly_rt,
            eq_poly_rt_inv,
        }
    }

    /// Changes RAM[x, t] to a new one, obtained by binding lowest coordinate of x to r (it also has a valid RAM encoding)
    pub fn bind(&mut self, r: F) -> () {
        assert!(self.x_logsize > 0);
        self.x_logsize -= 1;

        self.snapshots.par_iter_mut().for_each(|snapshot| bind_dense_poly_nonpar(snapshot, r));

        let nr = F::ONE - r;
        let diff = &mut self.diff;
        let acc = &mut self.acc;
        let multipliers = &mut self.multipliers;
        diff.par_iter_mut().zip(acc.par_iter_mut()).zip(multipliers.par_iter_mut()).for_each(|((d, a), m)| {
            let anew = *a >> 1;
            let abit = *a - (anew << 1);
            *a = anew;
            if abit == 1 {
                *d *= r;
                *m *= r;
            } else {
                *d *= nr;
                *m *= nr;
            }
        });
    }

    /// Called after x_logsize = 0 to extract all values. Sequential, but considering it only has additions,
    /// optimization is likely unnecessary.
    pub fn t_form(&self) -> Vec<F> {
        assert!(self.x_logsize == 0);
        let mut ret = Vec::with_capacity(1 << self.t_logsize);
        let mut a = self.snapshots[0][0];
        for &v in &self.diff {
            a += v;
            ret.push(a);
        }
        ret
    }
}

// Sumcheckable representing prover state for rounds along X coordinate.
pub struct TwReadPhaseSumcheckableX<F: Field> {
    pub ramdata: RAMData<F>,
    pub rs: Vec<F>, // challenges
    pub num_rounds: usize,
    pub round_idx: usize,
    pub cached_unipoly: Option<Vec<F>>,
    pub claim: F,
    // eq poly in a point rt where we are evaluating Read(rt) initially; after that it gets twisted by
    // the (1-r) and r values that Acc gets multiplied by, so we transfer coefficients that Acc gets multiplied by
    // and it stays one-hot
    // while this breaks MLE along t, this is actually fine as we only want to pass x-rounds
    // separate twists of Acc can then be easily recovered by division by eq[rt], so it is very cheap
}

#[derive(Clone)]
pub struct Prod3;
impl<F: FormalField> AlgFnSO<F> for Prod3 {
    fn exec(&self, args: &impl std::ops::Index<usize, Output = F>) -> F {
        args[0] * args[1] * args[2]
    }

    fn deg(&self) -> usize {
        3
    }

    fn n_ins(&self) -> usize {
        3
    }
}

/// t-phase is generally cheap, but this should be eventually replaced by Gruen version probably
pub type TwReadPhaseSumcheckableT<F> = DenseSumcheckableSO<F, Prod3>;

impl<F: Field> TwReadPhaseSumcheckableX<F> {
    /// Constructs a new sumcheckable for x-rounds of Read phase.
    /// n_snapshots should ideally be equal to amount of threads available for parallelization,
    /// as they are necessary to parallelize rounds after 1-st.
    pub fn new(diff: Vec<F>, acc: Vec<usize>, init_state: Vec<F>, rt: &[F], n_snapshots: usize, cfg: &TwReadPhase, claim: F) -> Self {
        let ramdata = RAMData::new(diff, acc, init_state, rt, n_snapshots, cfg);
        Self {
            num_rounds: ramdata.x_logsize,
            ramdata,
            rs: vec![],
            round_idx: 0,
            cached_unipoly: None,
            claim,
        }
    }

    pub fn finish(self) -> TwReadPhaseSumcheckableT<F> {
        let f = Prod3;

        // // DEBUG
        // self.ramdata.eq_poly_rt.iter().zip_eq(self.ramdata.eq_poly_rt_inv.iter()).for_each(|(&a, &b)| debug_assert!(a * b == F::ONE));
        // // DEBUG

        let num_vars = self.ramdata.t_logsize;
        let claim = self.claim;
        let ram = self.ramdata.t_form();
        let eq_poly_rt = self.ramdata.eq_poly_rt;
        let accmults =
            self.ramdata.multipliers
            .into_par_iter()
            .zip(
                self.ramdata.eq_poly_rt_inv
                .into_par_iter()
            ).map(|(x, y)| x * y).collect::<Vec<_>>();
        
        let polys = vec![ram, accmults, eq_poly_rt];
        TwReadPhaseSumcheckableT::new(polys, f, num_vars, claim)
    }
}

impl<F: Field> Sumcheckable<F> for TwReadPhaseSumcheckableX<F> {
    
    fn bind(&mut self, r: F) {
        assert!(self.round_idx < self.num_rounds, "the protocol has already ended");
        self.rs.push(r);
        self.ramdata.bind(r);
        self.round_idx += 1;
        match self.cached_unipoly.take() {
            None => {panic!("should evaluate unipoly before binding - it has an opportunity to change the state due to in-place evaluation")}
            Some(u) => {self.claim = evaluate_univar(&u, &r)}
        }
    }

    fn response(&mut self) -> Vec<F> {
        assert!(self.round_idx < self.num_rounds, "the protocol has already ended");

        match self.cached_unipoly.as_ref() {
            Some(p) => {return p.clone()},
            None => {
                // Single pass through RAM data. In the first round we also compute all snapshots.
                // In theory, 1st round can also be parallelized, but we don't do it here.
                let t_len = 1 << self.ramdata.t_logsize;
                let chunk_size = (t_len + self.ramdata.n_snapshots - 1)  / self.ramdata.n_snapshots;

                let mut buckets = [[F::ZERO; 2]; 2];                
                if self.round_idx == 0 { // iterate through everything in a single pass
                    let mut state = self.ramdata.snapshots[0].clone(); // initial state
                    for j in 0..self.ramdata.n_snapshots {
                        // each chunk except the first one starts by snapshotting the data *before* diffing it
                        // i.e. final state is never snapshotted
                        // scary off by ones
                        if j != 0 {
                            self.ramdata.snapshots.push(state.clone());
                        }
                        for i in j * chunk_size .. min(t_len, (j + 1) * chunk_size) {
                            // now we diff the state (recall that initial state is not included in ram(x, t), but final is included)
                            let a = self.ramdata.acc[i];
                            let d = self.ramdata.diff[i];
                            state[a] += d;
                            // read happens after diff, so now we observe a valid i-th row of the RAM
                            // we extract 2 neighboring cells at places (a >> 1) << 1, ((a >> 1) << 1) + 1 (MLE of acc outside
                            // of these is 0 so we dont care)
                            // depending on whether we read odd or even cell, a pair of neighbors goes to either one or the other
                            // bucket, while also being twisted by appropriate multiplier
                            
                            let a_fl = (a >> 1) << 1;
                            let bit = a - a_fl;
                            buckets[bit][0] += state[a_fl] * self.ramdata.multipliers[i];
                            buckets[bit][1] += state[a_fl + 1] * self.ramdata.multipliers[i];   
                        }
                    }
                } else { // in this case, we already have all the snapshots, so we parallelize
                    let buckets_parts = (0..self.ramdata.n_snapshots).into_par_iter().map(|j| {
                        let mut buckets_c = [[F::ZERO; 2]; 2];
                        let mut state = self.ramdata.snapshots[j].clone();
                        for i in j * chunk_size .. min(t_len, (j + 1) * chunk_size) {
                            let a = self.ramdata.acc[i];
                            let d = self.ramdata.diff[i];
                            state[a] += d;
                            
                            let a_fl = (a >> 1) << 1;
                            let bit = a - a_fl;
                            buckets_c[bit][0] += state[a_fl] * self.ramdata.multipliers[i];
                            buckets_c[bit][1] += state[a_fl + 1] * self.ramdata.multipliers[i];
                        }
                        buckets_c
                    }).collect::<Vec<_>>();
                    for b in buckets_parts {
                        for i in 0..2 {
                            for j in 0..2 {
                                buckets[i][j] += b[i][j]
                            }
                        }
                    }
                }
                // now, let's recover unipoly
                let a = [buckets[0][0], buckets[0][1], buckets[0][1].double() - buckets[0][0]]; // interpolation of a linear polynomial
                let b = [F::ONE, F::ZERO, - F::ONE]; // interpolation of [1, 0]

                let mut s = a.iter().zip(b.iter()).map(|(&x, &y)| x * y).collect::<Vec<_>>();

                let a = [buckets[1][0], buckets[1][1], buckets[1][1].double() - buckets[1][0]];
                let b = [F::ZERO, F::ONE, F::ONE.double()];

                for i in 0..3 {
                    s[i] += a[i] * b[i]
                }

                debug_assert!(s[0] + s[1] == self.claim);
                let unipoly = from_evals(&s);
                self.cached_unipoly = Some(unipoly);
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
    use crate::common::{algfn::AlgFnSO, claims::SumEvalClaim, koala_passthrough::KoalaBear5 as F, math::evaluate_multivar, random::Random};
    use fiat_shamir::{ProverState, VerifierState};
    use p3_challenger::{DuplexChallenger};
    use p3_field::{PrimeCharacteristicRing};
    use p3_koala_bear::{KoalaBear, Poseidon2KoalaBear, default_koalabear_poseidon2_16};
    use rand::{SeedableRng, TryRngCore, rngs::{OsRng, StdRng}};
    type KoalaChallenger = DuplexChallenger<KoalaBear, Poseidon2KoalaBear<16>, 16, 8>;

    #[test]
    fn twist_read_phase_verifier_accepts_prover() {
        let x_logsize = 6;
        let t_logsize = 10; // relatively small values so we can materialize ram naively and validate everything
        let n_snapshots = 12; // affects parallelization
        
        let rng = &mut OsRng;

        // generate random access pattern
        let acc = (0 .. 1 << t_logsize).map(|_| (rng.try_next_u32().unwrap() % (1 << x_logsize)) as usize).collect::<Vec<_>>();
        // generate random diffs
        let diff = (0 .. 1 << t_logsize).map(|_| F::rand(rng) ).collect::<Vec<_>>();

        let init_state = (0 .. 1 << x_logsize).map(|_| F::rand(rng) ).collect::<Vec<_>>();

        // compute ram and read directly:
        let mut ram = vec![];
        let mut read = vec![];
        let mut state = init_state.clone();
        for i in 0 .. 1 << t_logsize {
            state[acc[i]] += diff[i];
            read.push(state[acc[i]]);
            ram.push(state.clone())
        }
        
        // generate evaluation random point:
        let rt = (0 .. t_logsize).map(|_| F::rand(rng) ).collect::<Vec<_>>();

        // evaluate read in it
        let ev = evaluate_multivar(&read, &rt);

        let acc_ = acc.clone();
        
        let permutation = default_koalabear_poseidon2_16();
        let challenger = KoalaChallenger::new(permutation);
        let mut transcript_p = ProverState::new(challenger.clone());
        let protocol = TwReadPhase{ x_logsize, t_logsize };

        let claims = LinEvalClaim{ ev, point: rt.clone() };
        let advice 
        = TwReadPhaseAdvice {
            diff,
            acc,
            init_state,
            n_snapshots
        };

        protocol.prove(&mut transcript_p, claims.clone(), advice);
        
        let proof = transcript_p.proof_data();
        
        let mut transcript_v = VerifierState::new(proof.to_vec(), challenger.clone());

        let SinglePointClaims { evs, point } = protocol.verify(&mut transcript_v, claims);
        let ram_ev = evs[0];
        let acc_ev = evs[1];
        
        let ram = ram.into_iter().flatten().collect::<Vec<_>>();

        let mut acc = vec![F::ZERO; 1 << (x_logsize + t_logsize)];
        for i in 0 .. (1 << t_logsize) {
            acc[(i << x_logsize) + acc_[i]] = F::ONE;
        }

        assert!(evaluate_multivar(&ram, &point) == ram_ev);
        assert!(evaluate_multivar(&acc, &point) == acc_ev);
    }

    #[test]
    fn bench_read_phase () {
        _bench_read_phase(5, 24, 1);
        _bench_read_phase(5, 24, 16);
        _bench_read_phase(16, 22, 1);
        _bench_read_phase(16, 22, 16);        
    }

    fn _bench_read_phase(x_logsize: usize, t_logsize: usize, n_snapshots: usize) {
        println!("Benchmarking with x_logsize = {x_logsize}, t_logsize = {t_logsize}, n_snapshots = {n_snapshots}");

        let rng = &mut StdRng::from_seed([0; 32]);
        let acc = (0 .. 1 << t_logsize).map(|_| (rng.try_next_u32().unwrap() % (1 << x_logsize)) as usize).collect::<Vec<_>>();
        let diff = (0 .. 1 << t_logsize).map(|_| F::rand(rng) ).collect::<Vec<_>>();
        let init_state = (0 .. 1 << x_logsize).map(|_| F::rand(rng) ).collect::<Vec<_>>();
        let mut read = vec![];
        let mut state = init_state.clone();
        for i in 0 .. 1 << t_logsize {
            state[acc[i]] += diff[i];
            read.push(state[acc[i]]);
        }
        let rt = (0 .. t_logsize).map(|_| F::rand(rng) ).collect::<Vec<_>>();
        let ev = evaluate_multivar (&read, &rt);
        let permutation = default_koalabear_poseidon2_16();
        let challenger = KoalaChallenger::new(permutation);
        let mut transcript_p = ProverState::new(challenger.clone());
        let protocol = TwReadPhase{ x_logsize, t_logsize };
        let claims = LinEvalClaim{ ev, point: rt.clone() };
        let advice 
        = TwReadPhaseAdvice {
            diff,
            acc,
            init_state,
            n_snapshots
        };
        protocol.prove(&mut transcript_p, claims.clone(), advice);
    }
}