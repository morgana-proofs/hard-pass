use std::{cmp::min, marker::PhantomData};
use itertools::{Either, Itertools};
use p3_maybe_rayon::prelude::*;
use p3_util::log2_ceil_usize;
use crate::{common::{algfn::AlgFnSO, claims::{LinEvalClaim, SinglePointClaims, SumEvalClaim}, contexts::{ProverFieldCtx, VerifierFieldCtx}, formal_field::{Field, FormalField}, math::{bind_dense_poly, evaluate_univar, from_evals}, pack::{AlgTr, PackedField}, protocol::{ProtocolProver, ProtocolVerifier}}, sumcheck::{generic::{GenericSumcheckProver, GenericSumcheckVerifier}, sumcheckable::Sumcheckable}};

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
    pub fn pp(&self) -> DensePP<F, Fun> {
        DensePP::new(self.f.clone())
    }
}

pub struct DenseSumcheckProver<F: Field, Fun: AlgFnSO<F>, A: PackedField<Scalar = F>> {
    pub cfg: DenseSumcheck<F, Fun>,
    _marker: PhantomData<A>,
}

impl<F: Field, Fun: AlgFnSO<F>, A: PackedField<Scalar = F>> DenseSumcheckProver<F, Fun, A> {
    pub fn new(f: Fun, num_vars: usize) -> Self {
        Self { cfg: DenseSumcheck::new(f, num_vars), _marker: PhantomData }
    }

    pub fn pp(&self) -> DensePP<F, Fun> {
        DensePP::new(self.cfg.f.clone())
    }
}

impl<F: FormalField, Fun: AlgFnSO<F>, Ctx: VerifierFieldCtx<F=F>> ProtocolVerifier<Ctx> for DenseSumcheck<F, Fun> {
    type ClaimsBefore = SumEvalClaim<F>;
    type ClaimsAfter = SinglePointClaims<F>;

    fn verify(&self, ctx: &mut Ctx, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let generic_protocol_config = GenericSumcheckVerifier::<F>::new(self.f.deg(), self.num_vars);
        let claims = generic_protocol_config.verify(ctx, claims);
        self.pp().verify(ctx, claims)
    }
}

impl<
    F: Field,
    Fun: AlgFnSO<F>,
    A: PackedField<Scalar=F>,
    Ctx: ProverFieldCtx<F=F>
> ProtocolProver<Ctx> for DenseSumcheckProver<F, Fun, A> {
    type ProverInput = Vec<PackedPoly<F, A>>;
    type ProverOutput = ();
    type ClaimsBefore = SumEvalClaim<F>;
    type ClaimsAfter = SinglePointClaims<F>;

    fn prove(&self, ctx: &mut Ctx, claims: Self::ClaimsBefore, advice: Self::ProverInput) -> (Self::ClaimsAfter, Self::ProverOutput) {
        let generic_protocol_config = GenericSumcheckProver::new_partial(self.cfg.f.deg(), self.cfg.num_vars, self.cfg.num_rounds);

        let so = DenseSumcheckableSO::new(advice, self.cfg.f.clone(),  self.cfg.num_vars, claims.value.clone());

        let (claims, s) = generic_protocol_config.prove(ctx, claims, so);
        let poly_evs = s.final_evals();

        self.pp().prove(ctx, claims, poly_evs)
    }
}

pub const MIN_VARS_FOR_PACKING: usize = 8;

#[derive(Clone, Debug)]
pub enum PackedPoly<F: Field, A: PackedField<Scalar = F>> {
    Packed(Vec<A>),
    Unpacked(Vec<F>),
}
impl<F: Field, A: PackedField<Scalar = F>> PackedPoly<F, A> {
    
    pub fn from_packed(v: Vec<A>) -> Self {
        assert!(v.len() == 1 << log2_ceil_usize(v.len()));
        if v.len() < (1 << MIN_VARS_FOR_PACKING) {
            Self::Unpacked(A::unpack(v))
        } else {
            Self::Packed(v)
        }
    }

    pub fn from_unpacked(v: Vec<F>) -> Self {
        assert!(v.len() == 1 << log2_ceil_usize(v.len()));
        if v.len() < (1 << MIN_VARS_FOR_PACKING) {
            Self::Unpacked(v)
        } else {
            Self::Packed(A::pack(v))
        }
    }

    pub fn unwrap_unpacked(self) -> Vec<F> {
        if let Self::Unpacked(v) = self {v} else {panic!()}
    }

    pub fn unwrap_packed(self) -> Vec<A> {
        if let Self::Packed(v) = self {v} else {panic!()}
    }

    pub fn to_unpacked(self) -> Vec<F> {
        match self {
            PackedPoly::Packed(v) => A::unpack(v),
            PackedPoly::Unpacked(v) => v,
        }
    }

    pub fn len(&self) -> usize {
        match self {
            Self::Packed(v) => v.len(),
            Self::Unpacked(v) => v.len(),
        }
    }

    pub fn num_vars(&self) -> usize {
        log2_ceil_usize(self.len())
    }

}


#[derive(Clone, Debug)]
pub enum DenseSumcheckableSO<F: Field, Fun: AlgFnSO<F>, A: PackedField<Scalar = F>> {
    Packed(DenseSumcheckableSOInternal<F, Fun, A>),
    Unpacked(DenseSumcheckableSOInternal<F, Fun, F>),
    None, // for convenient mem::replace
}

impl<F: Field, Fun: AlgFnSO<F>, A: PackedField<Scalar = F>> DenseSumcheckableSO<F, Fun, A> {
    pub fn new(polys: Vec<PackedPoly<F, A>>, f: Fun, num_vars: usize, claim_hint: F) -> Self {
        if match &polys[0] {
            PackedPoly::Packed(_) => true,
            PackedPoly::Unpacked(_) => false,
        } {
            Self::new_packed(polys.into_iter().map(|poly| poly.unwrap_packed()).collect(), f, num_vars, claim_hint)
        } else {
            Self::new_unpacked(polys.into_iter().map(|poly| poly.unwrap_unpacked()).collect(), f, num_vars, claim_hint)
        }
    }
    
    pub fn new_packed(polys: Vec<Vec<A>>, f: Fun, num_vars: usize, claim_hint: F) -> Self {
        assert!(num_vars >= MIN_VARS_FOR_PACKING);
        Self::Packed(DenseSumcheckableSOInternal::new(polys, f, num_vars, claim_hint))
    }

    pub fn new_unpacked(polys: Vec<Vec<F>>, f: Fun, num_vars: usize, claim_hint: F) -> Self {
        assert!(num_vars < MIN_VARS_FOR_PACKING);
        Self::Unpacked(DenseSumcheckableSOInternal::new(polys, f, num_vars, claim_hint))
    }

    pub fn remaining_vars(&self) -> usize {
        match self {
            DenseSumcheckableSO::Packed(s) => s.num_vars - s.round_idx,
            DenseSumcheckableSO::Unpacked(s) => s.num_vars - s.round_idx,
            DenseSumcheckableSO::None => panic!(),
        }
    }

    pub fn final_evals(&self) -> Vec<F> {
        match self {
            Self::Unpacked(s) => {
                assert!(s.round_idx == s.num_vars, "can only call final evals after the last round");
                s.polys.iter().map(|poly| poly[0]).collect()
            },
            _ => panic!(),
        }
    }
}

impl<F: Field, Fun: AlgFnSO<F>, A: PackedField<Scalar = F>> Sumcheckable<F> for DenseSumcheckableSO<F, Fun, A> {
    fn bind(&mut self, r: F) {
        
        match self {
            Self::Packed(s) => s.bind(r),
            Self::Unpacked(s) => s.bind(r),
            _ => panic!(),
        }
        
        if self.remaining_vars() == MIN_VARS_FOR_PACKING {
            // Go from packed to unpacked form.
            let dummy = Self::None;
            let s = std::mem::replace(self, dummy);
            let Self::Packed(s) = s else {panic!()};
            let DenseSumcheckableSOInternal{ polys, rs, f, num_vars, round_idx, cached_response, claim } = s;
            let polys = polys.into_iter().map(|poly| A::unpack(poly)).collect_vec();
            let s = DenseSumcheckableSOInternal{ polys, rs, f, num_vars, round_idx, cached_response, claim };
            *self = DenseSumcheckableSO::Unpacked(s);
        }
    }

    fn response(&mut self) -> Vec<F> {
        match self {
            Self::Packed(s) => s.response(),
            Self::Unpacked(s) => s.response(),
            _ => panic!(),
        }
    }

    fn challenges(&self) -> &[F] {
        match self {
            Self::Packed(s) => s.challenges(),
            Self::Unpacked(s) => s.challenges(),
            _ => panic!(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct DenseSumcheckableSOInternal<F: Field, Fun: AlgFnSO<F>, A: AlgTr<F>> {
    pub polys: Vec<Vec<A>>,
    rs: Vec<F>,
    f: Fun,
    num_vars: usize,
    round_idx: usize,
    cached_response: Option<Vec<F>>,
    pub claim: F,
}

impl<F: Field, Fun: AlgFnSO<F>, A: AlgTr<F>> DenseSumcheckableSOInternal<F, Fun, A> {
    pub fn new(polys: Vec<Vec<A>>, f: Fun, num_vars: usize, claim_hint: F) -> Self {
        
        let l = polys.len();
        assert_eq!(l, f.n_ins());
        for i in 0..l {
            assert_eq!(polys[i].len() * A::WIDTH, 1 << num_vars);
        }
        Self { polys, f, num_vars, round_idx: 0, cached_response: None, rs: vec![], claim: claim_hint }
    }
}

impl<F: Field, Fun: AlgFnSO<F>, A: AlgTr<F>> Sumcheckable<F> for DenseSumcheckableSOInternal<F, Fun, A> {
    fn bind(&mut self, r: F) {
        assert!(self.round_idx < self.num_vars, "the protocol has already ended");
        self.rs.push(r);
        for poly in &mut self.polys {
            bind_dense_poly(poly, r);
        }
        self.round_idx += 1;
        match self.cached_response.take() {
            None => {panic!("should evaluate unipoly before binding - it has an opportunity to change the state due to in-place evaluation")}
            Some(u) => {self.claim = evaluate_univar(&u, &r)}
        }
    }

    fn response(&mut self) -> Vec<F>{
        assert!(self.round_idx < self.num_vars, "the protocol has already ended");

        println!("Current round: {}", self.round_idx);

        match self.cached_response.as_ref() {
            Some(p) => {return p.clone()},
            None => {
                let half = 1 << (self.num_vars - self.round_idx - log2_ceil_usize(A::WIDTH) - 1);
                println!("half: {}", half);
                println!("polys[0]: {}", self.polys[0].len());
                let n_polys = self.polys.len();

                let num_tasks = 8 * current_num_threads();

                let task_size = (half + num_tasks - 1) / num_tasks;

                let acc: Vec<Vec<A>> = (0..num_tasks).into_par_iter().map(|task_idx| {
                    let mut difs = vec![A::ZERO; n_polys];
                    let mut args = vec![A::ZERO; n_polys];
                    let mut acc = vec![A::ZERO; self.f.deg()];

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
                        total_acc[j + 1] = total_acc[j + 1] + acc[i][j].tr()
                    }
                }

                total_acc[0] = self.claim - total_acc[1];

                //---- debugging
                debug_assert!( total_acc[0] == {
                    let mut acc0 = F::ZERO;
                    let mut args = vec![A::ZERO; n_polys];
                    for i in 0..half {
                        for j in 0..n_polys {
                            args[j] = self.polys[j][2 * i];
                        }
                        acc0 += self.f.exec(&args).tr();
                    }
                    acc0
                });
                //------------------------------

                self.cached_response = Some(from_evals(&total_acc));
            }
        }
        self.cached_response.as_ref().unwrap().clone()

    }

    fn challenges(&self) -> &[F] {
        &self.rs
    }
}

pub struct DensePP<F: FormalField, Fun: AlgFnSO<F>> {
    pub f: Fun,
    _marker: PhantomData<F>
}

impl<F: FormalField, Fun: AlgFnSO<F>> DensePP<F, Fun> {
    pub fn new(f: Fun) -> Self {
        Self {f, _marker: PhantomData}
    }
}

impl<Ctx: VerifierFieldCtx, Fun: AlgFnSO<Ctx::F>> ProtocolVerifier<Ctx> for DensePP<Ctx::F, Fun> {
    type ClaimsBefore = SumEvalClaim<Ctx::F>;
    type ClaimsAfter = SinglePointClaims<Ctx::F>;

    fn verify(&self, ctx: &mut Ctx, claims: Self::ClaimsBefore) -> Self::ClaimsAfter {
        let SumEvalClaim {value: ev, point} = claims;
        let poly_evs = ctx.read_multi(self.f.n_ins());
        (self.f.exec(&poly_evs) - ev).require();
        SinglePointClaims{ evs: poly_evs, point }
    }
}

impl<Ctx: ProverFieldCtx, Fun: AlgFnSO<Ctx::F>> ProtocolProver<Ctx> for DensePP<Ctx::F, Fun> {
    type ClaimsBefore = SumEvalClaim<Ctx::F>;
    type ClaimsAfter = SinglePointClaims<Ctx::F>;
    type ProverInput = Vec<Ctx::F>; // poly evs
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
        let SumEvalClaim {value: ev, point} = claims;
        ctx.write_multi(self.f.n_ins(), &advice);
        debug_assert!({(self.f.exec(&advice) - ev).require(); true});
        (SinglePointClaims{ evs: advice, point }, ())
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use std::ops::Index;
    use crate::common::{algfn::AlgFnSO, claims::SumEvalClaim, koala_passthrough::KoalaBear5 as F, math::{eq_poly, evaluate_multivar, lte_ev}, pack::PackedField, random::Random};
    use fiat_shamir::{ProverState, VerifierState};
    use itertools::Itertools;
    use p3_challenger::{DuplexChallenger};
    use p3_field::{Algebra, PrimeCharacteristicRing};
    use p3_koala_bear::{KoalaBear, PackedQuinticExtensionFieldKB, Poseidon2KoalaBear, default_koalabear_poseidon2_16};
    use rand::{SeedableRng, distr::{Distribution, StandardUniform, Uniform}, rngs::{OsRng, StdRng}};
   
    type KoalaChallenger = DuplexChallenger<KoalaBear, Poseidon2KoalaBear<16>, 16, 8>;

    #[derive(Clone, Copy)]
    pub struct TestFunction {}

    impl AlgFnSO<F> for TestFunction {
        fn exec<A: Algebra<F> + Copy>(&self, args: &impl Index<usize, Output = A>) -> A {
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
        let rng = &mut StdRng::from_seed([0; 32]);
        let logsize = 15;
        let u = StandardUniform;
        let polys : Vec<Vec<F>> = (0..2).map(|_| (0 .. 1 << logsize).map(|_|u.sample(rng)).collect()).collect();

        let f = TestFunction{};

        let mut output = vec![];

        for i in 0 .. 1 << logsize {
            let args : Vec<F> = polys.iter().map(|poly| poly[i]).collect();
            output.push(f.exec(&args));
        }

        let polys
        = polys
        .into_iter()
        .map(|poly| {
            PackedPoly::<F, PackedQuinticExtensionFieldKB>::from_unpacked(poly)
        }).collect_vec();
        let output = PackedQuinticExtensionFieldKB::pack(output);
        
        let permutation = default_koalabear_poseidon2_16();
        let challenger = KoalaChallenger::new(permutation);

        let mut transcript_p = ProverState::new(challenger.clone());

        let claim = SumEvalClaim{value:output.into_iter().sum::<PackedQuinticExtensionFieldKB>().tr(), point: vec![]};
        let sumcheck = DenseSumcheckProver::new(f, logsize);
        let (output_claims, _) = sumcheck.prove(&mut transcript_p, claim.clone(), polys.clone());
        let proof = transcript_p.proof_data();
        
        let mut transcript_v = VerifierState::new(proof.to_vec(), challenger.clone());
        
        let sumcheck = DenseSumcheck::new(f, logsize);
        let expected_output_claims = sumcheck.verify(&mut transcript_v, claim.clone());
        assert_eq!(output_claims, expected_output_claims);

        let SinglePointClaims { point : mut new_point, evs } = output_claims;
        
        let polys = polys.into_iter().map(|poly| poly.to_unpacked()).collect_vec();

        assert_eq!(polys.iter().map(|poly| 
            evaluate_multivar(&poly, &new_point)
        ).collect::<Vec<_>>(), evs);

    }
}