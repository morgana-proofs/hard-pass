use fiat_shamir::{ProverState, VerifierState};
use crate::common::{contexts::{ChallengerCtx, ProverFieldCtx, VerifierFieldCtx}, formal_field::{ExtensionField, Field}};

// passthrough of types from leanvm (they almost satisfy our traits without any changes! :) )

impl<BF, EF, Challenger> ChallengerCtx for VerifierState<BF, EF, Challenger>
where
    EF: ExtensionField<BF>,
    BF: Field,
    Challenger: p3_challenger::FieldChallenger<BF> + p3_challenger::GrindingChallenger<Witness = BF>

{
    type F = EF;

    fn challenge(&mut self) -> Self::F {
        self.sample()
    }

    fn challenge_multi(&mut self, size: usize) -> Vec<Self::F> {
        self.sample_vec(size)
    }
}

impl<BF, EF, Challenger> VerifierFieldCtx for VerifierState<BF, EF, Challenger>
where
    EF: ExtensionField<BF>,
    BF: Field,
    Challenger: p3_challenger::FieldChallenger<BF> + p3_challenger::GrindingChallenger<Witness = BF>
{
    fn read(&mut self) -> Self::F {
        self.next_extension_scalars_const::<1>().unwrap()[0]
    }

    fn read_multi(&mut self, size: usize) -> Vec<Self::F> {
        self.next_extension_scalars_vec(size).unwrap()
    }

    fn unconstrained_read(&mut self) -> Self::F {
        self.receive_hint_extension_scalars(1).unwrap()[0]
    }

    fn unconstrained_read_multi(&mut self, size: usize) -> Vec<Self::F> {
        self.receive_hint_extension_scalars(size).unwrap()
    }
}

impl<BF, EF, Challenger> ChallengerCtx for ProverState<BF, EF, Challenger>
where
    EF: ExtensionField<BF>,
    BF: Field,
    Challenger: p3_challenger::FieldChallenger<BF> + p3_challenger::GrindingChallenger<Witness = BF>

{
    type F = EF;

    fn challenge(&mut self) -> Self::F {
        self.sample()
    }

    fn challenge_multi(&mut self, size: usize) -> Vec<Self::F> {
        self.sample_vec(size)
    }
}

impl<BF, EF, Challenger> ProverFieldCtx for ProverState<BF, EF, Challenger>
where
    EF: ExtensionField<BF>,
    BF: Field,
    Challenger: p3_challenger::FieldChallenger<BF> + p3_challenger::GrindingChallenger<Witness = BF>
{
    fn write(&mut self, value: Self::F) -> () {
        self.add_extension_scalar(value);
    }

    fn write_multi(&mut self, size: usize, values: &[Self::F]) -> () {
        assert!(values.len() == size);
        self.add_extension_scalars(values);
    }

    fn unconstrained_write(&mut self, value: Self::F) -> () {
        self.add_extension_scalars(&[value]);
    }

    fn unconstrained_write_multi(&mut self, size: usize, values: &[Self::F]) -> () {
        assert!(values.len() == size);
        self.hint_extension_scalars(values);
    }
}