use rand::{Rng, TryRngCore};

pub trait Random {
    fn rand<R: TryRngCore>(rng: &mut R) -> Self;
}