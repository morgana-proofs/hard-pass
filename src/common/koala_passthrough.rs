use p3_field::BasedVectorSpace;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use p3_field::PrimeCharacteristicRing;

use crate::common::{formal_field::{ExtensionField, Field}, random::Random};

pub type KoalaBear5 = QuinticExtensionFieldKB;

impl Field for KoalaBear {}
impl Field for KoalaBear5 {}
impl ExtensionField<KoalaBear> for KoalaBear5 {}

impl Random for KoalaBear {
    fn rand<R: rand::TryRngCore>(rng: &mut R) -> Self {
        let mut a = Self::ZERO;
        for i in 0..5 {
            a += Self::new(rng.try_next_u32().unwrap());
        }
        a
    }
}

impl Random for KoalaBear5 {
    fn rand<R: rand::TryRngCore>(rng: &mut R) -> Self {
        KoalaBear5::from_basis_coefficients_iter((0..5).map(|_|KoalaBear::rand(rng))).unwrap()
    }
}
