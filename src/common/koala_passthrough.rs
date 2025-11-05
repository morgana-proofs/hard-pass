use p3_field::{BasedVectorSpace, extension::BinomialExtensionField};
use p3_koala_bear::KoalaBear;
use p3_field::PrimeCharacteristicRing;

use crate::common::{formal_field::{ExtensionField, Field}, random::Random};

pub type KoalaBear4 = BinomialExtensionField<KoalaBear, 4>;

impl Field for KoalaBear {}
impl Field for KoalaBear4 {}
impl ExtensionField<KoalaBear> for KoalaBear4 {}

impl Random for KoalaBear {
    fn rand<R: rand::TryRngCore>(rng: &mut R) -> Self {
        let mut a = Self::ZERO;
        for i in 0..5 {
            a += Self::new(rng.try_next_u32().unwrap());
        }
        a
    }
}

impl Random for KoalaBear4 {
    fn rand<R: rand::TryRngCore>(rng: &mut R) -> Self {
        KoalaBear4::from_basis_coefficients_iter((0..4).map(|_|KoalaBear::rand(rng))).unwrap()
    }
}