// Bootleg version of packing trait that we gonna use.
// Does not assume any direct casts.
// Think it is fine for our application (and might be even better in some cases).

use std::ops::{Div, DivAssign};
use p3_field::{Algebra, PackedFieldExtension};
use p3_koala_bear::{KoalaBear, PackedQuinticExtensionFieldKB};
use crate::common::{formal_field::Field, koala_passthrough::KoalaBear5};

pub trait AlgTr<F>: Algebra<F> + Copy + Send + Sync {
    fn tr(&self) -> F;
}

impl<F: Field> AlgTr<F> for F {
    fn tr(&self) -> F {
        *self
    }
}

pub trait PackedField: AlgTr<Self::Scalar>
{
    type Scalar: Field;
    const WIDTH: usize;

    /// panics if vals.len() is not divisible by Self::WIDTH
    fn pack(vals: Vec<Self::Scalar>) -> Vec<Self>;
    fn unpack(vals: Vec<Self>) -> Vec<Self::Scalar>;
}

impl AlgTr<KoalaBear5> for PackedQuinticExtensionFieldKB {
    fn tr(&self) -> KoalaBear5 {
        Self::unpack(std::vec![*self]).into_iter().sum()
    }
}

impl PackedField for PackedQuinticExtensionFieldKB {
    type Scalar = KoalaBear5;

    const WIDTH: usize = <<KoalaBear as p3_field::Field>::Packing as p3_field::PackedValue>::WIDTH;

    fn pack(vals: Vec<Self::Scalar>) -> Vec<Self> {
        assert!(vals.len() % Self::WIDTH == 0);
        vals.chunks(Self::WIDTH).map(|x| Self::from_ext_slice(x)).collect()
    }

    fn unpack(vals: Vec<Self>) -> Vec<Self::Scalar> {
        Self::to_ext_iter_vec(vals)
    }
}