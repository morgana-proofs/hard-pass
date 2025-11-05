use std::ops::{Div, DivAssign};
use p3_field::Algebra;

pub trait FormalField: Algebra<Self::Constant> + Div<Output = Self> + DivAssign + Copy {
    type Constant: Field;

    /// Requires that the element is 0. In native execution, this is just an assertion.
    /// For verifier builders, it will apply a constraint.
    fn require(&self) -> ();
    /// Constructs a new constant value.
    fn constant(c: Self::Constant) -> Self;
}

/// Marker trait implemented on p3 fields that we actually intend to use, automatically implies FormalField.
/// Also implements some utility functions
pub trait Field: p3_field::Field {}
pub trait ExtensionField<F: Field>: p3_field::ExtensionField<F> + Field {}

impl<F: Field> FormalField for F {
    type Constant = Self;

    fn require(&self) -> () {
        assert!(*self == Self::ZERO)
    }

    fn constant(c: Self::Constant) -> Self {
        c
    }
}