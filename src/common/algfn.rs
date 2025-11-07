use std::{marker::PhantomData, ops::Index};

use crate::common::formal_field::Field;

/// An algebraic function of degree d with a single output.
pub trait AlgFnSO<F> : Clone + Send + Sync {
    /// Executes function.
    fn exec(&self, args: &impl Index<usize, Output = F>) -> F;
    /// Declares the degree.
    fn deg(&self) -> usize;
    /// Declares the expected number of inputs.
    fn n_ins(&self) -> usize;
}

/// An algebraic function of degree d with multiple outputs.
pub trait AlgFn<F> : Clone + Send + Sync {
    /// Executes function
    fn exec(&self, args: &impl Index<usize, Output = F>) -> impl Iterator<Item = F>;
    /// Declares the degree.
    fn deg(&self) -> usize;
    /// Declares the expected number of inputs.
    fn n_ins(&self) -> usize;
    /// Declares the expected number of outputs.
    fn n_outs(&self) -> usize;
}

#[derive(Clone)]
pub struct FoldedAlgFn<F: Field, Fun: AlgFn<F>> {
    gammas: Vec<F>,
    f: Fun,
}

impl <F: Field, Fun: AlgFn<F>> FoldedAlgFn<F, Fun> {
    pub fn new(f: Fun, gamma: F) -> Self {
        let mut gammas = vec![];
        let mut val = F::ONE;
        for i in 0 .. f.n_outs() {
            gammas.push(val);
            val *= gamma
        }
        Self { gammas, f }
    }
}

impl<F: Field, Fun: AlgFn<F>> AlgFnSO<F> for FoldedAlgFn<F, Fun> {
    fn exec(&self, args: &impl Index<usize, Output = F>) -> F {
        let mut iter = self.f.exec(args);
        let o = iter.next().unwrap();
        iter.zip(self.gammas[1..].iter()).map(|(a, &b)| a * b).fold(o, |a, b| {a + b})
    }

    fn deg(&self) -> usize {
        self.f.deg()
    }

    fn n_ins(&self) -> usize {
        self.f.n_ins()
    }
}