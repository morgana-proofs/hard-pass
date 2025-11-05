/// Represents prover view of multivariate polynomial that is being sumchecked.
pub trait Sumcheckable<F> {
    /// Binds the polynomial on the coordinate t. Might be fallible unless unipoly() method was called.
    fn bind(&mut self, t: F);
    /// Returns the sumcheck response.
    fn response(&mut self) -> Vec<F>;
    /// Returns the evaluations of multilinear polynomials in a final challenge point.
    /// Opaque because some evals can be skipped if recoverable by verifier itself.
    fn final_evals(&self) -> Vec<F>;
    /// Convenience method, returns challenge point (in a correct order).
    fn challenges(&self) -> &[F];
}

pub trait FoldToSumcheckable<F> {
    type Target : Sumcheckable<F>;

    fn rlc(self, gamma: F) -> Self::Target;
}