/// Represents prover view of multivariate polynomial that is being sumchecked.
pub trait Sumcheckable<F> {
    /// Binds the polynomial on the coordinate t. Might be fallible unless response() method was called.
    fn bind(&mut self, r: F);
    /// Returns the sumcheck response.
    fn response(&mut self) -> Vec<F>;
    /// Convenience method, returns challenge point (in a correct order).
    fn challenges(&self) -> &[F];
}

pub trait FoldToSumcheckable<F> {
    type Target : Sumcheckable<F>;

    fn rlc(self, gamma: F) -> Self::Target;
}