#[derive(Clone, Eq, PartialEq, Debug)]
pub struct UnivarEvalClaim<F> {
    pub ev: F,
    pub point: F,
}


/// Evaluation claim for a multilinear polynomial.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct LinEvalClaim<F> {
    pub ev: F,
    pub point: Vec<F>,
}

/// Summation claim for a multivariate polynomial, with initial few coordinates substituted to point.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct SumEvalClaim<F> {
    pub value: F,
    pub point: Vec<F>,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct SinglePointClaims<F> {
    pub evs: Vec<F>,
    pub point: Vec<F>,
}

