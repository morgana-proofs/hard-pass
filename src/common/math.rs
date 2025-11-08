use std::iter::once;
use multilinear_toolkit::prelude::{EvaluationsList, MultilinearPoint};
use p3_field::Algebra;
use p3_maybe_rayon::prelude::*;
use crate::common::{formal_field::{Field, FormalField}, pack::{AlgTr, PackedField}};
use itertools::Itertools;

pub fn evaluate_univar<F: FormalField>(poly: &[F], x: &F) -> F {
    let l = poly.len();
    assert!(l > 0);
    let mut run = poly[l - 1].clone();
    for i in 0 .. l - 1 {
        run = run.clone() * *x;
        run = run.clone() + poly[l - i - 2];
    }
    run
}

/// Returns p(0) + p(1) and all coefficients but the 1st one.
pub fn compress<F: FormalField>(coeffs: &[F]) -> (F, Vec<F>) {
    let sum = coeffs.iter().fold(coeffs[0], |acc, &upd| acc + upd); // add with coefficients 2, 1, 1, 1, 1 ...
    let coeffs_without_1st : Vec<F> = once(&coeffs[0]).chain(coeffs[2..].iter()).map(|x| x.clone()).collect();
    (sum, coeffs_without_1st)
}

/// Reverts compression
pub fn decompress<F: FormalField>(sum: &F, coeffs_without_1st: &[F]) -> Vec<F> {
    let first_coeff = coeffs_without_1st.iter().fold(*sum - coeffs_without_1st[0], |acc, &upd| acc - upd); // sum - 2 * coeff[0] - coeff[1] - coeff[2] ...
    once(&coeffs_without_1st[0]).chain(once(&first_coeff)).chain(coeffs_without_1st[1..].iter()).map(|x| x.clone()).collect()
}

pub fn bind_dense_poly<F: Field, A: AlgTr<F>>(poly: &mut Vec<A>, r: F) {
    let half = poly.len() / 2;
    *poly = (0..half).into_par_iter().map(|i| poly[2*i] + (poly[2*i + 1] - poly[2*i]) * r).collect();
}

// pub fn bind_dense_poly_nonpar<F: Field>(poly: &mut Vec<F>, t: F) {
//     let half = poly.len() / 2;
//     *poly = (0..half).into_iter().map(|i| poly[2*i] + t * (poly[2*i + 1] - poly[2*i])).collect();
// }

pub fn from_evals<F: Field>(evals: &[F]) -> Vec<F> {
    vandermonde_interpolation(evals)
}

pub fn vandermonde_interpolation<F: Field>(evals: &[F]) -> Vec<F> {
    let n = evals.len();
    let xs: Vec<F> = (0..n).map(|x| F::from_u64(x as u64)).collect();

    let mut vandermonde: Vec<Vec<F>> = Vec::with_capacity(n);
    for i in 0..n {
        let mut row = Vec::with_capacity(n);
        let x = xs[i];
        row.push(F::ONE);
        row.push(x);
        for j in 2..n {
        row.push(row[j - 1] * x);
        }
        row.push(evals[i]);
        vandermonde.push(row);
    }

    gaussian_elimination(&mut vandermonde)
}


pub fn gaussian_elimination<F: Field>(matrix: &mut [Vec<F>]) -> Vec<F> {
let size = matrix.len();
assert_eq!(size, matrix[0].len() - 1);

for i in 0..size - 1 {
    for j in i..size - 1 {
    echelon(matrix, i, j);
    }
}

for i in (1..size).rev() {
    eliminate(matrix, i);
}

// Disable cargo clippy warnings about needless range loops.
// Checking the diagonal like this is simpler than any alternative.
#[allow(clippy::needless_range_loop)]
for i in 0..size {
    if matrix[i][i] == F::ZERO {
    println!("Infinitely many solutions");
    }
}

let mut result: Vec<F> = vec![F::ZERO; size];
for i in 0..size {
    result[i] = matrix[i][size] * matrix[i][i].inverse();
}
result
}

fn echelon<F: Field>(matrix: &mut [Vec<F>], i: usize, j: usize) {
    let size = matrix.len();
    if matrix[i][i] == F::ZERO {
    } else {
        let factor = matrix[j + 1][i] * matrix[i][i].inverse();
        (i..size + 1).for_each(|k| {
            let tmp = matrix[i][k];
            matrix[j + 1][k] = matrix[j + 1][k] - factor * tmp;
        });
    }
  }
  
fn eliminate<F: Field>(matrix: &mut [Vec<F>], i: usize) {
    let size = matrix.len();
    if matrix[i][i] == F::ZERO {
    } else {
        for j in (1..i + 1).rev() {
        let factor = matrix[j - 1][i] * matrix[i][i].inverse();
        for k in (0..size + 1).rev() {
            let tmp = matrix[i][k];
            matrix[j - 1][k] = matrix[j - 1][k] - factor * tmp;
        }
        }
    }
}

pub fn eq_ev<F: FormalField>(x: &[F], y: &[F]) -> F {
    x.iter().zip_eq(y.iter()).map(|(&x, &y)| F::ONE - x - y + (x * y).double()).product()
}

/// returns (lte(x, y), eq(x,y))
pub fn lte_ev<F: FormalField>(x: &[F], y: &[F]) -> (F, F) {
    let l = x.len();
    assert!(y.len() == l);
    let mut partial_eqs = vec![F::ONE];
    for i in (0 .. l).rev() {
        let s = partial_eqs.last().unwrap();
        partial_eqs.push(*s * (F::ONE - x[i] - y[i] + x[i] * y[i].double()));
    }
    // we get eq_ev(x[l-i-1..], y[l-i-1..])
    for i in 0..l+1 {
        debug_assert!(partial_eqs[i] == eq_ev(&x[l-i ..], &y[l-i .. ]));
    }

    let lt: F = (0..l).map(|i| {
        (F::ONE - x[l - i - 1]) * y[l - i - 1] * partial_eqs[i] // l-i-1-st bit for x is 0, for y is 1, and all higher bits are equal  
    }).sum();

    (lt + partial_eqs[l], partial_eqs[l])
}

// // EQ poly evals
// struct EQPolyEvaluator<F: Field> {
//     padding_size: usize,
//     multiplier: F,
// }

// impl<F: Field> EQPolyEvaluator<F> {
//     fn new() -> Self {
//         Self {
//             padding_size: 0,
//             multiplier: F::ONE,
//         }
//     }

//     fn from_multiplier(multiplier: F) -> Self {
//         Self {
//             padding_size: 0,
//             multiplier,
//         }
//     }

//     fn from_padding(padding_size: usize) -> Self {
//         Self {
//             padding_size,
//             multiplier: F::ONE,
//         }
//     }

//     fn with_multiplier(mut self, poly: &F) -> Self {
//         self.multiplier = *poly;
//         self
//     }

//     fn with_padding(mut self, padding_size: usize) -> Self {
//         self.padding_size = padding_size;
//         self
//     }
//     fn seq(self, pt: &[F]) -> Vec<Vec<F>> {
//         let Self{  padding_size, multiplier } = self;
//         let l = pt.len();
//         let mut ret = Vec::with_capacity(l + 1);
//         ret.push(vec![multiplier]);
//         for i in 1..=padding_size {
//             ret.push(vec![ret[i - 1][0] * (F::ONE - pt[i - 1])]);
//         }

//         for i in (padding_size + 1)..=l {
//             let last = &ret[i - 1];
//             let multiplier = &pt[i - 1];

//             let mut incoming = vec![F::ZERO; 1 << (i - padding_size)];
//             for j in (0..1 << (i - 1 - padding_size)) {
//                 let w = last[j];
//                 let m = *multiplier * w;
//                 incoming[2 * j] = w - m;
//                 incoming[2 * j + 1] = m;
//             }
//             ret.push(incoming);

//             // let mut incoming = UninitArr::<F>::new(1 << (i - padding_size));
//             // unsafe {
//             //     let ptr = incoming.as_shared_mut_ptr();
//             //     #[cfg(not(feature = "parallel"))]
//             //     let iter = (0 .. (1 << (i - 1 - padding_size))).into_iter();
//             //
//             //     #[cfg(feature = "parallel")]
//             //     let iter = (0 .. (1 << (i - 1 - padding_size))).into_par_iter();
//             //
//             //     iter.map(|j|{
//             //         let w = &last[j];
//             //         let m = *multiplier * w;
//             //         *ptr.get_mut(2 * j) = *w - m;
//             //         *ptr.get_mut(2 * j + 1) = m;
//             //     }).count();
//             //     ret.push(incoming.assume_init());
//             // }
//         }

//         ret
//     }

//     fn last(self, pt: &[F]) -> Option<Vec<F>> {
//         self.seq(pt).pop()
//     }
// }
// pub fn padded_eq_poly_sequence<F: Field>(padding_size: usize, pt: &[F]) -> Vec<Vec<F>> {
//     EQPolyEvaluator::from_padding(padding_size).seq(pt)
// }

// pub fn eq_poly_sequence<F: Field>(pt: &[F]) -> Vec<Vec<F>> {
//     EQPolyEvaluator::new().seq(pt)
// }

// fn eq_poly_sequence_last<F: Field>(pt: &[F]) -> Option<Vec<F>> {
//     EQPolyEvaluator::new().last(pt)
// }

// pub fn eq_poly_sequence_from_multiplier_last<F: Field>(mul: F, pt: &[F]) -> Option<Vec<F>> {
//     EQPolyEvaluator::from_multiplier(mul).last(pt)
// }

// pub fn eq_poly_old<F: Field>(pt: &[F]) -> Vec<F> {
//     let mut pt = pt.to_vec();
//     pt.reverse();
//     eq_poly_sequence_last(&pt).unwrap()
// }

// // TODO: FIX THIS MESS

pub fn eq_poly_scaled<F: Field>(mul: F, pt: &[F]) -> Vec<F> {
    let mut pt = pt.to_vec();
    pt.reverse();
    multilinear_toolkit::prelude::eval_eq_scaled(&pt, mul)
}

pub fn eq_poly<F: Field>(pt: &[F]) -> Vec<F> {
    eq_poly_scaled(F::ONE, pt)
}

/// returns evaluations of (lte, eq)
/// note: this outputs lte(*, pt)
pub fn lte_poly<F: Field>(pt: &[F]) -> (Vec<F>, Vec<F>) {
    let eq = eq_poly(pt);
    let mut lte = vec![F::ZERO; eq.len()];
    let mut s = F::ZERO;
    // this can in theory be parallelized but considering these are only additions it is probably fine
    for i in (0..eq.len()).rev() {
        s += eq[i];
        lte[i] = s;
    }
    (lte, eq)
}

pub fn evaluate_multivar<F: Field>(poly: &[F], pt: &[F]) -> F {
    let mut pt = pt.to_vec();
    pt.reverse();
    poly.evaluate(&MultilinearPoint(pt))
}
