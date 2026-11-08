// Adapted from leanVM (https://github.com/leanEthereum/leanVM), commit 42422001, file crates/verifier/src/multilinear.rs:
// the same functions on a generic `Scalar`, without the table-driven `Scaler` (a speed-up of the native code, not a
// different computation). MIT OR Apache-2.0; see NOTICE.md.
//! Multilinear helpers.

use crate::scalar::Scalar;
use crate::{VerifierError, require};

/// `eq(i, point)` for every index `i`, LSB-first, at one product per entry: `v * (1 + r) = v + v * r`.
pub fn eq_kernel<S: Scalar>(point: &[S]) -> Vec<S> {
    let mut out = vec![S::zero(); 1 << point.len()];
    out[0] = S::one();
    for (k, &r) in point.iter().enumerate() {
        let (low, high) = out[..2 << k].split_at_mut(1 << k);
        for (v, h) in low.iter_mut().zip(high) {
            *h = *v * r;
            *v += *h;
        }
    }
    out
}

pub fn multilinear_eval<S: Scalar>(mle: &[S], point: &[S]) -> Result<S, VerifierError> {
    require(
        point.len() < 64 && mle.len() == 1 << point.len(),
        VerifierError::MultilinearSize,
    )?;
    let mut cur: Vec<S> = mle.to_vec();
    for &r in point {
        for i in 0..cur.len() / 2 {
            cur[i] = cur[2 * i] + r * (cur[2 * i] + cur[2 * i + 1]);
        }
        cur.truncate(cur.len() / 2);
    }
    Ok(cur[0])
}

pub fn log2_ceil(value: u64) -> usize {
    (64 - value.saturating_sub(1).leading_zeros()) as usize
}

pub fn eq_eval<S: Scalar>(left: &[S], right: &[S]) -> S {
    assert_eq!(left.len(), right.len());
    let mut result = S::one();
    for (&x, &y) in left.iter().zip(right) {
        result *= S::one() + x + y;
    }
    result
}

pub fn dot<S: Scalar>(left: &[S], right: &[S]) -> S {
    assert_eq!(left.len(), right.len());
    let mut result = S::zero();
    for (&x, &y) in left.iter().zip(right) {
        result += x * y;
    }
    result
}

/// A polynomial at `point`, by Horner over its coefficients, constant first.
pub fn poly_eval<S: Scalar>(coefficients: &[S], point: S) -> S {
    coefficients.iter().rev().fold(S::zero(), |acc, &c| acc * point + c)
}
