// Vendored from leanVM (https://github.com/leanEthereum/leanVM), commit 42422001, file crates/primitives/src/multilinear.rs:
// its barycentric Lagrange functions on the φ₈ table (`window_denominator`, `lagrange_weights`, `lagrange_eval`,
// `lagrange_weights_naive`), copied unchanged. leanVM c445e3d5's `primitives` (crates/vendor/leanvm-c445e3d5), which
// this crate runs on, has the rest of that file but not these.
// MIT OR Apache-2.0 (see LICENSE-MIT, LICENSE-APACHE and AGENTS.md at the repository root).
// CREDIT: https://github.com/succinctlabs/flock (`lagrange_weights_naive`), MIT OR Apache-2.0.
//! Lagrange interpolation on the GF(2^8) subfield's nodes (the φ₈ table), for the univariate skip.

use crate::field::PHI_8_TABLE_192 as PHI_8_TABLE;
use primitives::field::F192;

/// The one barycentric denominator an aligned `size`-node window of the φ₈ table has: `∏_{k≠0} φ₈(k)`,
/// inverted. φ₈ is F2-linear on its index, so `nodes[a] + nodes[b] = φ₈(a ^ b)` (the window's offset
/// cancels) and `b ↦ a ^ b` only permutes the window, leaving every node the same product.
pub fn window_denominator(size: usize) -> F192 {
    PHI_8_TABLE[1..size]
        .iter()
        .fold(F192::ONE, |acc, &node| acc * node)
        .inv()
}

/// The barycentric weights of `nodes` at `p`: `weights[i] =
/// ∏_{k≠i} (p + nodes[k]) / ∏_{k≠i} (nodes[i] + nodes[k])`. `O(n²)` multiplies
/// and, by `window_denominator`, a single inverse.
///
/// `nodes` must be an aligned window of the φ₈ table, `nodes[a] = nodes[0] + φ₈(a)`, which is what
/// every caller passes: a `2^k` prefix, or one of its cosets.
fn lagrange_weights(nodes: &[F192], p: F192) -> Vec<F192> {
    let n = nodes.len();
    debug_assert!(n.is_power_of_two() && n <= PHI_8_TABLE.len());
    debug_assert!(
        (0..n).all(|a| nodes[a] == nodes[0] + PHI_8_TABLE[a]),
        "not an aligned φ₈ window"
    );
    let denominator = window_denominator(n);
    (0..n)
        .map(|i| {
            let mut num = F192::ONE;
            for k in 0..n {
                if k != i {
                    num *= p + nodes[k];
                }
            }
            num * denominator
        })
        .collect()
}

/// Lagrange evaluation: given distinct `nodes` and a polynomial's `values` there,
/// evaluate the interpolant at `p`. Reads a sumcheck round's univariate (sent as
/// evaluations) at the verifier's challenge.
pub fn lagrange_eval(nodes: &[F192], values: &[F192], p: F192) -> F192 {
    debug_assert_eq!(nodes.len(), values.len());
    lagrange_weights(nodes, p)
        .iter()
        .zip(values)
        .fold(F192::ZERO, |acc, (&w, &v)| acc + v * w)
}

/// Barycentric weights over the first `2^k_skip` nodes of the GF(2^8) subfield.
/// O(2^{2·k_skip}) field multiplies, a one-time cost.
pub fn lagrange_weights_naive(k_skip: usize, z: F192) -> Vec<F192> {
    let ell = 1usize << k_skip;
    assert!(ell <= 256, "k_skip > 8 would exceed PHI_8_TABLE");
    lagrange_weights(&PHI_8_TABLE[..ell], z)
}
