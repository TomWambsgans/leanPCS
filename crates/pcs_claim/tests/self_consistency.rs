// Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Adapted from a review's randomized differential test
// of the commitments and openings (`perf2/provers`), turned into a self-check that needs no other build.
//! Randomized commitments and openings, checked against each other: for random stacks (`n`, the committed lanes, the
//! all-zero lanes' pattern, sparse lanes that must not be flagged) and claims at random points (wholly random, or
//! boolean in the lane coordinates, in the in-lane ones, or everywhere), a claim's proof is the same whichever way it
//! is made (alone or batched, from a kept codeword, compact when lanes are zero, or with its rows encoded again, the
//! zero lanes skipped or not), and every proof verifies. `small` runs by default; `wide` (ignored) takes
//! `SELF_SEED`, `SELF_CASES`, `SELF_MIN_N`, `SELF_MAX_N` (default 40 cases, `n` from 15 to 22).

use pcs_claim::*;
use primitives::field::{F64, F192};
use primitives::test_rng::Rng;

fn bit(rng: &mut Rng) -> F192 {
    if rng.next_u64() & 1 == 1 { F192::ONE } else { F192::ZERO }
}

/// A point of `n` coordinates: random, boolean everywhere, boolean inside a lane, or boolean in the lane's index.
fn point(rng: &mut Rng, n: usize, kind: u64) -> Vec<F192> {
    (0..n)
        .map(|j| match kind {
            0 => rng.ext(),
            1 => bit(rng),
            2 if j < n - LANE_FOLD => bit(rng),
            3 if j >= n - LANE_FOLD => bit(rng),
            _ => rng.ext(),
        })
        .collect()
}

/// A stack of `n_lanes` whole lanes of `2^(n - 6)` words, some of them all zero by `pattern`.
fn stack(rng: &mut Rng, n: usize, n_lanes: usize, pattern: u64) -> Vec<F64> {
    let lane = 1usize << (n - LANE_FOLD);
    let mut words: Vec<F64> = (0..n_lanes * lane).map(|_| F64(rng.next_u64())).collect();
    for l in 0..n_lanes {
        let zero = match pattern {
            0 => false,
            1 => l == n_lanes / 2,
            2 => l + 1 == n_lanes,
            3 => true,
            4 => l % 2 == 1,
            5 => l == 0,
            6 => l != 0,
            _ => rng.next_u64() % 3 == 0,
        };
        if zero {
            words[l * lane..(l + 1) * lane].fill(F64::ZERO);
        }
    }
    // A lane zero but for its last word: not all zero, so not flagged.
    if pattern == 7 && n_lanes > 1 && rng.next_u64() % 2 == 0 {
        let l = rng.next_u64() as usize % n_lanes;
        words[l * lane..(l + 1) * lane].fill(F64::ZERO);
        words[l * lane + lane - 1] = F64(1);
    }
    words
}

fn run(seed: u64, cases: usize, min_n: usize, max_n: usize) {
    let mut rng = Rng::new(seed);
    for case in 0..cases {
        let n = min_n + rng.next_u64() as usize % (max_n - min_n + 1);
        let n_lanes = match rng.next_u64() % 6 {
            0 => 1,
            1 => 64,
            2 => 63,
            _ => 1 + rng.next_u64() as usize % 64,
        };
        let pattern = rng.next_u64() % 8;
        let words = stack(&mut rng, n, n_lanes, pattern);
        let at = format!("seed {seed} case {case}: n {n}, {n_lanes} lanes, pattern {pattern}");
        // The same stack committed keeping its codeword and not: one commitment.
        let kept = commit_words(&words, n, true);
        let lean = commit_words(&words, n, false);
        assert_eq!((kept.root, kept.ood), (lean.root, lean.ood), "{at}: the commitment");
        let claims: Vec<PcsClaim> = (0..4)
            .map(|k| {
                let p = point(&mut rng, n, (k + case as u64) % 4);
                let v = evaluate_lanes(&words, &p);
                kept.claim(p, v)
            })
            .collect();
        // Each claim alone, from the kept codeword (not freed): the reference.
        let want: Vec<_> = claims.iter().map(|c| open(&words, &kept, c, Codeword::Keep)).collect();
        for (c, proof) in claims.iter().zip(&want) {
            assert!(verify(&c.encode(), &wire_proof(proof)), "{at}: a proof verifies");
        }
        assert_eq!(open_batch(&words, &kept, &claims, Codeword::Keep), want, "{at}: batched, kept");
        assert_eq!(open_batch(&words, &kept, &claims[..3], Codeword::Free), want[..3], "{at}: batched, then freed");
        assert_eq!(open_batch(&words, &kept, &claims[1..], Codeword::Free), want[1..], "{at}: batched, encoded again");
        assert_eq!(open(&words, &kept, &claims[2], Codeword::Free), want[2], "{at}: alone, encoded again");
        assert_eq!(open_batch(&words, &lean, &claims, Codeword::Free), want, "{at}: batched, never kept");
        assert_eq!(open(&words, &lean, &claims[3], Codeword::Free), want[3], "{at}: alone, never kept");
    }
}

#[test]
fn small() {
    run(1, 8, 15, 18);
}

#[test]
#[ignore]
fn wide() {
    let env = |name: &str, default: usize| std::env::var(name).ok().map_or(default, |s| s.parse().expect(name));
    run(env("SELF_SEED", 1) as u64, env("SELF_CASES", 40), env("SELF_MIN_N", 15), env("SELF_MAX_N", 22));
}
