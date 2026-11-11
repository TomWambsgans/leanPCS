// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The rank conditions of `HIDING.md`, checked exactly on the toy circuit at fixed random challenges.
//!
//! With the challenges fixed, the scalars a proof reveals besides the roots (the two out-of-domain answers and the
//! three row values `X`, `C`, `V + Y` at `t`; `next` is the public wiring's, and the three claims' values follow from
//! them) are functions of the prover's randomness, affine in each group below once the groups before it are fixed. A
//! group's scalars are uniform, whatever the witness, if its map has full rank over `K` (each scalar three
//! `K`-coordinates):
//!
//! - **W**: the three row values and the witness table's out-of-domain answer, over the random rows' words (12
//!   coordinates over [`RANDOM_WORDS`]): every cell of a random row is affine in its two words, and `W` is linear in
//!   the cells;
//! - **T**: the quotient table's out-of-domain answer, over the blinding of `h` (3 over `3 FREE_BLIND`), the random
//!   rows fixed: the free blinding `b_0, b_1` is `h`'s coefficients `n, n + 1` and moves `q` by `b d d'`; `b_2`,
//!   solved for so that `q`'s coefficient `n` is zero, is affine in them.
//!
//! Both maps are affine: [`revealed_scalars_are_uniform`] checks that two words changed together move the scalars
//! by the sum of their own changes, and a word scaled by an element of `K` by that multiple.
//!
//! Every challenge is fixed, the out-of-domain points too (`opening::FIXED_OOD`), as the argument fixes them.

use primitives::field::{F64, F192};
use primitives::test_rng::Rng;

use crate::circuit::{Circuit, RANDOM_WORDS};
use crate::statement::Statement;
use crate::opening::{Commitment, FIXED_OOD};
use crate::protocol::tests::{toy, toy_cells, toy_statement};
use crate::protocol::{FREE_BLIND, Index, Randomness, prove_with_randomness, stream};
use crate::transcript::FIXED;

/// The rank over `K` of `columns`, each a vector of `K`-coordinates, by Gaussian elimination.
fn rank(mut columns: Vec<Vec<F64>>) -> usize {
    let rows = columns.first().map_or(0, Vec::len);
    let mut rank = 0;
    for row in 0..rows {
        let Some(pivot) = (rank..columns.len()).find(|&c| !columns[c][row].is_zero()) else {
            continue;
        };
        columns.swap(rank, pivot);
        let inverse = columns[rank][row].inv();
        let pivot_column = columns[rank].clone();
        for (c, column) in columns.iter_mut().enumerate() {
            if c != rank && !column[row].is_zero() {
                let factor = column[row] * inverse;
                for (x, &p) in column.iter_mut().zip(&pivot_column) {
                    *x += factor * p;
                }
            }
        }
        rank += 1;
    }
    rank
}

fn coordinates(xs: &[F192]) -> Vec<F64> {
    xs.iter().flat_map(|x| [F64(x.c0), F64(x.c1), F64(x.c2)]).collect()
}

/// A word of the prover's randomness.
#[derive(Clone, Copy)]
enum Word {
    Row(usize),
    Blind(usize, usize),
}

fn word(r: &mut Randomness, w: Word) -> &mut F64 {
    match w {
        Word::Row(k) => &mut r.rows[k],
        Word::Blind(e, i) => &mut r.blind[e][i],
    }
}

/// The change of the `revealed` scalars when `change` is applied to the randomness `base`, whose stream is
/// `before`.
fn delta(
    reveal: &dyn Fn(&Randomness) -> Vec<F192>,
    (base, before): (&Randomness, &[F192]),
    revealed: &[usize],
    change: &dyn Fn(&mut Randomness),
) -> Vec<F64> {
    let mut changed = base.clone();
    change(&mut changed);
    let after = reveal(&changed);
    coordinates(&revealed.iter().map(|&i| after[i] + before[i]).collect::<Vec<_>>())
}

#[test]
fn revealed_scalars_are_uniform() {
    let mut rng = Rng::new(0x41D);
    let circuit = toy();
    let x: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
    let (statement, cells) = (toy_statement(&x), toy_cells(&circuit, &x));
    check_uniform(&circuit, &statement, &cells, &mut rng);
}

/// [`revealed_scalars_are_uniform`] on the membership circuit (`2^22` rows), one secret: 43 proofs without their
/// openings, under a minute on 64 threads: `cargo test --release -p quotient --lib hiding -- --ignored`.
#[test]
#[ignore]
fn revealed_scalars_are_uniform_on_membership() {
    use crate::circuit::{membership, membership_inputs};
    use crate::statement::{DEPTH, Secret};
    let mut rng = Rng::new(0x41F);
    let circuit = membership();
    let secret = Secret {
        x: std::array::from_fn(|_| rng.next_u8()),
        siblings: std::array::from_fn::<_, DEPTH, _>(|_| std::array::from_fn(|_| rng.next_u8())),
        directions: rng.next_u64() as u32,
    };
    let cells = circuit.cells(&membership_inputs(&secret));
    check_uniform(&circuit, &secret.statement(), &cells, &mut rng);
}

fn check_uniform(circuit: &Circuit, statement: &Statement, cells: &[F64], rng: &mut Rng) {
    let index = Index::new(circuit);
    // The wiring's coefficient `n − 2` is not zero: the prover's `b_2` exists but at one value of `α`.
    assert!(!index.wiring()[index.wiring().len() - 2].is_zero());
    let commitment = Commitment::of(&index.commit());
    let seed: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
    let base = Randomness::derive(&seed, &commitment, statement, cells);
    let challenges: Vec<F192> = (0..5).map(|_| F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64())).collect();
    FIXED.with(|fixed| *fixed.borrow_mut() = Some(challenges));
    let reveal = |randomness: &Randomness| {
        FIXED_OOD.with(|fixed| *fixed.borrow_mut() = Some((0x00D, 0)));
        prove_with_randomness(circuit, &index, &commitment, statement, cells, randomness)
            .proof
            .stream
    };
    let w: Vec<Word> = (0..RANDOM_WORDS).map(Word::Row).collect();
    let t: Vec<Word> = (0..3).flat_map(|e| (0..FREE_BLIND).map(move |i| Word::Blind(e, i))).collect();
    let rows = stream::ROW_VALUES..stream::ROW_VALUES + 3;
    let groups = [
        ("W", rows.chain([stream::WITNESS_OOD]).collect::<Vec<_>>(), w),
        ("T", vec![stream::TABLE_OOD], t),
    ];
    let before = reveal(&base);
    let base = (&base, &before[..]);
    for (name, revealed, words) in &groups {
        let columns: Vec<Vec<F64>> = words
            .iter()
            .map(|&w| delta(&reveal, base, revealed, &|r| *word(r, w) += F64::ONE))
            .collect();
        let r = rank(columns.clone());
        assert_eq!(r, 3 * revealed.len(), "group {name}: rank {r} of {} scalars", revealed.len());
        // Affine over `K`: two words together, and one word scaled.
        let (a, b) = (words[0], words[words.len() - 1]);
        let together = delta(&reveal, base, revealed, &|r| {
            *word(r, a) += F64::ONE;
            *word(r, b) += F64::ONE;
        });
        let sum: Vec<F64> = columns[0].iter().zip(&columns[words.len() - 1]).map(|(&x, &y)| x + y).collect();
        assert_eq!(together, sum, "group {name} is not additive");
        let c = F64(rng.next_u64());
        let scaled = delta(&reveal, base, revealed, &|r| *word(r, a) += c);
        assert_eq!(scaled, columns[0].iter().map(|&x| x * c).collect::<Vec<_>>(), "group {name} is not K-linear");
    }
    FIXED.with(|fixed| *fixed.borrow_mut() = None);
}
