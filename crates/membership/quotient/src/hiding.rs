// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The rank conditions of `docs/membership/PROTOCOL.md` ("Zero knowledge"), checked exactly on the toy circuit at fixed random challenges.
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
//! - **T**: the quotient table's out-of-domain answer, over the slack words ([`SLACK_WORDS`]: 3 over 4), the random
//!   rows and the blinding of `h` fixed. A slack word moves the answer by itself times a weight of the out-of-domain
//!   point alone, so this map is **the same whatever the random rows and the blinding** (checked: its columns at a
//!   second randomness are the first's). Over the blinding of `h` instead (the free `b_0, b_1`, which move `q` by
//!   `b d d'`, and `b_2`, solved affinely), the map depends on the random rows through `d d'` and `b_2`, so its rank
//!   could fall short on a set of random rows; the slack words make the answer uniform regardless.
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
use crate::protocol::{Index, Randomness, SLACK_WORDS, prove_with_randomness, stream};
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
    Slack(usize),
}

fn word(r: &mut Randomness, w: Word) -> &mut F64 {
    match w {
        Word::Row(k) => &mut r.rows[k],
        Word::Slack(k) => &mut r.slack[k],
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
    let commitment = Commitment::of(index.commit());
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
    let t: Vec<Word> = (0..SLACK_WORDS).map(Word::Slack).collect();
    let rows = stream::ROW_VALUES..stream::ROW_VALUES + 3;
    let groups = [
        ("W", rows.chain([stream::WITNESS_OOD]).collect::<Vec<_>>(), w),
        ("T", vec![stream::TABLE_OOD], t),
    ];
    let before = reveal(&base);
    // A second randomness: other random rows, other blinding, other slack.
    let other = Randomness::derive(&std::array::from_fn(|_| rng.next_u8()), &commitment, statement, cells);
    let other_before = reveal(&other);
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
        // The map is the same at another randomness (the slack words' weights depend on no randomness; the random
        // rows' on none either).
        let at_other: Vec<Vec<F64>> = words
            .iter()
            .map(|&w| delta(&reveal, (&other, &other_before[..]), revealed, &|r| *word(r, w) += F64::ONE))
            .collect();
        assert_eq!(at_other, columns, "group {name}'s map depends on the randomness");
    }
    FIXED.with(|fixed| *fixed.borrow_mut() = None);
}
