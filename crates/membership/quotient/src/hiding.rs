// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The rank conditions of `HIDING.md`, checked exactly on the toy circuit at fixed random challenges.
//!
//! With the challenges fixed, the scalars a proof reveals besides the roots (the out-of-domain answers, the four
//! `a_j`, `Q`'s and `G`'s values; `next` is the public wiring's, `H`'s value follows from the others) are functions
//! of the prover's randomness, affine in each group below once the groups before it are fixed. A group's scalars are
//! uniform, whatever the witness, if its map has full rank over `K` (each scalar three `K`-coordinates):
//!
//! - **F1**: `a_1, a_2` over the masks of `Y` and `C` (6 coordinates over 6);
//! - **A**: `a_0, a_3`, the witness table's and `G`'s out-of-domain answers and `G`'s value, over the masks of `X` and
//!   `V` and the random rows (15 over `6 + RANDOM_ROWS`), the masks of `Y` and `C` fixed (they enter the gate's
//!   quotient through `Y·C`);
//! - **B**: `H`'s and `Q`'s out-of-domain answers and `Q`'s value, over the blinding of `h` (9 over `3 H_BLIND`),
//!   the masks and the random rows fixed (they enter `q` through the copy argument's denominators).

use primitives::field::{F64, F192};
use primitives::test_rng::Rng;

use crate::circuit::RANDOM_ROWS;
use crate::opening::Commitment;
use crate::protocol::tests::{toy, toy_cells, toy_statement};
use crate::protocol::{H_BLIND, Index, Randomness, prove_with_randomness};
use crate::transcript::FIXED;

/// Where the revealed scalars sit in the proof's stream: the out-of-domain answers of the witness table, `H`, `Q`,
/// `G`; the `a_j`; `Q`'s and `G`'s values.
const OOD: [usize; 4] = [2, 5, 8, 11];
const A: [usize; 4] = [12, 13, 14, 15];
const VALUES: [usize; 2] = [17, 18];

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
    Mask(usize, usize),
    Row(usize),
    Blind(usize, usize),
}

fn word(r: &mut Randomness, w: Word) -> &mut F64 {
    match w {
        Word::Mask(j, i) => &mut r.masks[j][i],
        Word::Row(k) => &mut r.rows[k],
        Word::Blind(e, i) => &mut r.blind[e][i],
    }
}

/// The revealed scalars' map over one group of the randomness: a column per randomness word, the change of the
/// `revealed` scalars when that word changes by one.
fn columns(
    reveal: &dyn Fn(&Randomness) -> Vec<F192>,
    base: &Randomness,
    revealed: &[usize],
    words: &[Word],
) -> Vec<Vec<F64>> {
    let at = |stream: &[F192]| revealed.iter().map(|&i| stream[i]).collect::<Vec<_>>();
    let base_stream = at(&reveal(base));
    words
        .iter()
        .map(|&w| {
            let mut changed = base.clone();
            *word(&mut changed, w) += F64::ONE;
            let stream = at(&reveal(&changed));
            coordinates(&stream.iter().zip(&base_stream).map(|(&x, &y)| x + y).collect::<Vec<_>>())
        })
        .collect()
}

#[test]
fn revealed_scalars_are_uniform() {
    let mut rng = Rng::new(0x41D);
    let circuit = toy();
    let index = Index::new(&circuit);
    let commitment = Commitment::of(&index.commit());
    let x: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
    let statement = toy_statement(&x);
    let cells = toy_cells(&circuit, &x);
    let seed: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
    let base = Randomness::derive(&seed, &commitment, &statement, &cells);
    let challenges: Vec<F192> = (0..5).map(|_| F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64())).collect();
    FIXED.with(|fixed| *fixed.borrow_mut() = Some(challenges));
    let reveal = |randomness: &Randomness| {
        prove_with_randomness(&circuit, &index, &commitment, &statement, &cells, randomness)
            .proof
            .stream
    };
    let masks = |js: [usize; 2]| js.into_iter().flat_map(|j| (0..3).map(move |i| Word::Mask(j, i)));
    let f1: Vec<Word> = masks([1, 2]).collect();
    let a: Vec<Word> = masks([0, 3]).chain((0..RANDOM_ROWS).map(Word::Row)).collect();
    let b: Vec<Word> = (0..3).flat_map(|e| (0..H_BLIND).map(move |i| Word::Blind(e, i))).collect();
    let groups = [
        ("F1", vec![A[1], A[2]], f1),
        ("A", vec![A[0], A[3], OOD[0], OOD[3], VALUES[1]], a),
        ("B", vec![OOD[1], OOD[2], VALUES[0]], b),
    ];
    for (name, revealed, words) in &groups {
        let r = rank(columns(&reveal, &base, revealed, words));
        assert_eq!(r, 3 * revealed.len(), "group {name}: rank {r} of {} scalars", revealed.len());
    }
    FIXED.with(|fixed| *fixed.borrow_mut() = None);
}
