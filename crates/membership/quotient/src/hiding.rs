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
//!
//! Group **A** is not affine in its randomness: the masks of `X` and `V` meet in the gate's quotient (`G`) through
//! `Y·C` (the shifts of the one interleaved witness polynomial), and a random row's value `v` enters `G` through `v²`
//! too (`HIDING.md`). With the masks fixed the map is `GF(2)`-affine in the random rows' bits, and
//! `group_a_over_the_random_rows` measures it exactly: the rows reach every revealed bit but `a_3`'s (which only
//! `V`'s mask reaches) and one functional `ψ` of `G`'s value (a row moves `G`'s value by `γ^-1 (u + u²)`, `u` a
//! multiple of `v`, whose trace against `γ` vanishes). `group_a_over_fresh_randomness` then draws the masks and the
//! rows afresh, many times, for one witness: the revealed bits' affine hull is the whole space (no `GF(2)`-affine
//! relation holds for a fixed witness) and `ψ` is balanced. That is evidence of group A's uniformity, not a proof.
//!
//! Every challenge is fixed, the out-of-domain points too (`opening::FIXED_OOD`), as the argument fixes them.


use primitives::field::{F64, F192};
use primitives::test_rng::Rng;

use crate::circuit::RANDOM_ROWS;
use crate::opening::{Commitment, FIXED_OOD};
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

/// The rank over `GF(2)` of `vectors`, each a bit vector packed in `u64`s.
fn rank_gf2(mut vectors: Vec<Vec<u64>>) -> usize {
    let bits = vectors.first().map_or(0, |v| 64 * v.len());
    let mut rank = 0;
    for bit in 0..bits {
        let (w, m) = (bit / 64, 1u64 << (bit % 64));
        let Some(pivot) = (rank..vectors.len()).find(|&c| vectors[c][w] & m != 0) else {
            continue;
        };
        vectors.swap(rank, pivot);
        let pivot_vector = vectors[rank].clone();
        for (c, v) in vectors.iter_mut().enumerate() {
            if c != rank && v[w] & m != 0 {
                for (x, &p) in v.iter_mut().zip(&pivot_vector) {
                    *x ^= p;
                }
            }
        }
        rank += 1;
    }
    rank
}

/// `f` over `items` on the machine's threads (each sets its own thread-local state).
fn parallel_map<T: Sync, R: Send>(items: &[T], f: impl Fn(&T) -> R + Sync) -> Vec<R> {
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get());
    let chunk = items.len().div_ceil(threads);
    std::thread::scope(|scope| {
        let handles: Vec<_> = items.chunks(chunk).map(|c| scope.spawn(|| c.iter().map(&f).collect::<Vec<_>>())).collect();
        handles.into_iter().flat_map(|h| h.join().unwrap()).collect()
    })
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
        FIXED_OOD.with(|fixed| *fixed.borrow_mut() = Some((0x00D, 0)));
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


/// The revealed bits of group A (`a_0`, `a_3`, the witness table's and `G`'s answers, `G`'s value) as a function of
/// the prover's randomness at fixed challenges and out-of-domain points, on the toy circuit.
struct GroupA {
    reveal: Box<dyn Fn(&Randomness) -> Vec<u64> + Sync>,
    base: Randomness,
}

fn group_a(revealed: &'static [usize]) -> GroupA {
    let mut rng = Rng::new(0x41E);
    let circuit = toy();
    let index = Index::new(&circuit);
    let commitment = Commitment::of(&index.commit());
    let x: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
    let statement = toy_statement(&x);
    let cells = toy_cells(&circuit, &x);
    let seed: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
    let base = Randomness::derive(&seed, &commitment, &statement, &cells);
    let challenges: Vec<F192> = (0..5).map(|_| F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64())).collect();
    let reveal = move |randomness: &Randomness| -> Vec<u64> {
        FIXED.with(|fixed| *fixed.borrow_mut() = Some(challenges.clone()));
        FIXED_OOD.with(|fixed| *fixed.borrow_mut() = Some((0x00D, 0)));
        let stream = prove_with_randomness(&circuit, &index, &commitment, &statement, &cells, randomness)
            .proof
            .stream;
        FIXED.with(|fixed| *fixed.borrow_mut() = None);
        FIXED_OOD.with(|fixed| *fixed.borrow_mut() = None);
        coordinates(&revealed.iter().map(|&i| stream[i]).collect::<Vec<_>>()).into_iter().map(|c| c.0).collect()
    };
    GroupA { reveal: Box::new(reveal), base }
}

const GROUP_A: [usize; 5] = [A[0], A[3], OOD[0], OOD[3], VALUES[1]];

/// The left kernel of `vectors` (rows over `GF(2)`, `bits` columns): a basis of the functionals they all vanish on.
fn left_kernel(mut vectors: Vec<Vec<u64>>, bits: usize) -> Vec<Vec<u64>> {
    let words = bits / 64;
    let mut pivots = Vec::new();
    let mut rank = 0;
    for bit in 0..bits {
        let (w, m) = (bit / 64, 1u64 << (bit % 64));
        let Some(p) = (rank..vectors.len()).find(|&c| vectors[c][w] & m != 0) else {
            continue;
        };
        vectors.swap(rank, p);
        let pivot_vector = vectors[rank].clone();
        for (c, v) in vectors.iter_mut().enumerate() {
            if c != rank && v[w] & m != 0 {
                for (x, &q) in v.iter_mut().zip(&pivot_vector) {
                    *x ^= q;
                }
            }
        }
        pivots.push(bit);
        rank += 1;
    }
    (0..bits)
        .filter(|b| !pivots.contains(b))
        .map(|f| {
            let mut lambda = vec![0u64; words];
            lambda[f / 64] |= 1 << (f % 64);
            for (r, &p) in pivots.iter().enumerate() {
                if vectors[r][f / 64] >> (f % 64) & 1 == 1 {
                    lambda[p / 64] |= 1 << (p % 64);
                }
            }
            lambda
        })
        .collect()
}

fn parity(lambda: &[u64], v: &[u64]) -> bool {
    lambda.iter().zip(v).map(|(l, x)| (l & x).count_ones()).sum::<u32>() % 2 == 1
}

/// The random rows' `GF(2)`-affine map on group A, the masks fixed (one flip a bit, exact for an affine map, which
/// two-flip differences confirm): rank `960 − 193`, its left kernel `a_3`'s 192 bits and one functional `ψ` of `G`'s
/// value. About two minutes on 16 cores: `cargo test --release -p quotient --lib hiding -- --ignored`.
#[test]
#[ignore]
fn group_a_over_the_random_rows() {
    let GroupA { reveal, base } = group_a(&GROUP_A);
    let base_bits = reveal(&base);
    let flips: Vec<(usize, u32)> = (0..RANDOM_ROWS).flat_map(|k| (0..64).map(move |b| (k, b))).collect();
    let flip = |k: usize, b: u32| {
        let mut changed = base.clone();
        changed.rows[k].0 ^= 1u64 << b;
        changed
    };
    let vectors: Vec<Vec<u64>> =
        parallel_map(&flips, |&(k, b)| reveal(&flip(k, b)).iter().zip(&base_bits).map(|(x, y)| x ^ y).collect());
    // Affine: two flips (one row, then two rows) are the sums of the single ones.
    for ((k1, b1), (k2, b2)) in [((3, 5), (3, 40)), ((3, 5), (7, 40))] {
        let mut both = flip(k1, b1);
        both.rows[k2].0 ^= 1u64 << b2;
        let both: Vec<u64> = reveal(&both).iter().zip(&base_bits).map(|(x, y)| x ^ y).collect();
        let sum: Vec<u64> = vectors[64 * k1 + b1 as usize]
            .iter()
            .zip(&vectors[64 * k2 + b2 as usize])
            .map(|(x, y)| x ^ y)
            .collect();
        assert_eq!(both, sum, "the random rows' map is not GF(2)-affine");
    }
    let bits = 64 * 3 * GROUP_A.len();
    let kernel = left_kernel(vectors, bits);
    assert_eq!(kernel.len(), 193, "the random rows miss {} bits of group A", kernel.len());
    let words_of = |lambda: &Vec<u64>| -> Vec<usize> { (0..lambda.len()).filter(|&w| lambda[w] != 0).collect() };
    let a3 = [3, 4, 5];
    let g_value = [12, 13, 14];
    let (on_a3, rest): (Vec<_>, Vec<_>) = kernel.iter().partition(|l| words_of(l).iter().all(|w| a3.contains(w)));
    assert_eq!(on_a3.len(), 192, "a_3's bits");
    assert!(words_of(rest[0]).iter().all(|w| g_value.contains(w) || a3.contains(w)), "ψ is on G's value");
}

/// Group A over fresh uniform masks and random rows, one witness, the challenges and out-of-domain points fixed: the
/// affine hull of the revealed bits (with `a_1`, `a_2`: 1,344 bits) is the whole space, and `ψ` (found at the base
/// masks) is balanced within four standard deviations. About three minutes on 16 cores.
#[test]
#[ignore]
fn group_a_over_fresh_randomness() {
    const ALL: [usize; 7] = [A[0], A[1], A[2], A[3], OOD[0], OOD[3], VALUES[1]];
    let GroupA { reveal, base } = group_a(&ALL);
    let bits = 64 * 3 * ALL.len();
    let samples = bits + 64;
    let seeds: Vec<u64> = (0..samples as u64).collect();
    let vectors: Vec<Vec<u64>> = parallel_map(&seeds, |&s| {
        let mut r = Rng::new(0xABC0_0000 + s);
        let mut randomness = base.clone();
        randomness.masks.iter_mut().flatten().for_each(|m| *m = F64(r.next_u64()));
        randomness.rows.iter_mut().for_each(|v| *v = F64(r.next_u64()));
        reveal(&randomness)
    });
    let differences: Vec<Vec<u64>> =
        vectors[1..].iter().map(|v| v.iter().zip(&vectors[0]).map(|(a, b)| a ^ b).collect()).collect();
    assert_eq!(rank_gf2(differences), bits, "a GF(2)-affine relation holds for a fixed witness");
    // ψ: the rows' kernel at the base masks, past a_3's bits; here a_3 is words 9..12 and G's value 18..21.
    let GroupA { reveal: reveal_a, base: base_a } = group_a(&GROUP_A);
    let base_bits = reveal_a(&base_a);
    let flips: Vec<(usize, u32)> = (0..RANDOM_ROWS).flat_map(|k| (0..64).map(move |b| (k, b))).collect();
    let rows: Vec<Vec<u64>> = parallel_map(&flips, |&(k, b)| {
        let mut changed = base_a.clone();
        changed.rows[k].0 ^= 1u64 << b;
        reveal_a(&changed).iter().zip(&base_bits).map(|(x, y)| x ^ y).collect()
    });
    let kernel = left_kernel(rows, 64 * 3 * GROUP_A.len());
    let psi = kernel.iter().find(|l| (12..15).any(|w| l[w] != 0)).expect("ψ");
    // GROUP_A's words (a_0 0..3, a_3 3..6, W 6..9, G 9..12, G's value 12..15) into ALL's (a_0, a_1, a_2, a_3, ...).
    let mut psi_all = vec![0u64; 3 * ALL.len()];
    for (w, &l) in psi.iter().enumerate() {
        psi_all[if w < 3 { w } else { w + 6 }] = l;
    }
    let ones = vectors.iter().filter(|v| parity(&psi_all, v)).count() as f64;
    let (mean, sd) = (samples as f64 / 2.0, (samples as f64).sqrt() / 2.0);
    assert!((ones - mean).abs() < 4.0 * sd, "ψ = 1 on {ones} of {samples} samples");
}
