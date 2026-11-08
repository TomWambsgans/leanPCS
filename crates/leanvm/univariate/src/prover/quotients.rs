// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The second commitment's quotients (SPEC.md §5.2, §6), each from its numerator's values on the first points of an
//! extension coset `D_M = ω_(2^M) + V_M`, which avoids its domain: there over the vanishing polynomial's, interpolated
//! back to novel coefficients ([`ntt::interpolate_prefix`]). The points are the count rounded up, in blocks of cosets
//! (`Σ 2^(e_j)` of them), so a quotient of degree below its count is their interpolant. A numerator that does not
//! vanish on its domain is caught on one more block of points, where its value over the vanishing polynomial's is
//! checked against the interpolant's: [`Quotient::degree`] is then the points' count, never below the verifier's.
//!
//! Every numerator is read from K-columns' values ([`Points`]), eight columns a batch ([`ntt::K8`]), the batches
//! evaluated on each piece of points (a coset of `V_e`, `e ≤ r`, `2^r` the columns' length) by one transform each.

use leanvm_statement::layout::{OP_JUMP, OP_SHA3, keccak_slot, keccak_slot_offset, tables};
use leanvm_univariate_domain::{active_factors, padding_factors};
use primitives::field::{F64, F192};

use super::bus::Bus;
use super::columns::{C1Polys, SetupPolys};
use super::poly::omega;
use super::prints::{Print, PullPush, PullPush8};
use super::trace::Trace;
use crate::verifier::degree;
use quotient::ntt::{self, ESplat, Ex8, K8, Kx8, MixedSum};

/// The domain helpers the vanishing polynomials need, kept apart for the tests.
mod leanvm_univariate_domain {
    /// The active rows of a height-`r` table of `rows` rows as aligned cosets `ω_a + V_b`, the factors `(b, a)` of
    /// `Z_act = Π (w_b + ω_a)`: bit `b < r` of `rows` owns `[2^r - 2^(b+1), 2^r - 2^b)`, `a = 2^(r-b) - 2`, and a full
    /// table is `V_r` (`crate::domain::active_positions`, SPEC.md §13, F1b).
    pub fn active_factors(rows: u64, r: usize) -> Vec<(usize, u64)> {
        if rows == 1 << r {
            return vec![(r, 0)];
        }
        (0..r)
            .rev()
            .filter(|&b| rows >> b & 1 == 1)
            .map(|b| (b, (1 << (r - b)) - 2))
            .collect()
    }

    /// The padding rows likewise, the factors of `Z_pad = w_r / Z_act`: the cosets of the count's unset bits below
    /// `r`, and the last row `2^r - 1`, unless the table is full.
    pub fn padding_factors(rows: u64, r: usize) -> Vec<(usize, u64)> {
        if rows == 1 << r {
            return Vec::new();
        }
        let mut out: Vec<(usize, u64)> = (0..r)
            .rev()
            .filter(|&b| rows >> b & 1 == 0)
            .map(|b| (b, (1 << (r - b)) - 2))
            .collect();
        out.push((0, (1 << r) - 1));
        out
    }
}

/// Table `t`'s vanishing polynomials' factors `(b, a)`, `Π (w_b + ω_a)`: of its active rows (`Z_act`) and of its
/// padding rows (`Z_pad`), the rows' fixed cosets (SPEC.md §13, F1b).
pub fn vanishing_factors(trace: &Trace, t: usize) -> (Vec<(usize, u64)>, Vec<(usize, u64)>) {
    let (rows, r) = (trace.rows[t], trace.heights[t]);
    (active_factors(rows, r), padding_factors(rows, r))
}

/// A quotient's novel coefficients (its three limbs), the count the verifier declares, and its actual degree.
pub struct Quotient {
    pub novel: [Vec<F64>; 3],
    pub count: u64,
    /// The highest nonzero coefficient, `-1` for zero; the points' count if the numerator does not vanish.
    pub degree: i64,
}

impl Quotient {
    fn new(novel: [Vec<F64>; 3], count: u64, holds: bool) -> Self {
        let degree = if holds {
            novel
                .iter()
                .filter_map(|limb| limb.iter().rposition(|x| !x.is_zero()))
                .max()
                .map_or(-1, |d| d as i64)
        } else {
            novel[0].len() as i64
        };
        Self { novel, count, degree }
    }

    /// Whether its degree is below the verifier's count.
    pub fn fits(&self) -> bool {
        self.degree < self.count as i64
    }

    /// Limb `limb` of chunk `chunk` of `Q = Q_0 + w_(e_0) (Q_1 + w_(e_1) Q_2)` in basis `B`, into `out` (`2^(e_chunk)`
    /// words): the novel coefficients' slice (`X_(2^e + k) = w_e X_k` for `k < 2^e`), then its subset sums.
    pub fn chunk_b(&self, sizes: &[usize], chunk: usize, limb: usize, out: &mut [F64]) {
        assert_eq!(out.len(), 1 << sizes[chunk]);
        ntt::subset_sums_from(self.chunk_novel(sizes, chunk, limb), out);
    }

    /// Limb `limb`'s novel coefficients of chunk `chunk` (its slice, the zeros past the quotient's end cut), whose
    /// subset sums are [`Quotient::chunk_b`].
    pub fn chunk_novel(&self, sizes: &[usize], chunk: usize, limb: usize) -> &[F64] {
        let novel = &self.novel[limb];
        let at: usize = sizes[..chunk].iter().map(|&e| 1usize << e).sum();
        let end: usize = at + (1 << sizes[chunk]);
        let have = end.min(novel.len()).saturating_sub(at);
        if chunk + 1 == sizes.len() {
            assert!(
                novel[end.min(novel.len())..].iter().all(|x| x.is_zero()),
                "the chunks hold the whole quotient"
            );
        }
        &novel[at.min(novel.len())..at.min(novel.len()) + have]
    }

    /// Whether its numerator vanished on its domain (its degree is then below its points' count).
    fn holds(&self) -> bool {
        self.degree < self.novel[0].len() as i64
    }

    /// `self + other`, coefficient by coefficient.
    fn add(mut self, other: Quotient) -> Self {
        let holds = self.holds() && other.holds();
        for (mine, theirs) in self.novel.iter_mut().zip(other.novel) {
            if mine.len() < theirs.len() {
                mine.resize(theirs.len(), F64::ZERO);
            }
            mine.iter_mut().zip(&theirs).for_each(|(x, &y)| *x += y);
        }
        Self::new(self.novel, self.count.max(other.count), holds)
    }
}

/// The extension's variables: at least the domain's, and enough for `count` coefficients.
pub fn extension_vars(count: u64, r: usize) -> usize {
    let need = 64 - count.max(1).saturating_sub(1).leading_zeros() as usize;
    r.max(need)
}

/// A column's place among a quotient's batches: (batch, lane).
type Slot = (usize, usize);

/// The columns' values on one piece of points, eight points a run: column `slot` at the points `8 j..8 j + 8`; from
/// the batches (their runs transposed), or from each column's values alone (column `8 b + l` for the slot `(b, l)`).
pub enum Points<'a> {
    Batches(&'a [Vec<K8>]),
    Alone(&'a [Vec<F64>]),
}

impl Points<'_> {
    #[inline(always)]
    fn at(&self, (b, l): Slot, j: usize) -> Kx8 {
        match self {
            Self::Batches(v) => Kx8::row(&v[b][8 * j + l]),
            Self::Alone(v) => Kx8::load(&v[8 * b + l][8 * j..]),
        }
    }

    #[inline(always)]
    fn e(&self, limbs: [Slot; 3], j: usize) -> Ex8 {
        Ex8::from_limbs(limbs.map(|s| self.at(s, j)))
    }
}

/// The slot of the `k`-th column.
fn slot(k: usize) -> Slot {
    (k / 8, k % 8)
}

/// Whether `quotient::ntt`'s lanes are other than AVX-512's eight carry-less products: aarch64's NEON lanes (eight
/// PMULLs, four registers), or portable code. There [`table_leaf`] evaluates its numerator one point at a time in `E` ([`PullPush`]: a mixed
/// product three unreduced base products, a push from its pull's sum) rather than eight at a time ([`product`]: a
/// mixed product three reduced ones). With the NEON lanes (M4 Max), [`PullPush`] and [`product`] cost the same.
const PORTABLE_LANES: bool = !cfg!(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"));

/// The longest columns (`2^GROUPED_ROWS` entries) whose pieces [`prefix_quotient`] evaluates in rounds, a round's
/// batches transformed each by one worker ([`piece_rows`]), in at most `GROUPED_BYTES` a round (SHA3's leaf: 5 of its
/// 55 pieces, 60 tasks, 120 MB): there `ntt`'s transforms of one batch at a time, a few tasks a pass, leave workers idle between
/// their passes (on 64 threads, `SHA3`'s leaf was three quarters spinning; on the M4 Max's NEON lanes, the rounds took
/// "quotients: leaves" from 0.30 s to 0.18 s).
const GROUPED_ROWS: usize = 17;
const GROUPED_BYTES: usize = 1 << 29;

/// [`ntt::values_batch`] with `runs`, by one worker: row `i` of `data` becomes the eight columns at `offset + ω_i`,
/// then each eight rows transposed ([`Points::Batches`]). The layers from the highest down, two a pass above the
/// blocks of `2^LEAF` rows, which then take their own layers one by one.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
fn values_rows(data: &mut [K8], offset: F64) {
    const LEAF: usize = 10;
    /// `a += t b; b += a` between the halves of `chunk`.
    #[inline(always)]
    fn layer(chunk: &mut [K8], t: F64) {
        let (lo, hi) = chunk.split_at_mut(chunk.len() / 2);
        let t = Kx8::splat(t);
        for (a, b) in lo.iter_mut().zip(hi.iter_mut()) {
            let (x, y) = (Kx8::row(a), Kx8::row(b));
            let x = x + y * t;
            (*a, *b) = (x.to_row(), (y + x).to_row());
        }
    }
    let m = data.len().trailing_zeros() as usize;
    assert!(data.len() == 1 << m && m >= 3);
    let offsets = quotient::domain::chain(offset, m);
    let leaf = m.min(LEAF);
    let mut k = m;
    while k > leaf {
        if k - leaf >= 2 {
            // Layers `k - 1` and `k - 2`: each entry of a block's four quarters meets both of its butterflies.
            let block = 1usize << k;
            for (j, chunk) in data.chunks_exact_mut(block).enumerate() {
                let high = Kx8::splat(offsets[k - 1] + omega(2 * j));
                let low = [offsets[k - 2] + omega(4 * j), offsets[k - 2] + omega(4 * j + 2)].map(Kx8::splat);
                let q = block / 4;
                let (h0, h1) = chunk.split_at_mut(2 * q);
                let (q0, q1) = h0.split_at_mut(q);
                let (q2, q3) = h1.split_at_mut(q);
                for (((a0, a1), a2), a3) in q0.iter_mut().zip(q1.iter_mut()).zip(q2.iter_mut()).zip(q3.iter_mut()) {
                    let (mut x0, mut x1, mut x2, mut x3) = (Kx8::row(a0), Kx8::row(a1), Kx8::row(a2), Kx8::row(a3));
                    x0 = x0 + x2 * high;
                    x2 = x2 + x0;
                    x1 = x1 + x3 * high;
                    x3 = x3 + x1;
                    x0 = x0 + x1 * low[0];
                    x1 = x1 + x0;
                    x2 = x2 + x3 * low[1];
                    x3 = x3 + x2;
                    (*a0, *a1, *a2, *a3) = (x0.to_row(), x1.to_row(), x2.to_row(), x3.to_row());
                }
            }
            k -= 2;
        } else {
            let block = 1usize << k;
            for (j, chunk) in data.chunks_exact_mut(block).enumerate() {
                layer(chunk, offsets[k - 1] + omega(2 * j));
            }
            k -= 1;
        }
    }
    for (i, rows) in data.chunks_exact_mut(1 << leaf).enumerate() {
        let first = i << leaf;
        for k in (0..leaf).rev() {
            for (j, chunk) in rows.chunks_exact_mut(2 << k).enumerate() {
                layer(chunk, offsets[k] + omega(2 * ((first >> (k + 1)) + j)));
            }
        }
        ntt::transpose_runs(rows);
    }
}

/// [`values_rows`] elsewhere: `ntt`'s transform of a batch with `runs`, by the calling worker alone.
#[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
fn values_rows(data: &mut [K8], offset: F64) {
    ntt::values_batch_serial(data, offset, true);
}

/// Batch `src` (novel coefficients, `2^r` rows) on the piece `ω_first + V_p` (`3 ≤ p ≤ r`), into `dst`, by the calling
/// worker alone, each eight rows transposed ([`Points::Batches`]).
fn piece_rows(src: &[K8], first: usize, p: usize, dst: &mut Vec<K8>) {
    let size = 1usize << p;
    dst.resize(size, K8::ZERO);
    if size == src.len() {
        // Read from `src` tile by tile (no copy of the whole batch first), where `ntt`'s lanes serve.
        if cfg!(all(target_arch = "aarch64", target_feature = "aes")) {
            dst.copy_from_slice(src);
            values_rows(dst, omega(first));
        } else {
            ntt::values_batch_from_serial(src, dst, omega(first), true);
        }
    } else {
        ntt::fold_batch_serial(src, first, dst);
        values_rows(dst, omega(first));
    }
}

/// A quotient from its numerator on `D_M`'s first points: `columns` (novel coefficients, `2^r` each) evaluated on
/// every piece (a coset `ω_first + V_e`, `e ≤ r`), `piece(first, e)` what else the piece needs, and
/// `value(piece, points, j)` the quotient's values at the piece's points `8 j..8 j + 8`.
fn prefix_quotient<D: Sync>(
    r: usize,
    count: u64,
    columns: &[&[F64]],
    piece: impl Fn(usize, usize) -> D,
    value: impl Fn(&D, &Points, usize) -> Ex8 + Sync,
) -> Quotient {
    let n = 1usize << r;
    let prof = std::env::var_os("PI1_PROFILE").is_some();
    let started = std::time::Instant::now();
    let (mut t_transform, mut t_fill) = (0f64, 0f64);
    let sizes = ntt::prefix_sizes(count, r.saturating_sub(2));
    let base = 1usize << r.max(sizes[0] + 1);
    let total: usize = sizes.iter().map(|&e| 1usize << e).sum();
    // A few columns, or one piece: each column transformed alone (no batch to pack, no empty lanes); else eight at a
    // time.
    let pieces: usize = sizes.iter().map(|&e| 1usize << e.saturating_sub(r)).sum();
    let alone = columns.len() <= 5 || pieces == 1;
    let batches: Vec<Vec<K8>> = if alone {
        Vec::new()
    } else {
        columns.chunks(8).map(ntt::pack).collect()
    };
    // The pieces `(first point, place in the limbs, size)`, which tile the limbs in order; with columns short enough
    // (`GROUPED_ROWS`) in rounds, each round's batches (or columns) on its pieces transformed by one worker each, in
    // parallel.
    let all: Vec<(usize, usize, usize)> = ntt::prefix_starts(&sizes, base)
        .iter()
        .zip(&sizes)
        .flat_map(|(&first, &e)| {
            let p = e.min(r);
            (0..1usize << (e - p)).map(move |j| (first + (j << p), first - base + (j << p), p))
        })
        .collect();
    let grouped = (8..=1 << GROUPED_ROWS).contains(&n) && all.iter().all(|&(_, _, p)| p >= 3);
    // [`evaluate`]'s rows: grouped, the check's block alone (at most 64 points).
    let rows = if grouped { 64.min(n) } else { n }.max(8);
    let mut work: Vec<Vec<K8>> = batches.iter().map(|_| vec![K8::ZERO; rows]).collect();
    let mut singles: Vec<Vec<F64>> = if alone {
        columns.iter().map(|_| vec![F64::ZERO; rows]).collect()
    } else {
        Vec::new()
    };
    // The quotient's values on the piece `ω_first + V_e`, into `out`.
    let mut evaluate = |first: usize, e: usize, out: [&mut [F64]; 3]| {
        let size = 1usize << e;
        for (src, dst) in batches.iter().zip(work.iter_mut()) {
            let runs = size >= 8;
            if e == r {
                ntt::values_batch_from(src, &mut dst[..size], omega(first), runs);
            } else {
                ntt::fold_batch(src, first, &mut dst[..size]);
                ntt::values_batch(&mut dst[..size], omega(first), runs);
            }
            if !runs {
                ntt::transpose_runs(&mut dst[..8]);
            }
        }
        if alone {
            // Every column's passes in the same dispatches.
            let mut dsts: Vec<&mut [F64]> = singles.iter_mut().map(|d| &mut d[..size]).collect();
            if e == r {
                ntt::values_from_cols(columns, &mut dsts, omega(first));
            } else {
                for (dst, values) in dsts.iter_mut().zip(ntt::on_coset_prefix_cols(columns, first, e)) {
                    dst.copy_from_slice(&values);
                }
            }
        }
        let data = piece(first, e);
        let points = if alone {
            Points::Alone(&singles)
        } else {
            Points::Batches(&work)
        };
        ntt::fill_limbs8(out, |j| value(&data, &points, j));
    };
    let mut limbs: [Vec<F64>; 3] = std::array::from_fn(|_| vec![F64::ZERO; total]);
    if !grouped {
        for &(first, at, p) in &all {
            let [a, b, c] = &mut limbs;
            evaluate(
                first,
                p,
                [
                    &mut a[at..at + (1 << p)],
                    &mut b[at..at + (1 << p)],
                    &mut c[at..at + (1 << p)],
                ],
            );
        }
    } else {
        // The pieces tile the limbs in order: a round's are consecutive. A task: a batch (or a column) on a piece.
        let (width, unit) = if alone {
            (columns.len(), size_of::<F64>())
        } else {
            (batches.len(), size_of::<K8>())
        };
        // A round's tasks end together: the pieces a round that take the fewest waves of tasks on the pool, and of
        // those the fewest (the least memory: freed, the buffers stay with the allocator).
        let most = (GROUPED_BYTES / (width * n * unit)).clamp(1, all.len());
        let threads = parallel::num_threads();
        let waves = |per: usize| {
            let (full, rest) = (all.len() / per, all.len() % per);
            full * (per * width).div_ceil(threads) + (rest * width).div_ceil(threads)
        };
        let per_round = (1..=most).min_by_key(|&per| (waves(per), per)).expect("a piece");
        // The tasks' buffers, reserved here (their pages first written by the tasks).
        let mut transformed: Vec<Vec<K8>> = (0..if alone { 0 } else { per_round * width }).map(|_| Vec::with_capacity(n)).collect();
        let mut lone: Vec<Vec<F64>> = (0..if alone { per_round * width } else { 0 }).map(|_| Vec::with_capacity(n)).collect();
        for round in all.chunks(per_round) {
            let clock = std::time::Instant::now();
            let tasks = round.len() * width;
            if alone {
                parallel::chunks_mut(&mut lone[..tasks], 1, |i, dst| {
                    let (first, _, p) = round[i / width];
                    let dst = &mut dst[0];
                    dst.resize(1 << p, F64::ZERO);
                    ntt::on_coset_prefix_serial(columns[i % width], first, dst);
                });
            } else {
                parallel::chunks_mut(&mut transformed[..tasks], 1, |i, dst| {
                    let (first, _, p) = round[i / width];
                    piece_rows(&batches[i % width], first, p, &mut dst[0]);
                });
            }
            t_transform += clock.elapsed().as_secs_f64();
            let clock = std::time::Instant::now();
            let data: Vec<D> = round.iter().map(|&(first, _, p)| piece(first, p)).collect();
            let points: Vec<Points> = if alone {
                lone[..tasks].chunks(width).map(Points::Alone).collect()
            } else {
                transformed[..tasks].chunks(width).map(Points::Batches).collect()
            };
            // Each piece's first run in the round.
            let runs: Vec<usize> = round
                .iter()
                .scan(0, |acc, &(_, _, p)| {
                    let at = *acc;
                    *acc += (1usize << p) / 8;
                    Some(at)
                })
                .collect();
            let (at, last) = (round[0].1, round[round.len() - 1]);
            let end = last.1 + (1 << last.2);
            assert!(round.iter().zip(&runs).all(|(p, &j)| p.1 == at + 8 * j));
            let [a, b, c] = &mut limbs;
            ntt::fill_limbs8([&mut a[at..end], &mut b[at..end], &mut c[at..end]], |j| {
                let g = runs.partition_point(|&s| s <= j) - 1;
                value(&data[g], &points[g], j - runs[g])
            });
            t_fill += clock.elapsed().as_secs_f64();
        }
    }
    let evaluated = started.elapsed().as_secs_f64();
    {
        let [a, b, c] = &mut limbs;
        ntt::interpolate_prefix_cols(&mut [&mut a[..], &mut b[..], &mut c[..]], &sizes, base);
    }
    // One more block of points: the numerator's quotient there against the interpolant's values.
    let g = sizes[sizes.len() - 1].min(r).min(6);
    let first = base + total;
    let mut check: [Vec<F64>; 3] = std::array::from_fn(|_| vec![F64::ZERO; 1 << g]);
    let [a, b, c] = &mut check;
    evaluate(first, g, [a, b, c]);
    let holds = ntt::on_coset_prefix_cols(&[&limbs[0], &limbs[1], &limbs[2]], first, g) == check;
    if prof {
        eprintln!(
            "      prefix_quotient 2^{r}, {} columns, {} pieces, grouped {grouped}: evaluated {evaluated:.4} s (transforms {t_transform:.4}, fills {t_fill:.4}), interpolated and checked {:.4} s",
            columns.len(),
            all.len(),
            started.elapsed().as_secs_f64() - evaluated
        );
    }
    Quotient::new(limbs, count, holds)
}

/// A vanishing polynomial `Π (w_b + ω_a)` over its factors `(b, a)`, on eight points at once: at
/// `x = ω_(first + 8 j + p)`, `w_b(x) = ω_((first + 8 j) >> b) + ω_(p >> b)` (`8 | first`).
struct Vanishing {
    factors: Vec<(usize, F64)>,
    lanes: [Kx8; 4],
}

impl Vanishing {
    fn new(factors: &[(usize, u64)]) -> Self {
        Self {
            factors: factors.iter().map(|&(b, a)| (b, omega(a as usize))).collect(),
            lanes: std::array::from_fn(|b| Kx8::new(std::array::from_fn(|p| omega(p >> b)))),
        }
    }

    #[inline(always)]
    fn at(&self, first: usize, j: usize) -> Kx8 {
        let base = first + 8 * j;
        let mut acc = Kx8::splat(F64::ONE);
        for &(b, c) in &self.factors {
            acc = acc * (Kx8::splat(c + omega(base >> b)) + self.lanes[b.min(3)]);
        }
        acc
    }
}

/// What a piece of a quotient over `w_r` needs: its first point, and `1 / w_r` there.
struct Piece {
    first: usize,
    w_r_inv: F64,
}

fn piece_of(first: usize, r: usize) -> Piece {
    Piece {
        first,
        w_r_inv: omega(first >> r).inv(),
    }
}

/// The most columns (the heap's three included) [`table_leaf`]'s point-by-point numerator gathers.
const SCALAR_COLUMNS: usize = 128;

/// Table `t`'s leaf quotient: `((R P + P') Z_pad + (R + 1) Z_act) / w_r`, `R` the heap's block (its novel
/// coefficients `r_novel`, limb by limb), `P`, `P'` the row's pull and push products, `Z_act`, `Z_pad` the vanishing
/// polynomials of the active and the padding rows' fixed cosets (SPEC.md §13, F1b; the verifier checks it times
/// `Z_act`).
pub fn table_leaf(trace: &Trace, t: usize, c1: &C1Polys, bus: &Bus, r_novel: &[Vec<F64>; 3], count: u64) -> Quotient {
    let r = trace.heights[t];
    let mut used: Vec<usize> = bus.pull[t]
        .iter()
        .chain(&bus.push[t])
        .flat_map(|f| f.columns())
        .collect();
    used.sort_unstable();
    used.dedup();
    let (act, pad) = vanishing_factors(trace, t);
    let (z_act, z_pad) = (Vanishing::new(&act), Vanishing::new(&pad));
    let mut columns: Vec<&[F64]> = used.iter().map(|&c| &c1.tables[t][c].novel[..]).collect();
    let mut slots = vec![(0, 0); c1.tables[t].len()];
    for (k, &c) in used.iter().enumerate() {
        slots[c] = slot(k);
    }
    let heap: [Slot; 3] = std::array::from_fn(|k| slot(columns.len() + k));
    columns.extend(r_novel.iter().map(|l| &l[..]));
    if PORTABLE_LANES && columns.len() <= SCALAR_COLUMNS {
        // Column `k` (in `columns`' order) read as `k`, from the run's values gathered point by point.
        let both = PullPush::new(&bus.pull[t], &bus.push[t], |c| {
            let (b, l) = slots[c];
            8 * b + l
        });
        let width = columns.len();
        return prefix_quotient(
            r,
            count,
            &columns,
            |first, _| piece_of(first, r),
            |d, v, j| {
                let mut at = [[F64::ZERO; SCALAR_COLUMNS]; 8];
                for k in 0..width {
                    let x = v.at(slot(k), j).to_row();
                    for (p, row) in at.iter_mut().enumerate() {
                        row[k] = x.0[p];
                    }
                }
                let (za, zp) = (z_act.at(d.first, j).to_row().0, z_pad.at(d.first, j).to_row().0);
                let values: [F192; 8] = std::array::from_fn(|p| {
                    let x = &at[p];
                    let (pulled, pushed) = both.at(|k| x[k]);
                    let heap = F192::new(x[width - 3].0, x[width - 2].0, x[width - 1].0);
                    let za = F192::from(za[p]);
                    let numerator = heap * (pulled.mul_base(zp[p]) + za) + pushed.mul_base(zp[p]) + za;
                    numerator.mul_base(d.w_r_inv)
                });
                Ex8::from_limbs([
                    Kx8::new(values.map(|x| F64(x.c0))),
                    Kx8::new(values.map(|x| F64(x.c1))),
                    Kx8::new(values.map(|x| F64(x.c2))),
                ])
            },
        );
    }
    let both = PullPush8::new(&bus.pull[t], &bus.push[t], |c| slots[c]);
    prefix_quotient(
        r,
        count,
        &columns,
        |first, _| piece_of(first, r),
        |d, v, j| {
            let col = |s: Slot| v.at(s, j);
            let (p, p2) = both.at(col);
            let za = Ex8::from_k(z_act.at(d.first, j));
            let zp = z_pad.at(d.first, j);
            let numerator = v.e(heap, j) * (p.mul_k(zp) + za) + p2.mul_k(zp) + za;
            numerator.mul_k(Kx8::splat(d.w_r_inv))
        },
    )
}

/// The memory's leaf quotient: `(R D_fin + D_init) / w_lm`.
pub fn memory_leaf(
    trace: &Trace,
    c1: &C1Polys,
    setup: &SetupPolys,
    bus: &Bus,
    r_novel: &[Vec<F64>; 3],
    count: u64,
) -> Quotient {
    let r = trace.log_memory;
    let mut columns: Vec<&[F64]> = c1.memory.iter().map(|c| &c.novel[..]).collect();
    columns.push(&setup.address.novel);
    columns.extend(r_novel.iter().map(|l| &l[..]));
    let heap: [Slot; 3] = std::array::from_fn(|k| slot(5 + k));
    // `Bus::memory` is linear in the address, the count and the limbs: the cell's pulled (count its final count, in
    // column 3) and pushed (count 1) fingerprints.
    let w = &bus.weights;
    let terms = || [(slot(4), w[1]), (slot(0), w[3]), (slot(1), w[4]), (slot(2), w[5])];
    let zero = [F64::ZERO; 3];
    let fin = Print::linear(
        bus.memory(F64::ZERO, F64::ZERO, zero),
        terms().into_iter().chain([(slot(3), w[2])]),
    );
    let init = Print::linear(bus.memory(F64::ZERO, F64::ONE, zero), terms());
    prefix_quotient(
        r,
        count,
        &columns,
        |first, _| piece_of(first, r),
        |d, v, j| (v.e(heap, j) * fin.at(|s| v.at(s, j)) + init.at(|s| v.at(s, j))).mul_k(Kx8::splat(d.w_r_inv)),
    )
}

/// The bytecode's leaf quotient: `(R D_fin + D_init) / w_lb`, the tuple's slots from the setup.
pub fn bytecode_leaf(
    trace: &Trace,
    c1: &C1Polys,
    setup: &SetupPolys,
    bus: &Bus,
    r_novel: &[Vec<F64>; 3],
    count: u64,
) -> Quotient {
    let r = trace.log_bytecode;
    // Slot 2 is the count: the final counts' column, or 1.
    let mut columns: Vec<&[F64]> = (0..16).filter(|&s| s != 2).map(|s| &setup.slots[s].novel[..]).collect();
    let slot_of = |s: usize| slot(if s < 2 { s } else { s - 1 });
    columns.push(&c1.bytecode_final.novel);
    columns.extend(r_novel.iter().map(|l| &l[..]));
    let heap: [Slot; 3] = std::array::from_fn(|k| slot(16 + k));
    // `Bus::bytecode` is linear in the slots.
    let w = &bus.weights;
    let terms = || (0..16).filter(|&s| s != 2).map(move |s| (slot_of(s), w[s]));
    let fin = Print::linear(bus.bytecode(|_| F64::ZERO), terms().chain([(slot(15), w[2])]));
    let init = Print::linear(bus.bytecode(|s| if s == 2 { F64::ONE } else { F64::ZERO }), terms());
    prefix_quotient(
        r,
        count,
        &columns,
        |first, _| piece_of(first, r),
        |d, v, j| (v.e(heap, j) * fin.at(|s| v.at(s, j)) + init.at(|s| v.at(s, j))).mul_k(Kx8::splat(d.w_r_inv)),
    )
}

/// The tree quotient: `w_1 (T(s(x)) + T(x) T(x + 1)) / w_H`, of `2^H + 1` coefficients, on `D_(H+1)`'s first
/// `2^H + 2^e` points (blocks of `2^H` and `2^e`, `e = 13` or less: a fold onto a smaller block costs as much and
/// runs on fewer workers). At `x = ω_(first + i)`: `x + 1 = ω_(first + (i ^ 1))`, `s(x) = w_1(x) = ω_((first + i) >> 1)`.
pub fn tree(heap_novel: &[Vec<F64>; 3]) -> Quotient {
    let h = heap_novel[0].len().trailing_zeros() as usize;
    let sizes = [h, 13.min(h - 1)];
    let base = 1usize << (h + 1);
    let total = (1usize << h) + (1 << sizes[1]);
    // The quotient on `ω_first + V_e`, into `out`.
    let on = |first: usize, e: usize, out: [&mut [F64]; 3]| {
        let limbs: Vec<&[F64]> = heap_novel.iter().map(|l| &l[..]).collect();
        let at: Vec<Vec<F64>> = ntt::on_coset_prefix_cols(&limbs, first, e);
        let at_s: Vec<Vec<F64>> = ntt::on_coset_prefix_cols(&limbs, first >> 1, e - 1);
        let w_h_inv = Kx8::splat(omega(first >> h).inv());
        if e < 3 {
            let t = |v: &[Vec<F64>], i: usize| F192::new(v[0][i].0, v[1][i].0, v[2][i].0);
            return ntt::fill_limbs(out, 1 << 10, |i| {
                let w1 = omega((first + i) >> 1);
                (t(&at_s, i >> 1) + t(&at, i) * t(&at, i ^ 1))
                    .mul_base(w1)
                    .mul_base(w_h_inv.to_row().0[0])
            });
        }
        // Eight points a run: `x + 1` is the neighbour lane, `s(x)` the run's four points of `T(s(x))` twice, and
        // `w_1(x) = ω_((first + 8 j) >> 1) + ω_(p >> 1)`.
        let lanes = Kx8::new(std::array::from_fn(|p| omega(p >> 1)));
        ntt::fill_limbs8(out, |j| {
            let t = Ex8::from_limbs([0, 1, 2].map(|k| Kx8::load(&at[k][8 * j..])));
            let ts = Ex8::from_limbs([0, 1, 2].map(|k| Kx8::new(std::array::from_fn(|p| at_s[k][4 * j + p / 2]))));
            let w1 = Kx8::splat(omega((first + 8 * j) >> 1)) + lanes;
            (ts + t * t.swap_pairs()).mul_k(w1).mul_k(w_h_inv)
        });
    };
    let mut limbs: [Vec<F64>; 3] = std::array::from_fn(|_| vec![F64::ZERO; total]);
    for (&first, &e) in ntt::prefix_starts(&sizes, base).iter().zip(&sizes) {
        let at = first - base;
        let [a, b, c] = &mut limbs;
        on(
            first,
            e,
            [
                &mut a[at..at + (1 << e)],
                &mut b[at..at + (1 << e)],
                &mut c[at..at + (1 << e)],
            ],
        );
    }
    {
        let [a, b, c] = &mut limbs;
        ntt::interpolate_prefix_cols(&mut [&mut a[..], &mut b[..], &mut c[..]], &sizes, base);
    }
    let g = 6.min(sizes[1]);
    let mut check: [Vec<F64>; 3] = std::array::from_fn(|_| vec![F64::ZERO; 1 << g]);
    let [a, b, c] = &mut check;
    on(base + total, g, [a, b, c]);
    let holds = ntt::on_coset_prefix_cols(&[&limbs[0], &limbs[1], &limbs[2]], base + total, g) == check;
    Quotient::new(limbs, (1u64 << h) + 1, holds)
}

/// The constraint quotient `Σ_i γ^i M_i W_i / w_(r_W)`, in the verifier's order of powers: per table, JUMP's two
/// constraints, the counters, the `SHA3` table's fifty lane copies (`in_16`'s
/// with `END_BIT`: `copy + port + END_BIT`); then the public input's three limbs. As
/// `M_i = w_(r_W) / w_r`, it is the sum of each table's `Σ γ^i W_i / w_r` and the public input's part, each a
/// quotient of its own on its own points.
pub fn constraints(trace: &Trace, c1: &C1Polys, gamma: F192, count: u64, public_lines: [(F64, F64); 3]) -> Quotient {
    constraints_with(trace, &trace.qflock, c1, gamma, count, public_lines)
}

/// [`constraints`] with `q_flock`'s words `qflock` (the Keccak VM's: the Flock witness's, as `C1` holds them; the
/// trace keeps none).
pub fn constraints_with(
    trace: &Trace,
    qflock: &[F64],
    c1: &C1Polys,
    gamma: F192,
    count: u64,
    public_lines: [(F64, F64); 3],
) -> Quotient {
    let mut power = F192::ONE;
    let mut next = || {
        let current = power;
        power *= gamma;
        current
    };
    let mut parts: Vec<Quotient> = Vec::new();
    let row_bits = crate::verifier::QFLOCK_ROW_BITS;
    for table in &tables() {
        let t = table.opcode;
        let r = trace.heights[t];
        let n = 1usize << r;
        let cols = &c1.tables[t];
        let index = |name: &str| table.columns.iter().position(|&c| c == name).expect("a column");
        let jump = (t == OP_JUMP).then(|| (next(), next(), index("v_cond"), index("w"), index("b")));
        let counters: Vec<usize> = table.count_columns().collect();
        let g_counter = next();
        // (power, column, q_flock's word in the row's block, the constant the column differs from it by).
        let copies: Vec<(F192, usize, usize, u64)> = if t == OP_SHA3 {
            table
                .columns
                .iter()
                .enumerate()
                .filter_map(|(c, &name)| keccak_slot(name).map(|slot| (next(), c, slot, keccak_slot_offset(name))))
                .collect()
        } else {
            Vec::new()
        };
        // The part's count: its terms' quotients' degrees (`verifier::degree`), plus one.
        let n64 = n as u64;
        let mut most = degree((n64 - 1) * (1 + counters.len() as u64), n64);
        if jump.is_some() {
            most = most.max(degree(n64, 2));
        }
        if !copies.is_empty() {
            most = most.max(degree(r as u64 * (n64 / 2), n64));
        }
        // Columns: the inverse, the counters, JUMP's three, SHA3's copies combined by their powers (three limbs).
        let mut columns: Vec<&[F64]> = vec![&c1.inverses[t].novel];
        columns.extend(counters.iter().map(|&c| &cols[c].novel[..]));
        let jump_slots = jump.map(|(g1, g2, cond, w, b)| {
            let at = columns.len();
            columns.extend([&cols[cond].novel[..], &cols[w].novel[..], &cols[b].novel[..]]);
            (g1, g2, slot(at), slot(at + 1), slot(at + 2))
        });
        let combined: Option<([Vec<F64>; 3], [Vec<F64>; 3])> = (!copies.is_empty()).then(|| {
            // Σ g_j copy_j (novel coefficients), and Σ g_j v_j (the q_flock slots, as tables of the rows).
            let combine = |read: &(dyn Fn(usize, usize) -> F64 + Sync)| -> [Vec<F64>; 3] {
                let sums: Vec<F192> = parallel::map_collect(n, |i| {
                    copies
                        .iter()
                        .enumerate()
                        .fold(F192::ZERO, |acc, (j, &(g, ..))| acc + g.mul_base(read(j, i)))
                });
                limbs_of(&sums)
            };
            let copy = combine(&|j, i| cols[copies[j].1].novel[i]);
            // The slot's word plus the copy's constant: a table's multilinear plus a constant is the table plus it.
            let table = combine(&|j, i| qflock[(i << row_bits) | copies[j].2] + F64(copies[j].3));
            (copy, table)
        });
        let copy_slots: Option<[Slot; 3]> = combined.as_ref().map(|(copy, _)| {
            let at = columns.len();
            columns.extend(copy.iter().map(|l| &l[..]));
            std::array::from_fn(|k| slot(at + k))
        });
        let functionals = combined.as_ref().map(|_| crate::domain::coordinate_functionals(r));
        let counter_slots: Vec<Slot> = (1..=counters.len()).map(slot).collect();
        // A piece: `w_r` and its inverse; SHA3's `Σ g_j ℓ_j`, the slots' multilinear at `y(x) = y(ω_first) +
        // bits(i)`, a shifted cube (at least a run long).
        let piece = |first: usize, e: usize| {
            let cube = combined.as_ref().map(|(_, table)| {
                let delta = coordinates_k(omega(first), functionals.as_ref().expect("SHA3"));
                table
                    .iter()
                    .map(|l| {
                        let mut c = ntt::shifted_cube(l, &delta, e);
                        c.resize(c.len().max(8), F64::ZERO);
                        c
                    })
                    .collect::<Vec<Vec<F64>>>()
            });
            (piece_of(first, r), cube)
        };
        let one = Kx8::splat(F64::ONE);
        let jump_slots = jump_slots.map(|(g1, g2, cond, w, b)| (ESplat::new(g1), ESplat::new(g2), cond, w, b));
        let g_counter = ESplat::new(g_counter);
        parts.push(prefix_quotient(r, most + 1, &columns, piece, |(d, cube), v, j| {
            let mut sum = MixedSum::default();
            if let Some((g1, g2, cond, w, b)) = &jump_slots {
                let (cond, w, b) = (v.at(*cond, j), v.at(*w, j), v.at(*b, j));
                sum.add(g1, b + cond * w);
                sum.add(g2, cond * (b + one));
            }
            // The counters are nonzero on every row (SPEC.md §13, F1): z Π c + 1, without Z_pad.
            let product = counter_slots.iter().fold(v.at(slot(0), j), |acc, &s| acc * v.at(s, j));
            sum.add(&g_counter, product + one);
            let mut sum = sum.reduce();
            if let (Some(copy), Some(cube)) = (copy_slots, cube) {
                sum = sum + v.e(copy, j) + Ex8::from_limbs([0, 1, 2].map(|k| Kx8::load(&cube[k][8 * j..])));
            }
            sum.mul_k(Kx8::splat(d.w_r_inv))
        }));
    }
    // The public input: (mem_k + I_k) / w_1, I_k(x) = low + x (low + high), of degree below 2^lm - 2.
    let lm = trace.log_memory;
    let gs: Vec<F192> = (0..3).map(|_| next()).collect();
    let columns: Vec<&[F64]> = (0..3).map(|k| &c1.memory[k].novel[..]).collect();
    let piece = |first: usize, e: usize| {
        // 1 / w_1(x) = 1 / ω_((first + i) >> 1), shared by `i` and `i ^ 1` (at least a run's).
        let mut inverses: Vec<F64> = parallel::map_collect(((1usize << e) / 2).max(4), |q| omega((first >> 1) + q));
        invert(&mut inverses);
        (omega(first), inverses)
    };
    let gs: Vec<ESplat> = gs.into_iter().map(ESplat::new).collect();
    let lanes = Kx8::new(std::array::from_fn(omega));
    parts.push(prefix_quotient(
        lm,
        (1u64 << lm) - 2,
        &columns,
        piece,
        |(x0, inverses), v, j| {
            let x = Kx8::splat(*x0 + omega(8 * j)) + lanes;
            let mut sum = MixedSum::default();
            for (k, &(low, high)) in public_lines.iter().enumerate() {
                sum.add(&gs[k], v.at(slot(k), j) + Kx8::splat(low) + x * Kx8::splat(low + high));
            }
            sum.reduce()
                .mul_k(Kx8::new(std::array::from_fn(|p| inverses[4 * j + p / 2])))
        },
    ));
    let mut out = parts.pop().expect("the public part");
    while let Some(p) = parts.pop() {
        out = out.add(p);
    }
    out.count = count;
    out
}

/// E elements as their three limbs.
fn limbs_of(values: &[F192]) -> [Vec<F64>; 3] {
    [0, 1, 2].map(|k| parallel::map_collect(values.len(), |i| F64([values[i].c0, values[i].c1, values[i].c2][k])))
}

/// Batch inversion in K (Montgomery's trick per chunk); every entry must be nonzero.
fn invert(data: &mut [F64]) {
    parallel::chunks_mut(data, 1 << 12, |_, chunk| {
        let mut prefix = Vec::with_capacity(chunk.len());
        let mut acc = F64::ONE;
        for &x in chunk.iter() {
            prefix.push(acc);
            acc *= x;
        }
        let mut inv = acc.inv();
        for i in (0..chunk.len()).rev() {
            let x = chunk[i];
            chunk[i] = inv * prefix[i];
            inv *= x;
        }
    });
}

/// `y_l(x)` for a K point: `Σ_m a_(l,m) x^(2^m)`.
pub fn coordinates_k(x: F64, functionals: &[Vec<leanvm_statement::K>]) -> Vec<F64> {
    let r = functionals.len();
    let frobenius: Vec<F64> = std::iter::successors(Some(x), |&y| Some(y.square())).take(r).collect();
    functionals
        .iter()
        .map(|row| {
            row.iter()
                .zip(&frobenius)
                .fold(F64::ZERO, |acc, (a, &f)| acc + F64(a.0) * f)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// [`values_rows`] is `ntt`'s transform of a batch with `runs`, at every size it takes and offsets of each kind.
    #[test]
    fn values_rows_is_ntts() {
        let mut x = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = move || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            F64(x)
        };
        for m in [3, 4, 9, 10, 11, 12, 13, 15] {
            let src: Vec<K8> = (0..1usize << m).map(|_| K8(std::array::from_fn(|_| next()))).collect();
            for first in [0usize, 1 << m, 5 << m, 1 << 21] {
                let mut want = vec![K8::ZERO; 1 << m];
                ntt::values_batch_from(&src, &mut want, omega(first), true);
                let mut got = src.clone();
                values_rows(&mut got, omega(first));
                assert!(got == want, "2^{m} rows at {first}");
            }
        }
    }
}
