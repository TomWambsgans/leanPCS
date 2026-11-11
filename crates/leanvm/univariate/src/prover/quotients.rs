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

use std::any::Any;
use std::marker::PhantomData;
use std::ops::Range;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

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
    Batches(&'a [&'a [K8]]),
    Alone(&'a [&'a [F64]]),
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
/// PMULLs, four registers), or portable code. There [`table_leaf_numerator`] evaluates its numerator one point at a time in `E` ([`PullPush`]: a mixed
/// product three unreduced base products, a push from its pull's sum) rather than eight at a time ([`product`]: a
/// mixed product three reduced ones). With the NEON lanes (M4 Max), [`PullPush`] and [`product`] cost the same.
const PORTABLE_LANES: bool = !cfg!(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"));

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

/// A quotient from its numerator on `D_M`'s first points, its columns long (the memory's, the bytecode's, `Q_W`'s
/// public part; the tables' go by [`prefix_quotients`]): `columns` (novel coefficients, `2^r` each) evaluated on every
/// block (a coset `ω_first + V_e`, `e ≤ r`) by `ntt`'s transforms, `piece(first, e)` what else the block needs, and
/// `value(piece, points, j)` the quotient's values at the block's points `8 j..8 j + 8`.
fn prefix_quotient<D: Send + Sync>(
    r: usize,
    count: u64,
    columns: &[&[F64]],
    piece: impl Fn(usize, usize) -> D + Sync,
    value: impl Fn(&D, &Points, usize) -> Ex8 + Sync,
) -> Quotient {
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
    // The quotient's values on the piece `ω_first + V_e`, into `out`: the columns' values there in new buffers (not
    // zeroed first: these columns are long, and one thread's zeroing took milliseconds).
    let evaluate = |first: usize, e: usize, out: [&mut [F64]; 3]| {
        let size = 1usize << e;
        let work: Vec<Vec<K8>> = batches
            .iter()
            .map(|src| {
                if size >= 8 {
                    return ntt::on_coset_batch(src, first, e, true);
                }
                let mut dst = vec![K8::ZERO; 8];
                ntt::fold_batch(src, first, &mut dst[..size]);
                ntt::values_batch(&mut dst[..size], omega(first), false);
                ntt::transpose_runs(&mut dst);
                dst
            })
            .collect();
        // Every column's passes in the same dispatches.
        let mut singles: Vec<Vec<F64>> = match (alone, e <= 6) {
            (false, _) => Vec::new(),
            (true, true) => ntt::on_coset_prefix_each(&columns.iter().map(|&c| (c, first, e)).collect::<Vec<_>>()),
            (true, false) => ntt::on_coset_prefix_cols(columns, first, e),
        };
        singles.iter_mut().for_each(|s| s.resize(s.len().max(8), F64::ZERO));
        let data = piece(first, e);
        let (rows, words): (Vec<&[K8]>, Vec<&[F64]>) =
            (work.iter().map(|w| &w[..]).collect(), singles.iter().map(|w| &w[..]).collect());
        let points = if alone { Points::Alone(&words) } else { Points::Batches(&rows) };
        ntt::fill_limbs8(out, |j| value(&data, &points, j));
    };
    let mut limbs: [Vec<F64>; 3] = std::array::from_fn(|_| ntt::zeros(total));
    for (&first, &e) in ntt::prefix_starts(&sizes, base).iter().zip(&sizes) {
        let p = e.min(r);
        for j in 0..1usize << (e - p) {
            let (first, at) = (first + (j << p), first - base + (j << p));
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
    }
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
    let holds = ntt::on_coset_prefix_each(&limbs.each_ref().map(|l| (&l[..], first, g))) == check;
    Quotient::new(limbs, count, holds)
}

/// A quotient for [`prefix_quotients`]: its numerator over its vanishing polynomial, read from K-columns of `2^r`
/// novel coefficients evaluated on each piece of `D_M`'s first points, as [`prefix_quotient`] takes it.
pub trait Numerator: Sync {
    /// `r` (the columns' `2^r` entries) and the count the verifier declares.
    fn shape(&self) -> (usize, u64);
    fn columns(&self) -> &[&[F64]];
    /// What the piece `ω_first + V_e` needs besides the columns' values, by the calling worker alone.
    fn piece(&self, first: usize, e: usize) -> Box<dyn Any + Send + Sync>;
    /// The quotient's values at the piece's runs `runs` (eight points each): run `j` into `out[k][8 (j - runs.start)..]`,
    /// cut at the outputs' length.
    fn fill(&self, piece: &(dyn Any + Send + Sync), points: &Points, runs: Range<usize>, out: [&mut [F64]; 3]);
}

/// A [`Numerator`] from closures: `piece(first, e)` a piece's data (by the calling worker alone), `value(data,
/// points, j)` the quotient's values at the piece's points `8 j..8 j + 8`.
pub struct Prefix<'a, D, P, V> {
    r: usize,
    count: u64,
    columns: Vec<&'a [F64]>,
    piece: P,
    value: V,
    data: PhantomData<fn() -> D>,
}

impl<'a, D, P, V> Prefix<'a, D, P, V>
where
    D: Send + Sync + 'static,
    P: Fn(usize, usize) -> D + Sync,
    V: Fn(&D, &Points, usize) -> Ex8 + Sync,
{
    pub fn new(r: usize, count: u64, columns: Vec<&'a [F64]>, piece: P, value: V) -> Self {
        Self {
            r,
            count,
            columns,
            piece,
            value,
            data: PhantomData,
        }
    }
}

impl<D, P, V> Numerator for Prefix<'_, D, P, V>
where
    D: Send + Sync + 'static,
    P: Fn(usize, usize) -> D + Sync,
    V: Fn(&D, &Points, usize) -> Ex8 + Sync,
{
    fn shape(&self) -> (usize, u64) {
        (self.r, self.count)
    }

    fn columns(&self) -> &[&[F64]] {
        &self.columns
    }

    fn piece(&self, first: usize, e: usize) -> Box<dyn Any + Send + Sync> {
        Box::new((self.piece)(first, e))
    }

    fn fill(&self, piece: &(dyn Any + Send + Sync), points: &Points, runs: Range<usize>, out: [&mut [F64]; 3]) {
        let data = piece.downcast_ref::<D>().expect("the piece's data");
        let [a, b, c] = out;
        for j in runs.clone() {
            let at = 8 * (j - runs.start);
            let [x, y, z] = (self.value)(data, points, j).limbs();
            x.store_to(&mut a[at..]);
            y.store_to(&mut b[at..]);
            z.store_to(&mut c[at..]);
        }
    }
}

/// The transforms' outputs [`prefix_quotients`] holds at once (a piece's are freed once its values are computed).
const LIVE_BYTES: usize = 1 << 28;

/// The largest piece (as a log) [`prefix_quotients`] transforms by one worker: a task of a few milliseconds.
const PIECE_CAP: usize = 15;

/// Runs a fill task of [`prefix_quotients`] computes.
const FILL_RUNS: usize = 64;

/// A piece's transformed columns: a batch's rows (their runs transposed), or a column's values.
enum Values {
    Rows(Vec<K8>),
    Words(Vec<F64>),
}

/// [`prefix_quotients`]' schedule: the pieces' transforms in order, each piece's values once its transforms are done,
/// its buffers freed once its values are.
struct Schedule {
    /// The next piece whose transforms (and data) are to be handed out, and the next of its tasks.
    next_unit: usize,
    next_task: usize,
    /// The bytes of the pieces handed out whose values are not all computed.
    live: usize,
    /// The fills whose piece's transforms are done.
    ready: std::collections::VecDeque<usize>,
    /// Per piece: its transforms (and data) not yet done, its fills not yet done.
    transforms_left: Vec<usize>,
    fills_left: Vec<usize>,
    fills_done: usize,
    /// Buffers to reuse.
    free: Vec<Values>,
}

/// A task [`Schedule::next`] hands out.
enum Job {
    /// Piece `u`'s batch (or column) `c` (its data when `c` is its width), into the buffer.
    Transform(usize, usize, Option<Values>),
    /// Fill `f`.
    Fill(usize),
    /// Nothing yet: wait for a task to finish.
    Wait,
    Done,
}

/// Sets its flag if dropped by a panic's unwinding: a [`prefix_quotients`] task that panics stops the others.
struct AbortOnPanic<'a>(&'a AtomicBool);

impl Drop for AbortOnPanic<'_> {
    fn drop(&mut self) {
        if std::thread::panicking() {
            self.0.store(true, Ordering::Release);
        }
    }
}

/// Several quotients, as [`prefix_quotient`] makes each, every stage's tasks for all of them in one dispatch: the
/// columns' batches packed; then in one dispatch, the pieces' transforms (each a batch, or a column, on a piece by one
/// worker) and their values (a piece's as soon as its transforms are done, at most `LIVE_BYTES` of transforms held);
/// the interpolations ([`ntt::interpolate_prefix_many`]) and the checks' folds ([`ntt::on_coset_prefix_each`]). One
/// quotient at a time, on 64 threads, the tables' leaves and `Q_W`'s parts left most workers idle between short
/// dispatches. The same quotients.
pub fn prefix_quotients(jobs: &[&dyn Numerator]) -> Vec<Quotient> {
    struct Plan {
        count: u64,
        sizes: Vec<usize>,
        base: usize,
        total: usize,
        /// Each column transformed alone (no batch to pack, no empty lanes), else eight at a time.
        alone: bool,
        /// The batches (or the columns) a piece transforms.
        width: usize,
        /// The check's block: its first point and its size's log.
        check: (usize, usize),
    }
    // The pieces, each quotient's in the order of its limbs' words, then the checks' blocks: (quotient, first point,
    // size's log, whether a check's).
    let mut units: Vec<(usize, usize, usize, bool)> = Vec::new();
    let plans: Vec<Plan> = jobs
        .iter()
        .enumerate()
        .map(|(q, job)| {
            let (r, count) = job.shape();
            let columns = job.columns();
            assert!(r >= 3 && columns.iter().all(|c| c.len() == 1 << r));
            let sizes = ntt::prefix_sizes(count, r.saturating_sub(2));
            let base = 1usize << r.max(sizes[0] + 1);
            let total: usize = sizes.iter().map(|&e| 1usize << e).sum();
            let whole: usize = sizes.iter().map(|&e| 1usize << e.saturating_sub(r)).sum();
            let alone = columns.len() <= 5 || whole == 1;
            let cap = r.min(PIECE_CAP);
            for (&first, &e) in ntt::prefix_starts(&sizes, base).iter().zip(&sizes) {
                let p = e.min(cap);
                units.extend((0..1usize << (e - p)).map(|j| (q, first + (j << p), p, false)));
            }
            let g = sizes[sizes.len() - 1].min(r).min(6);
            assert!(g >= 3, "a piece is at least a run");
            Plan {
                count,
                sizes,
                base,
                total,
                alone,
                width: if alone { columns.len() } else { columns.len().div_ceil(8) },
                check: (base + total, g),
            }
        })
        .collect();
    units.extend(plans.iter().enumerate().map(|(q, p)| (q, p.check.0, p.check.1, true)));
    // The batches, packed in one dispatch, one a task.
    let packing: Vec<(usize, usize)> = plans
        .iter()
        .enumerate()
        .filter(|(_, p)| !p.alone)
        .flat_map(|(q, p)| (0..p.width).map(move |b| (q, b)))
        .collect();
    let mut packed: Vec<Vec<K8>> = parallel::map_collect(packing.len(), |k| {
        let (q, b) = packing[k];
        let columns = jobs[q].columns();
        let columns = &columns[8 * b..(8 * b + 8).min(columns.len())];
        (0..columns[0].len())
            .map(|i| K8(std::array::from_fn(|l| columns.get(l).map_or(F64::ZERO, |c| c[i]))))
            .collect()
    });
    let mut batches: Vec<Vec<Vec<K8>>> = plans.iter().map(|_| Vec::new()).collect();
    for (&(q, _), batch) in packing.iter().zip(packed.drain(..)) {
        batches[q].push(batch);
    }
    // The limbs, every word written by the fills (the pieces tile them), each zeroed by a worker.
    let lengths: Vec<usize> = plans.iter().flat_map(|p| [p.total; 3]).collect();
    let mut flat: Vec<Vec<F64>> = parallel::map_collect(lengths.len(), |k| vec![F64::ZERO; lengths[k]]);
    let mut limbs: Vec<[Vec<F64>; 3]> = Vec::with_capacity(plans.len());
    while !flat.is_empty() {
        let rest = flat.split_off(3);
        let [a, b, c]: [Vec<F64>; 3] = flat.try_into().expect("three limbs");
        limbs.push([a, b, c]);
        flat = rest;
    }
    let mut checks: Vec<[Vec<F64>; 3]> = plans
        .iter()
        .map(|p| std::array::from_fn(|_| vec![F64::ZERO; 1 << p.check.1]))
        .collect();
    let unit_bytes = |&(q, _, p, _): &(usize, usize, usize, bool)| plans[q].width << p << if plans[q].alone { 3 } else { 6 };
    {
        // The fills, piece by piece (`fill_first[u]..fill_first[u + 1]`): the piece, its runs, and its outputs, the
        // limbs (or the checks) split in the order of the pieces.
        let mut tails: Vec<[&mut [F64]; 3]> = limbs.iter_mut().map(|l| l.each_mut().map(|v| &mut v[..])).collect();
        let mut check_tails: Vec<[&mut [F64]; 3]> = checks.iter_mut().map(|l| l.each_mut().map(|v| &mut v[..])).collect();
        let mut fills: Vec<(usize, Range<usize>, Mutex<Option<[&mut [F64]; 3]>>)> = Vec::new();
        let mut fill_first = vec![0];
        for (u, &(q, _, p, check)) in units.iter().enumerate() {
            let size = 1usize << p;
            let tail = if check { &mut check_tails[q] } else { &mut tails[q] };
            let mut piece: [&mut [F64]; 3] = tail.each_mut().map(|t| {
                let (head, rest) = std::mem::take(t).split_at_mut(size);
                *t = rest;
                head
            });
            for b in 0..size.div_ceil(8 * FILL_RUNS) {
                let runs = b * FILL_RUNS..((b + 1) * FILL_RUNS).min(size.div_ceil(8));
                let words = (8 * runs.len()).min(piece[0].len());
                let out = piece.each_mut().map(|t| {
                    let (head, rest) = std::mem::take(t).split_at_mut(words);
                    *t = rest;
                    head
                });
                fills.push((u, runs, Mutex::new(Some(out))));
            }
            fill_first.push(fills.len());
        }
        // Each piece's transforms, shared by its fills; the last of them gives the buffers back.
        let outputs: Vec<Vec<Mutex<Option<Arc<Values>>>>> = units
            .iter()
            .map(|&(q, ..)| (0..plans[q].width).map(|_| Mutex::new(None)).collect())
            .collect();
        let data: Vec<OnceLock<Box<dyn Any + Send + Sync>>> = units.iter().map(|_| OnceLock::new()).collect();
        let schedule = Mutex::new(Schedule {
            next_unit: 0,
            next_task: 0,
            live: 0,
            ready: Default::default(),
            transforms_left: units.iter().map(|&(q, ..)| plans[q].width + 1).collect(),
            fills_left: (0..units.len()).map(|u| fill_first[u + 1] - fill_first[u]).collect(),
            fills_done: 0,
            free: Vec::new(),
        });
        let total_fills = fills.len();
        // Set when a task panics: its counters are never updated, so the others would wait for it forever; they stop
        // instead, and the pool re-raises the panic.
        let aborted = AtomicBool::new(false);
        // The next task: a ready fill first, else the next transform if its piece's buffers fit (or nothing is live).
        let next = |s: &mut Schedule| -> Job {
            if aborted.load(Ordering::Acquire) {
                return Job::Done;
            }
            if let Some(f) = s.ready.pop_front() {
                return Job::Fill(f);
            }
            if s.fills_done == total_fills {
                return Job::Done;
            }
            if s.next_unit == units.len() {
                return Job::Wait;
            }
            let u = s.next_unit;
            let (q, ..) = units[u];
            if s.next_task == 0 {
                let bytes = unit_bytes(&units[u]);
                if s.live > 0 && s.live + bytes > LIVE_BYTES {
                    return Job::Wait;
                }
                s.live += bytes;
            }
            let c = s.next_task;
            s.next_task += 1;
            if s.next_task > plans[q].width {
                (s.next_unit, s.next_task) = (u + 1, 0);
            }
            if c == plans[q].width {
                return Job::Transform(u, c, None);
            }
            let alone = plans[q].alone;
            let buf = match s.free.iter().rposition(|b| matches!(b, Values::Words(_)) == alone) {
                Some(i) => s.free.swap_remove(i),
                None if alone => Values::Words(Vec::new()),
                None => Values::Rows(Vec::new()),
            };
            Job::Transform(u, c, Some(buf))
        };
        let lock = || schedule.lock().expect("the schedule");
        parallel::for_each(parallel::num_threads(), |_| {
            let _abort = AbortOnPanic(&aborted);
            let mut job = next(&mut lock());
            loop {
                match job {
                    Job::Done => break,
                    Job::Wait => {
                        (0..64).for_each(|_| std::hint::spin_loop());
                        job = next(&mut lock());
                    }
                    Job::Transform(u, c, buf) => {
                        let (q, first, p, _) = units[u];
                        let size = 1usize << p;
                        match buf {
                            None => {
                                if data[u].set(jobs[q].piece(first, p)).is_err() {
                                    unreachable!("a piece's data computed once");
                                }
                            }
                            Some(mut buf) => {
                                match &mut buf {
                                    Values::Words(words) => {
                                        if words.len() < size {
                                            words.resize(size, F64::ZERO);
                                        }
                                        ntt::on_coset_prefix_serial(jobs[q].columns()[c], first, &mut words[..size]);
                                    }
                                    Values::Rows(rows) => {
                                        if rows.len() < size {
                                            rows.resize(size, K8::ZERO);
                                        }
                                        piece_rows_into(&batches[q][c], first, p, &mut rows[..size]);
                                    }
                                }
                                *outputs[u][c].lock().expect("a piece's transform") = Some(Arc::new(buf));
                            }
                        }
                        let mut s = lock();
                        s.transforms_left[u] -= 1;
                        if s.transforms_left[u] == 0 {
                            s.ready.extend(fill_first[u]..fill_first[u + 1]);
                        }
                        job = next(&mut s);
                    }
                    Job::Fill(f) => {
                        let (u, ref runs, ref out) = fills[f];
                        let (q, _, p, _) = units[u];
                        let size = 1usize << p;
                        let held: Vec<Arc<Values>> = outputs[u]
                            .iter()
                            .map(|v| v.lock().expect("a piece's transform").clone().expect("the piece's transforms"))
                            .collect();
                        let values = held.iter().map(|v| &**v);
                        let (rows, words): (Vec<&[K8]>, Vec<&[F64]>) = if plans[q].alone {
                            let words = values.map(|v| match v {
                                Values::Words(w) => &w[..size],
                                Values::Rows(_) => unreachable!("a column's values"),
                            });
                            (Vec::new(), words.collect())
                        } else {
                            let rows = values.map(|v| match v {
                                Values::Rows(r) => &r[..size],
                                Values::Words(_) => unreachable!("a batch's rows"),
                            });
                            (rows.collect(), Vec::new())
                        };
                        let points = if plans[q].alone { Points::Alone(&words) } else { Points::Batches(&rows) };
                        let piece = data[u].get().expect("the piece's data");
                        let out = out.lock().expect("a fill's outputs").take().expect("each fill once");
                        jobs[q].fill(&**piece, &points, runs.clone(), out);
                        drop(points);
                        drop((rows, words));
                        drop(held);
                        let mut s = lock();
                        s.fills_left[u] -= 1;
                        s.fills_done += 1;
                        if s.fills_left[u] == 0 {
                            // The piece's buffers, for the pieces after it (its other fills are done).
                            s.live -= unit_bytes(&units[u]);
                            for v in &outputs[u] {
                                let held = v.lock().expect("a piece's transform").take().expect("the piece's transforms");
                                s.free.push(Arc::into_inner(held).expect("the piece's fills are done"));
                            }
                        }
                        job = next(&mut s);
                    }
                }
            }
        });
    }
    drop(batches);
    {
        let mut parts: Vec<ntt::PrefixCols> = limbs
            .iter_mut()
            .zip(&plans)
            .map(|(l, p)| ntt::PrefixCols {
                cols: l.iter_mut().map(|v| &mut v[..]).collect(),
                sizes: p.sizes.clone(),
                base: p.base,
            })
            .collect();
        ntt::interpolate_prefix_many(&mut parts);
    }
    // One more block of points each: the numerator's quotient there against the interpolant's values.
    let at: Vec<(&[F64], usize, usize)> = limbs
        .iter()
        .zip(&plans)
        .flat_map(|(l, p)| l.iter().map(move |v| (&v[..], p.check.0, p.check.1)))
        .collect();
    let values = ntt::on_coset_prefix_each(&at);
    limbs
        .into_iter()
        .zip(plans.iter().zip(checks))
        .zip(values.chunks(3))
        .map(|((l, (plan, check)), values)| Quotient::new(l, plan.count, values == check))
        .collect()
}

/// Batch `src` (novel coefficients, `2^r` rows) on the piece `ω_first + V_p` (`3 ≤ p ≤ r`), into `dst` (`2^p` rows), by
/// the calling worker alone, each eight rows transposed ([`Points::Batches`]).
fn piece_rows_into(src: &[K8], first: usize, p: usize, dst: &mut [K8]) {
    assert_eq!(dst.len(), 1 << p);
    if dst.len() == src.len() {
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

/// The most columns (the heap's three included) [`table_leaf_numerator`]'s point-by-point numerator gathers.
const SCALAR_COLUMNS: usize = 128;

/// Table `t`'s leaf quotient's numerator, for [`prefix_quotients`]: the quotient is `((R P + P') Z_pad + (R + 1) Z_act)
/// / w_r`, `R` the heap's block (its novel coefficients `r_novel`, limb by limb), `P`, `P'` the row's pull and push
/// products, `Z_act`, `Z_pad` the vanishing polynomials of the active and the padding rows' fixed cosets (SPEC.md §13,
/// F1b; the verifier checks it times `Z_act`).
pub fn table_leaf_numerator<'a>(
    trace: &Trace,
    t: usize,
    c1: &'a C1Polys,
    bus: &'a Bus,
    r_novel: &'a [Vec<F64>; 3],
    count: u64,
) -> Box<dyn Numerator + 'a> {
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
        return Box::new(Prefix::new(
            r,
            count,
            columns,
            move |first, _| piece_of(first, r),
            move |d: &Piece, v: &Points, j| {
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
        ));
    }
    let both = PullPush8::new(&bus.pull[t], &bus.push[t], |c| slots[c]);
    Box::new(Prefix::new(
        r,
        count,
        columns,
        move |first, _| piece_of(first, r),
        move |d: &Piece, v: &Points, j| {
            let col = |s: Slot| v.at(s, j);
            let (p, p2) = both.at(col);
            let za = Ex8::from_k(z_act.at(d.first, j));
            let zp = z_pad.at(d.first, j);
            let numerator = v.e(heap, j) * (p.mul_k(zp) + za) + p2.mul_k(zp) + za;
            numerator.mul_k(Kx8::splat(d.w_r_inv))
        },
    ))
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
        let (at, at_s): (Vec<Vec<F64>>, Vec<Vec<F64>>) = if e <= 6 {
            // A few points (the check's): the six folds' partial sums in one dispatch.
            let mut both = ntt::on_coset_prefix_each(
                &limbs
                    .iter()
                    .map(|&l| (l, first, e))
                    .chain(limbs.iter().map(|&l| (l, first >> 1, e - 1)))
                    .collect::<Vec<_>>(),
            );
            let at_s = both.split_off(3);
            (both, at_s)
        } else {
            (ntt::on_coset_prefix_cols(&limbs, first, e), ntt::on_coset_prefix_cols(&limbs, first >> 1, e - 1))
        };
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
    let mut limbs: [Vec<F64>; 3] = std::array::from_fn(|_| ntt::zeros(total));
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
    let holds = ntt::on_coset_prefix_each(&limbs.each_ref().map(|l| (&l[..], base + total, g))) == check;
    Quotient::new(limbs, (1u64 << h) + 1, holds)
}

/// One table's part of `Q_W`, `Σ γ^i W_i / w_r` over its constraints, before its [`Numerator`]: its powers of `γ`
/// and, for `SHA3`, its lane copies combined by their powers.
pub struct ConstraintPart {
    r: usize,
    count: u64,
    /// JUMP's two powers and its columns `v_cond`, `w`, `b`.
    jump: Option<(F192, F192, usize, usize, usize)>,
    counters: Vec<usize>,
    g_counter: F192,
    t: usize,
    /// `SHA3`'s `Σ g_j copy_j` (novel coefficients) and `Σ g_j v_j` (`q_flock`'s slots, as tables of the rows), three
    /// limbs each, and the coordinates' functionals.
    combined: Option<([Vec<F64>; 3], [Vec<F64>; 3], Vec<Vec<leanvm_statement::K>>)>,
}

/// `Q_W`'s parts: the tables' (in the verifier's order of powers), and the public input's three powers.
pub struct ConstraintParts {
    pub tables: Vec<ConstraintPart>,
    pub publics: [F192; 3],
}

/// The tables' parts of `Q_W` and the public input's powers of `γ`, in the verifier's order. `Q_W` is
/// `Σ_i γ^i M_i W_i / w_(r_W)`, in the verifier's order of powers: per table, JUMP's two constraints, the counters,
/// the `SHA3` table's fifty lane copies (`in_16`'s with `END_BIT`: `copy + port + END_BIT`); then the public input's
/// three limbs. As `M_i = w_(r_W) / w_r`, it is the sum of each table's `Σ γ^i W_i / w_r` and the public input's part,
/// each a quotient of its own on its own points (`prefix_quotients`, `public_part`, `sum_parts`).
pub fn constraint_parts(trace: &Trace, qflock: &[F64], c1: &C1Polys, gamma: F192) -> ConstraintParts {
    let mut power = F192::ONE;
    let mut next = || {
        let current = power;
        power *= gamma;
        current
    };
    let row_bits = crate::verifier::QFLOCK_ROW_BITS;
    let mut parts = Vec::new();
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
        let combined = (!copies.is_empty()).then(|| {
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
            (copy, table, crate::domain::coordinate_functionals(r))
        });
        parts.push(ConstraintPart {
            r,
            count: most + 1,
            jump,
            counters,
            g_counter,
            t,
            combined,
        });
    }
    ConstraintParts {
        tables: parts,
        publics: [next(), next(), next()],
    }
}

impl ConstraintPart {
    /// Its numerator, for [`prefix_quotients`]: the inverse, the counters, JUMP's three columns, `SHA3`'s copies
    /// combined by their powers (three limbs); a piece's data `1 / w_r` and `SHA3`'s `Σ g_j ℓ_j`, the slots'
    /// multilinear at `y(x) = y(ω_first) + bits(i)`, a shifted cube (at least a run long).
    pub fn numerator<'a>(&'a self, c1: &'a C1Polys) -> Box<dyn Numerator + 'a> {
        let (r, t) = (self.r, self.t);
        let cols = &c1.tables[t];
        let mut columns: Vec<&[F64]> = vec![&c1.inverses[t].novel];
        columns.extend(self.counters.iter().map(|&c| &cols[c].novel[..]));
        let jump_slots = self.jump.map(|(g1, g2, cond, w, b)| {
            let at = columns.len();
            columns.extend([&cols[cond].novel[..], &cols[w].novel[..], &cols[b].novel[..]]);
            (ESplat::new(g1), ESplat::new(g2), slot(at), slot(at + 1), slot(at + 2))
        });
        let copy_slots: Option<[Slot; 3]> = self.combined.as_ref().map(|(copy, ..)| {
            let at = columns.len();
            columns.extend(copy.iter().map(|l| &l[..]));
            std::array::from_fn(|k| slot(at + k))
        });
        let counter_slots: Vec<Slot> = (1..=self.counters.len()).map(slot).collect();
        let combined = &self.combined;
        let piece = move |first: usize, e: usize| {
            let cube = combined.as_ref().map(|(_, table, functionals)| {
                let delta = coordinates_k(omega(first), functionals);
                table
                    .iter()
                    .map(|l| {
                        let mut c = ntt::shifted_cube_serial(l, &delta, e);
                        c.resize(c.len().max(8), F64::ZERO);
                        c
                    })
                    .collect::<Vec<Vec<F64>>>()
            });
            (piece_of(first, r), cube)
        };
        let one = Kx8::splat(F64::ONE);
        let g_counter = ESplat::new(self.g_counter);
        Box::new(Prefix::new(
            r,
            self.count,
            columns,
            piece,
            move |(d, cube): &(Piece, Option<Vec<Vec<F64>>>), v: &Points, j| {
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
            },
        ))
    }
}

/// `Q_W`'s public part: `(mem_k + I_k) / w_1` at the powers `gs`, `I_k(x) = low + x (low + high)`, of degree below
/// `2^lm - 2`.
pub fn public_part(trace: &Trace, c1: &C1Polys, gs: [F192; 3], public_lines: [(F64, F64); 3]) -> Quotient {
    let lm = trace.log_memory;
    let columns: Vec<&[F64]> = (0..3).map(|k| &c1.memory[k].novel[..]).collect();
    let piece = |first: usize, e: usize| {
        // 1 / w_1(x) = 1 / ω_((first + i) >> 1), shared by `i` and `i ^ 1` (at least a run's).
        let len = ((1usize << e) / 2).max(4);
        let mut inverses: Vec<F64> = parallel::map_collect(len, |q| omega((first >> 1) + q));
        invert(&mut inverses);
        (omega(first), inverses)
    };
    let gs = gs.map(ESplat::new);
    let lanes = Kx8::new(std::array::from_fn(omega));
    prefix_quotient(
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
    )
}

/// The sum of quotients, coefficient by coefficient, in one dispatch: `count` the result's.
pub fn sum_parts(mut parts: Vec<Quotient>, count: u64) -> Quotient {
    let holds = parts.iter().all(|q| q.holds());
    let longest = (0..parts.len())
        .max_by_key(|&i| parts[i].novel[0].len())
        .expect("a part");
    let mut out = parts.swap_remove(longest);
    const CHUNK: usize = 1 << 14;
    let [a, b, c] = &mut out.novel;
    parallel::chunks_mut3(a, b, c, CHUNK, |i, a, b, c| {
        let lo = i * CHUNK;
        for (k, dst) in [a, b, c].into_iter().enumerate() {
            for p in &parts {
                let src = &p.novel[k];
                if lo < src.len() {
                    dst.iter_mut().zip(&src[lo..]).for_each(|(x, &y)| *x += y);
                }
            }
        }
    });
    Quotient::new(out.novel, count, holds)
}

/// E elements as their three limbs.
fn limbs_of(values: &[F192]) -> [Vec<F64>; 3] {
    [0, 1, 2].map(|k| parallel::map_collect(values.len(), |i| F64([values[i].c0, values[i].c1, values[i].c2][k])))
}

/// Batch inversion in K (Montgomery's trick per chunk); every entry must be nonzero.
fn invert(data: &mut [F64]) {
    parallel::chunks_mut(data, 1 << 12, |_, chunk| invert_chunk(chunk));
}

/// [`invert`] by the calling worker alone (one chunk): the same inverses.
fn invert_chunk(chunk: &mut [F64]) {
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

    /// A task of [`prefix_quotients`] that panics (in a piece's data, or in a fill) makes the call panic, rather than
    /// leave the other workers waiting for it forever.
    #[test]
    fn a_panicking_task_panics_the_call() {
        // 3,000 points from `2^12` on: blocks of `2^11` and `2^10` points, so pieces at 4096, 5120 and 6144 (the
        // panicking one the second), each of 128 runs, and the check's block.
        let r = 10;
        let columns: Vec<Vec<F64>> = (0..2).map(|c| (0..1u64 << r).map(|i| F64(i ^ c)).collect()).collect();
        for (bad_piece, bad_fill) in [(true, false), (false, true)] {
            let columns = columns.clone();
            let (tx, rx) = std::sync::mpsc::channel();
            std::thread::spawn(move || {
                let numerator = Prefix::new(
                    r,
                    3000,
                    columns.iter().map(|c| &c[..]).collect(),
                    move |first, _| assert!(!(bad_piece && first == 5 << 10), "an injected panic in a piece's data"),
                    move |_: &(), _: &Points, j| {
                        assert!(!(bad_fill && j == 5), "an injected panic in a fill");
                        Ex8::splat(F192::ZERO)
                    },
                );
                let jobs: [&dyn Numerator; 1] = [&numerator];
                let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| prefix_quotients(&jobs)));
                tx.send(outcome.is_err()).expect("the test waits");
            });
            // Under Miri (whose clock runs with the interpreted code, slowly) the test waits for good, else it fails.
            let wait = std::time::Duration::from_secs(if cfg!(miri) { u32::MAX as u64 } else { 120 });
            let panicked = rx.recv_timeout(wait).expect("prefix_quotients returned or panicked rather than hung");
            assert!(panicked, "the injected panic (piece {bad_piece}, fill {bad_fill}) reached the caller");
        }
    }
}
