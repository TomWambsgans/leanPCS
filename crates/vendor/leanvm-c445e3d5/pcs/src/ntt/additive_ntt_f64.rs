// Vendored from leanVM (https://github.com/leanEthereum/leanVM), commit c445e3d51a5a85031df47240595698f3b24897bf, file crates/pcs/src/ntt/additive_ntt_f64.rs.
// MIT OR Apache-2.0 (see LICENSE-MIT, LICENSE-APACHE and AGENTS.md at the repository root).
// Modified here: per-layer twiddle offsets and `AdditiveNttF64::replica`, so that a codeword can be encoded one
// replica at a time (the same words, in half the memory at rate 1/2); and `encode_interleaved_rows_in_place` /
// `encode_interleaved_rows_with`, whose deep pass runs only on the blocks holding a wanted row.
// Also modified here (an aliasing fix, to report upstream): the in-place encodes
// (`encode_interleaved_in_place`, `encode_interleaved_in_place_with`, `encode_interleaved_rows_in_place`) took the
// message pointer from `data` and then lent `data` out as a `&mut` (LLVM `noalias`) while the first pass and
// `replicate` read through that pointer, which Miri reports as undefined behavior under Stacked Borrows and Tree
// Borrows. The message is now [`Message::InPlace`], and each pass that reads it derives its pointer from the
// buffer it was handed. The codewords are the same, word for word.
// Also modified here, for speed, every codeword unchanged: the two-sweep encodes (`encode_two_sweep_with`,
// `encode_two_sweep_into`, which needs no work buffer: a tile is finished where its first sweep wrote it,
// `encoded_rows_two_sweep`), which encode a lane-major or row-major message as it lies, a batch of replicas per read
// of it, the transpose fused into the second sweep; on AVX-512, the fused layers run slab by slab in registers
// (`slabs_avx512`), the tiles transposed eight by eight in registers (`transpose_8x8`), and with GFNI the
// butterfly's reduction takes byte maps for shifts (`gfni_reduce`); and sub-blocks too short to fill the hash's
// batches hand their rows over afterwards. The first sweep gathers rows of up to 64 words where its group fits a
// core's L2 (`WIDE_GATHER_WORDS`), and copies them inline (`copy_words`, `stream_words`). On AVX-512 the transposed
// butterfly is one pass (`transposed_butterfly_lanes`).
// Added here, every codeword unchanged: the two-sweep encodes of a lane-major message given block by block
// (`encode_two_sweep_blocks_with`, `encoded_rows_two_sweep_blocks`; the message's `Source`), for a commitment that
// skips its all-zero lanes, and into a kept codeword of those lanes alone (`encode_two_sweep_blocks_into`).
//! Additive NTT over GF(2^64) in the Lin-Chung-Han novel polynomial basis.
//!
//! It is the Reed-Solomon encoder of every WHIR commitment over K = F_{2^64}.
//!
//! - Layers run neighbors-last: layer 0 pairs rows half the domain apart.
//! - Many independent transforms share one buffer, interleaved row by row.
//! - The E-valued encodes of deeper WHIR levels reuse it, one F64 lane per F192 coefficient.
//! - Large transforms are bound by memory bandwidth, so the driver minimizes sweeps of the buffer.

use std::cell::RefCell;

use primitives::field::F64;
use primitives::log2_strict_usize;
use primitives::stream::Stream;

/// Table of the normalized subspace polynomials at the basis.
///
/// - Row `i` holds `s_i(b_j)` for every basis element `b_j` with `j >= i`.
/// - Each row is scaled so that its first entry is one.
fn generate_evals_from_subspace(basis: &[F64]) -> Vec<Vec<F64>> {
    let l = basis.len();
    let mut evals: Vec<Vec<F64>> = Vec::with_capacity(l);
    evals.push(basis.to_vec());
    for i in 1..l {
        let mut row = Vec::with_capacity(l - i);
        for k in 1..evals[i - 1].len() {
            let val = evals[i - 1][k] * (evals[i - 1][k] + evals[i - 1][0]);
            row.push(val);
        }
        evals.push(row);
    }
    for row in evals.iter_mut() {
        let inv = row[0].inv();
        for v in row.iter_mut() {
            *v *= inv;
        }
    }
    evals
}

/// `Σ_j bit_j(idx) · basis[j]`.
#[inline]
fn span_get(basis: &[F64], idx: usize) -> F64 {
    let mut acc = F64::ZERO;
    for (j, &b) in basis.iter().enumerate() {
        if (idx >> j) & 1 == 1 {
            acc += b;
        }
    }
    acc
}

/// Receives a finished block of codeword rows, as `(first_row, rows)`.
pub type RowSink<'a> = dyn Fn(usize, &[F64]) + Sync + 'a;

/// Where an encode's message is, which its first pass reads.
#[derive(Clone, Copy)]
enum Message<'a> {
    /// The buffer's own first replica.
    ///
    /// No pointer to it is taken before the buffer is lent to a pass: each pass that reads the message derives
    /// its pointer from the `&mut` it was handed, so that the pointer stays valid while the pass writes the
    /// buffer. A pointer taken before the buffer was lent would be invalidated by that `&mut` (`noalias`).
    InPlace,
    /// A message of its own, one replica long, disjoint from the codeword.
    Separate(&'a [F64]),
}

/// Additive NTT over F_{2^64} with the standard polynomial-basis subspace
/// `{1, x, x², …}`: the F_2-subspace is `{0, 1, …, 2^ℓ−1}` under the natural
/// integer encoding, exactly as in the extension-field version (whose domain already
/// lived inside this very subfield).
#[derive(Clone, Debug)]
pub struct AdditiveNttF64 {
    evals: Vec<Vec<F64>>,
    /// What each layer's twiddles add, all zero when empty: a transform of one replica of a larger codeword
    /// ([`Self::replica`]).
    offsets: Vec<F64>,
}

impl AdditiveNttF64 {
    fn new(basis: &[F64]) -> Self {
        Self {
            evals: generate_evals_from_subspace(basis),
            offsets: Vec::new(),
        }
    }

    /// The transform of replica `replica` alone of a codeword this one encodes at log inverse rate
    /// `log_inv_rate`: `2^(d - log_inv_rate)` rows whose layer `L` is this transform's layer `L + log_inv_rate`
    /// on that replica's blocks, so that encoding the message with it leaves exactly the rows
    /// `[replica · 2^(d - log_inv_rate), (replica + 1) · 2^(d - log_inv_rate))` of the whole codeword.
    ///
    /// A twiddle is F_2-linear in its block index, and at layer `L + log_inv_rate` a block of the replica has
    /// index `replica · 2^L + b`: the replica adds one constant per layer.
    pub fn replica(&self, log_inv_rate: usize, replica: usize) -> Self {
        let l = self.log_domain_size();
        assert!(log_inv_rate <= l && replica < 1 << log_inv_rate);
        Self {
            evals: self.evals[..l - log_inv_rate].to_vec(),
            offsets: (0..l - log_inv_rate)
                .map(|layer| self.twiddle(layer + log_inv_rate, replica << layer))
                .collect(),
        }
    }

    /// What layer `layer`'s twiddles add.
    #[inline]
    fn offset(&self, layer: usize) -> F64 {
        self.offsets.get(layer).copied().unwrap_or(F64::ZERO)
    }

    /// Standard NTT with basis `{1, x, …, x^(dim-1)}`. Requires `dim ≤ 63` so
    /// the evaluation domain (and the twiddles) stay inside F_{2^64} without
    /// wrap; far beyond any codeword size in use.
    pub fn standard(dim: usize) -> Self {
        assert!(dim <= 63, "standard NTT requires dim ≤ 63");
        let basis: Vec<F64> = (0..dim).map(|i| F64(1u64 << i)).collect();
        Self::new(&basis)
    }

    pub fn log_domain_size(&self) -> usize {
        self.evals.len()
    }

    /// Twiddle of one block at one layer.
    ///
    /// - It is `s_i(sum_j bit_j(block) * b_(i+1+j))`, with `i = L - layer - 1` on a `2^L`-point domain.
    /// - The normalized `s_i` is F_2-linear, so this is a subset sum of row `i` of the table.
    pub fn twiddle(&self, layer: usize, block: usize) -> F64 {
        let v = &self.evals[self.log_domain_size() - layer - 1];
        span_get(&v[1..], block) + self.offset(layer)
    }

    /// The seven twiddles a radix-8 group needs, breadth-first: layer `layer`,
    /// then `layer + 1` (one per half), then `layer + 2` (one per quarter).
    ///
    /// `span_get` is F_2-linear in the block index, so the six deeper twiddles are
    /// the block's own contribution plus a fixed correction per sub-block index:
    /// one scan of the three basis rows replaces seven.
    pub(crate) fn twiddles_radix8(&self, layer: usize, block: usize) -> [F64; 7] {
        let l = self.log_domain_size();
        let (v0, v1, v2) = (
            &self.evals[l - layer - 1],
            &self.evals[l - layer - 2],
            &self.evals[l - layer - 3],
        );
        let (mut t0, mut a, mut c) = (self.offset(layer), self.offset(layer + 1), self.offset(layer + 2));
        for j in 0..layer {
            if (block >> j) & 1 == 1 {
                t0 += v0[1 + j];
                a += v1[2 + j];
                c += v2[3 + j];
            }
        }
        let (d, e0, e1) = (v1[1], v2[1], v2[2]);
        [t0, a, a + d, c, c + e0, c + e1, c + e0 + e1]
    }

    /// RS-encode a message already stored in the codeword's first replica.
    ///
    /// # Overview
    ///
    /// - The message fills the first `1 / 2^r` of the buffer, `r` the log inverse rate.
    /// - It is row-major: word `row * n + lane` for `n` interleaved lanes.
    /// - The buffer ends as `2^r` copies of it, each transformed from layer `r` on.
    ///
    /// # Why the replication is free
    ///
    /// - A butterfly whose bottom input is zero copies its top input to both outputs.
    /// - So the first `r` layers on the zero-padded message leave `2^r` copies of it.
    /// - The first pass therefore reads its rows from the message itself.
    /// - No pass fills the replicas only to read them back.
    ///
    /// # Why the transpose stays separate
    ///
    /// - A lane-major caller transposes its message into place first.
    /// - The transpose wants one long contiguous run per lane.
    /// - The first pass wants hundreds of scattered rows at once.
    pub fn encode_interleaved_in_place(&self, data: &mut [F64], num_ntts: usize, log_inv_rate: usize) {
        // The message is the buffer's own first replica.
        self.transform(data, num_ntts, log_inv_rate, Some(Message::InPlace), None, None);
    }

    /// [`Self::encode_interleaved_in_place`] for the rows `rows` (sorted, distinct) alone: those rows are the
    /// codeword's, every other row is left part-transformed.
    ///
    /// A row's value is the butterflies of the blocks that hold it, one per layer, so the deep pass runs only on
    /// the blocks holding a wanted row: a few hundred rows of millions leave the deep layers a few full sweeps'
    /// work rather than one per layer.
    pub fn encode_interleaved_rows_in_place(
        &self,
        data: &mut [F64],
        num_ntts: usize,
        log_inv_rate: usize,
        rows: &[usize],
    ) {
        assert!(rows.is_sorted_by(|a, b| a < b), "sorted, distinct rows");
        self.transform(data, num_ntts, log_inv_rate, Some(Message::InPlace), None, Some(rows));
    }

    /// Encode in place, handing `on_rows` every finished block of rows.
    ///
    /// - It is called as `on_rows(first_row, rows)`, from pool tasks.
    /// - Each row is handed over exactly once.
    /// - Blocks are aligned, and all of one power-of-two size.
    /// - A block is handed over while its rows are still in cache.
    pub fn encode_interleaved_in_place_with(
        &self,
        data: &mut [F64],
        num_ntts: usize,
        log_inv_rate: usize,
        on_rows: &RowSink<'_>,
    ) {
        let msg = Some(Message::InPlace);
        self.transform(data, num_ntts, log_inv_rate, msg, Some(on_rows), None);
    }

    /// RS-encode a message held in a buffer of its own, handing `on_rows` every finished block of rows.
    ///
    /// - The result equals encoding in place.
    /// - Every codeword word is written before it is read, so the codeword may start uninitialized.
    /// - The blocks are as for the in-place encode.
    ///
    /// # Panics
    ///
    /// Panics unless the codeword is exactly `2^r` messages long.
    pub fn encode_interleaved_with(
        &self,
        data: &mut [F64],
        msg: &[F64],
        num_ntts: usize,
        log_inv_rate: usize,
        on_rows: &RowSink<'_>,
    ) {
        assert_eq!(
            msg.len() << log_inv_rate,
            data.len(),
            "the codeword is 2^log_inv_rate messages"
        );
        let msg = Some(Message::Separate(msg));
        self.transform(data, num_ntts, log_inv_rate, msg, Some(on_rows), None);
    }

    /// [`Self::encode_interleaved_with`] for the rows `rows` (sorted, distinct) alone, as
    /// [`Self::encode_interleaved_rows_in_place`] leaves them.
    pub fn encode_interleaved_rows_with(
        &self,
        data: &mut [F64],
        msg: &[F64],
        num_ntts: usize,
        log_inv_rate: usize,
        rows: &[usize],
    ) {
        assert_eq!(
            msg.len() << log_inv_rate,
            data.len(),
            "the codeword is 2^log_inv_rate messages"
        );
        assert!(rows.is_sorted_by(|a, b| a < b), "sorted, distinct rows");
        let msg = Some(Message::Separate(msg));
        self.transform(data, num_ntts, log_inv_rate, msg, None, Some(rows));
    }

    /// Run layers `start..d` of a `2^d`-row transform in as few sweeps of the buffer as possible.
    ///
    /// A large transform is bound by memory bandwidth, so its cost is its number of sweeps.
    ///
    /// # Plan
    ///
    /// ```text
    ///     layers:  start ............ deep_start ............ d
    ///              |---- gathered passes ----|---- deep pass ----|
    ///
    ///     gathered pass:  one task per row group of 2^g rows, 2^(d - layer - g) apart
    ///                     gathered into L2 scratch, all g layers run there, written back
    ///     deep pass:      one task per contiguous sub-block, its layers run in place
    ///                     (or in scratch, when a separate message has to be copied in)
    /// ```
    ///
    /// - When every layer fits one L3-sized sub-block, the deep pass is the whole transform: one sweep.
    /// - Otherwise gathered passes run until the rest fits one L2-sized sub-block.
    /// - With `n` words a row, a block of up to `(L2 words / n)^2` rows then costs two sweeps.
    ///
    /// # With a message
    ///
    /// - The layer-`start` blocks are not in the buffer yet: each is a copy of the message.
    /// - The first pass reads its rows from the message instead.
    ///
    /// # Why block 0 goes last
    ///
    /// - The message may be the buffer's own block 0.
    /// - So a gathered task visits blocks in descending order, and overwrites block 0 last.
    /// - Tasks own disjoint row residues, so no task reads rows another task writes.
    ///
    /// # Finished rows
    ///
    /// - Each deep sub-block is final, and hands its rows to `on_rows` while they are in L2.
    /// - Without a split deep pass, the rows go over in parallel blocks at the end.
    fn transform(
        &self,
        data: &mut [F64],
        num_ntts: usize,
        start: usize,
        msg: Option<Message<'_>>,
        on_rows: Option<&RowSink<'_>>,
        wanted: Option<&[usize]>,
    ) {
        // The buffer is 2^log_d rows of `num_ntts` words.
        assert!(num_ntts > 0);
        assert_eq!(data.len() % num_ntts, 0);
        let log_d = log2_strict_usize(data.len() / num_ntts);
        assert!(log_d <= self.log_domain_size());
        assert!(start <= log_d);

        /// Below this domain the transform is too small to split across the pool.
        const PARALLEL_FLOOR_LOG_D: usize = 12;
        /// Fewest rows a deep sub-block takes when splitting for parallelism.
        const MIN_SUB_LOG: usize = 8;

        // How many rows, as a log, each cache budget holds.
        //
        //     56 lanes:  2^16 / 56 -> 2^10 rows in L2,  2^18 / 56 -> 2^12 rows in L3
        let fit = |words: usize| (words / num_ntts).max(1).ilog2() as usize;
        let (fit2, fit3) = (fit(L2_WORDS), fit(L3_WORDS));

        // From 2^12 rows on, cut at least 2^LOG_SUBS_PER_WORKER deep sub-blocks per worker.
        let par_log = if log_d >= PARALLEL_FLOOR_LOG_D {
            (log2_strict_usize(parallel::num_threads().next_power_of_two()) + LOG_SUBS_PER_WORKER)
                .min(log_d - MIN_SUB_LOG)
        } else {
            0
        };

        // Where the deep pass starts.
        //
        //     every layer fits one L3 sub-block  ->  deep pass only, one sweep
        //     otherwise                          ->  as few gathered passes as an L3 deep pass needs,
        //                                            then the smallest deep pass, at least L2-sized, they leave
        let rest = log_d - start;
        let deep = if rest <= fit3 {
            fit3
        } else {
            fit2.max(rest.saturating_sub((rest - fit3).div_ceil(fit2) * fit2))
        };
        let deep_start = log_d.saturating_sub(deep).max(par_log).max(start);

        // A buffer this large is evicted before the next pass reads it back.
        let stream = data.len() >= STREAM_MIN_WORDS;

        // Phase 1: gathered passes, each at most one L2 group of layers.
        //
        // Only the first one reads the message.
        let mut msg = msg;
        let mut layer = start;
        while layer < deep_start {
            let g = (deep_start - layer).min(fit2);
            self.gathered_pass(data, log_d, num_ntts, layer, g, msg.take(), stream);
            layer += g;
        }

        // Phase 2: replicas a deep-only plan cannot build inside its tasks.
        //
        //     message is block 0 of the buffer  ->  a task could overwrite it while others still copy it
        //     no layer left to run              ->  no deep task would write the buffer at all
        if let Some(m) = msg.take_if(|m| matches!(m, Message::InPlace) || deep_start == log_d) {
            replicate(data, m, data.len() >> start);
        }
        // What is left for the deep pass is a separate message: one in place was replicated above.
        let msg = msg.map(|m| match m {
            Message::Separate(m) => m,
            Message::InPlace => unreachable!("an in-place message is replicated before the deep pass"),
        });

        // A lone sub-block runs on this thread, so its rows go over in parallel afterwards; so do the rows of
        // sub-blocks too short to fill the hash's batches (a deep level at a high rate: a few rows a replica).
        /// Fewest rows, as a log, a deep sub-block hands over by itself.
        const FUSE_MIN_LOG_ROWS: usize = 6;
        let fuse = 0 < deep_start && deep_start < log_d && log_d - deep_start >= FUSE_MIN_LOG_ROWS;
        let deep_rows = on_rows.filter(|_| fuse);

        // Phase 3: the deep pass, one task per contiguous sub-block.
        if deep_start < log_d {
            let log_sub = log_d - deep_start;
            let sub_len = num_ntts << log_sub;
            let block_len = data.len() >> start;
            // The deep layers of one sub-block: all its blocks, or those holding a wanted row.
            let deep_layers = |buf: &mut [F64], sub_idx: usize| match wanted {
                None => self.run_layers(buf, log_d, num_ntts, deep_start, log_d, deep_start, sub_idx),
                Some(rows) => {
                    let first = sub_idx << log_sub;
                    let rows = &rows
                        [rows.partition_point(|&r| r < first)..rows.partition_point(|&r| r < first + (1 << log_sub))];
                    self.run_layers_on_rows(buf, log_d, num_ntts, deep_start, sub_idx, first, rows);
                }
            };
            parallel::chunks_mut(data, sub_len, |sub_idx, sub| match msg {
                // A separate message: build the sub-block in scratch, then write it out once.
                //
                // Streamed out whole, the codeword is written without ever being read.
                Some(m) => with_scratch(sub_len, |scratch| {
                    // A sub-block sits at the same offset in every replica.
                    //
                    //     sub-block at offset off of its replica  <-  message words [off, off + sub_len)
                    let off = (sub_idx * sub_len) % block_len;
                    // The message is one whole replica, and this sub-block ends inside its replica.
                    scratch.copy_from_slice(&m[off..off + sub_len]);
                    deep_layers(scratch, sub_idx);
                    if let Some(f) = deep_rows {
                        f(sub_idx << log_sub, scratch);
                    }
                    if stream {
                        Stream::new().copy(sub, scratch);
                    } else {
                        sub.copy_from_slice(scratch);
                    }
                }),
                // The replicas are already in place: run the layers where they are.
                None => {
                    deep_layers(sub, sub_idx);
                    if let Some(f) = deep_rows {
                        f(sub_idx << log_sub, sub);
                    }
                }
            });
        }

        if let Some(f) = on_rows.filter(|_| !fuse) {
            // Four blocks per worker.
            let log_tasks = (4 * parallel::num_threads()).next_power_of_two().ilog2() as usize;
            let log_rows = log_d - log_tasks.min(log_d);
            parallel::chunks_mut(data, num_ntts << log_rows, |i, rows| f(i << log_rows, rows));
        }
    }

    /// Run layers `layer..layer + g` in one sweep of the buffer, one row group at a time.
    ///
    /// # Row groups
    ///
    /// - A group takes rows `r + i * step`, for `i < 2^g`, of one layer-`layer` block.
    /// - Here `step = 2^(d - layer - g)` and the residue `r < step`.
    /// - Those are exactly the rows the next `g` layers pair with each other.
    ///
    /// ```text
    ///     g = 2, a 16-row block, step = 4, residue r = 1:
    ///
    ///     rows:     0  1  2  3 |  4  5  6  7 |  8  9 10 11 | 12 13 14 15
    ///                  ^              ^              ^              ^
    ///     scratch:  [ row 1, row 5, row 9, row 13 ]   ->  a 4-row transform of its own
    /// ```
    ///
    /// # Why the twiddles still match
    ///
    /// - At layer `L`, a row's block index is `row >> (d - L)`.
    /// - The residue is below `step`, so that shift drops it.
    /// - The scratch transform therefore takes the same twiddles as the full one.
    ///
    /// # With a message
    ///
    /// - Every block's rows come from the message.
    /// - One task takes one residue across all blocks, block 0 last.
    #[allow(clippy::too_many_arguments)]
    fn gathered_pass(
        &self,
        data: &mut [F64],
        log_d: usize,
        num_ntts: usize,
        layer: usize,
        g: usize,
        msg: Option<Message<'_>>,
        stream: bool,
    ) {
        // A group is 2^g rows, `step` rows apart.
        let log_step = log_d - layer - g;
        let (rows, step) = (1usize << g, 1usize << log_step);
        // With a message, a task is one residue across every block.
        // Without one, a task is one (block, residue) pair.
        let n_tasks = if msg.is_some() { step } else { step << layer };
        let base = parallel::SendPtr(data.as_mut_ptr());
        // Where the message's rows are read: the buffer's own block 0 through `base`, which the tasks also write
        // through (a pointer from before `data` was lent here would not be valid while they do), or a separate
        // message, only read.
        let msg = msg.map(|m| match m {
            Message::InPlace => base,
            Message::Separate(m) => parallel::SendPtr(m.as_ptr().cast_mut()),
        });
        // With a message, every block of a residue starts from the same rows: they are gathered
        // once, and each block but the last transforms a copy.
        let n_blocks = if msg.is_some() { 1usize << layer } else { 1 };
        let len = rows * num_ntts;
        parallel::for_each_chunk(n_tasks, |lo, hi| {
            // One L2-resident scratch of 2^g rows (two with copies) serves every group of the task.
            with_scratch(if n_blocks > 1 { 2 * len } else { len }, |scratch| {
                let (gathered, work) = scratch.split_at_mut(len);
                // One fence at the end of the task covers all its streaming stores.
                let stream = stream.then(Stream::new);
                // Row `i` of residue `r`, as a word offset inside its block.
                let row = |r: usize, i: usize| (r + (i << log_step)) * num_ntts;
                let block_off = |block: usize| (block << (log_d - layer)) * num_ntts;
                // Gather: the scattered rows become one contiguous 2^g-row buffer.
                let gather = |dst: &mut [F64], block: usize, r: usize| {
                    let src_row = |i: usize| match msg {
                        Some(m) => m.0.wrapping_add(row(r, i)).cast_const(),
                        None => base.0.wrapping_add(block_off(block) + row(r, i)).cast_const(),
                    };
                    for (i, dst) in dst.chunks_exact_mut(num_ntts).enumerate() {
                        // No prefetcher follows rows this far apart.
                        if i + PREFETCH_ROWS < rows {
                            prefetch(src_row(i + PREFETCH_ROWS), num_ntts);
                        }
                        // SAFETY:
                        // - The message and the codeword both cover every row addressed here.
                        // - Tasks own disjoint residues, so no other task writes these rows.
                        // - A residue reads all its message rows before it writes any of block 0.
                        dst.copy_from_slice(unsafe { std::slice::from_raw_parts(src_row(i), num_ntts) });
                    }
                };
                // Transform, then scatter every row back to its place.
                let finish = |buf: &mut [F64], block: usize, r: usize| {
                    // A (layer + g)-layer domain whose sub-block index is the global block.
                    self.run_layers(buf, layer + g, num_ntts, layer, layer + g, layer, block);
                    for (i, src) in buf.chunks_exact(num_ntts).enumerate() {
                        // SAFETY: this group alone owns these rows of the codeword.
                        let dst = unsafe { base.slice(block_off(block) + row(r, i), num_ntts) };
                        match &stream {
                            Some(s) => s.copy(dst, src),
                            None => dst.copy_from_slice(src),
                        }
                    }
                };
                for t in lo..hi {
                    if msg.is_some() {
                        gather(gathered, 0, t);
                        // Block 0 may be the message itself, so it is written last.
                        for block in (1..n_blocks).rev() {
                            work.copy_from_slice(gathered);
                            finish(work, block, t);
                        }
                        finish(gathered, 0, t);
                    } else {
                        // Task index = block * step + residue.
                        let (block, r) = (t >> log_step, t & (step - 1));
                        gather(gathered, block, r);
                        finish(gathered, block, r);
                    }
                }
            });
        });
    }

    /// Run a range of layers in place over one sub-block of the domain.
    ///
    /// - The domain has `2^d` rows and splits into `2^o` equal sub-blocks.
    /// - The buffer is one of them; its index fixes the global block index, and so the twiddle, of each block.
    /// - Three layers fuse into one radix-8 sweep where blocks are wide enough, then two, then one.
    #[allow(clippy::too_many_arguments)]
    fn run_layers(
        &self,
        buf: &mut [F64],
        log_d: usize,
        num_ntts: usize,
        first_layer: usize,
        end_layer: usize,
        outer_log: usize,
        sub_idx: usize,
    ) {
        let mut layer = first_layer;
        while layer < end_layer {
            // This layer's blocks inside the buffer: how many, and their size in rows and words.
            let num_blocks_in_buf = 1usize << (layer - outer_log);
            let block_size = 1usize << (log_d - layer);
            let block_elems = block_size * num_ntts;
            // A block's index in the whole domain, which picks its twiddle.
            let global = |block_in_buf: usize| sub_idx * num_blocks_in_buf + block_in_buf;

            if layer + 2 < end_layer && block_size >= 8 {
                // Three layers to go and blocks of at least 8 rows: one radix-8 sweep.
                let eighth = block_size >> 3;
                for block_in_buf in 0..num_blocks_in_buf {
                    let t = self.twiddles_radix8(layer, global(block_in_buf));
                    let start = block_in_buf * block_elems;
                    butterfly_interleaved_fused_3layer(&mut buf[start..start + block_elems], &t, eighth, num_ntts);
                }
                layer += 3;
            } else if layer + 1 < end_layer && block_size >= 4 {
                // Two layers to go: one radix-4 sweep.
                let quarter = block_size >> 2;
                for block_in_buf in 0..num_blocks_in_buf {
                    let global_block = global(block_in_buf);
                    let t_outer = self.twiddle(layer, global_block);
                    let t_inner_a = self.twiddle(layer + 1, 2 * global_block);
                    let t_inner_b = self.twiddle(layer + 1, 2 * global_block + 1);
                    let start = block_in_buf * block_elems;
                    butterfly_interleaved_fused_2layer(
                        &mut buf[start..start + block_elems],
                        t_outer,
                        t_inner_a,
                        t_inner_b,
                        quarter,
                        num_ntts,
                    );
                }
                layer += 2;
            } else {
                // One layer: a plain butterfly sweep.
                let block_size_half = block_size >> 1;
                for block_in_buf in 0..num_blocks_in_buf {
                    let twiddle = self.twiddle(layer, global(block_in_buf));
                    let start = block_in_buf * block_elems;
                    butterfly_interleaved_block(
                        &mut buf[start..start + block_elems],
                        twiddle,
                        block_size_half,
                        num_ntts,
                    );
                }
                layer += 1;
            }
        }
    }

    /// [`Self::run_layers`] over a whole `2^log_d`-row domain, leaving only the rows `rows` (sorted, distinct)
    /// final: whole layers while they have no more blocks than there are rows, then the blocks holding one of
    /// them alone.
    fn run_layers_toward(&self, buf: &mut [F64], log_d: usize, num_ntts: usize, rows: &[usize]) {
        let whole = (rows.len().max(1).ilog2() as usize).min(log_d);
        self.run_layers(buf, log_d, num_ntts, 0, whole, 0, 0);
        for layer in whole..log_d {
            let block_size = 1usize << (log_d - layer);
            let mut done = None;
            for &row in rows {
                let block = row / block_size;
                if done == Some(block) {
                    continue;
                }
                done = Some(block);
                let start = block * block_size * num_ntts;
                butterfly_interleaved_block(
                    &mut buf[start..start + block_size * num_ntts],
                    self.twiddle(layer, block),
                    block_size / 2,
                    num_ntts,
                );
            }
        }
    }

    /// [`Self::run_layers`] from `first_layer` to the last, over sub-block `sub_idx` (of `2^first_layer`) whose
    /// first row is `first`, on the blocks that hold one of `rows` (sorted, in the sub-block) alone.
    #[allow(clippy::too_many_arguments)]
    fn run_layers_on_rows(
        &self,
        buf: &mut [F64],
        log_d: usize,
        num_ntts: usize,
        first_layer: usize,
        sub_idx: usize,
        first: usize,
        rows: &[usize],
    ) {
        for layer in first_layer..log_d {
            let block_size = 1usize << (log_d - layer);
            let num_blocks_in_buf = 1usize << (layer - first_layer);
            let mut done = None;
            for &row in rows {
                let block = (row - first) / block_size;
                if done == Some(block) {
                    continue;
                }
                done = Some(block);
                let twiddle = self.twiddle(layer, sub_idx * num_blocks_in_buf + block);
                let start = block * block_size * num_ntts;
                butterfly_interleaved_block(
                    &mut buf[start..start + block_size * num_ntts],
                    twiddle,
                    block_size / 2,
                    num_ntts,
                );
            }
        }
    }

    /// Recover novel-basis coefficients from evaluations with a scalar inverse NTT.
    pub fn inverse_transform(&self, data: &mut [F64]) {
        let log_d = log2_strict_usize(data.len());
        assert!(log_d <= self.log_domain_size());
        for layer in (0..log_d).rev() {
            let num_blocks = 1usize << layer;
            let block_size_half = 1usize << (log_d - layer - 1);
            for block in 0..num_blocks {
                let twiddle = self.twiddle(layer, block);
                let block_start = block << (log_d - layer);
                for idx0 in block_start..(block_start + block_size_half) {
                    let idx1 = idx0 | block_size_half;
                    let u = data[idx0];
                    let new_v = data[idx1] + u;
                    data[idx1] = new_v;
                    data[idx0] = u + new_v * twiddle;
                }
            }
        }
    }
}

// ===================================================================
// Two-sweep encodes: from the message as it lies
// ===================================================================
//
// Every lane of a codeword is a transform of its own, with the same twiddles, and a replica's transform starts
// from the message itself. So the first layers can run on the message as it lies, lane-major (a commitment's
// stack: `n` blocks of `2^d` words, block `b` the codeword's lane `n - 1 - b`) or row-major (a deeper level's
// folded message):
//
//     sweep 1 (gathered):  a task takes a few adjacent residues (lane-major: words of one lane; row-major: whole
//                          rows), 2^g of each, 2^(d-g) rows apart; runs layers 0..g on them for each replica of a
//                          batch, and writes them to that replica's work buffer, laid out as the message
//     sweep 2 (per tile):  a task takes 2^(d-g) consecutive rows of one replica: one contiguous run of every lane
//                          (transposed) or of rows (copied) into a row-major tile in cache; runs layers g..d there
//                          and hands the finished rows on, the work buffer never written back
//
// The row-major encode of a lane-major message transposes it (a read and a write of it), then sweeps the buffer
// twice in place (two reads and two writes): three reads and three writes, against two reads and one write here,
// and a batch of replicas reads the message once. The codeword is the same, word for word: every butterfly is the
// row-major transform's, at the same twiddle.

/// How a message's words lie, for [`AdditiveNttF64::encode_two_sweep_with`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MsgLayout {
    /// `n` blocks of `2^d` words, block `b` the codeword's lane `n - 1 - b`: a commitment's stack.
    LaneMajor,
    /// `2^d` rows of `n` words, in the codeword's lane order: a deeper level's folded message.
    RowMajor,
}

/// Words a first-sweep task takes of each gathered row, at least: two vectors.
const GATHER_WORDS: usize = 16;

/// Words a first-sweep task takes of each gathered row, at most: eight vectors, as long as its group fits a whole
/// core's L2 (`2 * L2_WORDS`). Longer runs of each row read the message and write the work buffer in fewer, longer
/// bursts: the first sweep is bound by the memory (a commitment's at `2^22` rows of 60 lanes: 20 ms a replica at
/// 16 words, 14 ms at 64).
const WIDE_GATHER_WORDS: usize = 64;

/// Words a second-sweep tile may span (its rows by their words): it stays in cache from its fill to its last layer
/// and its rows' hashing.
///
/// - Off Apple silicon, 2^17 words (1 MiB) is a core's L2.
/// - On Apple silicon the transform is compute bound (see [`L2_WORDS`]) and the tile is sized as the deep pass.
#[cfg(not(all(target_arch = "aarch64", target_os = "macos")))]
const TWO_SWEEP_TILE_WORDS: usize = 1 << 17;
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
const TWO_SWEEP_TILE_WORDS: usize = L3_WORDS;

/// The message of a two-sweep encode: whole, laid out as its plan says, or lane-major block by block.
#[derive(Clone, Copy)]
enum Source<'m> {
    Whole(&'m [F64]),
    /// Block `b` of a lane-major message, `2^d` words each.
    Blocks(&'m [&'m [F64]]),
}

impl<'m> Source<'m> {
    fn len(&self) -> usize {
        match self {
            Source::Whole(msg) => msg.len(),
            Source::Blocks(blocks) => {
                let block = blocks.first().map_or(0, |b| b.len());
                assert!(blocks.iter().all(|b| b.len() == block), "blocks of one length");
                block * blocks.len()
            }
        }
    }

    /// The whole message, if it is given whole.
    fn whole(&self) -> Option<&'m [F64]> {
        match self {
            Source::Whole(msg) => Some(msg),
            Source::Blocks(_) => None,
        }
    }

    /// The message from first-sweep task `task`'s first gathered row on, as far as the task reads.
    fn at_task(&self, plan: &TwoSweep, task: usize) -> &'m [F64] {
        match self {
            Source::Whole(msg) => &msg[plan.row_offset(task, 0)..],
            Source::Blocks(blocks) => {
                let (b, r0) = (task / plan.blocks(), (task % plan.blocks()) * plan.per);
                &blocks[b][r0..]
            }
        }
    }
}

/// The plan of a two-sweep encode of one replica: `2^log_rows` rows of `n` words, `g` layers in the first sweep,
/// tiles of `2^t` rows, first-sweep tasks of `per` residues, whose gathered rows are `width` words.
#[derive(Clone, Copy, Debug)]
struct TwoSweep {
    layout: MsgLayout,
    n: usize,
    log_rows: usize,
    g: usize,
    t: usize,
    per: usize,
    width: usize,
}

impl TwoSweep {
    /// The plan, or `None` for a shape two sweeps do not cover (or too small to split across the pool). With `wide`
    /// (an encode's plan), the first sweep gathers rows of up to [`WIDE_GATHER_WORDS`]; the rows of
    /// [`AdditiveNttF64::encoded_rows_two_sweep`], whose first sweep is bound by its transforms, would gain nothing by
    /// them but larger scratch buffers.
    fn new(layout: MsgLayout, n: usize, log_rows: usize, wide: bool) -> Option<Self> {
        if n == 0 || log_rows < 12 {
            return None;
        }
        let mut t = ((TWO_SWEEP_TILE_WORDS / n).max(1).ilog2() as usize).min(log_rows);
        // At least a tile per worker.
        let min_g = parallel::num_threads().next_power_of_two().ilog2() as usize;
        t = t.min(log_rows.saturating_sub(min_g));
        let g = log_rows - t;
        let gather = |words: usize| match layout {
            MsgLayout::LaneMajor => (words, words),
            MsgLayout::RowMajor => {
                let per = words.div_ceil(n).next_power_of_two();
                (per, per * n)
            }
        };
        // A first-sweep group stays in L2, and a tile holds a task's residues.
        let (per, width) = gather(GATHER_WORDS);
        if (width << g) > L2_WORDS || (1usize << t) < per {
            return None;
        }
        // Then the widest rows whose group fits the core's L2.
        let widest = if wide { WIDE_GATHER_WORDS } else { GATHER_WORDS };
        let (per, width) = std::iter::successors(Some(widest), |&w| (w > GATHER_WORDS).then_some(w / 2))
            .map(gather)
            .find(|&(per, width)| (width << g) <= 2 * L2_WORDS && (1usize << t) >= per)
            .unwrap_or((per, width));
        Some(Self {
            layout,
            n,
            log_rows,
            g,
            t,
            per,
            width,
        })
    }

    /// Words of a replica: of the message.
    fn len(&self) -> usize {
        self.n << self.log_rows
    }

    /// Words of a tile.
    fn tile_words(&self) -> usize {
        self.n << self.t
    }

    /// Residue blocks a lane (lane-major) or the message (row-major) splits into.
    fn blocks(&self) -> usize {
        (1usize << self.t) / self.per
    }

    /// First-sweep tasks.
    fn tasks(&self) -> usize {
        match self.layout {
            MsgLayout::LaneMajor => self.n * self.blocks(),
            MsgLayout::RowMajor => self.blocks(),
        }
    }

    /// Where gathered row `i` of task `task` starts in the message (or a work buffer laid out as it): row `i` lies
    /// in tile `i`, [`Self::row_stride`] words past row `i - 1`.
    fn row_offset(&self, task: usize, i: usize) -> usize {
        let first = match self.layout {
            MsgLayout::LaneMajor => {
                let (b, r0) = (task / self.blocks(), (task % self.blocks()) * self.per);
                (b << self.log_rows) + r0
            }
            MsgLayout::RowMajor => task * self.per * self.n,
        };
        first + i * self.row_stride()
    }

    /// Words from one gathered row of a task to the next: a tile's.
    fn row_stride(&self) -> usize {
        match self.layout {
            MsgLayout::LaneMajor => 1 << self.t,
            MsgLayout::RowMajor => self.n << self.t,
        }
    }

    /// Where task `task`'s words of a tile start inside that tile, laid out as the message (lane-major: lane by
    /// lane, each `2^t` words; row-major: row by row).
    fn in_tile(&self, task: usize) -> usize {
        match self.layout {
            MsgLayout::LaneMajor => {
                let (b, r0) = (task / self.blocks(), (task % self.blocks()) * self.per);
                (b << self.t) + r0
            }
            MsgLayout::RowMajor => task * self.per * self.n,
        }
    }

    /// Fill the row-major tile `buf` from a tile laid out as the message: lane `b`'s run at `src[b * stride..]`
    /// (lane-major), or the rows from `src[0..]` (row-major).
    fn fill_tile(&self, buf: &mut [F64], src: &[F64], stride: usize) {
        let rows = 1usize << self.t;
        match self.layout {
            MsgLayout::LaneMajor => transpose_tile(buf, self.n, rows, |b| &src[b * stride..][..rows]),
            MsgLayout::RowMajor => buf.copy_from_slice(&src[..self.tile_words()]),
        }
    }
}

impl AdditiveNttF64 {
    /// RS-encode `msg` (laid out as `layout` says, `2^d` rows of `n` words, one replica long) by this whole
    /// codeword's transform at log inverse rate `log_inv_rate`, handing `on_rows(first_row, rows)` every
    /// finished block of rows of the whole codeword, as [`Self::encode_interleaved_in_place_with`] does (after
    /// [`transpose_lane_major`], for a lane-major message).
    ///
    /// `work` holds a batch of whole replicas (at least one), which the first sweep writes and the second reads:
    /// a batch reads the message once. It is left holding no codeword.
    ///
    /// Returns false, having done nothing, for a shape two sweeps do not cover.
    pub fn encode_two_sweep_with(
        &self,
        work: &mut [F64],
        msg: &[F64],
        layout: MsgLayout,
        n: usize,
        log_inv_rate: usize,
        on_rows: &RowSink<'_>,
    ) -> bool {
        self.encode_two_sweep_of(work, Source::Whole(msg), layout, n, log_inv_rate, on_rows)
    }

    /// [`Self::encode_two_sweep_with`] of the lane-major message whose block `b` is `blocks[b]` (`2^d` words each),
    /// the blocks lying anywhere: the codeword of their concatenation, its lane `blocks.len() - 1 - b` block `b`'s.
    /// Returns false, having done nothing, for a shape two sweeps do not cover, or one with no first sweep.
    pub fn encode_two_sweep_blocks_with(
        &self,
        work: &mut [F64],
        blocks: &[&[F64]],
        log_inv_rate: usize,
        on_rows: &RowSink<'_>,
    ) -> bool {
        let n = blocks.len();
        self.encode_two_sweep_of(work, Source::Blocks(blocks), MsgLayout::LaneMajor, n, log_inv_rate, on_rows)
    }

    fn encode_two_sweep_of(
        &self,
        work: &mut [F64],
        source: Source<'_>,
        layout: MsgLayout,
        n: usize,
        log_inv_rate: usize,
        on_rows: &RowSink<'_>,
    ) -> bool {
        let msg_len = source.len();
        assert!(n > 0 && msg_len.is_multiple_of(n));
        let log_rows = log2_strict_usize(msg_len / n);
        assert_eq!(
            log_rows + log_inv_rate,
            self.log_domain_size(),
            "the codeword's own transform"
        );
        let Some(plan) = TwoSweep::new(layout, n, log_rows, true) else {
            return false;
        };
        // Without a first sweep, the second reads the message whole.
        let Some(msg) = source.whole().or((plan.g > 0).then_some(&[][..])) else {
            return false;
        };
        let msg_at = |task: usize| source.at_task(&plan, task);
        let len = plan.len();
        assert!(work.len() >= len, "the work buffer holds a replica");
        let replicas: Vec<AdditiveNttF64> = (0..1usize << log_inv_rate)
            .map(|r| self.replica(log_inv_rate, r))
            .collect();
        let batch = (work.len() / len).min(replicas.len());
        let (g, t) = (plan.g, plan.t);
        for (first, group) in replicas.chunks(batch).enumerate().map(|(i, c)| (i * batch, c)) {
            if g > 0 {
                let work_ptr = parallel::SendPtr(work.as_mut_ptr());
                let stream = len >= STREAM_MIN_WORDS;
                let group: Vec<&AdditiveNttF64> = group.iter().collect();
                let stride = plan.row_stride();
                self.two_sweep_gathered(&plan, &group, None, msg_at, |task, r, rows, stream_out| {
                    let first = r * len + plan.row_offset(task, 0);
                    for (i, src) in rows.chunks_exact(plan.width).enumerate() {
                        // SAFETY: each (task, replica) alone writes these words of the replica's work buffer.
                        let dst = unsafe { work_ptr.slice(first + i * stride, plan.width) };
                        match stream {
                            true => stream_words(stream_out, dst, src),
                            false => copy_words(dst, src),
                        }
                    }
                });
            }
            let work = &work[..];
            parallel::for_each(group.len() << g, |task| {
                let (r, tile) = (task >> g, task & ((1 << g) - 1));
                let src = if g > 0 { &work[r * len..][..len] } else { msg };
                let at = match layout {
                    MsgLayout::LaneMajor => tile << t,
                    MsgLayout::RowMajor => (tile << t) * n,
                };
                with_scratch(plan.tile_words(), |buf| {
                    plan.fill_tile(buf, &src[at..], 1 << log_rows);
                    group[r].run_layers(buf, log_rows, n, g, log_rows, g, tile);
                    on_rows(((first + r) << log_rows) + (tile << t), buf);
                })
            });
        }
        true
    }

    /// [`Self::encode_two_sweep_with`] into the whole codeword `data` (`2^log_inv_rate` replicas, row-major as
    /// [`Self::encode_interleaved_in_place_with`] leaves it), with no work buffer: the first sweep reads the message
    /// once for every replica and writes each replica's region tile by tile (a tile's `2^t` rows of every lane
    /// together, laid out as the message), so that the second sweep finishes each tile in the very words it read
    /// it from.
    ///
    /// Returns false, having done nothing, for a shape two sweeps do not cover.
    pub fn encode_two_sweep_into(
        &self,
        data: &mut [F64],
        msg: &[F64],
        layout: MsgLayout,
        n: usize,
        log_inv_rate: usize,
        on_rows: &RowSink<'_>,
    ) -> bool {
        self.encode_two_sweep_into_of(data, Source::Whole(msg), layout, n, log_inv_rate, on_rows)
    }

    /// [`Self::encode_two_sweep_into`] of the lane-major message whose block `b` is `blocks[b]` (`2^d` words each),
    /// the blocks lying anywhere: the codeword of their concatenation, its lane `blocks.len() - 1 - b` block `b`'s.
    /// Returns false, having done nothing, for a shape two sweeps do not cover, or one with no first sweep. [Added
    /// here.]
    pub fn encode_two_sweep_blocks_into(
        &self,
        data: &mut [F64],
        blocks: &[&[F64]],
        log_inv_rate: usize,
        on_rows: &RowSink<'_>,
    ) -> bool {
        let n = blocks.len();
        self.encode_two_sweep_into_of(
            data,
            Source::Blocks(blocks),
            MsgLayout::LaneMajor,
            n,
            log_inv_rate,
            on_rows,
        )
    }

    fn encode_two_sweep_into_of(
        &self,
        data: &mut [F64],
        source: Source<'_>,
        layout: MsgLayout,
        n: usize,
        log_inv_rate: usize,
        on_rows: &RowSink<'_>,
    ) -> bool {
        let msg_len = source.len();
        assert!(n > 0 && msg_len.is_multiple_of(n));
        let log_rows = log2_strict_usize(msg_len / n);
        assert_eq!(
            log_rows + log_inv_rate,
            self.log_domain_size(),
            "the codeword's own transform"
        );
        assert_eq!(data.len(), msg_len << log_inv_rate, "the whole codeword");
        let Some(plan) = TwoSweep::new(layout, n, log_rows, true) else {
            return false;
        };
        // Without a first sweep, the second reads the message whole.
        let Some(msg) = source.whole().or((plan.g > 0).then_some(&[][..])) else {
            return false;
        };
        let (len, g, t, tile_words) = (plan.len(), plan.g, plan.t, plan.tile_words());
        let replicas: Vec<AdditiveNttF64> = (0..1usize << log_inv_rate)
            .map(|r| self.replica(log_inv_rate, r))
            .collect();
        let stream = data.len() >= STREAM_MIN_WORDS;
        if g > 0 {
            let data_ptr = parallel::SendPtr(data.as_mut_ptr());
            let refs: Vec<&AdditiveNttF64> = replicas.iter().collect();
            let msg_at = |task: usize| source.at_task(&plan, task);
            self.two_sweep_gathered(&plan, &refs, None, msg_at, |task, r, rows, stream_out| {
                let first = r * len + plan.in_tile(task);
                for (i, src) in rows.chunks_exact(plan.width).enumerate() {
                    // SAFETY: each (task, replica) alone writes these words of tile `i` of the replica's region.
                    let dst = unsafe { data_ptr.slice(first + i * tile_words, plan.width) };
                    match stream {
                        true => stream_words(stream_out, dst, src),
                        false => copy_words(dst, src),
                    }
                }
            });
        }
        // Without a first sweep, a tile is read from the message itself.
        let (msg_stride, tile_stride) = (1usize << log_rows, 1usize << t);
        parallel::chunks_mut(data, tile_words, |k, region| {
            let (r, tile) = (k >> g, k & ((1 << g) - 1));
            with_scratch(tile_words, |buf| {
                if g > 0 {
                    plan.fill_tile(buf, region, tile_stride);
                } else {
                    let at = match layout {
                        MsgLayout::LaneMajor => tile << t,
                        MsgLayout::RowMajor => (tile << t) * n,
                    };
                    plan.fill_tile(buf, &msg[at..], msg_stride);
                }
                replicas[r].run_layers(buf, log_rows, n, g, log_rows, g, tile);
                on_rows((r << log_rows) + (tile << t), buf);
                match stream {
                    true => Stream::new().copy(region, buf),
                    false => region.copy_from_slice(buf),
                }
            })
        });
        true
    }

    /// The first sweep: every task gathers its `2^g` rows of `plan.width` words from the message (`msg(task)`, the
    /// message from the task's first row on: [`TwoSweep::row_offset`] in a flat one) into scratch,
    /// and for each of `replicas` runs layers `0..g` on them and hands them to `out(task, replica, rows,
    /// stream)`, `stream` a streaming-store handle the task fences at its end. With `wanted`, replica `r`'s rows
    /// are final at the rows `wanted[r]` (sorted, distinct) alone ([`Self::run_layers_toward`]).
    fn two_sweep_gathered<'m>(
        &self,
        plan: &TwoSweep,
        replicas: &[&AdditiveNttF64],
        wanted: Option<&[Vec<usize>]>,
        msg: impl Fn(usize) -> &'m [F64] + Sync,
        out: impl Fn(usize, usize, &[F64], &Stream) + Sync,
    ) {
        let (g, width) = (plan.g, plan.width);
        let len = width << g;
        let copies = replicas.len() > 1;
        parallel::for_each_chunk(plan.tasks(), |lo, hi| {
            with_scratch(if copies { 2 * len } else { len }, |scratch| {
                let (gathered, work) = scratch.split_at_mut(len);
                let stream = Stream::new();
                let (n, stride) = (1usize << g, plan.row_stride());
                for task in lo..hi {
                    let rows = &msg(task)[..(n - 1) * stride + width];
                    for (i, dst) in gathered.chunks_exact_mut(width).enumerate() {
                        // No prefetcher follows rows this far apart.
                        if i + PREFETCH_ROWS < n {
                            prefetch(rows[(i + PREFETCH_ROWS) * stride..].as_ptr(), width);
                        }
                        copy_words(dst, &rows[i * stride..][..width]);
                    }
                    for (r, ntt) in replicas.iter().enumerate() {
                        // Layers 0..g of a g-layer domain whose one block is the whole transform's block 0.
                        let buf = if copies {
                            work.copy_from_slice(gathered);
                            &mut work[..]
                        } else {
                            &mut gathered[..]
                        };
                        match wanted {
                            None => ntt.run_layers(buf, g, width, 0, g, 0, 0),
                            Some(rows) => ntt.run_layers_toward(buf, g, width, &rows[r]),
                        }
                        out(task, r, buf, &stream);
                    }
                }
            })
        });
    }

    /// The rows at `wanted` (sorted, distinct) of the codeword this transform encodes at log inverse rate
    /// `log_inv_rate` from `msg` (as [`Self::encode_two_sweep_with`] takes it), each a row of `n` words, in
    /// `wanted`'s order; `None` for a shape two sweeps do not cover.
    ///
    /// The first sweep reads the message once for every replica and keeps, of each gathered transform, only the
    /// tiles holding a wanted row; the second runs on those tiles alone, and in them on the blocks holding a
    /// wanted row ([`Self::encode_interleaved_rows_in_place`]).
    pub fn encoded_rows_two_sweep(
        &self,
        msg: &[F64],
        layout: MsgLayout,
        n: usize,
        log_inv_rate: usize,
        wanted: &[usize],
    ) -> Option<Vec<F64>> {
        self.encoded_rows_two_sweep_of(Source::Whole(msg), layout, n, log_inv_rate, wanted)
    }

    /// [`Self::encoded_rows_two_sweep`] of the lane-major message whose block `b` is `blocks[b]`
    /// ([`Self::encode_two_sweep_blocks_with`]); `None` also for a shape with no first sweep.
    pub fn encoded_rows_two_sweep_blocks(
        &self,
        blocks: &[&[F64]],
        log_inv_rate: usize,
        wanted: &[usize],
    ) -> Option<Vec<F64>> {
        let n = blocks.len();
        self.encoded_rows_two_sweep_of(Source::Blocks(blocks), MsgLayout::LaneMajor, n, log_inv_rate, wanted)
    }

    fn encoded_rows_two_sweep_of(
        &self,
        source: Source<'_>,
        layout: MsgLayout,
        n: usize,
        log_inv_rate: usize,
        wanted: &[usize],
    ) -> Option<Vec<F64>> {
        assert!(wanted.is_sorted_by(|a, b| a < b), "sorted, distinct rows");
        let msg_len = source.len();
        assert!(n > 0 && msg_len.is_multiple_of(n));
        let log_rows = log2_strict_usize(msg_len / n);
        assert_eq!(
            log_rows + log_inv_rate,
            self.log_domain_size(),
            "the codeword's own transform"
        );
        let plan = TwoSweep::new(layout, n, log_rows, false)?;
        // Without a first sweep, the second reads the message whole.
        let msg = source.whole().or((plan.g > 0).then_some(&[][..]))?;
        let msg_at = |task: usize| source.at_task(&plan, task);
        let (g, t) = (plan.g, plan.t);
        let rows = 1usize << log_rows;
        // The wanted tiles, (replica, tile) ascending.
        let mut tiles: Vec<(usize, usize)> = wanted.iter().map(|&q| (q >> log_rows, (q & (rows - 1)) >> t)).collect();
        tiles.dedup();
        assert!(
            tiles.last().is_none_or(|&(r, _)| r < 1 << log_inv_rate),
            "rows of the codeword"
        );
        // The replicas holding a wanted tile, and where their tiles start in `tiles`.
        let mut used: Vec<(usize, usize)> = vec![];
        for (k, &(r, _)) in tiles.iter().enumerate() {
            if used.last().is_none_or(|&(last, _)| last != r) {
                used.push((r, k));
            }
        }
        let replicas: Vec<AdditiveNttF64> = used.iter().map(|&(r, _)| self.replica(log_inv_rate, r)).collect();
        let tile_words = plan.tile_words();
        // `kept[k * tile_words ..]`: wanted tile `k` after the first sweep, laid out as the message.
        let mut kept = if g > 0 {
            // SAFETY: the first sweep writes every word of every wanted tile before the second reads it.
            unsafe { primitives::uninit_vec::<F64>(tiles.len() * tile_words) }
        } else {
            Vec::new()
        };
        if g > 0 {
            let kept_ptr = parallel::SendPtr(kept.as_mut_ptr());
            let refs: Vec<&AdditiveNttF64> = replicas.iter().collect();
            // Each replica's wanted tiles: the first sweep's rows that are kept.
            let rows: Vec<Vec<usize>> = (0..used.len())
                .map(|u| {
                    let end = used.get(u + 1).map_or(tiles.len(), |&(_, k)| k);
                    tiles[used[u].1..end].iter().map(|&(_, tile)| tile).collect()
                })
                .collect();
            self.two_sweep_gathered(&plan, &refs, Some(&rows), msg_at, |task, u, buf, _| {
                let first = used[u].1;
                let end = used.get(u + 1).map_or(tiles.len(), |&(_, k)| k);
                for (k, &(_, tile)) in tiles.iter().enumerate().take(end).skip(first) {
                    let src = &buf[tile * plan.width..][..plan.width];
                    // SAFETY: each (task, wanted tile) alone writes these words of `kept`.
                    unsafe { kept_ptr.slice(k * tile_words + plan.in_tile(task), plan.width) }.copy_from_slice(src);
                }
            });
        }
        let mut out = vec![F64::ZERO; wanted.len() * n];
        let out_ptr = parallel::SendPtr(out.as_mut_ptr());
        parallel::for_each(tiles.len(), |k| {
            let (replica, tile) = tiles[k];
            let u = used.partition_point(|&(r, _)| r < replica);
            let first = (replica << log_rows) + (tile << t);
            let at = wanted.partition_point(|&q| q < first);
            let local: Vec<usize> = wanted[at..wanted.partition_point(|&q| q < first + (1 << t))]
                .iter()
                .map(|&q| q - (replica << log_rows))
                .collect();
            with_scratch(tile_words, |buf| {
                if g > 0 {
                    plan.fill_tile(buf, &kept[k * tile_words..], 1 << t);
                } else {
                    let at = match layout {
                        MsgLayout::LaneMajor => tile << t,
                        MsgLayout::RowMajor => (tile << t) * n,
                    };
                    plan.fill_tile(buf, &msg[at..], rows);
                }
                replicas[u].run_layers_on_rows(buf, log_rows, n, g, tile, tile << t, &local);
                for (j, &q) in local.iter().enumerate() {
                    let row = &buf[(q - (tile << t)) * n..][..n];
                    // SAFETY: each wanted row is one tile's alone, and its slot one row of `out`.
                    unsafe { out_ptr.slice((at + j) * n, n) }.copy_from_slice(row);
                }
            })
        });
        Some(out)
    }
}

/// Fill the row-major tile `buf` (`rows` rows of `n_lanes` words) from the lane runs `lane(b)` (`rows` words of
/// message block `b`), codeword lane `n_lanes - 1 - b` taking block `b`, a few rows at a time so that they stay
/// in L1.
fn transpose_tile<'a>(buf: &mut [F64], n_lanes: usize, rows: usize, lane: impl Fn(usize) -> &'a [F64]) {
    const CHUNK: usize = 64;
    debug_assert_eq!(buf.len(), n_lanes * rows);
    // On AVX-512, eight lanes by eight rows at a time, transposed in registers; the lanes past the last eight
    // below.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
    let lanes_done = if rows.is_multiple_of(8) {
        let groups = n_lanes / 8;
        for b0 in (0..groups).map(|g| 8 * g) {
            let runs: [&[F64]; 8] = std::array::from_fn(|k| &lane(b0 + 7 - k)[..rows]);
            for x0 in (0..rows).step_by(8) {
                // SAFETY: the cfg enables avx512f; every run holds `rows` words, and row `x0 + j` of `buf` the
                // eight words from `n_lanes - 8 - b0`.
                unsafe { transpose_8x8(&runs, x0, &mut buf[x0 * n_lanes + n_lanes - 8 - b0..], n_lanes) };
            }
        }
        8 * groups
    } else {
        0
    };
    #[cfg(not(all(target_arch = "x86_64", target_feature = "avx512f")))]
    let lanes_done = 0;
    for x0 in (0..rows).step_by(CHUNK) {
        let n = CHUNK.min(rows - x0);
        let out = &mut buf[x0 * n_lanes..(x0 + n) * n_lanes];
        for b in lanes_done..n_lanes {
            let src = &lane(b)[x0..x0 + n];
            for (slot, &word) in out[n_lanes - 1 - b..].iter_mut().step_by(n_lanes).zip(src) {
                *slot = word;
            }
        }
    }
}

/// Words `x0 .. x0 + 8` of the eight runs, transposed: row `j` (`runs[k][x0 + j]` for `k < 8`) to
/// `out[j * stride ..][..8]`.
///
/// # Safety
///
/// The cfg enables avx512f, every run holds the eight words, and `out` the eight rows.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
#[inline(always)]
unsafe fn transpose_8x8(runs: &[&[F64]; 8], x0: usize, out: &mut [F64], stride: usize) {
    use core::arch::x86_64::*;
    debug_assert!(out.len() >= 7 * stride + 8 && runs.iter().all(|r| r.len() >= x0 + 8));
    // SAFETY: the caller vouches for the bounds and the features.
    unsafe {
        let v: [__m512i; 8] = std::array::from_fn(|k| _mm512_loadu_si512(runs[k].as_ptr().add(x0).cast()));
        // Pairs: per 128-bit lane i, [v_k[2i], v_k+1[2i]] and [v_k[2i+1], v_k+1[2i+1]].
        let lo: [__m512i; 4] = std::array::from_fn(|p| _mm512_unpacklo_epi64(v[2 * p], v[2 * p + 1]));
        let hi: [__m512i; 4] = std::array::from_fn(|p| _mm512_unpackhi_epi64(v[2 * p], v[2 * p + 1]));
        // Row 2i (from `lo`) or 2i + 1 (from `hi`) is 128-bit lane i of the four pair registers.
        let rows = |t: &[__m512i; 4]| {
            let (a, b) = (
                _mm512_shuffle_i64x2::<0x44>(t[0], t[1]),
                _mm512_shuffle_i64x2::<0x44>(t[2], t[3]),
            );
            let (c, d) = (
                _mm512_shuffle_i64x2::<0xEE>(t[0], t[1]),
                _mm512_shuffle_i64x2::<0xEE>(t[2], t[3]),
            );
            [
                _mm512_shuffle_i64x2::<0x88>(a, b),
                _mm512_shuffle_i64x2::<0xDD>(a, b),
                _mm512_shuffle_i64x2::<0x88>(c, d),
                _mm512_shuffle_i64x2::<0xDD>(c, d),
            ]
        };
        let (even, odd) = (rows(&lo), rows(&hi));
        for i in 0..4 {
            _mm512_storeu_si512(out.as_mut_ptr().add(2 * i * stride).cast(), even[i]);
            _mm512_storeu_si512(out.as_mut_ptr().add((2 * i + 1) * stride).cast(), odd[i]);
        }
    }
}

/// Visit every row group of a fused multi-layer block.
///
/// ```text
///     the block is N slabs of equal height
///
///     slab 0:     row 0   row 1   ...   row r   ...
///     slab 1:     row 0   row 1   ...   row r   ...
///     ...
///     slab N-1:   row 0   row 1   ...   row r   ...
///
///     group r  =  row r of every slab
/// ```
///
/// # Why the rows are disjoint
///
/// - Distinct groups take distinct rows inside each slab.
/// - The slabs do not overlap.
/// - So the groups are pairwise disjoint, and one base pointer can stand in for N nested splits.
fn fused_rows<const N: usize>(
    block: &mut [F64],
    stride_rows: usize,
    num_ntts: usize,
    do_one: impl Fn(&mut [&mut [F64]; N]),
) {
    // Words from one slab to the next.
    let stride = stride_rows * num_ntts;
    debug_assert_eq!(block.len(), N * stride);
    let base = block.as_mut_ptr();
    for r in 0..stride_rows {
        // Row `r` of each slab starts this many words into it.
        let off = r * num_ntts;
        // SAFETY:
        // - The groups are disjoint, as argued above.
        // - The row ends inside its slab, since the row index is below the slab height.
        let mut rows: [&mut [F64]; N] =
            std::array::from_fn(|i| unsafe { std::slice::from_raw_parts_mut(base.add(i * stride + off), num_ntts) });
        do_one(&mut rows);
    }
}

/// Layers L, L+1 and L+2 fused into one sweep over a layer-L block.
///
/// ```text
///     a group is 8 rows, e = (block rows) / 8 apart:  r, r + e, ..., r + 7e
///
///     layer L     pairs rows 4e apart
///     layer L+1   pairs rows 2e apart
///     layer L+2   pairs rows  e apart
/// ```
///
/// - The eight rows stay in L1 across all twelve butterflies.
/// - The seven twiddles are breadth-first: one for layer L, two for L+1, four for L+2.
fn butterfly_interleaved_fused_3layer(block: &mut [F64], t: &[F64; 7], eighth: usize, num_ntts: usize) {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        assert_eq!(block.len(), 8 * eighth * num_ntts);
        // SAFETY: the block is exactly eight slabs of `eighth * num_ntts` words, and the features are enabled.
        return unsafe { slabs_avx512::radix8(block.as_mut_ptr(), eighth * num_ntts, t) };
    }
    #[allow(unreachable_code)]
    fused_rows::<8>(block, eighth, num_ntts, |rows| radix8_butterflies(rows, t));
}

/// Fused layers on AVX-512, slab by slab rather than row by row.
///
/// # Why slabs
///
/// - Within one block every row of a slab takes the same twiddles, and a slab's rows are contiguous.
/// - So the butterflies pair word `k` of one slab with word `k` of another, for every `k` of the slab at once:
///   the rows' lanes need no loop of their own, and only the slab's end needs a masked vector.
///
/// # Why in registers
///
/// - A radix-8 group's eight vectors are loaded once, take all twelve butterflies in registers, and are stored once.
/// - Butterfly by butterfly through L1 costs four memory operations a butterfly instead of 4/3; Zen 4 stores one
///   512-bit vector every two cycles, so the stores alone would cost more than the arithmetic.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
mod slabs_avx512 {
    use super::butterfly_zmm_v;
    use core::arch::x86_64::*;
    use primitives::field::F64;

    /// The butterflies `(a, b, t)` of a fused group, on vectors `a` and `b` at twiddle `t`, each on every column
    /// before the next: written out, so that the group stays in registers.
    macro_rules! butterflies {
        ($x:ident, $tw:ident; $(($a:literal, $b:literal, $t:literal)),*) => {{
            $(
                for col in $x.iter_mut() {
                    (col[$a], col[$b]) = butterfly_zmm_v(col[$a], col[$b], $tw[$t]);
                }
            )*
        }};
    }

    /// Run the butterflies `bfs` on the `N` slabs at `base`, `C` vectors of each at a time.
    ///
    /// The `C` columns' butterflies are interleaved: a group's twelve butterflies are three dependent layers,
    /// too long a chain for the out-of-order window to overlap the next group's on its own. The columns past the
    /// last whole `C` go one at a time, the very last masked.
    ///
    /// # Safety
    ///
    /// `base` addresses `N` slabs of `slab` words, readable and writable.
    #[inline(always)]
    unsafe fn sweep<const N: usize, const C: usize>(base: *mut F64, slab: usize, kernel: impl Fn(&mut [[__m512i; N]])) {
        // SAFETY: every vector lies inside its slab: whole ones below the slab's last whole vector, the masked
        // one past it; the caller vouches for the slabs.
        unsafe {
            let full = slab & !7;
            let mut k = 0;
            while k + 8 * C <= full {
                let p = base.add(k);
                let mut x: [[__m512i; N]; C] = std::array::from_fn(|c| {
                    std::array::from_fn(|i| _mm512_loadu_si512(p.add(i * slab + 8 * c).cast()))
                });
                kernel(&mut x);
                for (c, col) in x.iter().enumerate() {
                    for (i, &v) in col.iter().enumerate() {
                        _mm512_storeu_si512(p.add(i * slab + 8 * c).cast(), v);
                    }
                }
                k += 8 * C;
            }
            while k < slab {
                let mask = if k < full {
                    0xFF
                } else {
                    ((1u16 << (slab - k)) - 1) as u8
                };
                let p = base.add(k);
                let mut x: [[__m512i; N]; 1] = [std::array::from_fn(|i| {
                    _mm512_maskz_loadu_epi64(mask, p.add(i * slab).cast())
                })];
                kernel(&mut x);
                let [x] = x;
                for (i, &v) in x.iter().enumerate() {
                    _mm512_mask_storeu_epi64(p.add(i * slab).cast(), mask, v);
                }
                k += 8;
            }
        }
    }

    #[inline(always)]
    fn splat(t: F64) -> __m512i {
        // SAFETY: the cfg enables avx512f.
        unsafe { _mm512_set1_epi64(t.0 as i64) }
    }

    /// Three layers over eight slabs: [`super::radix8_butterflies`] on every row of them.
    ///
    /// # Safety
    ///
    /// `base` addresses eight slabs of `slab` words, readable and writable.
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx2")]
    pub(super) unsafe fn radix8(base: *mut F64, slab: usize, t: &[F64; 7]) {
        let tw = t.map(splat);
        // SAFETY: forwarded.
        unsafe {
            sweep::<8, 2>(base, slab, |x| {
                butterflies!(x, tw; (0, 4, 0), (1, 5, 0), (2, 6, 0), (3, 7, 0), (0, 2, 1), (1, 3, 1), (4, 6, 2),
                    (5, 7, 2), (0, 1, 3), (2, 3, 4), (4, 5, 5), (6, 7, 6));
            })
        }
    }

    /// Two layers over four slabs: [`super::butterfly_interleaved_fused_2layer`]'s butterflies.
    ///
    /// # Safety
    ///
    /// `base` addresses four slabs of `slab` words, readable and writable.
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx2")]
    pub(super) unsafe fn radix4(base: *mut F64, slab: usize, t_outer: F64, t_inner_a: F64, t_inner_b: F64) {
        let tw = [t_outer, t_inner_a, t_inner_b].map(splat);
        // SAFETY: forwarded.
        unsafe {
            sweep::<4, 4>(
                base,
                slab,
                |x| butterflies!(x, tw; (0, 2, 0), (1, 3, 0), (0, 1, 1), (2, 3, 2)),
            )
        }
    }

    /// One layer over two slabs.
    ///
    /// # Safety
    ///
    /// `base` addresses two slabs of `slab` words, readable and writable.
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx2")]
    pub(super) unsafe fn radix2(base: *mut F64, slab: usize, t: F64) {
        let tw = [splat(t)];
        // SAFETY: forwarded.
        unsafe { sweep::<2, 4>(base, slab, |x| butterflies!(x, tw; (0, 1, 0))) }
    }
}

/// The twelve butterflies of one radix-8 row group, with its seven twiddles breadth-first.
#[inline(always)]
fn radix8_butterflies(rows: &mut [&mut [F64]; 8], t: &[F64; 7]) {
    let [r0, r1, r2, r3, r4, r5, r6, r7] = rows;
    // Layer L: rows 4 apart, one twiddle for the whole block.
    butterfly_lanes(r0, r4, t[0]);
    butterfly_lanes(r1, r5, t[0]);
    butterfly_lanes(r2, r6, t[0]);
    butterfly_lanes(r3, r7, t[0]);
    // Layer L+1: rows 2 apart, one twiddle per half.
    butterfly_lanes(r0, r2, t[1]);
    butterfly_lanes(r1, r3, t[1]);
    butterfly_lanes(r4, r6, t[2]);
    butterfly_lanes(r5, r7, t[2]);
    // Layer L+2: adjacent rows, one twiddle per quarter.
    butterfly_lanes(r0, r1, t[3]);
    butterfly_lanes(r2, r3, t[4]);
    butterfly_lanes(r4, r5, t[5]);
    butterfly_lanes(r6, r7, t[6]);
}

/// Transpose a lane-major message into the row-major order the encoder reads.
///
/// # Layout
///
/// ```text
///     input, lane-major:   [ block 0 | block 1 | ... | block n-1 ]   each 2^rows_log words
///     output, row-major:   row x = [ block n-1 word x, ..., block 1 word x, block 0 word x ]
/// ```
///
/// - Codeword lane `t` takes message block `n - 1 - t`.
/// - Any lane count works: a commitment encodes only the lanes that carry data.
///
/// # Why descending
///
/// - A Merkle leaf reads its lanes from the top index down.
/// - So the absent all-zero lanes lead every leaf image.
/// - Their whole 136-byte blocks are then one sponge state that every leaf shares.
/// - The proof can leave them out.
/// - Each lane is an independent codeword, so the order costs nothing.
///
/// # Performance
///
/// - Rows are handled one tile at a time.
/// - Each lane adds a contiguous burst of words to an L1-resident tile.
/// - The finished tile goes out as one contiguous run.
/// - That keeps an n-way gather at a `2^rows_log` stride near memory bandwidth.
pub fn transpose_lane_major(out: &mut [F64], msg: &[F64], n_lanes: usize, log_rows: usize) {
    let rows = 1usize << log_rows;
    assert!(n_lanes > 0, "a commitment needs at least one lane");
    assert_eq!(msg.len(), n_lanes * rows, "message is n_lanes contiguous lane blocks");
    assert_eq!(out.len(), msg.len(), "the transpose is the same words, reordered");

    /// Words per cache-resident row tile.
    const TILE_WORDS: usize = 4096;
    assert!(n_lanes <= TILE_WORDS, "a codeword row must fit the transpose tile");
    // Largest power-of-two row count whose tile fits: both it and `rows` are then
    // powers of two, so the tiles cover every row. They have to: this is the sole
    // initializer of an uninitialized codeword's message region, and a truncating
    // tile count would leave the tail reading the previous phase's plausible bytes,
    // whose symptom is a proof that stops verifying rather than a crash.
    let tile_rows = (1usize << (TILE_WORDS / n_lanes).ilog2()).min(rows);
    assert_eq!(rows % tile_rows, 0, "row tiles must cover every row");

    // Nothing reads the output back before a buffer this large is evicted.
    let stream = out.len() >= STREAM_MIN_WORDS;
    parallel::chunks_mut(out, tile_rows * n_lanes, |t, out_tile| {
        with_scratch(out_tile.len(), |tile| {
            // First message row this tile covers.
            let r0 = t * tile_rows;
            // Fill the tile column by column: lane `lane` takes every `n_lanes`-th word.
            for lane in 0..n_lanes {
                let block = n_lanes - 1 - lane;
                let src = &msg[block * rows + r0..][..tile_rows];
                for (slot, &word) in tile[lane..].iter_mut().step_by(n_lanes).zip(src) {
                    *slot = word;
                }
            }
            // Write the finished tile out as one contiguous run.
            if stream {
                Stream::new().copy(out_tile, tile);
            } else {
                out_tile.copy_from_slice(tile);
            }
        });
    });
}

/// Rows a gather fetches ahead of the one it copies.
const PREFETCH_ROWS: usize = 8;

/// Hint the cache lines of `len` words at `p` into L1. A hint only: it never faults.
#[inline(always)]
pub(crate) fn prefetch(p: *const F64, len: usize) {
    #[cfg(target_arch = "x86_64")]
    {
        use core::arch::x86_64::{_MM_HINT_T0, _mm_prefetch};
        let (start, end) = (p as usize & !63, p as usize + 8 * len);
        for line in (start..end).step_by(64) {
            // SAFETY: a prefetch never faults, whatever the address.
            unsafe { _mm_prefetch::<_MM_HINT_T0>(line as *const i8) };
        }
    }
    #[cfg(not(target_arch = "x86_64"))]
    let _ = (p, len);
}

/// `dst.copy_from_slice(src)`, inlined: whole lines of eight words as vectors, so that a short row is not a call.
#[inline(always)]
fn copy_words(dst: &mut [F64], src: &[F64]) {
    assert_eq!(dst.len(), src.len());
    let (d, d_rest) = dst.as_chunks_mut::<8>();
    let (s, s_rest) = src.as_chunks::<8>();
    for (d, s) in d.iter_mut().zip(s) {
        *d = *s;
    }
    if !d_rest.is_empty() {
        d_rest.copy_from_slice(s_rest);
    }
}

/// `stream.copy(dst, src)`, inlined for a row of whole cache lines starting on one: each line one streaming store.
#[inline(always)]
fn stream_words(stream: &Stream, dst: &mut [F64], src: &[F64]) {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
    if dst.len().is_multiple_of(8) && (dst.as_ptr() as usize).is_multiple_of(64) {
        use core::arch::x86_64::{_mm512_loadu_si512, _mm512_stream_si512};
        assert_eq!(dst.len(), src.len());
        for (d, s) in dst.as_chunks_mut::<8>().0.iter_mut().zip(src.as_chunks::<8>().0) {
            // SAFETY: the cfg enables avx512f, `d` is a whole aligned line and `s` eight words; the stream's region
            // fences the store before anything reads it.
            unsafe { _mm512_stream_si512(d.as_mut_ptr().cast(), _mm512_loadu_si512(s.as_ptr().cast())) };
        }
        return;
    }
    stream.copy(dst, src);
}

/// Words one L2-resident unit of work may span: a gathered row group or a deep sub-block.
///
/// # Why this value
///
/// - 2^16 words is 512 KiB.
/// - Two SMT threads share a core's L2 of 1 MiB, so each budgets for half.
///
/// # On Apple silicon
///
/// - A deep layer costs about the same whether its sub-block fits a cache or not: the transform is compute bound.
/// - A gathered layer costs more than a deep one, its rows scattered over more streams than the prefetcher follows.
/// - So the budget is sized to push layers into the deep pass, not to fit a cache.
/// - It exceeds [`L3_WORDS`], which then changes no plan.
#[cfg(not(all(target_arch = "aarch64", target_os = "macos")))]
const L2_WORDS: usize = 1 << 16;
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
const L2_WORDS: usize = 1 << 21;

/// Deep sub-blocks cut per worker, as a log.
///
/// - Apple silicon mixes performance and efficiency cores.
/// - With one sub-block each, the performance cores would wait on the efficiency cores' sub-blocks.
/// - Elsewhere every core is alike, and one each suffices.
#[cfg(not(all(target_arch = "aarch64", target_os = "macos")))]
const LOG_SUBS_PER_WORKER: usize = 0;
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
const LOG_SUBS_PER_WORKER: usize = 2;

/// Words a deep sub-block may span when it alone covers every layer.
///
/// # Why this value
///
/// - 2^18 words is 2 MiB, one thread's share of L3.
/// - Such a sub-block spills from L2 into L3.
/// - That costs extra L3 traffic, but saves a whole sweep of DRAM.
const L3_WORDS: usize = 1 << 18;

/// Buffers of at least this many words get streaming stores for data a pass does not read back.
///
/// # Why this value
///
/// - 2^23 words is 64 MiB, more than L3 keeps until the next pass.
/// - A streaming store then skips the read an ordinary store makes before it writes.
/// - A smaller buffer stays in L3 for the next pass, which a streaming store would give up.
const STREAM_MIN_WORDS: usize = 1 << 23;

/// Lend this thread's scratch buffer, grown to the requested length.
///
/// - It is cache-line aligned, so a full-width load never splits a line.
/// - It lives as long as the thread, so no pass allocates in its hot loop.
fn with_scratch<R>(len: usize, f: impl FnOnce(&mut [F64]) -> R) -> R {
    // One cache line of words.
    #[derive(Clone, Copy)]
    #[repr(C, align(64))]
    struct Line([F64; 8]);
    thread_local! {
        static SCRATCH: RefCell<Vec<Line>> = const { RefCell::new(Vec::new()) };
    }
    SCRATCH.with_borrow_mut(|lines| {
        // Grow only; a later, smaller request reuses the same lines.
        if lines.len() * 8 < len {
            lines.resize(len.div_ceil(8), Line([F64::ZERO; 8]));
        }
        // SAFETY:
        // - A line is exactly eight contiguous words, with no padding.
        // - The buffer holds at least the requested words, all initialized.
        f(unsafe { std::slice::from_raw_parts_mut(lines.as_mut_ptr().cast::<F64>(), len) })
    })
}

/// Fill every replica of the buffer with a copy of the message.
///
/// - This is the unfused form of a gathered first pass.
/// - The message may be the buffer's own first replica, which is then left as it is.
fn replicate(data: &mut [F64], msg: Message<'_>, msg_len: usize) {
    // Copy granularity: small enough to spread a short message over every worker.
    const CHUNK: usize = 1 << 14;
    let replicas = data.len() / msg_len;
    let chunks = msg_len.div_ceil(CHUNK);
    let dst = parallel::SendPtr(data.as_mut_ptr());
    // The message: the buffer's replica 0, read through `dst`, which the tasks also write through, or a separate
    // message, only read.
    let (msg, in_place) = match msg {
        Message::InPlace => (dst, true),
        Message::Separate(m) => {
            assert_eq!(m.len(), msg_len);
            (parallel::SendPtr(m.as_ptr().cast_mut()), false)
        }
    };
    // Replica index innermost, so one worker copies a chunk into several replicas while it is cached.
    parallel::for_each(chunks * replicas, |t| {
        let (c, replica) = (t / replicas, t % replicas);
        // The message already occupies replica 0.
        if in_place && replica == 0 {
            return;
        }
        let start = c * CHUNK;
        let len = CHUNK.min(msg_len - start);
        // SAFETY:
        // - The message holds `msg_len` words, and the buffer `replicas` times as many.
        // - Only this task writes this range.
        // - The range skips replica 0, so it never overlaps a message stored there.
        unsafe {
            let src = std::slice::from_raw_parts(msg.add(start), len);
            dst.slice(replica * msg_len + start, len).copy_from_slice(src);
        }
    });
}

/// Test oracle: fill every replica with a copy of a message held elsewhere.
#[cfg(test)]
fn replicate_rows(data: &mut [F64], msg: &[F64]) {
    for replica in data.chunks_mut(msg.len()) {
        replica.copy_from_slice(msg);
    }
}

/// Layers L and L+1 fused into one sweep over a layer-L block, four rows at a time.
fn butterfly_interleaved_fused_2layer(
    block: &mut [F64],
    t_outer: F64,
    t_inner_a: F64,
    t_inner_b: F64,
    quarter: usize,
    num_ntts: usize,
) {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        assert_eq!(block.len(), 4 * quarter * num_ntts);
        // SAFETY: the block is exactly four slabs of `quarter * num_ntts` words, and the features are enabled.
        return unsafe { slabs_avx512::radix4(block.as_mut_ptr(), quarter * num_ntts, t_outer, t_inner_a, t_inner_b) };
    }
    #[allow(unreachable_code)]
    fused_rows::<4>(block, quarter, num_ntts, |rows| {
        let [row_a, row_b, row_c, row_d] = rows;
        // Layer L: rows 2 apart, one twiddle for the block.
        butterfly_lanes(row_a, row_c, t_outer);
        butterfly_lanes(row_b, row_d, t_outer);
        // Layer L+1: adjacent rows, one twiddle per half.
        butterfly_lanes(row_a, row_b, t_inner_a);
        butterfly_lanes(row_c, row_d, t_inner_b);
    });
}

#[inline]
fn butterfly_interleaved_block(block: &mut [F64], twiddle: F64, block_size_half: usize, num_ntts: usize) {
    let half_offset = block_size_half * num_ntts;
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        assert_eq!(block.len(), 2 * half_offset);
        // SAFETY: the block is exactly two slabs of `half_offset` words, and the features are enabled.
        return unsafe { slabs_avx512::radix2(block.as_mut_ptr(), half_offset, twiddle) };
    }
    #[allow(unreachable_code)]
    let (top, bot) = block.split_at_mut(half_offset);
    for r in 0..block_size_half {
        let off = r * num_ntts;
        butterfly_lanes(&mut top[off..off + num_ntts], &mut bot[off..off + num_ntts], twiddle);
    }
}

/// The transposed butterfly over every lane of a (top row, bottom row) pair:
/// `s = u + v; new_u = s; new_v = v + s*t`.
pub(crate) fn transposed_butterfly_lanes(top: &mut [F64], bot: &mut [F64], twiddle: F64) {
    assert_eq!(top.len(), bot.len());
    // On AVX-512, in one pass: `s = u + v` to the top, `v + s*t` (the forward butterfly of (v, s)'s first output)
    // to the bottom, eight lanes at a time, the last few masked.
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        use core::arch::x86_64::*;
        let n = top.len();
        // SAFETY: the target features are enabled at compile time; every access is inside both rows (whole
        // vectors below `n / 8 * 8`, masked past it).
        unsafe {
            let tw = _mm512_set1_epi64(twiddle.0 as i64);
            let mut k = 0;
            while k < n {
                let mask: u8 = if n - k >= 8 { 0xFF } else { (1u8 << (n - k)) - 1 };
                let (pu, pv) = (top.as_mut_ptr().add(k), bot.as_mut_ptr().add(k));
                let u = _mm512_maskz_loadu_epi64(mask, pu.cast());
                let v = _mm512_maskz_loadu_epi64(mask, pv.cast());
                let s = _mm512_xor_si512(u, v);
                let (nv, _) = butterfly_zmm_v(v, s, tw);
                _mm512_mask_storeu_epi64(pu.cast(), mask, s);
                _mm512_mask_storeu_epi64(pv.cast(), mask, nv);
                k += 8;
            }
        }
        return;
    }
    #[allow(unreachable_code)]
    // The forward butterfly of (v, s) leaves v + s*t in v and s + (v + s*t) in s, which one more XOR undoes.
    for (u, v) in top.iter_mut().zip(bot.iter()) {
        *u += *v;
    }
    butterfly_lanes(bot, top, twiddle);
    for (u, v) in top.iter_mut().zip(bot.iter()) {
        *u += *v;
    }
}

/// Butterfly all `num_ntts` lanes of one (top row, bottom row) pair with a
/// shared twiddle: new_u = u + v*t; new_v = v + new_u.
///
/// On NEON this processes eight lanes per iteration. Four independent pair
/// reductions stay in the vector register file, exposing their PMULL chains
/// in parallel and amortizing the loop branch and constant setup. The pair
/// kernel handles a short even tail, and the scalar path handles an odd tail.
#[inline]
fn butterfly_lanes(top: &mut [F64], bot: &mut [F64], twiddle: F64) {
    debug_assert_eq!(top.len(), bot.len());
    // The lanes the vector kernels cover; the scalar loop at the end takes the rest.
    let done: usize;
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        let vectors = top.len() / 8;
        let tail = top.len() % 8;
        // SAFETY: the target features are enabled at compile time; each full
        // iteration reads and writes exactly eight elements from both rows, and
        // the masked tail only the `tail` elements left.
        unsafe {
            for i in 0..vectors {
                butterfly_lanes_avx512(top.as_mut_ptr().add(8 * i), bot.as_mut_ptr().add(8 * i), twiddle.0);
            }
            if tail != 0 {
                butterfly_lanes_avx512_masked(
                    top.as_mut_ptr().add(8 * vectors),
                    bot.as_mut_ptr().add(8 * vectors),
                    twiddle.0,
                    (1u8 << tail) - 1,
                );
            }
        }
        done = top.len();
    }
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "pclmulqdq",
        target_feature = "avx2",
        not(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))
    ))]
    {
        let vectors = top.len() / 4;
        let tail = top.len() % 4;
        // SAFETY: the target features are enabled at compile time; each full
        // iteration reads and writes exactly four elements from both rows, and
        // the masked tail only the `tail` elements left.
        unsafe {
            for i in 0..vectors {
                butterfly_lanes_avx2(top.as_mut_ptr().add(4 * i), bot.as_mut_ptr().add(4 * i), twiddle.0);
            }
            if tail != 0 {
                butterfly_lanes_avx2_masked(
                    top.as_mut_ptr().add(4 * vectors),
                    bot.as_mut_ptr().add(4 * vectors),
                    twiddle.0,
                    tail,
                );
            }
        }
        done = top.len();
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    {
        let vectors = top.len() / 8;
        let mut lane = 8 * vectors;
        // SAFETY: aes target feature is enabled at compile time; the kernels
        // read/write exactly lanes [8i, 8i+8) and [lane, lane + 2) of each row.
        unsafe {
            for i in 0..vectors {
                butterfly_lanes_neon_8(top.as_mut_ptr().add(8 * i), bot.as_mut_ptr().add(8 * i), twiddle.0);
            }
            while lane + 2 <= top.len() {
                butterfly_lane_pair_neon(top.as_mut_ptr().add(lane), bot.as_mut_ptr().add(lane), twiddle.0);
                lane += 2;
            }
        }
        done = lane;
    }
    #[cfg(not(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(target_arch = "x86_64", target_feature = "pclmulqdq", target_feature = "avx2")
    )))]
    {
        done = 0;
    }
    for lane in done..top.len() {
        let v = bot[lane];
        let new_u = top[lane] + v * twiddle;
        top[lane] = new_u;
        bot[lane] = v + new_u;
    }
}

/// [`butterfly_lanes_avx512`] at half the width, for a machine with AVX2 but not both
/// VPCLMULQDQ and AVX-512.
///
/// # Safety
/// Requires PCLMULQDQ + AVX2; `top` and `bot` must each address four readable
/// and writable F64 values.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "pclmulqdq",
    target_feature = "avx2",
    not(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))
))]
#[inline]
#[target_feature(enable = "pclmulqdq", enable = "avx2")]
unsafe fn butterfly_lanes_avx2(top: *mut F64, bot: *mut F64, twiddle: u64) {
    use core::arch::x86_64::*;
    // SAFETY: the caller supplies valid four-element rows and the function's
    // target features cover every intrinsic below.
    unsafe {
        let (new_u, new_v) = butterfly_ymm(_mm256_loadu_si256(top.cast()), _mm256_loadu_si256(bot.cast()), twiddle);
        _mm256_storeu_si256(top.cast(), new_u);
        _mm256_storeu_si256(bot.cast(), new_v);
    }
}

/// [`butterfly_lanes_avx2`] over the first `n < 4` lanes only.
///
/// # Safety
/// Requires PCLMULQDQ + AVX2; `top` and `bot` must each address `n` readable
/// and writable F64 values.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "pclmulqdq",
    target_feature = "avx2",
    not(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))
))]
#[inline]
#[target_feature(enable = "pclmulqdq", enable = "avx2")]
unsafe fn butterfly_lanes_avx2_masked(top: *mut F64, bot: *mut F64, twiddle: u64, n: usize) {
    use core::arch::x86_64::*;
    // SAFETY: masked-off lanes are neither read nor written, and the caller
    // supplies the `n` lanes that are.
    unsafe {
        let mask = _mm256_cmpgt_epi64(_mm256_set1_epi64x(n as i64), _mm256_setr_epi64x(0, 1, 2, 3));
        let u = _mm256_maskload_epi64(top.cast(), mask);
        let v = _mm256_maskload_epi64(bot.cast(), mask);
        let (new_u, new_v) = butterfly_ymm(u, v, twiddle);
        _mm256_maskstore_epi64(top.cast(), mask, new_u);
        _mm256_maskstore_epi64(bot.cast(), mask, new_v);
    }
}

/// Four butterflies `u' = u + v * t`, `v' = v + u'` in registers: the products one per 128-bit
/// lane, even lanes then odd lanes as in `butterfly_zmm`, then one shift-and-XOR reduction.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "pclmulqdq",
    target_feature = "avx2",
    not(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))
))]
#[inline]
#[target_feature(enable = "pclmulqdq", enable = "avx2")]
#[cfg_attr(target_feature = "vpclmulqdq", target_feature(enable = "vpclmulqdq"))]
fn butterfly_ymm(
    u: core::arch::x86_64::__m256i,
    v: core::arch::x86_64::__m256i,
    twiddle: u64,
) -> (core::arch::x86_64::__m256i, core::arch::x86_64::__m256i) {
    use core::arch::x86_64::*;
    use primitives::field::gf2_64x3::x86_64::reduce_halves256;

    #[cfg(target_feature = "vpclmulqdq")]
    let (even, odd) = {
        let tw = _mm256_set1_epi64x(twiddle as i64);
        (
            _mm256_clmulepi64_epi128::<0x00>(v, tw),
            _mm256_clmulepi64_epi128::<0x11>(v, tw),
        )
    };
    // Four 128-bit multiplies; immediate bit 0 picks the qword of `v`.
    #[cfg(not(target_feature = "vpclmulqdq"))]
    let (even, odd) = {
        let tw = _mm_cvtsi64_si128(twiddle as i64);
        let (v01, v23) = (_mm256_castsi256_si128(v), _mm256_extracti128_si256::<1>(v));
        (
            _mm256_set_m128i(
                _mm_clmulepi64_si128::<0x00>(v23, tw),
                _mm_clmulepi64_si128::<0x00>(v01, tw),
            ),
            _mm256_set_m128i(
                _mm_clmulepi64_si128::<0x01>(v23, tw),
                _mm_clmulepi64_si128::<0x01>(v01, tw),
            ),
        )
    };
    let new_u = _mm256_xor_si256(u, reduce_halves256(even, odd));
    (new_u, _mm256_xor_si256(v, new_u))
}

/// Eight F64 butterflies as four independent NEON lane-pair reductions.
/// Loading all four bottom vectors before reducing them gives the out-of-order
/// core four independent PMULL chains to schedule, while one call amortizes
/// loop control and the duplicated twiddle/reduction constants over 8 lanes.
///
/// # Safety
/// Requires the `aes` target feature; `top`/`bot` must each point at eight
/// readable+writable F64 values.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline]
#[target_feature(enable = "aes")]
unsafe fn butterfly_lanes_neon_8(top: *mut F64, bot: *mut F64, twiddle: u64) {
    use core::arch::aarch64::*;
    use primitives::field::gf2_64::aarch64::reduce_pair_pmull4;

    // SAFETY: caller guarantees the two eight-element regions; F64 is
    // repr(transparent) over u64 and this function carries the aes feature.
    unsafe {
        let v0 = vld1q_u64(bot.cast());
        let v1 = vld1q_u64(bot.cast::<u64>().add(2));
        let v2 = vld1q_u64(bot.cast::<u64>().add(4));
        let v3 = vld1q_u64(bot.cast::<u64>().add(6));
        let tw = vdupq_n_u64(twiddle);

        let p00: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(v0), twiddle));
        let p01: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(v0),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));
        let p10: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(v1), twiddle));
        let p11: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(v1),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));
        let p20: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(v2), twiddle));
        let p21: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(v2),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));
        let p30: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(v3), twiddle));
        let p31: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(v3),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));

        let prod0 = reduce_pair_pmull4(p00, p01);
        let prod1 = reduce_pair_pmull4(p10, p11);
        let prod2 = reduce_pair_pmull4(p20, p21);
        let prod3 = reduce_pair_pmull4(p30, p31);

        let u0 = vld1q_u64(top.cast());
        let u1 = vld1q_u64(top.cast::<u64>().add(2));
        let u2 = vld1q_u64(top.cast::<u64>().add(4));
        let u3 = vld1q_u64(top.cast::<u64>().add(6));
        let new_u0 = veorq_u64(u0, prod0);
        let new_u1 = veorq_u64(u1, prod1);
        let new_u2 = veorq_u64(u2, prod2);
        let new_u3 = veorq_u64(u3, prod3);
        let new_v0 = veorq_u64(v0, new_u0);
        let new_v1 = veorq_u64(v1, new_u1);
        let new_v2 = veorq_u64(v2, new_u2);
        let new_v3 = veorq_u64(v3, new_u3);

        vst1q_u64(top.cast(), new_u0);
        vst1q_u64(top.cast::<u64>().add(2), new_u1);
        vst1q_u64(top.cast::<u64>().add(4), new_u2);
        vst1q_u64(top.cast::<u64>().add(6), new_u3);
        vst1q_u64(bot.cast(), new_v0);
        vst1q_u64(bot.cast::<u64>().add(2), new_v1);
        vst1q_u64(bot.cast::<u64>().add(4), new_v2);
        vst1q_u64(bot.cast::<u64>().add(6), new_v3);
    }
}

/// Eight F64 butterflies with a shared twiddle, one per 64-bit lane of an AVX-512 register.
///
/// # Safety
///
/// - Requires VPCLMULQDQ and AVX-512F.
/// - Each pointer must address eight readable and writable words.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx2")]
unsafe fn butterfly_lanes_avx512(top: *mut F64, bot: *mut F64, twiddle: u64) {
    use core::arch::x86_64::*;
    // SAFETY:
    // - The caller supplies two valid eight-word rows.
    // - This function's target features cover every intrinsic below.
    unsafe {
        let (new_u, new_v) = butterfly_zmm(_mm512_loadu_si512(top.cast()), _mm512_loadu_si512(bot.cast()), twiddle);
        _mm512_storeu_si512(top.cast(), new_u);
        _mm512_storeu_si512(bot.cast(), new_v);
    }
}

/// [`butterfly_lanes_avx512`] over the lanes set in `mask` only.
///
/// # Safety
///
/// - Requires VPCLMULQDQ and AVX-512F.
/// - Each pointer must address the masked lanes, readable and writable; the others are never touched.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx2")]
unsafe fn butterfly_lanes_avx512_masked(top: *mut F64, bot: *mut F64, twiddle: u64, mask: u8) {
    use core::arch::x86_64::*;
    // SAFETY: masked loads and stores touch only the lanes the caller vouches for.
    unsafe {
        let u = _mm512_maskz_loadu_epi64(mask, top.cast());
        let v = _mm512_maskz_loadu_epi64(mask, bot.cast());
        let (new_u, new_v) = butterfly_zmm(u, v, twiddle);
        _mm512_mask_storeu_epi64(top.cast(), mask, new_u);
        _mm512_mask_storeu_epi64(bot.cast(), mask, new_v);
    }
}

/// Eight butterflies `u' = u + v * t`, `v' = v + u'` in registers, one per 64-bit lane.
///
/// # Algorithm
///
/// ```text
///     products:   even lanes 0,2,4,6 -> CLMUL 0x00      odd lanes 1,3,5,7 -> CLMUL 0x11
///                 each 128-bit lane then holds one whole 128-bit product
///
///     unpack:     lo = [ lo(p_0), lo(p_1), ..., lo(p_7) ]     hi = [ hi(p_0), ..., hi(p_7) ]
///
///     reduce:     p = lo + hi * x^64,  x^64 = x^4 + x^3 + x + 1
///                 p mod f = lo ^ g(hi ^ spill),  g(y) = y ^ y<<1 ^ y<<3 ^ y<<4
///                 spill = hi>>61 ^ hi>>60, the bits g pushes past x^63 (hi has 63 bits)
/// ```
///
/// - The unpacks stay inside 128-bit lanes, so no shuffle crosses lanes.
/// - The reduction takes shifts and three-way XORs, `vpternlogq 0x96`, instead of two more carry-less multiplies.
/// - Zen 5 has one carry-less multiplier per core, so those two would dominate the kernel.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx2")]
fn butterfly_zmm(
    u: core::arch::x86_64::__m512i,
    v: core::arch::x86_64::__m512i,
    twiddle: u64,
) -> (core::arch::x86_64::__m512i, core::arch::x86_64::__m512i) {
    butterfly_zmm_v(u, v, core::arch::x86_64::_mm512_set1_epi64(twiddle as i64))
}

/// [`butterfly_zmm`] with the twiddle already broadcast to every lane.
///
/// The product's high half has at most 63 bits (two 64-bit factors), so its bit 63, which `hi >> 63` would
/// spill, is always clear and that shift is left out. With GFNI the reduction's shifts are byte maps instead
/// ([`gfni_reduce`]): fewer instructions on Zen 4's shift pipes.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline(always)]
fn butterfly_zmm_v(
    u: core::arch::x86_64::__m512i,
    v: core::arch::x86_64::__m512i,
    tw: core::arch::x86_64::__m512i,
) -> (core::arch::x86_64::__m512i, core::arch::x86_64::__m512i) {
    use core::arch::x86_64::*;
    // SAFETY: the cfg enables vpclmulqdq and avx512f, which every intrinsic below needs.
    unsafe {
        // Products v * t: even lanes, then odd lanes, one 128-bit product per 128-bit lane.
        let even = _mm512_clmulepi64_epi128::<0x00>(v, tw);
        let odd = _mm512_clmulepi64_epi128::<0x11>(v, tw);
        // Back to lane order: qword i of lo / hi is the low / high half of lane i's product.
        let lo = _mm512_unpacklo_epi64(even, odd);
        let hi = _mm512_unpackhi_epi64(even, odd);

        // Reduce modulo x^64 + x^4 + x^3 + x + 1 with three-way XORs, and byte maps or shifts.
        const XOR3: i32 = 0x96;
        #[cfg(target_feature = "gfni")]
        let red = {
            use gfni_reduce::{H, L, T};
            // g(hi) byte by byte: each byte's product by 0x1B is its low byte in place, and its high nibble a
            // byte up; the top byte's high nibble wraps to byte 0 and stands for the spill, whose own product
            // by 0x1B lands in byte 0 too: rotating the nibbles leaves the spill once, which T adds in times 0x1A.
            let low = _mm512_gf2p8affine_epi64_epi8::<0>(hi, _mm512_set1_epi64(L));
            let high = _mm512_rol_epi64::<8>(_mm512_gf2p8affine_epi64_epi8::<0>(hi, _mm512_set1_epi64(H)));
            let spill = _mm512_gf2p8affine_epi64_epi8::<0>(_mm512_srli_epi64::<56>(hi), _mm512_set1_epi64(T));
            _mm512_ternarylogic_epi64::<XOR3>(low, high, spill)
        };
        #[cfg(not(target_feature = "gfni"))]
        let red = {
            // hi ^ the bits of hi * (x^4 + x^3 + x + 1) that land past x^63 (bit 63 of hi is clear): both are
            // multiplied by the same constant, so they are folded first.
            let x = _mm512_ternarylogic_epi64::<XOR3>(hi, _mm512_srli_epi64::<61>(hi), _mm512_srli_epi64::<60>(hi));
            // g(x) = x ^ x<<1 ^ x<<3 ^ x<<4, split across two three-way XORs.
            let fx = _mm512_ternarylogic_epi64::<XOR3>(x, _mm512_slli_epi64::<1>(x), _mm512_slli_epi64::<3>(x));
            _mm512_xor_si512(fx, _mm512_slli_epi64::<4>(x))
        };
        // u' = u + v * t, with the product's lo and the reduced high half folded in one step.
        let new_u = _mm512_ternarylogic_epi64::<XOR3>(u, lo, red);
        (new_u, _mm512_xor_si512(v, new_u))
    }
}

/// The byte maps of the reduction on GFNI, as `vgf2p8affineqb` matrices.
///
/// A product's high half `hi` (at most 63 bits) is folded in as `g(hi ^ spill)`, `g(y) = y · 0x1B` truncated to
/// 64 bits and `spill` the bits of `hi · 0x1B` past bit 63 (three at most). Byte by byte, `b · 0x1B` is twelve
/// bits: its low byte `L(b)` stays in place and its high nibble `H(b)` moves a byte up. The top byte's nibble moves
/// out: it is the spill. So `g(hi ^ spill) = L(hi) ^ rotl8(H(hi)) ^ T(top byte)` in byte 0, `T(b) = H(b) · 0x1A`:
/// the rotation brings the spill to byte 0 once, and `spill · 0x1B ^ spill = spill · 0x1A`.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "vpclmulqdq",
    target_feature = "avx512f",
    target_feature = "gfni"
))]
mod gfni_reduce {
    /// The carry-less product of two 16-bit polynomials, truncated.
    const fn clmul16(a: u16, b: u16) -> u16 {
        let mut acc = 0;
        let mut j = 0;
        while j < 16 {
            if (b >> j) & 1 == 1 {
                acc ^= a << j;
            }
            j += 1;
        }
        acc
    }

    /// The byte map `which` (0: L, 1: H, 2: T) of one byte.
    const fn map(which: u8, b: u8) -> u8 {
        let p = clmul16(b as u16, 0x1B);
        match which {
            0 => p as u8,
            1 => (p >> 8) as u8,
            _ => clmul16(p >> 8, 0x1A) as u8,
        }
    }

    /// The matrix of byte map `which`: output bit `i` is the parity of the input under byte `7 - i`.
    const fn matrix(which: u8) -> i64 {
        let mut m = 0u64;
        let mut i = 0;
        while i < 8 {
            let mut row = 0u64;
            let mut j = 0;
            while j < 8 {
                if (map(which, 1 << j) >> i) & 1 == 1 {
                    row |= 1 << j;
                }
                j += 1;
            }
            m |= row << (8 * (7 - i));
            i += 1;
        }
        m as i64
    }

    pub(super) const L: i64 = matrix(0);
    pub(super) const H: i64 = matrix(1);
    pub(super) const T: i64 = matrix(2);
}

/// Two F64 butterflies with a shared twiddle, NEON-resident end to end.
/// The two products issue as PMULL/PMULL2 on the loaded row (no lane
/// extraction) and reduce through the all-PMULL lane-pair fold
/// ([`primitives::field::gf2_64::aarch64::reduce_pair_pmull4`]), replacing the
/// old 10-op shift-XOR fold chain.
///
/// # Safety
/// Requires the `aes` target feature; `top`/`bot` must each point at two
/// readable+writable F64 values.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline]
#[target_feature(enable = "aes")]
unsafe fn butterfly_lane_pair_neon(top: *mut F64, bot: *mut F64, twiddle: u64) {
    use core::arch::aarch64::*;
    use primitives::field::gf2_64::aarch64::reduce_pair_pmull4;
    // SAFETY: caller guarantees the pointees; F64 is repr(transparent) u64.
    unsafe {
        let u = vld1q_u64(top as *const u64);
        let v = vld1q_u64(bot as *const u64);
        // Products v_lane * twiddle: PMULL on the low lanes, PMULL2 on the
        // highs (the dup is loop-invariant and hoisted after inlining).
        let tw = vdupq_n_u64(twiddle);
        let p0: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(v), twiddle));
        let p1: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(v),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));
        let prod = reduce_pair_pmull4(p0, p1);
        let new_u = veorq_u64(u, prod);
        let new_v = veorq_u64(v, new_u);
        vst1q_u64(top as *mut u64, new_u);
        vst1q_u64(bot as *mut u64, new_v);
    }
}

#[cfg(test)]
mod adversarial;

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// Scalar reference: one butterfly at a time over `num_ntts` interleaved lanes.
    fn forward_scalar_from_layer(ntt: &AdditiveNttF64, data: &mut [F64], num_ntts: usize, start_layer: usize) {
        let n_total = data.len();
        let log_d = log2_strict_usize(n_total / num_ntts);

        for layer in start_layer..log_d {
            let num_blocks = 1usize << layer;
            let block_size = 1usize << (log_d - layer);
            let block_size_half = block_size >> 1;
            let block_elems = block_size * num_ntts;
            for block in 0..num_blocks {
                let twiddle = ntt.twiddle(layer, block);
                let block_start = block * block_elems;
                for row in 0..block_size_half {
                    let off_top = block_start + row * num_ntts;
                    let off_bot = off_top + block_size_half * num_ntts;
                    for lane in 0..num_ntts {
                        let v = data[off_bot + lane];
                        let new_u = data[off_top + lane] + v * twiddle;
                        data[off_top + lane] = new_u;
                        data[off_bot + lane] = v + new_u;
                    }
                }
            }
        }
    }

    #[test]
    fn two_sweep_encodes_match_the_row_major_encode() {
        // Invariant: the two-sweep encodes from the message as it lies give the codeword the row-major encode
        // gives (of the transpose, for a lane-major message), word for word: every row through
        // `encode_two_sweep_with`, whatever the batch of replicas, and any rows through `encoded_rows_two_sweep`.
        let mut rng = Rng::new(0x1A4E);
        for (layout, log_rows, n, log_inv_rate) in [
            (MsgLayout::LaneMajor, 13usize, 63usize, 1usize),
            (MsgLayout::LaneMajor, 12, 40, 1),
            (MsgLayout::LaneMajor, 12, 3, 2),
            (MsgLayout::LaneMajor, 14, 17, 1),
            // Large enough for streaming stores (`STREAM_MIN_WORDS`).
            (MsgLayout::LaneMajor, 17, 64, 1),
            (MsgLayout::RowMajor, 13, 48, 4),
            (MsgLayout::RowMajor, 12, 6, 2),
            (MsgLayout::RowMajor, 14, 3, 1),
        ] {
            let shape = format!("{layout:?} {log_rows}/{n}/{log_inv_rate}");
            let rows = 1usize << log_rows;
            let msg: Vec<F64> = (0..n << log_rows).map(|_| F64(rng.next_u64())).collect();
            let ntt = AdditiveNttF64::standard(log_rows + log_inv_rate);
            let mut want = vec![F64::ZERO; msg.len() << log_inv_rate];
            match layout {
                MsgLayout::LaneMajor => {
                    transpose_lane_major(&mut want[..msg.len()], &msg, n, log_rows);
                    ntt.encode_interleaved_in_place(&mut want, n, log_inv_rate);
                }
                MsgLayout::RowMajor => ntt.encode_interleaved_with(&mut want, &msg, n, log_inv_rate, &|_, _| {}),
            }

            for batch in [1usize, 3] {
                let got = std::sync::Mutex::new(vec![F64::ZERO; want.len()]);
                let mut work = vec![F64::ZERO; batch * msg.len()];
                let sink = |row: usize, block: &[F64]| {
                    got.lock().unwrap()[row * n..][..block.len()].copy_from_slice(block);
                };
                assert!(ntt.encode_two_sweep_with(&mut work, &msg, layout, n, log_inv_rate, &sink));
                assert!(*got.lock().unwrap() == want, "every row, batch {batch}, {shape}");
            }
            // Straight into the codeword: the codeword, and every row handed over.
            let got = std::sync::Mutex::new(vec![F64::ZERO; want.len()]);
            let sink = |row: usize, block: &[F64]| {
                got.lock().unwrap()[row * n..][..block.len()].copy_from_slice(block);
            };
            let mut codeword: Vec<F64> = (0..want.len()).map(|_| F64(rng.next_u64())).collect();
            assert!(ntt.encode_two_sweep_into(&mut codeword, &msg, layout, n, log_inv_rate, &sink));
            assert!(codeword == want, "the codeword, {shape}");
            assert!(*got.lock().unwrap() == want, "every row into the codeword, {shape}");

            let mut wanted: Vec<usize> = (0..40)
                .map(|_| rng.next_u64() as usize % (rows << log_inv_rate))
                .collect();
            wanted.extend([0, (rows << log_inv_rate) - 1, rows, rows - 1]);
            wanted.sort_unstable();
            wanted.dedup();
            let found = ntt
                .encoded_rows_two_sweep(&msg, layout, n, log_inv_rate, &wanted)
                .expect("a two-sweep shape");
            for (i, &q) in wanted.iter().enumerate() {
                assert_eq!(found[i * n..(i + 1) * n], want[q * n..(q + 1) * n], "row {q}, {shape}");
            }
        }
    }

    /// Check forward∘inverse = id and scalar == parallel.
    #[test]
    fn inverse_roundtrip_and_variants_agree() {
        let ntt = AdditiveNttF64::standard(12);
        let mut rng = Rng::new(1);
        for log_d in [1usize, 3, 6, 10] {
            let n = 1usize << log_d;
            let orig: Vec<F64> = (0..n).map(|_| F64(rng.next_u64())).collect();

            let mut a = orig.clone();
            forward_scalar_from_layer(&ntt, &mut a, 1, 0);
            let mut c = orig.clone();
            ntt.transform(&mut c, 1, 0, None, None, None);
            assert_eq!(a, c, "parallel == scalar at log_d={log_d}");

            ntt.inverse_transform(&mut a);
            assert_eq!(a, orig, "inverse roundtrip at log_d={log_d}");
        }
    }

    #[test]
    fn interleaved_parallel_matches_scalar() {
        // Invariant: the parallel transform equals the scalar reference, word for word.
        //
        // Each shape forces one plan of the driver, under the budgets used off Apple silicon:
        //
        //     (log_d, lanes, start)   plan
        //     (7, 3, 0)               deep pass only, a single sub-block
        //     (12, 8, 0 or 1)         one gathered pass, then deep sub-blocks
        //     (14, 64, 0 or 1)        one gathered pass, then deep sub-blocks
        //     (10, 2048, 0)           wide rows shrink the cache budgets: one gathered pass
        //     (12, 2048, 1)           two gathered passes, with streaming stores
        //
        // A non-zero start is the commit path, which enters at the rate layer.
        let mut rng = Rng::new(0xC0FFEE);
        for (log_d, lanes, start_layer) in [
            (7usize, 3usize, 0usize),
            (12, 8, 0),
            (12, 8, 1),
            (14, 64, 0),
            (14, 64, 1),
            (10, 2048, 0),
            (12, 2048, 1),
        ] {
            let ntt = AdditiveNttF64::standard(log_d);
            let original: Vec<F64> = (0..lanes << log_d).map(|_| F64(rng.next_u64())).collect();

            // Reference: one butterfly at a time.
            let mut want = original.clone();
            forward_scalar_from_layer(&ntt, &mut want, lanes, start_layer);
            // Under test: the pass-planning driver.
            let mut got = original;
            ntt.transform(&mut got, lanes, start_layer, None, None, None);

            assert_eq!(got, want, "log_d={log_d}, lanes={lanes}, start_layer={start_layer}");
        }
    }

    #[test]
    fn fused_encode_matches_replicate_then_transform() {
        // Invariant: encoding in place equals replicating the message, then transforming.
        //
        // The in-place encode never materializes the replicas up front.
        // Its message is the buffer's own first replica, which the plan must overwrite last.
        // The plans are those of the budgets used off Apple silicon.
        //
        //     (log_d, lanes, rate)   plan
        //     (9, 8, 1)              replicate first, then deep pass only
        //     (12, 64, 2)            one gathered pass reading the first replica
        //     (14, 8, 1)             one gathered pass reading the first replica
        //     (14, 64, 2)            one gathered pass reading the first replica
        //     (12, 2048, 1)          two gathered passes, with streaming stores
        //     (4, 8, 4)              rate = log_d: no layer left, rows handed over at the end
        //
        // The handed-over rows must tile the codeword once, each block already final.
        let mut rng = Rng::new(0xE0C0DE);
        for (log_d, lanes, log_inv_rate) in [
            (9usize, 8usize, 1usize),
            (12, 64, 2),
            (14, 8, 1),
            (14, 64, 2),
            (12, 2048, 1),
            (4, 8, 4),
        ] {
            let ntt = AdditiveNttF64::standard(log_d);
            let msg_len = (lanes << log_d) >> log_inv_rate;
            let msg: Vec<F64> = (0..msg_len).map(|_| F64(rng.next_u64())).collect();

            // Reference: 2^rate explicit copies, then the scalar transform from the rate layer.
            let mut want = vec![F64::ZERO; msg_len << log_inv_rate];
            replicate_rows(&mut want, &msg);
            forward_scalar_from_layer(&ntt, &mut want, lanes, log_inv_rate);

            // Under test: only the first replica holds the message, the rest is zero.
            let mut got = vec![F64::ZERO; msg_len << log_inv_rate];
            got[..msg_len].copy_from_slice(&msg);
            let blocks = std::sync::Mutex::new(Vec::new());
            ntt.encode_interleaved_in_place_with(&mut got, lanes, log_inv_rate, &|row, rows| {
                blocks.lock().unwrap().push((row, rows.to_vec()))
            });
            assert_eq!(got, want, "log_d={log_d}, lanes={lanes}, rate={log_inv_rate}");

            let mut blocks = blocks.into_inner().unwrap();
            blocks.sort_by_key(|b| b.0);
            let mut next = 0;
            for (row, rows) in blocks {
                assert_eq!(row, next, "blocks tile the rows, log_d={log_d}");
                assert_eq!(
                    rows[..],
                    want[row * lanes..][..rows.len()],
                    "a handed-over block is final"
                );
                next += rows.len() / lanes;
            }
            assert_eq!(next, 1 << log_d, "every row handed over, log_d={log_d}");
        }
    }

    /// Every lane of the codeword must be exactly the single-lane RS codeword of
    /// that lane's contiguous message block, which is what makes a commitment over
    /// `n_lanes` lanes equal to the `2^log_batch_size`-lane one with a zero tail.
    /// The shapes cover the transposing fused first pass, its fallback, and lane
    /// counts that are not powers of two (the padding-free commit's whole point).
    #[test]
    fn lane_major_msg_encode_matches_per_lane_reference() {
        let mut rng = Rng::new(0x1A2E);
        for (log_rows, log_inv_rate, n_lanes) in [
            (2usize, 1usize, 3usize),
            (3, 1, 1),
            (5, 2, 7),
            (9, 1, 5),
            (12, 2, 37),
            (14, 1, 64),
        ] {
            let log_d = log_rows + log_inv_rate;
            let ntt = AdditiveNttF64::standard(log_d);
            let rows = 1usize << log_rows;
            let msg: Vec<F64> = (0..rows * n_lanes).map(|_| F64(rng.next_u64())).collect();

            let mut got = vec![F64::ZERO; msg.len() << log_inv_rate];
            transpose_lane_major(&mut got[..msg.len()], &msg, n_lanes, log_rows);
            ntt.encode_interleaved_in_place(&mut got, n_lanes, log_inv_rate);

            let block_len = 1usize << log_d;
            for lane in 0..n_lanes {
                // Lane `lane` encodes message block `n_lanes - 1 - lane`.
                let block = n_lanes - 1 - lane;
                let mut want = vec![F64::ZERO; block_len];
                replicate_rows(&mut want, &msg[block * rows..(block + 1) * rows]);
                ntt.transform(&mut want, 1, log_inv_rate, None, None, None);
                for pos in 0..block_len {
                    assert_eq!(
                        got[pos * n_lanes + lane],
                        want[pos],
                        "lane {lane} pos {pos} at log_rows={log_rows}, rate={log_inv_rate}, n_lanes={n_lanes}"
                    );
                }
            }
        }
    }

    #[test]
    fn interleaved_lanes_are_independent_ntts() {
        let ntt = AdditiveNttF64::standard(10);
        let mut rng = Rng::new(2);
        let log_d = 7;
        let n = 1usize << log_d;
        for lanes in [1usize, 2, 4, 8, 64] {
            // SoA buffer + per-lane copies.
            let mut soa = vec![F64::ZERO; n * lanes];
            let mut per_lane: Vec<Vec<F64>> = vec![vec![F64::ZERO; n]; lanes];
            for pos in 0..n {
                for lane in 0..lanes {
                    let v = F64(rng.next_u64());
                    soa[pos * lanes + lane] = v;
                    per_lane[lane][pos] = v;
                }
            }
            ntt.transform(&mut soa, lanes, 0, None, None, None);
            for (lane, lane_data) in per_lane.iter_mut().enumerate() {
                forward_scalar_from_layer(&ntt, lane_data, 1, 0);
                for pos in 0..n {
                    assert_eq!(soa[pos * lanes + lane], lane_data[pos]);
                }
            }
        }
    }
}
