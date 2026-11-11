// Vendored from leanVM (https://github.com/leanEthereum/leanVM), commit c445e3d51a5a85031df47240595698f3b24897bf, file crates/pcs/src/whir.rs.
// MIT OR Apache-2.0 (see LICENSE-MIT, LICENSE-APACHE and AGENTS.md at the repository root).
// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Added here: a lane tensor may carry a scale for every lane of the cube (`LaneTensor::scales`, `tensor_lane_rounds`),
// for a claim at a point of the whole stack opened against a commitment of its leading lanes (the rest zero), as a
// verifier that knows only `log_n` checks it (`crates/pcs_claim`); a tensor of one scale per committed lane is proven
// as before.
// Modified here, in the prover alone and with every proof unchanged, to cut its memory: `commit_tree` (and
// `commit_tree_in`), a commitment encoded one replica at a time that keeps its Merkle tree alone, and
// `encoded_rows`, the rows an opening reads from it, encoded again; deeper levels whose codeword reaches 1 GiB
// kept the same way (`LigeroRows`); and `recursive_prover_with_lane_tensors`, the lane rounds on a weight given
// as lane tensors rather than written out, its committed message freed once the first queries are answered.
// One comment corrected (no code change): the level-0 query grinding is `QUERY_GRINDING_BITS = 17` bits in the
// production profile, not "0 bits" as leanVM's comment says (`whir_config.rs`, and the verifier's
// `QUERY_GRINDING_BITS`); to report upstream.
// Also modified here, for speed, every proof unchanged: `commit` (into its codeword, `encode_two_sweep_into`),
// `commit_tree`, `encoded_rows` and the lean deeper levels
// encode in two sweeps from the message as it lies (`AdditiveNttF64::encode_two_sweep_with`,
// `encoded_rows_two_sweep`; a lean level holds `LEAN_BATCH` replicas' work buffers while it commits), and the lane
// rounds sum sparse low weights at their nonzero entries alone (`SparseLow`), the dense ones with `dot_base` on x86,
// and fold the witness on AVX-512 eight words at a time (`collapse_avx512`); a lean level's message, kept for its
// queries, is copied by the workers (`copied`) rather than by one thread. A test pins the chunked dense induce to its
// per-query form (`chunked_induce_matches_the_per_query_one`). The E rounds (the folds, their messages, the OOD
// evaluation, the glue, the collapsed weight) take four products at a time (`mul4`, `mul_unreduced4`;
// `vectored_ext_rounds_match_one_product_at_a_time`). A dense low weight is told from its first chunk, a sparse one's
// entries collected in parallel (`sparse_lows`).
// Also added here, for speed, every proof unchanged: the lane tensors' inner products with the committed lanes as a
// public function (`dense_lane_inner_products`, which a commitment's out-of-domain answer is computed by), the lane
// rounds given some of them (`recursive_prover_with_lane_tensors_known`), and several openings on one commitment at
// once (`recursive_prover_with_lane_tensors_batch`, `LaneJob`): their lane rounds read the message twice in all (the
// inner products in one pass, every opening's collapse in another), then each opening goes on as alone
// (`after_lane_rounds`, the rest of `recursive_prover` from level 1's commitment). A lane tensor's low weight is a
// `Low`: a table as before, or `eq(point, ·)`, read a chunk at a time as two small tables' product (`EqSplit`,
// `Chunked`) and never written out.
// Added here, for speed, every proof unchanged: a commitment and an opening told which committed lanes are all zero
// encode the others alone, the zero lanes' words of each row zero when it is hashed or opened
// (`commit_tree_skipping_in`, `encoded_rows_skipping`, `recursive_prover_with_lane_tensors_skipping`; the L0 rows'
// source `L0Rows`; with the batched openings, `recursive_prover_with_lane_tensors_batch`'s `zero_lanes`).
// Changed here, every proof unchanged: `commit_tree_skipping_in`'s spread rows are lent from a list the commitment
// owns (and frees), not from a thread-local buffer that kept a tile's whole rows on every worker after it. A test,
// `vectored_ext_rounds_match_one_product_at_a_time`, calls the round kernels at powers of two alone (their
// `debug_assert`s), its other lengths testing the folds' and the terms' tails. `collapse_avx512::stage` asserts its
// bounds (it checked them only with a `debug_assert`; once a call, a block of every lane `packed` names).
// Added here, for speed, every proof unchanged (`docs/PERF_PROVER2.md`): a kept codeword of the lanes not flagged all
// zero alone (`commit_skipping`, read through `L0Rows::Compact`); the lane rounds' passes leave the flagged lanes out
// (`lane_inner_products`, `collapse_lanes`, `dense_lane_inner_products_skipping`); and a batch's openings, made in
// turn, keep their level-1 codewords up to 2 GiB (`LEAN_LIGERO_BYTES_IN_TURN`; `after_lane_rounds`' `lean_bytes`).

//! WHIR with `K = GF(2)[x]/(x^64+x^4+x^3+x+1)` and
//! `E = K[y]/(y^3+y+1)`.
//!
//! The committed message is a
//! vector of [`F64`] values; every verifier challenge, sumcheck message, basis
//! poly, and post-fold witness is [`F192`]-valued.
//!
//! Representations:
//! - committed message / L0 codeword / L0 opened rows: `F64` (8 bytes)
//! - challenges, sumcheck messages, folded witnesses, deeper-level codewords
//!   and opened rows, `b_initial`, betas, alphas, `yr`: `F192` (24 bytes)
//! - the RS-encoding evaluation domain and all LCH twiddles stay in K, so the
//!   deeper-level (E-valued) encodes use K-twiddles via the mixed product
//!   [`F192::mul_base`] (3 PMULL) instead of a full E multiplication.
//!
//! Soundness note: [`WhirSecurityConfig`] analyzes the actual challenge
//! field size `q = 2^192`; the committed alphabet remains `K = GF(2^64)`.

use crate::merkle::{self, Hash};
use crate::ntt::AdditiveNttF64;
use crate::ntt::additive_ntt_f64::MsgLayout;
use fiat_shamir::merkle::PrunedMerklePaths;
use fiat_shamir::transcript::ProverState;
use primitives::{
    field::{F64, F192, F192Unreduced, mul_unreduced4, mul4, powers},
    stream::Stream,
};

pub use super::whir_config::{
    FinalBlockConfig, INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0, LevelShapes, MAX_LOG_INV_RATE, MIN_LOG_INV_RATE,
    ProverConfig, QUERY_GRINDING_BITS, RESIDUAL_MAX_LOG, RS_DOMAIN_INITIAL_REDUCTION_FACTOR, SECURITY_BITS,
    SUBSEQUENT_FOLDING_FACTOR, WhirLevelConfig, WhirSecurityConfig, validate_log_inv_rate,
};
#[cfg(test)]
pub use super::whir_config::{default_config, udr_queries};

pub use crate::whir_induce::*;
use crate::whir_ntt_ext::*;

// ===================================================================
// Multilinear helpers over E
// ===================================================================

/// Build the eq-MLE table at `point`, LSB-first, without dispatching to the worker pool.
pub fn build_eq_table_ext(point: &[F192]) -> Vec<F192> {
    let d = point.len();
    let mut out: Vec<F192> = Vec::with_capacity(1usize << d);
    out.push(F192::ONE);
    for j in 0..d {
        let r_j = point[j];
        let len = 1usize << j;
        out.resize(2 * len, F192::ZERO);
        for i in 0..len {
            let v = out[i];
            let high = v * r_j;
            out[i + len] = high;
            out[i] = v + high;
        }
    }
    out
}

use primitives::multilinear::eq_table as build_eq_table_ext_parallel;

/// Mixed inner product `Σ_i b[i] · witness[i]` (E x K via `mul_base`). The
/// evaluation-claim `target` for a K-witness against an E-basis.
pub fn inner_product_base_ext(witness: &[F64], b: &[F192]) -> F192 {
    assert_eq!(witness.len(), b.len());
    const PAR_THRESHOLD: usize = 4096;
    if witness.len() < PAR_THRESHOLD {
        return witness
            .iter()
            .zip(b.iter())
            .map(|(&w, &e)| e.mul_base(w))
            .fold(F192::ZERO, |a, v| a + v);
    }
    parallel::map_reduce(
        witness.len(),
        || F192::ZERO,
        |i| b[i].mul_base(witness[i]),
        |a, v| a + v,
    )
}

// ===================================================================
// Config reuse
// ===================================================================

/// Derive the shared prover/verifier config for a K-witness of `2^log_n` F64
/// elements at L0 inverse-rate logarithm `log_inv_rate`, using the production
/// 128-bit Johnson/OOD profile at `m = log_n + LOG_PACKING`.
pub fn config_for_rate(log_n: usize, log_inv_rate: usize) -> Result<ProverConfig, String> {
    let sec = WhirSecurityConfig::derive_config_with_log_inv_rate(log_n + crate::LOG_PACKING, log_inv_rate)?;
    sec.to_config()
}

// ===================================================================
// Commit: F64 message -> interleaved RS codeword -> Merkle root
// ===================================================================

/// Public commitment for an `F64` message: the L0 Merkle root.
#[derive(Clone, Debug)]
pub struct Commitment {
    pub root: Hash,
}

/// Prover-side state retained after commit for the opening phase. The message
/// itself is not stored; the caller retains it for opening.
pub struct ProverData {
    pub codeword: Vec<F64>,
    pub merkle_tree: Vec<Hash>,
}

/// Commit to the `F64` message of a `2^log_n`-word witness: the message is its
/// leading `n_lanes` lane blocks of `2^(log_n - log_batch_size)` words each, one
/// RS codeword per lane, Merkle-committed one leaf per codeword position, the
/// leaf being that position across all `2^log_batch_size` lanes
/// (`2^log_batch_size * 8` bytes).
///
/// `n_lanes` is read off the message length, and `n_lanes < 2^log_batch_size` is
/// the padding-free case: the stacked witness's zero tail is whole lanes, so those
/// lanes are never encoded. Their codeword is zero (the encoding is linear), so the
/// leaf image is the one a full-width commitment would have hashed, with those
/// zeros LEADING it: lane `t` of the codeword is message block `n_lanes-1-t`, which
/// puts them at the front of the image where their whole chunks are one sponge
/// state every leaf shares. Only the image's tail, the committed lanes,
/// rides the proof, so a verifier derives `n_lanes` from the announced layout to
/// read a row and supplies the prefix itself.
pub fn commit(message: &[F64], log_n: usize, log_batch_size: usize, log_inv_rate: usize) -> (Commitment, ProverData) {
    assert!(log_inv_rate >= 1, "log_inv_rate must be >= 1 for a non-trivial RS code");
    assert!(log_n > log_batch_size, "witness must be wider than the interleaving");
    let log_rows = log_n - log_batch_size;
    let n_lanes = message.len() >> log_rows;
    assert_eq!(message.len(), n_lanes << log_rows, "message is whole lane blocks");
    assert!(
        n_lanes >= 1 && n_lanes <= 1usize << log_batch_size,
        "at most 2^log_batch_size lanes carry data"
    );
    let k_code = log_rows + log_inv_rate;
    let n_positions = 1usize << k_code;
    let codeword_len = n_positions * n_lanes;

    // SAFETY: every codeword element is written before it is read.
    // `transpose_lane_major` covers every word of the message region (its tiles are
    // asserted to), and `encode_interleaved_in_place` writes every other replica from
    // it before transforming that region in place. The two-sweep encode instead writes every word of every
    // replica in its first sweep (each task its residues of every tile, the tasks covering them) before the second
    // reads a tile, or, with no first sweep, fills each tile from the message.
    let mut codeword = unsafe { primitives::uninit_vec::<F64>(codeword_len) };

    // Leaves are hashed as the encode finishes each block of rows.
    let tree = merkle::MerkleBuilder::new(n_positions, n_lanes, 1usize << log_batch_size);
    tracing::info_span!("NTT", kind = "base encode", log_domain = k_code, lanes = n_lanes).in_scope(|| {
        let ntt = AdditiveNttF64::standard(k_code);
        let on_rows = |row: usize, rows: &[F64]| tree.absorb(row, rows);
        // From the lane-major message in two sweeps where the shape allows it, straight into the codeword.
        if ntt.encode_two_sweep_into(
            &mut codeword,
            message,
            MsgLayout::LaneMajor,
            n_lanes,
            log_inv_rate,
            &on_rows,
        ) {
            return;
        }
        crate::ntt::transpose_lane_major(&mut codeword[..message.len()], message, n_lanes, log_rows);
        ntt.encode_interleaved_in_place_with(&mut codeword, n_lanes, log_inv_rate, &on_rows);
    });
    let merkle_tree = tracing::info_span!("Merkle").in_scope(|| tree.finish());
    let root = *merkle_tree.last().expect("merkle tree non-empty");

    (Commitment { root }, ProverData { codeword, merkle_tree })
}

/// [`commit`], keeping the Merkle tree alone: the codeword is encoded one replica (`2^-log_inv_rate` of it) at
/// a time into one replica's buffer, each hashed as it is finished, so the commitment holds the message, one
/// replica and the tree at once rather than the whole codeword. The root and tree are [`commit`]'s; an opening
/// reads its rows with [`encoded_rows`].
pub fn commit_tree(
    message: &[F64],
    log_n: usize,
    log_batch_size: usize,
    log_inv_rate: usize,
) -> (Commitment, Vec<Hash>) {
    commit_tree_in(message, log_n, log_batch_size, log_inv_rate, Vec::new())
}

/// [`commit_tree`], encoding in `scratch`'s allocation when that holds one replica (as many words as the
/// message): a buffer the caller is done with, so that the encode need not map fresh memory.
pub fn commit_tree_in(
    message: &[F64],
    log_n: usize,
    log_batch_size: usize,
    log_inv_rate: usize,
    scratch: Vec<F64>,
) -> (Commitment, Vec<Hash>) {
    let (n_lanes, log_rows) = lane_shape(message, log_n, log_batch_size, log_inv_rate);
    let k_code = log_rows + log_inv_rate;
    let tree = merkle::MerkleBuilder::new(1usize << k_code, n_lanes, 1usize << log_batch_size);
    tracing::info_span!(
        "NTT",
        kind = "base encode by replica",
        log_domain = k_code,
        lanes = n_lanes
    )
    .in_scope(|| {
        // From the lane-major message in two sweeps where the shape allows it, one replica at a time in
        // `scratch`'s allocation.
        let mut work = scratch;
        work.clear();
        work.reserve_exact(message.len());
        // SAFETY: the capacity holds the message's length of plain words, which the first sweep writes before
        // the second reads them.
        unsafe { work.set_len(message.len()) };
        let ntt = AdditiveNttF64::standard(k_code);
        let on_rows = |row: usize, rows: &[F64]| tree.absorb(row, rows);
        if ntt.encode_two_sweep_with(
            &mut work,
            message,
            MsgLayout::LaneMajor,
            n_lanes,
            log_inv_rate,
            &on_rows,
        ) {
            return;
        }
        each_replica(
            message,
            n_lanes,
            log_rows,
            log_inv_rate,
            work,
            |replica, ntt, buffer| {
                let first = replica << log_rows;
                ntt.encode_interleaved_in_place_with(buffer, n_lanes, 0, &|row, rows| tree.absorb(first + row, rows));
            },
        )
    });
    let merkle_tree = tracing::info_span!("Merkle").in_scope(|| tree.finish());
    let root = *merkle_tree.last().expect("merkle tree non-empty");
    (Commitment { root }, merkle_tree)
}

/// Words of codeword [`encoded_rows`] encodes at a time: 1 GiB. The transform's kernels are built for rows of
/// many lanes, and below some sixteen they slow down sharply (59 lanes of `2^23` positions, encoded whole: 16 at
/// a time 0.33 s, 8 at a time 0.46 s, 4 at a time 0.69 s, all at once 0.32 s).
const REENCODE_WORDS: usize = 1 << 27;

/// The rows of [`commit`]'s codeword at `positions` (in that order, repeats allowed), encoded again from the
/// message. Every lane is a codeword of its own, so they are encoded a few lanes at a time, in a buffer of at
/// most [`REENCODE_WORDS`] (or one lane's codeword).
pub fn encoded_rows(
    message: &[F64],
    log_n: usize,
    log_batch_size: usize,
    log_inv_rate: usize,
    positions: &[usize],
) -> Vec<Vec<F64>> {
    encoded_rows_within(message, log_n, log_batch_size, log_inv_rate, positions, REENCODE_WORDS)
}

/// [`encoded_rows`] in a buffer of at most `budget` words (or one lane's codeword).
fn encoded_rows_within(
    message: &[F64],
    log_n: usize,
    log_batch_size: usize,
    log_inv_rate: usize,
    positions: &[usize],
    budget: usize,
) -> Vec<Vec<F64>> {
    let (n_lanes, log_rows) = lane_shape(message, log_n, log_batch_size, log_inv_rate);
    let k_code = log_rows + log_inv_rate;
    let group = (budget >> k_code).clamp(1, n_lanes);
    let mut rows = vec![vec![F64::ZERO; n_lanes]; positions.len()];
    let _span = tracing::info_span!("NTT", kind = "base re-encode", log_domain = k_code, lanes = n_lanes).entered();
    let ntt = AdditiveNttF64::standard(k_code);
    let mut wanted = positions.to_vec();
    wanted.sort_unstable();
    wanted.dedup();
    // From the lane-major message in two sweeps where the shape allows it: one read of it for every replica.
    if let Some(found) = ntt.encoded_rows_two_sweep(message, MsgLayout::LaneMajor, n_lanes, log_inv_rate, &wanted) {
        return positions
            .iter()
            .map(|q| {
                let at = wanted.binary_search(q).expect("a wanted row");
                found[at * n_lanes..(at + 1) * n_lanes].to_vec()
            })
            .collect();
    }
    // SAFETY: every group starts with a transpose that writes its message region, from which the encode writes
    // the rest of its codeword before reading it.
    let mut buffer = unsafe { primitives::uninit_vec::<F64>(group << k_code) };
    for first in (0..n_lanes).step_by(group) {
        let g = group.min(n_lanes - first);
        let codeword = &mut buffer[..g << k_code];
        let lanes = &message[first << log_rows..(first + g) << log_rows];
        crate::ntt::transpose_lane_major(&mut codeword[..g << log_rows], lanes, g, log_rows);
        ntt.encode_interleaved_rows_in_place(codeword, g, log_inv_rate, &wanted);
        // The group's lane `t` is message block `first + g - 1 - t`, which the whole codeword puts at lane
        // `n_lanes - first - g + t`.
        for (row, &q) in rows.iter_mut().zip(positions) {
            row[n_lanes - first - g..n_lanes - first].copy_from_slice(&codeword[q * g..(q + 1) * g]);
        }
    }
    rows
}

/// The committed lanes of `message` (lane-major, `n_lanes` blocks of `2^log_rows` words) that are not all zero,
/// given by `zero[b]` (block `b` is zero): `(b, block)`, `b` ascending. `None` when none is zero (nothing to skip).
fn nonzero_blocks<'m>(message: &'m [F64], log_rows: usize, zero: &[bool]) -> Option<Vec<(usize, &'m [F64])>> {
    let n_lanes = message.len() >> log_rows;
    assert_eq!(zero.len(), n_lanes, "a flag for every committed lane");
    if !zero.iter().any(|&z| z) || zero.iter().all(|&z| z) {
        return None;
    }
    Some(
        message
            .chunks_exact(1 << log_rows)
            .enumerate()
            .filter(|&(b, _)| !zero[b])
            .collect(),
    )
}

/// Spread rows of the nonzero blocks' codeword (`blocks.len()` words, lane `k - 1 - c` block `blocks[c]`'s) into
/// rows of the whole one (`n_lanes` words, lane `n_lanes - 1 - b` block `b`'s), the zero blocks' lanes zero.
fn spread_rows(compact: &[F64], blocks: &[usize], n_lanes: usize, out: &mut [F64]) {
    let k = blocks.len();
    // Runs of consecutive blocks `c..e`: compact lanes `k - e..k - c` are whole lanes `n_lanes - b_(e-1) - 1..`.
    let mut runs: Vec<(usize, usize, usize)> = Vec::new();
    let mut c = 0;
    while c < k {
        let e = (c + 1..k).find(|&e| blocks[e] != blocks[e - 1] + 1).unwrap_or(k);
        runs.push((k - e, n_lanes - 1 - blocks[e - 1], e - c));
        c = e;
    }
    out.fill(F64::ZERO);
    for (row, full) in compact.chunks_exact(k).zip(out.chunks_exact_mut(n_lanes)) {
        for &(from, to, len) in &runs {
            full[to..to + len].copy_from_slice(&row[from..from + len]);
        }
    }
}

/// [`commit_tree_in`], told which committed lanes are all zero (`zero[b]`, one flag a lane block of `message`):
/// their codeword is zero, so they are not encoded, and their words of each row are zero when it is hashed. The
/// root and the tree are [`commit_tree_in`]'s.
pub fn commit_tree_skipping_in(
    message: &[F64],
    log_n: usize,
    log_batch_size: usize,
    log_inv_rate: usize,
    zero: &[bool],
    scratch: Vec<F64>,
) -> (Commitment, Vec<Hash>) {
    let (n_lanes, log_rows) = lane_shape(message, log_n, log_batch_size, log_inv_rate);
    let Some(blocks) = nonzero_blocks(message, log_rows, zero) else {
        return commit_tree_in(message, log_n, log_batch_size, log_inv_rate, scratch);
    };
    let k_code = log_rows + log_inv_rate;
    let tree = merkle::MerkleBuilder::new(1usize << k_code, n_lanes, 1usize << log_batch_size);
    let encoded = tracing::info_span!(
        "NTT",
        kind = "base encode by replica",
        log_domain = k_code,
        lanes = blocks.len()
    )
    .in_scope(|| {
        let mut work = scratch;
        work.clear();
        work.reserve_exact(blocks.len() << log_rows);
        // SAFETY: the capacity holds the nonzero blocks' words, which the first sweep writes before the second
        // reads them.
        unsafe { work.set_len(blocks.len() << log_rows) };
        let ntt = AdditiveNttF64::standard(k_code);
        let slices: Vec<&[F64]> = blocks.iter().map(|&(_, block)| block).collect();
        let indices: Vec<usize> = blocks.iter().map(|&(b, _)| b).collect();
        // [`spread_rows`]' outputs, one a worker at a time, reused tile after tile and freed with the commitment (a
        // thread-local buffer would keep a tile's whole rows on every worker for good).
        let spare: std::sync::Mutex<Vec<Vec<F64>>> = std::sync::Mutex::new(Vec::new());
        let on_rows = |row: usize, rows: &[F64]| {
            let take = || spare.lock().unwrap_or_else(std::sync::PoisonError::into_inner).pop();
            let mut full = take().unwrap_or_default();
            full.resize(rows.len() / blocks.len() * n_lanes, F64::ZERO);
            spread_rows(rows, &indices, n_lanes, &mut full);
            tree.absorb(row, &full);
            spare.lock().unwrap_or_else(std::sync::PoisonError::into_inner).push(full);
        };
        ntt.encode_two_sweep_blocks_with(&mut work, &slices, log_inv_rate, &on_rows)
    });
    if !encoded {
        return commit_tree_in(message, log_n, log_batch_size, log_inv_rate, Vec::new());
    }
    let merkle_tree = tracing::info_span!("Merkle").in_scope(|| tree.finish());
    let root = *merkle_tree.last().expect("merkle tree non-empty");
    (Commitment { root }, merkle_tree)
}

/// [`commit`], told which committed lanes are all zero (`zero[b]`, one flag a lane block of `message`): they are
/// not encoded, and the codeword kept is the other lanes' alone, rows of as many words as lanes not flagged
/// (`blocks` of [`nonzero_blocks`], lane `k - 1 - c` block `c`'s), which an opening given the same flags spreads
/// back to whole rows ([`recursive_prover_with_lane_tensors_batch`]). The root and the tree are [`commit`]'s. `None`,
/// having done nothing, when no lane (or every lane) is flagged or the shape takes no two sweeps. [Added here.]
pub fn commit_skipping(
    message: &[F64],
    log_n: usize,
    log_batch_size: usize,
    log_inv_rate: usize,
    zero: &[bool],
) -> Option<(Commitment, ProverData)> {
    let (n_lanes, log_rows) = lane_shape(message, log_n, log_batch_size, log_inv_rate);
    let blocks = nonzero_blocks(message, log_rows, zero)?;
    let k_code = log_rows + log_inv_rate;
    let tree = merkle::MerkleBuilder::new(1usize << k_code, n_lanes, 1usize << log_batch_size);
    // SAFETY: the two-sweep encode of blocks always has a first sweep, which writes every word of every replica
    // before the second reads a tile; when it declines the shape, nothing reads the buffer.
    let mut codeword = unsafe { primitives::uninit_vec::<F64>(blocks.len() << k_code) };
    let encoded =
        tracing::info_span!("NTT", kind = "base encode", log_domain = k_code, lanes = blocks.len()).in_scope(|| {
            let slices: Vec<&[F64]> = blocks.iter().map(|&(_, block)| block).collect();
            let indices: Vec<usize> = blocks.iter().map(|&(b, _)| b).collect();
            // The spread rows lent from a list the commitment owns, as `commit_tree_skipping_in`'s.
            let spare: std::sync::Mutex<Vec<Vec<F64>>> = std::sync::Mutex::new(Vec::new());
            let on_rows = |row: usize, rows: &[F64]| {
                let take = || spare.lock().unwrap_or_else(std::sync::PoisonError::into_inner).pop();
                let mut full = take().unwrap_or_default();
                full.resize(rows.len() / blocks.len() * n_lanes, F64::ZERO);
                spread_rows(rows, &indices, n_lanes, &mut full);
                tree.absorb(row, &full);
                spare.lock().unwrap_or_else(std::sync::PoisonError::into_inner).push(full);
            };
            AdditiveNttF64::standard(k_code).encode_two_sweep_blocks_into(
                &mut codeword,
                &slices,
                log_inv_rate,
                &on_rows,
            )
        });
    if !encoded {
        return None;
    }
    let merkle_tree = tracing::info_span!("Merkle").in_scope(|| tree.finish());
    let root = *merkle_tree.last().expect("merkle tree non-empty");
    Some((Commitment { root }, ProverData { codeword, merkle_tree }))
}

/// [`encoded_rows`], told which committed lanes are all zero ([`commit_tree_skipping_in`]): the same rows.
pub fn encoded_rows_skipping(
    message: &[F64],
    log_n: usize,
    log_batch_size: usize,
    log_inv_rate: usize,
    zero: &[bool],
    positions: &[usize],
) -> Vec<Vec<F64>> {
    let (n_lanes, log_rows) = lane_shape(message, log_n, log_batch_size, log_inv_rate);
    let Some(blocks) = nonzero_blocks(message, log_rows, zero) else {
        return encoded_rows(message, log_n, log_batch_size, log_inv_rate, positions);
    };
    let k_code = log_rows + log_inv_rate;
    let _span =
        tracing::info_span!("NTT", kind = "base re-encode", log_domain = k_code, lanes = blocks.len()).entered();
    let mut wanted = positions.to_vec();
    wanted.sort_unstable();
    wanted.dedup();
    let slices: Vec<&[F64]> = blocks.iter().map(|&(_, block)| block).collect();
    let Some(found) = AdditiveNttF64::standard(k_code).encoded_rows_two_sweep_blocks(&slices, log_inv_rate, &wanted)
    else {
        drop(_span);
        return encoded_rows(message, log_n, log_batch_size, log_inv_rate, positions);
    };
    let k = blocks.len();
    let indices: Vec<usize> = blocks.iter().map(|&(b, _)| b).collect();
    positions
        .iter()
        .map(|q| {
            let at = wanted.binary_search(q).expect("a wanted row");
            let mut row = vec![F64::ZERO; n_lanes];
            spread_rows(&found[at * k..(at + 1) * k], &indices, n_lanes, &mut row);
            row
        })
        .collect()
}

/// The committed lanes and their log length, checked as [`commit`] checks them.
fn lane_shape(message: &[F64], log_n: usize, log_batch_size: usize, log_inv_rate: usize) -> (usize, usize) {
    assert!(log_inv_rate >= 1, "log_inv_rate must be >= 1 for a non-trivial RS code");
    assert!(log_n > log_batch_size, "witness must be wider than the interleaving");
    let log_rows = log_n - log_batch_size;
    let n_lanes = message.len() >> log_rows;
    assert_eq!(message.len(), n_lanes << log_rows, "message is whole lane blocks");
    assert!(
        n_lanes >= 1 && n_lanes <= 1usize << log_batch_size,
        "at most 2^log_batch_size lanes carry data"
    );
    (n_lanes, log_rows)
}

/// Hand `encode(replica, transform, buffer)` each replica of the codeword in turn, the buffer (in `scratch`'s
/// allocation when that holds it) holding the transposed message and the transform being that replica's
/// ([`AdditiveNttF64::replica`]).
fn each_replica(
    message: &[F64],
    n_lanes: usize,
    log_rows: usize,
    log_inv_rate: usize,
    scratch: Vec<F64>,
    mut encode: impl FnMut(usize, &AdditiveNttF64, &mut [F64]),
) {
    let ntt = AdditiveNttF64::standard(log_rows + log_inv_rate);
    let mut buffer = scratch;
    buffer.clear();
    buffer.reserve_exact(message.len());
    // SAFETY: the capacity holds the message's length of plain words, and every replica starts with a transpose
    // that writes each of them before the encode reads any.
    unsafe { buffer.set_len(message.len()) };
    for replica in 0..1usize << log_inv_rate {
        crate::ntt::transpose_lane_major(&mut buffer, message, n_lanes, log_rows);
        encode(replica, &ntt.replica(log_inv_rate, replica), &mut buffer);
    }
}

/// Codeword + Merkle tree for one deeper WHIR commitment level.
/// `mat[pos * num_interleaved + lane]`; each row (one `pos` across all lanes)
/// is one Merkle leaf of `num_interleaved * 16` bytes.
pub(crate) struct LigeroWitness {
    rows: LigeroRows,
    pub tree: Vec<Hash>,
    pub block_len: usize,
    pub num_interleaved: usize,
}

/// Codewords of at least this many bytes are not kept: [`LigeroRows::Message`].
const LEAN_LIGERO_BYTES: usize = 1 << 30;

#[cfg(test)]
thread_local! {
    /// Test knob: the lean threshold [`ligero_commit_ext`] uses on this thread, in place of
    /// [`LEAN_LIGERO_BYTES`], so that a whole proof can take the lean deeper levels at a small size.
    pub(crate) static LEAN_LIGERO_BYTES_OVERRIDE: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) };
}

/// [`LEAN_LIGERO_BYTES`], or (in tests) the knob's value on this thread.
fn lean_ligero_bytes() -> usize {
    #[cfg(test)]
    if let Some(bytes) = LEAN_LIGERO_BYTES_OVERRIDE.get() {
        return bytes;
    }
    LEAN_LIGERO_BYTES
}

/// Level-1 codewords of at least this many bytes are not kept by the openings of a batch made one after another (its
/// level-0 rows read from a kept codeword: π2's `Q`, three openings): kept, a codeword's queried rows are read rather
/// than encoded again (`Q`: 1.5 GB a level-1 codeword, 16 ms an opening at 8 threads), and each opening's codeword
/// reuses the memory of the one before. A lone opening keeps [`LEAN_LIGERO_BYTES`]: the membership proof's `T`, opened
/// once in a cold process, would map 0.94 GiB more for 3 ms; a batch whose level-0 rows are encoded at once holds all
/// its level-1 commitments together, and keeps [`LEAN_LIGERO_BYTES`] too. [Added here.]
const LEAN_LIGERO_BYTES_IN_TURN: usize = 2 << 30;

/// [`LEAN_LIGERO_BYTES_IN_TURN`], or (in tests) the knob's value on this thread.
fn lean_ligero_bytes_in_turn() -> usize {
    #[cfg(test)]
    if let Some(bytes) = LEAN_LIGERO_BYTES_OVERRIDE.get() {
        return bytes;
    }
    LEAN_LIGERO_BYTES_IN_TURN
}

/// Where a level's opened rows come from.
enum LigeroRows {
    /// The codeword, `mat[pos * num_interleaved + lane]`.
    Codeword(Vec<F192>),
    /// The row-major message, which the rows a query opens are encoded again from, one replica (`2^-log_inv_rate`
    /// of the codeword) at a time: what a large codeword is kept as, between its commitment and its queries.
    Message { msg: Vec<F192>, log_inv_rate: usize },
}

impl LigeroWitness {
    /// The rows at `positions`, in that order, repeats allowed.
    pub fn rows(&self, positions: &[usize]) -> Vec<Vec<F192>> {
        let lanes = self.num_interleaved;
        match &self.rows {
            LigeroRows::Codeword(mat) => positions
                .iter()
                .map(|&q| mat[q * lanes..(q + 1) * lanes].to_vec())
                .collect(),
            LigeroRows::Message { msg, log_inv_rate } => {
                let _span = tracing::info_span!(
                    "NTT",
                    kind = "extension re-encode",
                    log_domain = self.block_len.ilog2(),
                    lanes
                )
                .entered();
                let replica_rows = self.block_len >> log_inv_rate;
                let ntt = AdditiveNttF64::standard(self.block_len.ilog2() as usize);
                let mut wanted = positions.to_vec();
                wanted.sort_unstable();
                wanted.dedup();
                // In two sweeps where the shape allows it: one read of the message for every replica.
                if let Some(found) =
                    ntt.encoded_rows_two_sweep(ext_words(msg), MsgLayout::RowMajor, 3 * lanes, *log_inv_rate, &wanted)
                {
                    return positions
                        .iter()
                        .map(|q| {
                            let at = wanted.binary_search(q).expect("a wanted row");
                            found[3 * lanes * at..3 * lanes * (at + 1)]
                                .as_chunks::<3>()
                                .0
                                .iter()
                                .map(|&[c0, c1, c2]| F192::new(c0.0, c1.0, c2.0))
                                .collect()
                        })
                        .collect();
                }
                let mut rows = vec![Vec::new(); positions.len()];
                // SAFETY: every encode below writes the whole replica before anything reads it.
                let mut replica = unsafe { primitives::uninit_vec::<F192>(msg.len()) };
                for b in 0..1usize << log_inv_rate {
                    let local: Vec<usize> = wanted
                        .iter()
                        .filter(|&&q| q / replica_rows == b)
                        .map(|&q| q - b * replica_rows)
                        .collect();
                    if local.is_empty() {
                        continue;
                    }
                    let ntt = ntt.replica(*log_inv_rate, b);
                    encode_interleaved_ext_rows(&ntt, &mut replica, msg, lanes, 0, &local);
                    for (row, &q) in rows.iter_mut().zip(positions) {
                        if q / replica_rows == b {
                            let at = (q - b * replica_rows) * lanes;
                            *row = replica[at..at + lanes].to_vec();
                        }
                    }
                }
                rows
            }
        }
    }

    #[inline]
    pub fn root(&self) -> Hash {
        self.tree[self.tree.len() - 1]
    }
}

/// `src` copied by the workers (a lean level's message is up to a gigabyte, which one thread copies slowly).
fn copied<T: Copy + Send + Sync>(src: &[T]) -> Vec<T> {
    // SAFETY: the chunks below cover the vector, each written whole from `src` before it is read.
    let mut out = unsafe { primitives::uninit_vec::<T>(src.len()) };
    let chunk = (1usize << 16).min(src.len().max(1));
    parallel::chunks_mut(&mut out, chunk, |k, dst| {
        dst.copy_from_slice(&src[k * chunk..k * chunk + dst.len()])
    });
    out
}

/// Replicas of a lean level's codeword ([`LigeroRows::Message`]) encoded per read of its message: their work
/// buffers, each as large as the message, are what the level holds beside it while it commits.
const LEAN_BATCH: usize = 4;

/// An E-valued buffer as its K words: three a coefficient, the row-major lanes then three times as many.
fn ext_words(v: &[F192]) -> &[F64] {
    // SAFETY: an `F192` is three `F64`s (`whir_ntt_ext`'s layout asserts), so the view covers the same memory.
    unsafe { std::slice::from_raw_parts(v.as_ptr().cast::<F64>(), 3 * v.len()) }
}

/// The rows of `rows` (opened at `positions`, in order) by position, for a Merkle opening.
fn row_at<'r, T>(positions: &[usize], rows: &'r [Vec<T>]) -> impl Fn(usize) -> &'r [T] {
    let positions = positions.to_vec();
    move |q| &rows[positions.iter().position(|&p| p == q).expect("a queried position")]
}

/// Commit an extension-field polynomial at one recursive WHIR level.
///
/// - Each lane of the row-major message is RS-encoded with base-field twiddles.
/// - The codeword is then Merkle-committed, one leaf per row.
pub(crate) fn ligero_commit_ext(
    poly: &[F192],
    log_msg_cols: usize,
    log_num_interleaved: usize,
    log_inv_rate: usize,
    ntt: &AdditiveNttF64,
) -> LigeroWitness {
    ligero_commit_ext_within(
        poly,
        log_msg_cols,
        log_num_interleaved,
        log_inv_rate,
        ntt,
        lean_ligero_bytes(),
    )
}

/// [`ligero_commit_ext`], keeping the message rather than a codeword of at least `lean_bytes`.
fn ligero_commit_ext_within(
    poly: &[F192],
    log_msg_cols: usize,
    log_num_interleaved: usize,
    log_inv_rate: usize,
    ntt: &AdditiveNttF64,
    lean_bytes: usize,
) -> LigeroWitness {
    let msg_cols = 1usize << log_msg_cols;
    let num_interleaved = 1usize << log_num_interleaved;
    let block_len = msg_cols << log_inv_rate;
    let log_block_len = log_msg_cols + log_inv_rate;
    assert_eq!(poly.len(), num_interleaved * msg_cols);
    assert!(log_block_len <= ntt.log_domain_size());

    let codeword_len = block_len * num_interleaved;
    // One leaf per row, its F192s as K words: hashed as the encode finishes each block.
    let row_words = 3 * num_interleaved;
    let builder = merkle::MerkleBuilder::new(block_len, row_words, row_words);
    let span = tracing::info_span!(
        "NTT",
        kind = "extension encode",
        log_domain = log_block_len,
        lanes = num_interleaved
    );
    let rows = if codeword_len * size_of::<F192>() < lean_bytes {
        // The encode builds the replicas itself, so the codeword starts uninitialized.
        //
        // SAFETY: the encode writes every matrix element before reading it.
        let mut mat = unsafe { primitives::uninit_vec::<F192>(codeword_len) };
        span.in_scope(|| {
            encode_interleaved_ext(ntt, &mut mat, poly, num_interleaved, log_inv_rate, &|row, rows| {
                builder.absorb(row, rows)
            })
        });
        LigeroRows::Codeword(mat)
    } else {
        // One replica at a time, each hashed as it is encoded, and the message kept for the queries.
        assert_eq!(ntt.log_domain_size(), log_block_len, "the codeword's own transform");
        // In two sweeps where the shape allows it, a batch of replicas reading the message once.
        let batch = LEAN_BATCH.min(1 << log_inv_rate);
        // SAFETY: the first sweep writes every word of the batch's replicas before the second reads them.
        let mut work = unsafe { primitives::uninit_vec::<F64>(batch * 3 * poly.len()) };
        let two_sweep = span.in_scope(|| {
            ntt.encode_two_sweep_with(
                &mut work,
                ext_words(poly),
                MsgLayout::RowMajor,
                row_words,
                log_inv_rate,
                &|row, rows| builder.absorb(row, rows),
            )
        });
        drop(work);
        // SAFETY: every encode below writes the whole replica before anything reads it.
        let mut replica = unsafe { primitives::uninit_vec::<F192>(if two_sweep { 0 } else { poly.len() }) };
        span.in_scope(|| {
            for b in (0..1usize << log_inv_rate).filter(|_| !two_sweep) {
                let first = b * msg_cols;
                let ntt = ntt.replica(log_inv_rate, b);
                encode_interleaved_ext(&ntt, &mut replica, poly, num_interleaved, 0, &|row, rows| {
                    builder.absorb(first + row, rows)
                });
            }
        });
        LigeroRows::Message {
            msg: copied(poly),
            log_inv_rate,
        }
    };
    let tree = tracing::info_span!("Merkle").in_scope(|| builder.finish());

    LigeroWitness {
        rows,
        tree,
        block_len,
        num_interleaved,
    }
}

// ===================================================================
// Stateful sumcheck over E with a two-phase (Base then Ext) witness
// ===================================================================
//
// Each round sends (u_0, u_2) of the quadratic
// q(X) = u_0 + u_1 X + u_2 X^2 with q(0) + q(1) = T_r, verifier derives
// u_1 = T_r + u_2 (char 2), round eval q(r) = u_0 + r T_r + (r + r^2) u_2.
//
// Round 0 pairs the K-witness with the E-basis via `mul_base`; the first fold
// lifts the witness into E and all later rounds are pure E.

/// (u_0, u_2) per round in E.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SumcheckMessage {
    u_0: F192,
    u_2: F192,
}

/// Transmit the constant and quadratic coefficients; the claim fixes the linear coefficient.
fn send_msg(ps: &mut ProverState, m: SumcheckMessage, claim: F192) {
    ps.add_round_poly(&[m.u_0, claim + m.u_2, m.u_2], false);
}

/// Round-quadratic in coefficient form `c + b X + a X^2`.
#[derive(Clone, Copy, Debug)]
struct RoundQuad {
    c: F192, // u_0
    b: F192, // u_1 (X coeff), derived from T_r and u_2
    a: F192, // u_2 (X^2 coeff)
}

impl RoundQuad {
    /// The quadratic a round message stands for, given the claim it answers:
    /// `h(0) + h(1) = claim` fixes the linear coefficient.
    #[inline]
    fn from_msg(msg: SumcheckMessage, t_r: F192) -> Self {
        Self {
            c: msg.u_0,
            b: t_r + msg.u_2,
            a: msg.u_2,
        }
    }
    #[inline]
    fn eval(&self, r: F192) -> F192 {
        (self.a * r + self.b) * r + self.c
    }
    #[inline]
    fn fold(p1: &Self, p2: &Self, alpha: F192) -> Self {
        Self {
            c: p1.c + alpha * p2.c,
            b: p1.b + alpha * p2.b,
            a: p1.a + alpha * p2.a,
        }
    }
}

/// Sumcheck witness element: `F64` before the first fold (each product against
/// the E basis is a mixed `mul_base`, 2 PMULL), `F192` after it (full E
/// products, 3 PMULL). The associated accumulator is the matching
/// deferred-reduction type.
trait RoundWitness: Copy + Sync + std::ops::Add<Output = Self> {
    type Acc: Copy + Send + core::ops::BitXorAssign;
    const ZERO_ACC: Self::Acc;
    fn mul_basis_unreduced(self, b: F192) -> Self::Acc;
    fn reduce(acc: Self::Acc) -> F192;
    /// Characteristic-two interpolation `x0·(1+r) + x1·r = x0 + r·(x0+x1)`,
    /// lifting the witness into E. One product rather than two, bit-identical
    /// to the two-product form and still just one reduction.
    fn fold_pair(x0: Self, x1: Self, r: F192) -> F192;
    /// [`Self::fold_pair`] against an absent partner: the lane rounds pair the
    /// last committed lane with the stacked witness's zero padding, so the
    /// interpolation collapses to `x0·(1+r)`.
    fn fold_lone(x0: Self, r: F192) -> F192;
    /// `out[t] = fold_pair(f[2t], f[2t + 1], r)` for every `t`.
    #[inline]
    fn fold_into(f: &[Self], r: F192, out: &mut [F192]) {
        for (o, x) in out.iter_mut().zip(f.as_chunks::<2>().0) {
            *o = Self::fold_pair(x[0], x[1], r);
        }
    }
    /// `(Σ f0·b0, Σ (f0 + f1)·(b0 + b1))` over the adjacent pairs of `f` and `b`, unreduced.
    #[inline]
    fn msg_terms(f: &[Self], b: &[F192]) -> (Self::Acc, Self::Acc) {
        let (mut u_0, mut u_2) = (Self::ZERO_ACC, Self::ZERO_ACC);
        for (x, y) in f.as_chunks::<2>().0.iter().zip(b.as_chunks::<2>().0) {
            u_0 ^= x[0].mul_basis_unreduced(y[0]);
            u_2 ^= (x[0] + x[1]).mul_basis_unreduced(y[0] + y[1]);
        }
        (u_0, u_2)
    }
}

impl RoundWitness for F64 {
    type Acc = F192Unreduced;
    const ZERO_ACC: Self::Acc = F192Unreduced::ZERO;
    #[inline]
    fn mul_basis_unreduced(self, b: F192) -> Self::Acc {
        b.mul_base_unreduced(self)
    }
    #[inline]
    fn reduce(acc: Self::Acc) -> F192 {
        acc.reduce()
    }
    #[inline]
    fn fold_pair(x0: Self, x1: Self, r: F192) -> F192 {
        F192::from(x0) + r.mul_base(x0 + x1)
    }
    #[inline]
    fn fold_lone(x0: Self, r: F192) -> F192 {
        F192::from(x0) + r.mul_base(x0)
    }
}

impl RoundWitness for F192 {
    type Acc = F192Unreduced;
    const ZERO_ACC: Self::Acc = F192Unreduced::ZERO;
    #[inline]
    fn mul_basis_unreduced(self, b: F192) -> Self::Acc {
        self.mul_unreduced(b)
    }
    #[inline]
    fn reduce(acc: Self::Acc) -> F192 {
        acc.reduce()
    }
    #[inline]
    fn fold_pair(x0: Self, x1: Self, r: F192) -> F192 {
        x0 + r * (x0 + x1)
    }
    #[inline]
    fn fold_lone(x0: Self, r: F192) -> F192 {
        x0 + r * x0
    }
    #[inline]
    fn fold_into(f: &[Self], r: F192, out: &mut [F192]) {
        fold_ext_into(f, r, out);
    }
    #[inline]
    fn msg_terms(f: &[Self], b: &[F192]) -> (Self::Acc, Self::Acc) {
        fold_msg_terms(f, b)
    }
}

/// `out[t] = x0 + r·(x0 + x1)` for the pairs `(x0, x1) = (src[2t], src[2t + 1])`: [`RoundWitness::fold_pair`] in
/// `E`, four products at a time ([`mul4`]: one vector of carry-less products for four, on AVX-512).
#[inline]
fn fold_ext_into(src: &[F192], r: F192, out: &mut [F192]) {
    debug_assert_eq!(src.len(), 2 * out.len());
    let (o4, o_rest) = out.as_chunks_mut::<4>();
    let (s8, _) = src.as_chunks::<8>();
    for (o, s) in o4.iter_mut().zip(s8) {
        let p = mul4([r; 4], std::array::from_fn(|i| s[2 * i] + s[2 * i + 1]));
        *o = std::array::from_fn(|i| s[2 * i] + p[i]);
    }
    let done = 4 * o4.len();
    for (o, x) in o_rest.iter_mut().zip(src[2 * done..].as_chunks::<2>().0) {
        *o = x[0] + r * (x[0] + x[1]);
    }
}

/// Round message over a witness `f` and an E basis `b`. Mirror of
/// `whir::round_msg_lsb`.
///
/// Deferred reduction: XOR-accumulate the raw lane products (no reduction tail
/// per term) and reduce once per accumulator. Reduction commutes with XOR, so
/// the message is bit-identical to reducing every term.
fn round_msg_lsb<T: RoundWitness>(f: &[T], b: &[F192]) -> SumcheckMessage {
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);

    let half = n / 2;
    // A chunk of `ROUND_CHUNK` pairs a task ([`RoundWitness::msg_terms`]: in `E`, four products at a time).
    let chunk = 2 * ROUND_CHUNK;
    let term = |c: usize| -> (T::Acc, T::Acc) {
        let range = c * chunk..((c + 1) * chunk).min(n);
        T::msg_terms(&f[range.clone()], &b[range])
    };
    let (u_0, u_2) = accumulate_msg(n.div_ceil(chunk), half, T::ZERO_ACC, term);
    SumcheckMessage {
        u_0: T::reduce(u_0),
        u_2: T::reduce(u_2),
    }
}

/// Build the round message and the full inner product in one pass. For an OOD
/// basis `b = eq(z, ·)`, the inner product is the claimed MLE evaluation.
fn round_msg_and_eval_lsb_ext(f: &[F192], b: &[F192]) -> (SumcheckMessage, F192) {
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);

    // A chunk of `ROUND_CHUNK` pairs a task, their products `f0·b0`, `(f0 + f1)·(b0 + b1)` and `f1·b1` summed
    // unreduced, four at a time ([`mul_unreduced4`]); the reduction is linear, so the sums are the reduced terms'.
    let zero = F192Unreduced::ZERO;
    let chunk = 2 * ROUND_CHUNK;
    let term = |c: usize| {
        let range = c * chunk..((c + 1) * chunk).min(n);
        let (f, b) = (&f[range.clone()], &b[range]);
        let (mut u_0, mut u_2, mut y) = (zero, zero, zero);
        // Four pairs at a time: their twelve products, `f0·b0`, `(f0 + f1)·(b0 + b1)` and `f1·b1` for each pair.
        let operands = |v: &[F192; 8]| -> [F192; 12] {
            std::array::from_fn(|i| {
                let (p, k) = (i / 3, i % 3);
                match k {
                    0 => v[2 * p],
                    1 => v[2 * p] + v[2 * p + 1],
                    _ => v[2 * p + 1],
                }
            })
        };
        let (f8, _) = f.as_chunks::<8>();
        for (x, w) in f8.iter().zip(b.as_chunks::<8>().0) {
            let (x, w) = (operands(x), operands(w));
            for g in 0..3 {
                let p = mul_unreduced4(
                    std::array::from_fn(|j| x[4 * g + j]),
                    std::array::from_fn(|j| w[4 * g + j]),
                );
                for (j, v) in p.into_iter().enumerate() {
                    match (4 * g + j) % 3 {
                        0 => {
                            u_0 ^= v;
                            y ^= v;
                        }
                        1 => u_2 ^= v,
                        _ => y ^= v,
                    }
                }
            }
        }
        for (x, w) in f[8 * f8.len()..]
            .as_chunks::<2>()
            .0
            .iter()
            .zip(b[8 * f8.len()..].as_chunks::<2>().0)
        {
            let e0 = x[0].mul_unreduced(w[0]);
            u_0 ^= e0;
            u_2 ^= (x[0] + x[1]).mul_unreduced(w[0] + w[1]);
            y ^= e0;
            y ^= x[1].mul_unreduced(w[1]);
        }
        (u_0, u_2, y)
    };
    const PAR_THRESHOLD: usize = 4096;
    let half = n / 2;
    let tasks = n.div_ceil(chunk);
    let xor3 = |(mut a0, mut a2, mut ay): (F192Unreduced, F192Unreduced, F192Unreduced),
                (b0, b2, by): (F192Unreduced, F192Unreduced, F192Unreduced)| {
        a0 ^= b0;
        a2 ^= b2;
        ay ^= by;
        (a0, a2, ay)
    };
    let (u_0, u_2, y) = if half < PAR_THRESHOLD {
        (0..tasks).map(term).fold((zero, zero, zero), xor3)
    } else {
        parallel::map_reduce(tasks, || (zero, zero, zero), term, xor3)
    };
    (
        SumcheckMessage {
            u_0: u_0.reduce(),
            u_2: u_2.reduce(),
        },
        y.reduce(),
    )
}

/// Uninitialized output for an initial-sumcheck fold.
///
/// # Safety
/// Every element must be written before it is read, which every fold kernel
/// below does: one output slot per input pair.
#[inline]
unsafe fn fold_out_buf(n: usize) -> Vec<F192> {
    // SAFETY: forwarded to the caller's obligation, documented above.
    unsafe { primitives::uninit_vec(n) }
}

/// Unreduced `(u_0, u_2)` over the already-folded E buffers, pair by pair. A
/// trailing odd element contributes nothing, exactly as in the pre-fold
/// message: at the last round `half = 1` and the message is zero.
#[inline]
fn fold_msg_terms(nf: &[F192], nb: &[F192]) -> (F192Unreduced, F192Unreduced) {
    let mut u_0 = F192Unreduced::ZERO;
    let mut u_2 = F192Unreduced::ZERO;
    // Two pairs at a time, their four products together ([`mul_unreduced4`]).
    let (f4, _) = nf.as_chunks::<4>();
    for (f, b) in f4.iter().zip(nb.as_chunks::<4>().0) {
        let p = mul_unreduced4(
            [f[0], f[0] + f[1], f[2], f[2] + f[3]],
            [b[0], b[0] + b[1], b[2], b[2] + b[3]],
        );
        u_0 ^= p[0];
        u_2 ^= p[1];
        u_0 ^= p[2];
        u_2 ^= p[3];
    }
    let mut k = 4 * f4.len();
    while k + 1 < nf.len() {
        let f0 = nf[k];
        let f1 = nf[k + 1];
        let b0 = nb[k];
        let b1 = nb[k + 1];
        u_0 ^= f0.mul_unreduced(b0);
        u_2 ^= (f0 + f1).mul_unreduced(b0 + b1);
        k += 2;
    }
    (u_0, u_2)
}

/// Fused fold + next-round message: the witness folds into E, the basis folds
/// in E, and the next-round message is built over the freshly folded E values
/// in the same pass. Mirror of `whir::fold_and_msg_lsb`.
fn fold_and_msg_lsb<T: RoundWitness>(f: &[T], b: &[F192], r: F192) -> (Vec<F192>, Vec<F192>, SumcheckMessage) {
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);
    let half = n / 2;

    const PAR_THRESHOLD: usize = 4096;
    if half < PAR_THRESHOLD {
        let mut nf = vec![F192::ZERO; half];
        let mut nb = vec![F192::ZERO; half];
        T::fold_into(f, r, &mut nf);
        fold_ext_into(b, r, &mut nb);
        let (u_0, u_2) = fold_msg_terms(&nf, &nb);
        return (
            nf,
            nb,
            SumcheckMessage {
                u_0: u_0.reduce(),
                u_2: u_2.reduce(),
            },
        );
    }

    // Parallel path: `half` is a power of two >= PAR_THRESHOLD and ROUND_CHUNK is a
    // power of two, so every chunk has even length and starts at an even
    // global index (message pairs never straddle a chunk boundary).
    // SAFETY (x2): every slot of `nf`/`nb` is written by the chunked loop below
    // (one output per input pair) before any is read.
    let mut nf = unsafe { fold_out_buf(half) };
    let mut nb = unsafe { fold_out_buf(half) };
    // The fold writes and the message accumulate share one pass per chunk, so
    // the freshly folded values are still in L1 when they are multiplied.
    let nf_base = parallel::SendPtr(nf.as_mut_ptr());
    let nb_base = parallel::SendPtr(nb.as_mut_ptr());
    let (u_0, u_2) = parallel::map_reduce(
        half.div_ceil(ROUND_CHUNK),
        || (F192Unreduced::ZERO, F192Unreduced::ZERO),
        |ci| {
            let base = ci * ROUND_CHUNK;
            let len = ROUND_CHUNK.min(half - base);
            // SAFETY: distinct `ci` own disjoint in-bounds `ROUND_CHUNK`-windows of
            // `nf`/`nb`, and both buffers stay borrowed for the whole dispatch.
            let fc = unsafe { nf_base.slice(base, len) };
            let bc = unsafe { nb_base.slice(base, len) };
            T::fold_into(&f[2 * base..2 * (base + len)], r, fc);
            fold_ext_into(&b[2 * base..2 * (base + len)], r, bc);
            fold_msg_terms(fc, bc)
        },
        |(mut a0, mut a2), (c0, c2)| {
            a0 ^= c0;
            a2 ^= c2;
            (a0, a2)
        },
    );
    (
        nf,
        nb,
        SumcheckMessage {
            u_0: u_0.reduce(),
            u_2: u_2.reduce(),
        },
    )
}

// ===================================================================
// Lane rounds: the L0 fold binds whole lanes, not adjacent words
// ===================================================================
//
// The committed witness is stored lane-major (lane `l` is the contiguous stack
// block `q[l·H .. (l+1)·H)`, `H = 2^(log_n − initial_k)`), because that is what
// makes the stacked witness's zero padding whole lanes and lets the commitment
// leave them out entirely. The first `initial_k` sumcheck rounds are therefore
// the lane fold: round `j` binds lane bit `j`, pairing block `2i` with block
// `2i+1`, and an odd block count pairs the last one with the absent zero
// padding. After them the buffer is one `H`-element block and every later round
// is the ordinary adjacent-pair fold.

/// Elements per task wherever a round is chunked: the fused adjacent-pair fold,
/// and the lane rounds, whose block is the whole L0 message divided by the
/// interleaving and so has to be fed to the pool from inside a block pair rather
/// than across them.
const ROUND_CHUNK: usize = 2048;

/// Sum the per-task `(u_0, u_2)` accumulators, sequentially for the small
/// instances where dispatch costs more than the work. Unreduced accumulators
/// combine by XOR and `reduce` is linear, so both paths land on the same message.
#[inline]
fn accumulate_msg<A: Copy + Send + core::ops::BitXorAssign>(
    n_tasks: usize,
    n_pairs: usize,
    zero: A,
    task: impl Fn(usize) -> (A, A) + Sync,
) -> (A, A) {
    const PAR_THRESHOLD: usize = 4096;
    if n_pairs < PAR_THRESHOLD {
        let mut u_0 = zero;
        let mut u_2 = zero;
        for t in 0..n_tasks {
            let (t0, t2) = task(t);
            u_0 ^= t0;
            u_2 ^= t2;
        }
        (u_0, u_2)
    } else {
        parallel::map_reduce(
            n_tasks,
            || (zero, zero),
            task,
            |(mut a0, mut a2), (c0, c2)| {
                a0 ^= c0;
                a2 ^= c2;
                (a0, a2)
            },
        )
    }
}

/// `(u_0, u_2)` over one pair of blocks, elementwise.
#[inline]
fn msg_terms_pair<T: RoundWitness>(f0: &[T], f1: &[T], b0: &[F192], b1: &[F192]) -> (T::Acc, T::Acc) {
    let mut u_0 = T::ZERO_ACC;
    let mut u_2 = T::ZERO_ACC;
    for (((&x0, &x1), &y0), &y1) in f0.iter().zip(f1).zip(b0).zip(b1) {
        u_0 ^= x0.mul_basis_unreduced(y0);
        u_2 ^= (x0 + x1).mul_basis_unreduced(y0 + y1);
    }
    (u_0, u_2)
}

/// [`msg_terms_pair`] against an absent partner block. With `f1 = b1 = 0` both
/// `h(0)` and `h(inf)` collect the same `Σ f0·b0`, so this is NOT a no-op the way
/// a trailing odd element is in an adjacent-pair round.
#[inline]
fn msg_terms_lone<T: RoundWitness>(f0: &[T], b0: &[F192]) -> (T::Acc, T::Acc) {
    let mut u = T::ZERO_ACC;
    for (&x0, &y0) in f0.iter().zip(b0) {
        u ^= x0.mul_basis_unreduced(y0);
    }
    (u, u)
}

/// Round message for a lane round, over `f.len() / block` blocks.
fn round_msg_blocks<T: RoundWitness>(f: &[T], b: &[F192], block: usize) -> SumcheckMessage {
    // Real asserts, not debug ones: the crate is only ever built in release, and a
    // block count that truncates drops the trailing block from BOTH u_0 and u_2,
    // which is a well-formed but wrong round message rather than a panic.
    assert_eq!(b.len(), f.len());
    assert!(block > 0 && f.len().is_multiple_of(block));
    let n_blocks = f.len() / block;
    let per = block.div_ceil(ROUND_CHUNK);
    let task = |t: usize| -> (T::Acc, T::Acc) {
        let (i, c) = (t / per, t % per);
        let x0 = c * ROUND_CHUNK;
        let len = ROUND_CHUNK.min(block - x0);
        let lo = 2 * i * block + x0;
        if 2 * i + 1 < n_blocks {
            let hi = lo + block;
            msg_terms_pair(&f[lo..lo + len], &f[hi..hi + len], &b[lo..lo + len], &b[hi..hi + len])
        } else {
            msg_terms_lone(&f[lo..lo + len], &b[lo..lo + len])
        }
    };
    let (u_0, u_2) = accumulate_msg(n_blocks.div_ceil(2) * per, f.len() / 2, T::ZERO_ACC, task);
    SumcheckMessage {
        u_0: T::reduce(u_0),
        u_2: T::reduce(u_2),
    }
}

pub(crate) const INITIAL_BASIS_CHUNK: usize = 256;

pub(crate) fn build_initial_basis(
    f: &[F64],
    block: usize,
    fill: impl Fn(usize, &mut [F192]) + Sync,
) -> (Vec<F192>, SumcheckMessage) {
    assert!(block.is_power_of_two() && f.len().is_multiple_of(block));
    let n_blocks = f.len() / block;
    let per = block.div_ceil(INITIAL_BASIS_CHUNK);
    // SAFETY: each task fills and publishes its disjoint lane windows before returning.
    let mut basis = unsafe { primitives::uninit_vec::<F192>(f.len()) };
    let dst = parallel::SendPtr(basis.as_mut_ptr());
    let task = |t: usize| {
        let (pair, chunk) = (t / per, t % per);
        let offset = chunk * INITIAL_BASIS_CHUNK;
        let len = INITIAL_BASIS_CHUNK.min(block - offset);
        let lo = 2 * pair * block + offset;
        let mut b0 = [F192::ZERO; INITIAL_BASIS_CHUNK];
        let mut b1 = [F192::ZERO; INITIAL_BASIS_CHUNK];
        fill(lo, &mut b0[..len]);
        let stream = Stream::new();
        let message = if 2 * pair + 1 < n_blocks {
            let hi = lo + block;
            fill(hi, &mut b1[..len]);
            let message = msg_terms_pair(&f[lo..lo + len], &f[hi..hi + len], &b0[..len], &b1[..len]);
            // SAFETY: this task owns the high lane window, disjoint from every other task.
            unsafe { stream.copy(dst.slice(hi, len), &b1[..len]) };
            message
        } else {
            msg_terms_lone(&f[lo..lo + len], &b0[..len])
        };
        // SAFETY: this task owns the low lane window, disjoint from every other task.
        unsafe { stream.copy(dst.slice(lo, len), &b0[..len]) };
        message
    };
    let (u_0, u_2) = accumulate_msg(n_blocks.div_ceil(2) * per, f.len() / 2, F192Unreduced::ZERO, task);
    (
        basis,
        SumcheckMessage {
            u_0: u_0.reduce(),
            u_2: u_2.reduce(),
        },
    )
}

/// Words a lane round folds at a time, in an L1-resident stage.
const STAGE: usize = 128;

/// One lane round's fold of `f` at `r`: `fold(out, o, x0)` writes words
/// `x0 .. x0 + out.len()` of output lane `o`, folding lane `2o` with lane `2o+1`
/// (absent past the last lane).
fn lane_fold<T: RoundWitness>(f: &[T], block: usize, r: F192) -> impl Fn(&mut [F192], usize, usize) + Sync + '_ {
    let n_in = f.len() / block;
    move |out, o, x0| {
        let len = out.len();
        let src0 = 2 * o * block + x0;
        // Sliced, not indexed: runs of one length let the bounds checks fall out
        // and the pair fold vectorise, as the adjacent-pair kernel's do.
        let lo = &f[src0..src0 + len];
        if 2 * o + 1 < n_in {
            for ((d, &x0), &x1) in out.iter_mut().zip(lo).zip(&f[src0 + block..src0 + block + len]) {
                *d = T::fold_pair(x0, x1, r);
            }
        } else {
            for (d, &x0) in out.iter_mut().zip(lo) {
                *d = T::fold_lone(x0, r);
            }
        }
    }
}

/// [`lane_fold`] twice, at `r0` then `r1`, straight from the base lanes, so the
/// first lane round need not store its fold. Output lane `o` over base lanes
/// `a_j = 4o + j` (absent ones zero) is
/// `a0 + r0·(a0+a1) + r1·(a0+a2) + r0·r1·(a0+a1+a2+a3)`: three mixed products
/// in place of reading back a stored E-vector.
fn lifted_lane_fold(f: &[F64], block: usize, r0: F192, r1: F192) -> impl Fn(&mut [F192], usize, usize) + Sync + '_ {
    let r01 = r0 * r1;
    move |out, o, x0| {
        let len = out.len();
        let [l0, l1, l2, l3] = std::array::from_fn(|j| base_lane(f, block, 4 * o + j, x0, len));
        for ((((d, &a0), &a1), &a2), &a3) in out.iter_mut().zip(l0).zip(l1).zip(l2).zip(l3) {
            let (s1, s2) = (a0 + a1, a0 + a2);
            let acc = r0.mul_base_unreduced(s1) ^ r1.mul_base_unreduced(s2) ^ r01.mul_base_unreduced(s1 + a2 + a3);
            *d = F192::from(a0) + acc.reduce();
        }
    }
}

/// Words `x0 .. x0 + len` of base lane `l`, zero past the last lane.
fn base_lane(f: &[F64], block: usize, l: usize, x0: usize, len: usize) -> &[F64] {
    const ZERO: [F64; STAGE] = [F64::ZERO; STAGE];
    if l < f.len() / block {
        &f[l * block + x0..l * block + x0 + len]
    } else {
        &ZERO[..len]
    }
}

/// The first of several lane rounds: folds `b` alone, the witness's fold being
/// left for the next round to recompute ([`lifted_lane_fold`]). The message is
/// linear in the folded witness `a0 + r·(a0+a1)`, so it is built from the base
/// lanes as `msg(a0) + r·msg(a0+a1)`, with mixed products only.
fn fold_base_and_msg_blocks(f: &[F64], b: &[F192], r: F192, block: usize) -> (Vec<F192>, SumcheckMessage) {
    assert!(block > 0 && b.len().is_multiple_of(block) && b.len() == f.len());
    let n_in = b.len() / block;
    let n_out = n_in.div_ceil(2);
    let fold_b = lane_fold(b, block, r);
    // SAFETY: the loop below writes every slot before any is read.
    let mut nb = unsafe { fold_out_buf(n_out * block) };
    let nb_base = parallel::SendPtr(nb.as_mut_ptr());
    let per = block.div_ceil(ROUND_CHUNK);
    let task = |t: usize| -> (F192Unreduced, F192Unreduced) {
        let (i, c) = (t / per, t % per);
        let x0 = c * ROUND_CHUNK;
        let len = ROUND_CHUNK.min(block - x0);
        let stream = Stream::new();
        let mut stage = [[F192::ZERO; STAGE]; 2];
        let mut sums = [[F64::ZERO; STAGE]; 2];
        let (mut acc_a, mut acc_s) = (
            (F192Unreduced::ZERO, F192Unreduced::ZERO),
            (F192Unreduced::ZERO, F192Unreduced::ZERO),
        );
        for s in (0..len).step_by(STAGE) {
            let n = STAGE.min(len - s);
            let [lo_b, hi_b] = &mut stage;
            let [lo_s, hi_s] = &mut sums;
            let lane = |l: usize| base_lane(f, block, l, x0 + s, n);
            let fold = |out: &mut [F192], sum: &mut [F64], o: usize| {
                fold_b(out, o, x0 + s);
                // SAFETY: distinct (o, x0 + s) name disjoint in-bounds windows of
                // `nb`, which stays borrowed for the whole dispatch.
                unsafe { stream.copy(nb_base.slice(o * block + x0 + s, n), out) };
                for ((d, &a0), &a1) in sum.iter_mut().zip(lane(2 * o)).zip(lane(2 * o + 1)) {
                    *d = a0 + a1;
                }
            };
            fold(&mut lo_b[..n], &mut lo_s[..n], 2 * i);
            let (a, sum) = if 2 * i + 1 < n_out {
                fold(&mut hi_b[..n], &mut hi_s[..n], 2 * i + 1);
                (
                    msg_terms_pair(lane(4 * i), lane(4 * i + 2), &lo_b[..n], &hi_b[..n]),
                    msg_terms_pair(&lo_s[..n], &hi_s[..n], &lo_b[..n], &hi_b[..n]),
                )
            } else {
                (
                    msg_terms_lone(lane(4 * i), &lo_b[..n]),
                    msg_terms_lone(&lo_s[..n], &lo_b[..n]),
                )
            };
            acc_a.0 ^= a.0;
            acc_a.1 ^= a.1;
            acc_s.0 ^= sum.0;
            acc_s.1 ^= sum.1;
        }
        let scaled = |a: F192Unreduced, s: F192Unreduced| a ^ F192Unreduced::from(r * s.reduce());
        (scaled(acc_a.0, acc_s.0), scaled(acc_a.1, acc_s.1))
    };
    let (u_0, u_2) = accumulate_msg(n_out.div_ceil(2) * per, b.len() / 2, F192Unreduced::ZERO, task);
    (
        nb,
        SumcheckMessage {
            u_0: u_0.reduce(),
            u_2: u_2.reduce(),
        },
    )
}

/// Fused lane fold + next-round message. Mirror of [`fold_and_msg_lsb`] for the
/// block pairing: a task owns one output *pair* (so four input blocks), because
/// that is the smallest unit the next round's message is local to.
///
/// `fold_f` is the witness's fold (see [`lane_fold`]).
/// `last` says this is the final lane round, so the round after it pairs adjacent
/// elements of the single output block rather than another pair of blocks. Which
/// pairing comes next is what lets the message be built here, while the folded
/// values are still in L1.
fn fold_and_msg_blocks(
    fold_f: impl Fn(&mut [F192], usize, usize) + Sync,
    b: &[F192],
    r: F192,
    block: usize,
    last: bool,
) -> (Vec<F192>, Vec<F192>, SumcheckMessage) {
    assert!(block > 0 && b.len().is_multiple_of(block));
    let n_in = b.len() / block;
    let n_out = n_in.div_ceil(2);
    // Adjacent pairing next round is only possible once the lanes have collapsed
    // to a single block.
    assert!(!last || n_out == 1);
    let fold_b = lane_fold(b, block, r);

    // SAFETY (x2): the loop below writes every slot of both buffers, one output
    // element per input pair, before any is read.
    let mut nf = unsafe { fold_out_buf(n_out * block) };
    let mut nb = unsafe { fold_out_buf(n_out * block) };
    let nf_base = parallel::SendPtr(nf.as_mut_ptr());
    let nb_base = parallel::SendPtr(nb.as_mut_ptr());

    let per = block.div_ceil(ROUND_CHUNK);
    // Fold into an L1-resident stage rather than straight into `nf`/`nb`. The
    // message reads the folded values back, and reading them here instead of out
    // of the destination is what lets the destination be published with
    // streaming stores: nothing else touches it until the next round, by which
    // time a buffer this size is long evicted, so the fetch an ordinary store
    // would make of every line it overwrites is pure waste.
    let fold_block = |stage: &mut [F192], stage_b: &mut [F192], out_blk: usize, x0: usize, stream: &Stream| {
        let len = stage.len();
        fold_f(stage, out_blk, x0);
        fold_b(stage_b, out_blk, x0);
        // SAFETY: distinct (out_blk, x0) name disjoint in-bounds windows of `nf`
        // and `nb`, which stay borrowed for the whole dispatch.
        unsafe {
            stream.copy(nf_base.slice(out_blk * block + x0, len), stage);
            stream.copy(nb_base.slice(out_blk * block + x0, len), stage_b);
        }
    };

    let task = |t: usize| -> (F192Unreduced, F192Unreduced) {
        let (i, c) = (t / per, t % per);
        let x0 = c * ROUND_CHUNK;
        let len = ROUND_CHUNK.min(block - x0);
        let stream = Stream::new();
        let mut stage = [[F192::ZERO; STAGE]; 4];
        let mut acc = (F192Unreduced::ZERO, F192Unreduced::ZERO);
        for s in (0..len).step_by(STAGE) {
            let n = STAGE.min(len - s);
            let [lo_f, lo_b, hi_f, hi_b] = &mut stage;
            fold_block(&mut lo_f[..n], &mut lo_b[..n], 2 * i, x0 + s, &stream);
            let (u_0, u_2) = if 2 * i + 1 < n_out {
                fold_block(&mut hi_f[..n], &mut hi_b[..n], 2 * i + 1, x0 + s, &stream);
                msg_terms_pair(&lo_f[..n], &hi_f[..n], &lo_b[..n], &hi_b[..n])
            } else if last {
                // `ROUND_CHUNK`, `STAGE` and `block` are powers of two, so every
                // slice has even length and starts even: no message pair
                // straddles one.
                fold_msg_terms(&lo_f[..n], &lo_b[..n])
            } else {
                msg_terms_lone(&lo_f[..n], &lo_b[..n])
            };
            acc.0 ^= u_0;
            acc.1 ^= u_2;
        }
        acc
    };
    let (u_0, u_2) = accumulate_msg(n_out.div_ceil(2) * per, b.len() / 2, F192Unreduced::ZERO, task);
    (
        nf,
        nb,
        SumcheckMessage {
            u_0: u_0.reduce(),
            u_2: u_2.reduce(),
        },
    )
}

// ===================================================================
// Lane rounds on a weight that is a sum of lane tensors
// ===================================================================
//
// When the weight is `b(l, x) = Σ_c s_c[l] · e_c(x)`, with one scale per lane and
// one low weight `e_c` shared by every lane, a lane round folds the scales alone:
// it never touches `x`. Its message is bilinear in the witness and the weight, so
// it is a sum over the claims of products of the folded scales with the folded
// inner products `p_c[l] = Σ_x f(l, x) · e_c(x)`, which fold exactly as the
// witness does. One pass over the witness gives every `p_c[l]`, every lane round
// is then a few products per lane, and a second pass builds the folded witness
// and weight once the lanes have collapsed. The field is exact, so every message
// and every folded value is the one the dense rounds compute from `b` written
// out, without the dense `b` or its folds ever existing.

/// One claim's weight on the committed lanes, as a tensor: word `x` of lane `l` weighs `scales[l] · low[x]`.
#[derive(Clone, Debug)]
pub struct LaneTensor {
    /// One per committed lane, or one per lane of the whole cube (`2^initial_k`): a weight that does not vanish on
    /// the absent lanes (a claim at a point of the whole stack, which a verifier knowing only `log_n` evaluates over
    /// the whole cube). [Added here.]
    pub scales: Vec<F192>,
    /// One per word of a lane, `2^(log_n - initial_k)` of them.
    pub low: Low,
}

/// A lane tensor's low weight: written out, or `eq(point, ·)` over a lane's words, which the lane rounds read a
/// chunk at a time as the product of two small tables ([`EqSplit`]) rather than from a table of a lane's length.
/// [Added here: the `eq` form, for speed; the proofs are the same.]
#[derive(Clone, Debug)]
pub enum Low {
    Table(Vec<F192>),
    /// `eq(point, x)`, `x`'s bit `j` against `point[j]`: [`build_eq_table_ext`]'s order.
    Eq(Vec<F192>),
}

impl Low {
    /// The words of a lane it weighs.
    pub fn len(&self) -> usize {
        match self {
            Low::Table(t) => t.len(),
            Low::Eq(point) => 1 << point.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Its weight of word `x`.
    pub fn at(&self, x: usize) -> F192 {
        match self {
            Low::Table(t) => t[x],
            Low::Eq(point) => point.iter().enumerate().fold(F192::ONE, |w, (j, &p)| {
                w * if (x >> j) & 1 == 1 { p } else { F192::ONE + p }
            }),
        }
    }
}

/// `eq(point, ·)` split at chunks of `2^log_chunk` words: `eq(point, x) = lo[x mod 2^log_chunk] · hi[x >> log_chunk]`
/// (the products are exact, so the values are the written-out table's).
struct EqSplit {
    lo: Vec<F192>,
    hi: Vec<F192>,
}

impl EqSplit {
    fn new(point: &[F192], chunk: usize) -> Self {
        let log_chunk = chunk.trailing_zeros() as usize;
        assert!(chunk.is_power_of_two() && log_chunk <= point.len());
        Self {
            lo: build_eq_table_ext(&point[..log_chunk]),
            hi: build_eq_table_ext(&point[log_chunk..]),
        }
    }
}

/// A dense low weight as the chunk-wise passes read it: chunk `t`'s weights are `weights(t)` times `factor(t)`.
enum Chunked<'a> {
    Table(&'a [F192], usize),
    Eq(EqSplit),
}

impl<'a> Chunked<'a> {
    fn new(low: &'a Low, chunk: usize) -> Self {
        match low {
            Low::Table(t) => Chunked::Table(t, chunk),
            Low::Eq(point) => Chunked::Eq(EqSplit::new(point, chunk)),
        }
    }

    /// Chunk `t`'s weights, and the factor they take (`None`: one).
    #[inline]
    fn chunk(&self, t: usize) -> (&[F192], Option<F192>) {
        match self {
            Chunked::Table(table, chunk) => (&table[t * chunk..(t + 1) * chunk], None),
            Chunked::Eq(split) => (&split.lo[..], Some(split.hi[t])),
        }
    }
}

/// Fold adjacent pairs at `r`, as a lane round folds lanes `2i` and `2i+1`.
fn fold_pairs(v: &mut Vec<F192>, r: F192) {
    let half = v.len() / 2;
    for i in 0..half {
        v[i] = F192::fold_pair(v[2 * i], v[2 * i + 1], r);
    }
    v.truncate(half);
}

/// A lane round's message from the folded scales and inner products, claim by claim.
fn tensor_msg(scales: &[Vec<F192>], inner: &[Vec<F192>]) -> SumcheckMessage {
    let (mut u_0, mut u_2) = (F192::ZERO, F192::ZERO);
    for (s, p) in scales.iter().zip(inner) {
        for ([s0, s1], [p0, p1]) in s.as_chunks::<2>().0.iter().zip(p.as_chunks::<2>().0) {
            u_0 += *s0 * *p0;
            u_2 += (*s0 + *s1) * (*p0 + *p1);
        }
    }
    SumcheckMessage { u_0, u_2 }
}

/// Low weights with at most this many nonzero entries are summed at those entries alone ([`SparseLow`]).
const SPARSE_LOW_MAX: usize = 64;

/// A tensor's low weight, by its nonzero entries when it has at most [`SPARSE_LOW_MAX`] of them (a hidden
/// layout's gadget patterns have three): the lane rounds then read it at those entries alone, the field sums
/// being the same without the zero terms.
enum SparseLow {
    Dense,
    Sparse(Vec<(usize, F192)>),
}

/// Each tensor's [`SparseLow`].
fn sparse_lows(weight: &[&LaneTensor]) -> Vec<SparseLow> {
    weight
        .iter()
        .map(|tensor| {
            let low = match &tensor.low {
                Low::Table(t) => t,
                // `eq(point, ·)` is nonzero exactly where `x` agrees with the point's boolean coordinates: its
                // entries are those of the free ones (the rest weigh one).
                Low::Eq(point) => {
                    let free: Vec<usize> = (0..point.len())
                        .filter(|&j| point[j] != F192::ZERO && point[j] != F192::ONE)
                        .collect();
                    if 1usize << free.len() > SPARSE_LOW_MAX {
                        return SparseLow::Dense;
                    }
                    let base = (0..point.len())
                        .filter(|&j| point[j] == F192::ONE)
                        .fold(0usize, |x, j| x | 1 << j);
                    let mut entries: Vec<(usize, F192)> = (0..1usize << free.len())
                        .map(|k| {
                            let x = free.iter().enumerate().fold(base, |x, (b, &j)| x | ((k >> b) & 1) << j);
                            (x, tensor.low.at(x))
                        })
                        .collect();
                    entries.sort_unstable_by_key(|&(x, _)| x);
                    return SparseLow::Sparse(entries);
                }
            };
            let chunk = ROUND_CHUNK.min(low.len()).max(1);
            let nonzero = |t: usize| -> Vec<(usize, F192)> {
                let first = t * chunk;
                low[first..(first + chunk).min(low.len())]
                    .iter()
                    .enumerate()
                    .filter(|(_, e)| !e.is_zero())
                    .map(|(x, &e)| (first + x, e))
                    .collect()
            };
            // A dense weight (an `eq` table: no zero at all) shows itself in its first chunk.
            if nonzero(0).len() > SPARSE_LOW_MAX {
                return SparseLow::Dense;
            }
            let count = parallel::map_reduce(
                low.len().div_ceil(chunk),
                || 0usize,
                |t| {
                    low[t * chunk..((t + 1) * chunk).min(low.len())]
                        .iter()
                        .filter(|e| !e.is_zero())
                        .count()
                },
                |a, b| a + b,
            );
            if count > SPARSE_LOW_MAX {
                return SparseLow::Dense;
            }
            // The entries, chunk by chunk in parallel, in order.
            SparseLow::Sparse(parallel::map_collect(low.len().div_ceil(chunk), nonzero).concat())
        })
        .collect()
}

/// `p_c[l] = Σ_x f(l, x) · low_c[x]` for every claim `c` and lane `l`, claim-major: in one pass over `f` for the
/// dense low weights, at their nonzero entries for the sparse ones. A tensor whose products are `known` (one per
/// committed lane) is not read, nor a lane `zero` flags all zero, whose products are zero. [Known products and the
/// flagged lanes added here.]
fn lane_inner_products(
    f: &[F64],
    block: usize,
    weight: &[&LaneTensor],
    sparse: &[SparseLow],
    known: &[Option<&[F192]>],
    zero: Option<&[bool]>,
) -> Vec<Vec<F192>> {
    let n_lanes = f.len() / block;
    let dense: Vec<usize> = (0..weight.len())
        .filter(|&c| matches!(sparse[c], SparseLow::Dense) && known[c].is_none())
        .collect();
    let lows: Vec<&Low> = dense.iter().map(|&c| &weight[c].low).collect();
    let dense_sums = dense_lane_sums(f, block, &lows, zero);
    let mut sums = vec![F192Unreduced::ZERO; weight.len() * n_lanes];
    for (k, &c) in dense.iter().enumerate() {
        sums[c * n_lanes..(c + 1) * n_lanes].copy_from_slice(&dense_sums[k * n_lanes..(k + 1) * n_lanes]);
    }
    let lanes = read_lanes(n_lanes, zero);
    for (c, low) in sparse.iter().enumerate() {
        if let (SparseLow::Sparse(entries), None) = (low, known[c]) {
            for &l in &lanes {
                for &(x, e) in entries {
                    sums[c * n_lanes + l] ^= e.mul_base_unreduced(f[l * block + x]);
                }
            }
        }
    }
    sums.chunks_exact(n_lanes)
        .zip(known)
        .map(|(claim, known)| match known {
            Some(products) => {
                assert_eq!(products.len(), n_lanes, "one known product per committed lane");
                products.to_vec()
            }
            None => claim.iter().map(|s| s.reduce()).collect(),
        })
        .collect()
}

/// `p_c[l] = Σ_x f(l, x) · lows[c][x]` for every low weight `c` (`block` words each) and every lane `l` of `f`
/// (whole lanes of `block` words), claim-major, in one pass over `f`: [`lane_inner_products`]' dense ones. [Added
/// here: a commitment's out-of-domain answer from its lanes' products, which its openings' lane rounds reuse.]
pub fn dense_lane_inner_products(f: &[F64], block: usize, lows: &[&Low]) -> Vec<Vec<F192>> {
    dense_lane_inner_products_skipping(f, block, lows, None)
}

/// [`dense_lane_inner_products`], the lanes `zero` flags (one flag a lane of `f`) all zero: they are not read, their
/// products zero. [Added here.]
pub fn dense_lane_inner_products_skipping(
    f: &[F64],
    block: usize,
    lows: &[&Low],
    zero: Option<&[bool]>,
) -> Vec<Vec<F192>> {
    let n_lanes = f.len() / block;
    assert!(n_lanes >= 1 && f.len() == n_lanes * block, "whole lanes");
    for low in lows {
        assert_eq!(low.len(), block, "one low weight per word of a lane");
    }
    dense_lane_sums(f, block, lows, zero)
        .chunks_exact(n_lanes)
        .map(|claim| claim.iter().map(|s| s.reduce()).collect())
        .collect()
}

/// The lanes of `n_lanes` a pass over them reads: all but those `zero` flags all zero.
fn read_lanes(n_lanes: usize, zero: Option<&[bool]>) -> Vec<usize> {
    if let Some(zero) = zero {
        assert_eq!(zero.len(), n_lanes, "a flag for every committed lane");
    }
    (0..n_lanes).filter(|&l| !zero.is_some_and(|z| z[l])).collect()
}

/// The unreduced sums of [`dense_lane_inner_products`], `lows.len() · n_lanes` of them, claim-major. A chunk of an
/// `eq` weight is its small table times one factor ([`Chunked`]): the chunk's sums against the table, reduced, then
/// times the factor. A lane `zero` flags is not read: its sums are zero.
fn dense_lane_sums(f: &[F64], block: usize, lows: &[&Low], zero: Option<&[bool]>) -> Vec<F192Unreduced> {
    let n_lanes = f.len() / block;
    if lows.is_empty() {
        return Vec::new();
    }
    let lanes = read_lanes(n_lanes, zero);
    let lanes = &lanes[..];
    let chunk = ROUND_CHUNK.min(block);
    let chunked: Vec<Chunked<'_>> = lows.iter().map(|low| Chunked::new(low, chunk)).collect();
    // On a vector carry-less multiplier: the chunk's dense low weights packed once for `dot_base`, which takes
    // eight terms at a time (an `eq` weight's small table once for all chunks), then the lanes in turn against them.
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    let fold = {
        use primitives::field::{Weights8, dot_base};
        let pack = |w: &[F192]| -> Vec<Weights8> { w.as_chunks::<8>().0.iter().map(Weights8::new).collect() };
        let vectored = chunk.is_multiple_of(8);
        let packed_eq: Vec<Option<Vec<Weights8>>> = chunked
            .iter()
            .map(|c| match c {
                Chunked::Eq(split) if vectored => Some(pack(&split.lo)),
                _ => None,
            })
            .collect();
        move |acc: &mut Vec<F192Unreduced>, t: usize| {
            let x0 = t * chunk;
            if !vectored {
                return lane_inner_products_chunk(f, block, &chunked, lanes, acc, t, chunk);
            }
            let packed_tables: Vec<Option<Vec<Weights8>>> = chunked
                .iter()
                .map(|c| match c {
                    Chunked::Table(..) => Some(pack(c.chunk(t).0)),
                    Chunked::Eq(_) => None,
                })
                .collect();
            let weights: Vec<(&[Weights8], Option<F192>)> = chunked
                .iter()
                .enumerate()
                .map(|(c, low)| match (&packed_tables[c], &packed_eq[c]) {
                    (Some(w), _) => (&w[..], None),
                    (None, Some(w)) => (&w[..], low.chunk(t).1),
                    (None, None) => unreachable!("every weight packed"),
                })
                .collect();
            for &l in lanes {
                let lane = &f[l * block + x0..l * block + x0 + chunk];
                for (c, &(w, factor)) in weights.iter().enumerate() {
                    let dot = dot_base(w, lane);
                    acc[c * n_lanes + l] ^= match factor {
                        None => dot,
                        Some(h) => h.mul_unreduced(dot.reduce()),
                    };
                }
            }
        }
    };
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2")))]
    let fold =
        |acc: &mut Vec<F192Unreduced>, t: usize| lane_inner_products_chunk(f, block, &chunked, lanes, acc, t, chunk);
    parallel::fold_reduce(
        block / chunk,
        || vec![F192Unreduced::ZERO; lows.len() * n_lanes],
        fold,
        |mut a, b| {
            a.iter_mut().zip(b).for_each(|(a, b)| *a ^= b);
            a
        },
    )
}

/// The dense low weights' terms of [`lane_inner_products`] over chunk `t` (of `chunk` words) of every lane, one
/// product at a time.
#[allow(clippy::ptr_arg)]
fn lane_inner_products_chunk(
    f: &[F64],
    block: usize,
    lows: &[Chunked<'_>],
    lanes: &[usize],
    acc: &mut Vec<F192Unreduced>,
    t: usize,
    chunk: usize,
) {
    let n_lanes = f.len() / block;
    let x0 = t * chunk;
    let weights: Vec<(&[F192], Option<F192>)> = lows.iter().map(|low| low.chunk(t)).collect();
    for &l in lanes {
        let lane = &f[l * block + x0..l * block + x0 + chunk];
        for (c, &(low, factor)) in weights.iter().enumerate() {
            let mut sum = F192Unreduced::ZERO;
            for (&w, &e) in lane.iter().zip(low) {
                sum ^= e.mul_base_unreduced(w);
            }
            acc[c * n_lanes + l] ^= match factor {
                None => sum,
                Some(h) => h.mul_unreduced(sum.reduce()),
            };
        }
    }
}

/// One opening's lane collapse ([`collapse_lanes`]): its lane rounds' challenges, and its tensors with their sparse
/// forms and folded scales.
struct Collapse<'w> {
    rs: Vec<F192>,
    tensors: Vec<(&'w LaneTensor, &'w SparseLow, F192)>,
}

/// The lanes collapsed at each opening's lane rounds' challenges `rs`: its folded witness `Σ_l eq(rs, l) · f(l, ·)`,
/// its folded weight `Σ_c scales[c] · low_c`, and the message of the adjacent-pair round that follows; every
/// opening's in one pass over `f`, a stage of its words read once for all of them. [Several openings at once added
/// here.]
fn collapse_lanes(
    f: &[F64],
    block: usize,
    jobs: &[Collapse<'_>],
    zero: Option<&[bool]>,
) -> Vec<(Vec<F192>, Vec<F192>, SumcheckMessage)> {
    let n_lanes = f.len() / block;
    // The lanes read: all but those flagged all zero, which add nothing to the fold. [Added here.]
    let lanes = read_lanes(n_lanes, zero);
    // Each job's coefficients of the lanes read, with their lanes.
    let coeffs: Vec<Vec<(usize, F192)>> = jobs
        .iter()
        .map(|job| {
            let eq = build_eq_table_ext(&job.rs);
            lanes.iter().map(|&l| (l, eq[l])).collect()
        })
        .collect();
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    let packed: Vec<Vec<(usize, collapse_avx512::Packed)>> = coeffs
        .iter()
        .map(|c| {
            let packed = collapse_avx512::pack(&c.iter().map(|&(_, x)| x).collect::<Vec<_>>());
            c.iter().map(|&(l, _)| l).zip(packed).collect()
        })
        .collect();
    // SAFETY (x2 a job): every task writes its whole window of both buffers before anything reads them.
    let mut out: Vec<(Vec<F192>, Vec<F192>)> = jobs
        .iter()
        .map(|_| unsafe { (fold_out_buf(block), fold_out_buf(block)) })
        .collect();
    let bases: Vec<(parallel::SendPtr<F192>, parallel::SendPtr<F192>)> = out
        .iter_mut()
        .map(|(nf, nb)| (parallel::SendPtr(nf.as_mut_ptr()), parallel::SendPtr(nb.as_mut_ptr())))
        .collect();
    let chunk = ROUND_CHUNK.min(block);
    // Each job's dense low weights as the chunks read them, with their scales.
    let dense: Vec<Vec<(Chunked<'_>, F192)>> = jobs
        .iter()
        .map(|job| {
            job.tensors
                .iter()
                .filter(|(_, low, _)| matches!(low, SparseLow::Dense))
                .map(|&(tensor, _, scale)| (Chunked::new(&tensor.low, chunk), scale))
                .collect()
        })
        .collect();
    let zero = (F192Unreduced::ZERO, F192Unreduced::ZERO);
    let task = |t: usize| -> Vec<(F192Unreduced, F192Unreduced)> {
        let x0 = t * chunk;
        let stream = Stream::new();
        let mut acc = vec![zero; jobs.len()];
        for s in (x0..x0 + chunk).step_by(STAGE) {
            let n = STAGE.min(x0 + chunk - s);
            for (j, job) in jobs.iter().enumerate() {
                let mut stage = [[F192::ZERO; STAGE]; 2];
                let [lo_f, lo_b] = &mut stage;
                // The witness folded at the lanes' coefficients: on AVX-512 eight words at a time, every lane's
                // products summed unreduced in registers ([`collapse_avx512`]).
                #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
                let vectored = n.is_multiple_of(8);
                #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
                let vectored = false;
                if vectored {
                    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
                    // SAFETY: the features are enabled, every lane holds the stage's words, and `n` is whole vectors.
                    unsafe {
                        collapse_avx512::stage(f, block, s, &packed[j], &mut lo_f[..n])
                    };
                } else {
                    let mut sums = [F192Unreduced::ZERO; STAGE];
                    for &(l, coeff) in &coeffs[j] {
                        for (sum, &w) in sums.iter_mut().zip(&f[l * block + s..l * block + s + n]) {
                            *sum ^= coeff.mul_base_unreduced(w);
                        }
                    }
                    for (d, sum) in lo_f[..n].iter_mut().zip(&sums) {
                        *d = sum.reduce();
                    }
                }
                // The dense low weights at every word, four products at a time ([`mul4`]), the sparse ones at
                // their entries in the stage.
                lo_b[..n].fill(F192::ZERO);
                for (low, scale) in &dense[j] {
                    let (weights, factor) = low.chunk(t);
                    let low = &weights[s - x0..s - x0 + n];
                    let scale = factor.map_or(*scale, |h| *scale * h);
                    let (d4, d_rest) = lo_b[..n].as_chunks_mut::<4>();
                    for (d, e) in d4.iter_mut().zip(low.as_chunks::<4>().0) {
                        let p = mul4([scale; 4], *e);
                        *d = std::array::from_fn(|i| d[i] + p[i]);
                    }
                    for (d, &e) in d_rest.iter_mut().zip(&low[n / 4 * 4..]) {
                        *d += scale * e;
                    }
                }
                for &(_, low, scale) in &job.tensors {
                    if let SparseLow::Sparse(entries) = low {
                        let from = entries.partition_point(|&(x, _)| x < s);
                        for &(x, e) in entries[from..].iter().take_while(|&&(x, _)| x < s + n) {
                            lo_b[x - s] += scale * e;
                        }
                    }
                }
                // SAFETY: distinct stages name disjoint in-bounds windows of each job's `nf` and `nb`, which stay
                // borrowed for the whole dispatch.
                unsafe {
                    stream.copy(bases[j].0.slice(s, n), &lo_f[..n]);
                    stream.copy(bases[j].1.slice(s, n), &lo_b[..n]);
                }
                // `STAGE`, `ROUND_CHUNK` and `block` are powers of two, so no message pair straddles a stage.
                let (u_0, u_2) = fold_msg_terms(&lo_f[..n], &lo_b[..n]);
                acc[j].0 ^= u_0;
                acc[j].1 ^= u_2;
            }
        }
        acc
    };
    let xor = |mut a: Vec<(F192Unreduced, F192Unreduced)>, b: Vec<(F192Unreduced, F192Unreduced)>| {
        for (a, b) in a.iter_mut().zip(b) {
            a.0 ^= b.0;
            a.1 ^= b.1;
        }
        a
    };
    // Sequentially for the small instances where dispatch costs more than the work ([`accumulate_msg`]).
    const PAR_THRESHOLD: usize = 4096;
    let sums = if block / 2 < PAR_THRESHOLD {
        (0..block / chunk).map(task).fold(vec![zero; jobs.len()], xor)
    } else {
        parallel::map_reduce(block / chunk, || vec![zero; jobs.len()], task, xor)
    };
    out.into_iter()
        .zip(sums)
        .map(|((nf, nb), (u_0, u_2))| {
            (
                nf,
                nb,
                SumcheckMessage {
                    u_0: u_0.reduce(),
                    u_2: u_2.reduce(),
                },
            )
        })
        .collect()
}

/// The witness fold of [`collapse_lanes`] on AVX-512.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
mod collapse_avx512 {
    use core::arch::x86_64::*;
    use primitives::field::{F64, F192};

    /// Vectors of a lane fetched ahead of the one multiplied.
    const PREFETCH_VECTORS: usize = 8;

    /// A lane's coefficient in every 128-bit lane: `[c0, c1]`, then `[c2, c2]`.
    #[derive(Clone, Copy)]
    pub(super) struct Packed(__m512i, __m512i);

    pub(super) fn pack(coeffs: &[F192]) -> Vec<Packed> {
        // SAFETY: the cfg enables avx512f.
        coeffs
            .iter()
            .map(|c| unsafe {
                Packed(
                    _mm512_broadcast_i32x4(_mm_set_epi64x(c.c1 as i64, c.c0 as i64)),
                    _mm512_set1_epi64(c.c2 as i64),
                )
            })
            .collect()
    }

    /// `lo ^ hi · x^64` modulo `x^64 + x^4 + x^3 + x + 1`, qword by qword, `hi` of at most 63 bits (a sum of
    /// products of two 64-bit polynomials).
    #[inline(always)]
    unsafe fn reduce(lo: __m512i, hi: __m512i) -> __m512i {
        const XOR3: i32 = 0x96;
        // SAFETY: the cfg enables avx512f.
        unsafe {
            let x = _mm512_ternarylogic_epi64::<XOR3>(hi, _mm512_srli_epi64::<61>(hi), _mm512_srli_epi64::<60>(hi));
            let fx = _mm512_ternarylogic_epi64::<XOR3>(x, _mm512_slli_epi64::<1>(x), _mm512_slli_epi64::<3>(x));
            _mm512_ternarylogic_epi64::<XOR3>(lo, fx, _mm512_slli_epi64::<4>(x))
        }
    }

    /// `out[k] = Σ_l coeffs[l] · f[l · block + s + k]`, eight words at a time: per lane six carry-less products
    /// (each coefficient against the even and the odd words), summed unreduced, and one reduction at the end.
    ///
    /// # Safety
    ///
    /// The features are enabled, `out.len()` is a multiple of 8, and every lane `l` that `packed` names holds the
    /// words `s .. s + out.len()` of `f`. [The lanes named, rather than all of them in order, changed here: a lane
    /// flagged all zero is left out.]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
    pub(super) unsafe fn stage(f: &[F64], block: usize, s: usize, packed: &[(usize, Packed)], out: &mut [F192]) {
        // Once a stage (`STAGE` words of every lane named): the loads below read lane `l`'s words `s .. s + out.len()`.
        assert!(
            packed.iter().all(|&(l, _)| (l + 1).checked_mul(block).is_some_and(|w| w <= f.len())) && s + out.len() <= block
        );
        let xor = |a, b| _mm512_xor_si512(a, b);
        for (g, out) in out.as_chunks_mut::<8>().0.iter_mut().enumerate() {
            let mut acc = [_mm512_setzero_si512(); 6];
            for &(l, Packed(t01, t2)) in packed {
                let at = f.as_ptr().wrapping_add(l * block + s + 8 * g);
                // Every lane is its own stream, more than the prefetchers follow: fetch a few vectors ahead. A
                // prefetch never faults, past the lane's end included.
                _mm_prefetch::<_MM_HINT_T0>(at.wrapping_add(8 * PREFETCH_VECTORS).cast());
                // SAFETY: the caller vouches for the lane's words.
                let k = unsafe { _mm512_loadu_si512(at.cast()) };
                acc = [
                    xor(acc[0], _mm512_clmulepi64_epi128::<0x00>(t01, k)),
                    xor(acc[1], _mm512_clmulepi64_epi128::<0x01>(t01, k)),
                    xor(acc[2], _mm512_clmulepi64_epi128::<0x10>(t01, k)),
                    xor(acc[3], _mm512_clmulepi64_epi128::<0x11>(t01, k)),
                    xor(acc[4], _mm512_clmulepi64_epi128::<0x00>(t2, k)),
                    xor(acc[5], _mm512_clmulepi64_epi128::<0x11>(t2, k)),
                ];
            }
            // Word 2j: [c0, c1] · k_2j in acc 0 and 1; word 2j + 1: in acc 2 and 3; c2 · k in acc 4 and 5.
            let halves = |a: __m512i, b: __m512i| {
                // SAFETY: the features are enabled.
                unsafe { reduce(_mm512_unpacklo_epi64(a, b), _mm512_unpackhi_epi64(a, b)) }
            };
            // SAFETY: a register is eight qwords.
            let (even, odd, c2) = unsafe {
                (
                    core::mem::transmute::<__m512i, [u64; 8]>(halves(acc[0], acc[1])),
                    core::mem::transmute::<__m512i, [u64; 8]>(halves(acc[2], acc[3])),
                    core::mem::transmute::<__m512i, [u64; 8]>(halves(acc[4], acc[5])),
                )
            };
            for (i, o) in out.iter_mut().enumerate() {
                let (j, w) = (i / 2, if i % 2 == 0 { &even } else { &odd });
                *o = F192::new(w[2 * j], w[2 * j + 1], c2[i]);
            }
        }
    }
}

/// One opening of a batch on one commitment ([`recursive_prover_with_lane_tensors_batch`]): its weight, the sum of
/// the batch's tensors it names (in that order), its target and its transcript. [Added here.]
pub struct LaneJob<'p> {
    pub tensors: Vec<usize>,
    pub target: F192,
    pub ps: &'p mut ProverState,
}

/// The `initial_k` lane rounds on a lane-tensor weight, transcript operation for transcript operation those of
/// [`SumcheckProver::fold_lane`] on the dense weight, leaving the prover where they leave it, and their
/// challenges: for each of `jobs`, all on the same message `f`, the tensors' inner products in one pass over `f`
/// (but those `known`), the collapse in another ([`collapse_lanes`]). [Several openings at once, and the known
/// products, added here; each job's rounds are those it would have alone.]
fn tensor_lane_rounds(
    f: &[F64],
    block: usize,
    initial_k: usize,
    weight: &[LaneTensor],
    known: &[Option<&[F192]>],
    jobs: &mut [LaneJob<'_>],
    zero: Option<&[bool]>,
) -> Vec<(SumcheckProver<'static>, Vec<F192>)> {
    let n_lanes = f.len() / block;
    let width = 1usize << initial_k;
    // No tensor at all (an opening of no claims) is the zero weight, which the dense prover proves too.
    assert!(n_lanes <= width);
    assert_eq!(known.len(), weight.len(), "one known entry per tensor");
    for tensor in weight {
        assert!(
            tensor.scales.len() == n_lanes || tensor.scales.len() == width,
            "one scale per committed lane, or per lane of the cube"
        );
        assert_eq!(tensor.low.len(), block, "one low weight per word of a lane");
    }
    // Past the committed lanes the witness is zero, and the weight too unless its scales cover the cube (then the
    // lane rounds pair the absent lanes' scales with zero inner products): what the dense rounds pair them with.
    let padded = |mut v: Vec<F192>| {
        v.resize(width, F192::ZERO);
        v
    };
    // The tensors some job reads.
    let mut used = vec![false; weight.len()];
    jobs.iter().flat_map(|job| &job.tensors).for_each(|&c| used[c] = true);
    let span = tracing::info_span!("Sumcheck round", round = 0, log_size = f.len().ilog2()).entered();
    let read: Vec<usize> = (0..weight.len()).filter(|&c| used[c]).collect();
    let sparse = sparse_lows(&read.iter().map(|&c| &weight[c]).collect::<Vec<_>>());
    let all_inner = lane_inner_products(
        f,
        block,
        &read.iter().map(|&c| &weight[c]).collect::<Vec<_>>(),
        &sparse,
        &read.iter().map(|&c| known[c]).collect::<Vec<_>>(),
        zero,
    );
    drop(span);
    let at = |c: usize| read.binary_search(&c).expect("a tensor some job reads");
    // Each job's rounds up to its last challenge.
    let mut ends = Vec::with_capacity(jobs.len());
    for job in jobs.iter_mut() {
        let ps = &mut *job.ps;
        let mut scales: Vec<Vec<F192>> = job.tensors.iter().map(|&c| padded(weight[c].scales.clone())).collect();
        let mut inner: Vec<Vec<F192>> = job.tensors.iter().map(|&c| padded(all_inner[at(c)].clone())).collect();
        let msg = tensor_msg(&scales, &inner);
        send_msg(ps, msg, job.target);
        let (mut t_r, mut quad) = (job.target, RoundQuad::from_msg(msg, job.target));
        let mut rs = Vec::with_capacity(initial_k);
        for j in 0..initial_k {
            let r = ps.sample();
            rs.push(r);
            t_r = quad.eval(r);
            scales.iter_mut().chain(&mut inner).for_each(|v| fold_pairs(v, r));
            if j + 1 < initial_k {
                let msg = tensor_msg(&scales, &inner);
                quad = RoundQuad::from_msg(msg, t_r);
                send_msg(ps, msg, t_r);
            }
        }
        let last: Vec<F192> = scales.iter().map(|s| s[0]).collect();
        ends.push((rs, t_r, last));
    }
    let span = tracing::info_span!("Sumcheck round", round = initial_k, log_size = block.ilog2()).entered();
    let collapses: Vec<Collapse<'_>> = jobs
        .iter()
        .zip(&ends)
        .map(|(job, (rs, _, last))| Collapse {
            rs: rs.clone(),
            tensors: job
                .tensors
                .iter()
                .zip(last)
                .map(|(&c, &scale)| (&weight[c], &sparse[at(c)], scale))
                .collect(),
        })
        .collect();
    let collapsed = collapse_lanes(f, block, &collapses, zero);
    drop(span);
    jobs.iter_mut()
        .zip(ends)
        .zip(collapsed)
        .map(|((job, (rs, t_r, _)), (nf, nb, msg))| {
            let quad = RoundQuad::from_msg(msg, t_r);
            send_msg(job.ps, msg, t_r);
            let prover = SumcheckProver {
                f: Witness::Ext(nf),
                combined_basis: nb,
                t_r,
                quad,
                round: initial_k,
                pending: Vec::new(),
            };
            (prover, rs)
        })
        .collect()
}

/// The witness: the committed K-message (borrowed from the caller, it is only
/// read during the lane rounds) before the first fold, the same message once the
/// first lane round has folded it at the challenge it carries (that fold left
/// unstored, see [`lifted_lane_fold`]), and an owned E-vector afterwards.
enum Witness<'a> {
    Base(&'a [F64]),
    Lifted(&'a [F64], F192),
    Ext(Vec<F192>),
}

/// Running sumcheck over the committed base witness and subsequent extension-field folds.
struct SumcheckProver<'a> {
    f: Witness<'a>,
    /// Single combined basis poly: `glue_pending(lambda)` folds each claim
    /// introduced since the last glue in as `combined_basis += lambda^tau *
    /// b_new`, `tau` counting from 1 (the running claim is `tau = 0`).
    combined_basis: Vec<F192>,
    /// The running claim and its quadratic; `h(0) + h(1) = t_r` fixes the linear coefficient.
    t_r: F192,
    quad: RoundQuad,
    round: usize,
    /// The level's claims, in Protocol 1 step 1 order: the OOD claims, then the
    /// query batch. Drained by `glue_pending`.
    pending: Vec<(Vec<F192>, F192, RoundQuad)>,
}

impl<'a> SumcheckProver<'a> {
    /// `block` is the lane block size `2^(log_n - initial_k)`: the first
    /// `initial_k` rounds are the lane fold, so round 0's message already pairs
    /// whole blocks rather than adjacent words.
    fn new(
        f: &'a [F64],
        b1: Vec<F192>,
        h1: F192,
        block: usize,
        initial_message: Option<SumcheckMessage>,
    ) -> (Self, SumcheckMessage) {
        let _span = tracing::info_span!("Sumcheck round", round = 0, log_size = f.len().ilog2()).entered();
        assert_eq!(f.len(), b1.len());
        let msg = initial_message.unwrap_or_else(|| round_msg_blocks(f, &b1, block));
        let inst = Self {
            f: Witness::Base(f),
            combined_basis: b1,
            t_r: h1,
            quad: RoundQuad::from_msg(msg, h1),
            round: 0,
            pending: Vec::new(),
        };
        (inst, msg)
    }

    /// The prover once the lane rounds have lifted the witness into an owned E-vector, no longer borrowing the
    /// committed message.
    fn into_ext(self) -> SumcheckProver<'static> {
        let Witness::Ext(f) = self.f else {
            panic!("witness still in base phase (lane rounds not done)")
        };
        SumcheckProver {
            f: Witness::Ext(f),
            combined_basis: self.combined_basis,
            t_r: self.t_r,
            quad: self.quad,
            round: self.round,
            pending: self.pending,
        }
    }

    /// The claim that fixes the next message's linear coefficient.
    #[inline]
    fn claim(&self) -> F192 {
        self.t_r
    }

    /// One lane round: fold block `2i` with block `2i+1` (the last one with the
    /// absent zero padding when the block count is odd) and build the message for
    /// the round after it, which is another lane round unless this was the last.
    fn fold_lane(&mut self, r: F192, block: usize, last: bool) -> SumcheckMessage {
        self.t_r = self.quad.eval(r);
        self.round += 1;
        // `ilog2` rather than `trailing_zeros`: a lane round's length is
        // `n_lanes * block`, so it is generally not a power of two, and the two
        // kinds of round have to report a comparable number.
        let log_size = self.combined_basis.len().ilog2();
        let _span = tracing::info_span!("Sumcheck round", round = self.round, log_size).entered();
        let b = &self.combined_basis;
        let (f, nb, msg) = match self.f {
            Witness::Base(f) if !last => {
                let (nb, msg) = fold_base_and_msg_blocks(f, b, r, block);
                (Witness::Lifted(f, r), nb, msg)
            }
            Witness::Base(f) => {
                let (nf, nb, msg) = fold_and_msg_blocks(lane_fold(f, block, r), b, r, block, last);
                (Witness::Ext(nf), nb, msg)
            }
            Witness::Lifted(f, r0) => {
                let (nf, nb, msg) = fold_and_msg_blocks(lifted_lane_fold(f, block, r0, r), b, r, block, last);
                (Witness::Ext(nf), nb, msg)
            }
            Witness::Ext(ref f) => {
                let (nf, nb, msg) = fold_and_msg_blocks(lane_fold(f, block, r), b, r, block, last);
                (Witness::Ext(nf), nb, msg)
            }
        };
        drop(std::mem::replace(&mut self.f, f));
        drop(std::mem::replace(&mut self.combined_basis, nb));
        self.quad = RoundQuad::from_msg(msg, self.t_r);
        msg
    }

    fn fold(&mut self, r: F192) -> SumcheckMessage {
        self.t_r = self.quad.eval(r);
        self.round += 1;
        let log_size = self.combined_basis.len().ilog2();
        let _span = tracing::info_span!("Sumcheck round", round = self.round, log_size).entered();
        // In affine ranges ([`parallel::affine`]): a thread's outputs are the next round's inputs it reads.
        let (nf, nb, msg) = parallel::affine(|| match &self.f {
            Witness::Base(f) => fold_and_msg_lsb(f, &self.combined_basis, r),
            Witness::Ext(f) => fold_and_msg_lsb(f, &self.combined_basis, r),
            Witness::Lifted(..) => unreachable!("a lane round follows the first"),
        });
        // Swap the freshly folded buffers in and drop the consumed ones, so the
        // allocator serves the next round's `fold_out_buf` from their memory.
        drop(std::mem::replace(&mut self.f, Witness::Ext(nf)));
        drop(std::mem::replace(&mut self.combined_basis, nb));
        self.quad = RoundQuad::from_msg(msg, self.t_r);
        msg
    }

    /// Introduce a fresh basis poly with claimed sum `h_new`; sends the
    /// (u_0, u_2) for `Σ_x f(x) · b_new(x)` at the current dim.
    fn introduce_new(&mut self, b_new: Vec<F192>, h_new: F192) -> SumcheckMessage {
        let msg = parallel::affine(|| match &self.f {
            Witness::Base(f) => {
                assert_eq!(b_new.len(), f.len());
                round_msg_lsb(f, &b_new)
            }
            Witness::Ext(f) => {
                assert_eq!(b_new.len(), f.len());
                round_msg_lsb(f, &b_new)
            }
            Witness::Lifted(..) => unreachable!("no claim is introduced between lane rounds"),
        });
        self.pending.push((b_new, h_new, RoundQuad::from_msg(msg, h_new)));
        msg
    }

    /// Introduce `b_new` and compute its claimed inner product in the same
    /// pass as the round message. OOD claims only occur after the first fold,
    /// when the witness has already been lifted from K to E.
    fn introduce_new_with_eval(&mut self, b_new: Vec<F192>) -> (SumcheckMessage, F192) {
        let f = match &self.f {
            Witness::Ext(f) => f,
            Witness::Base(_) | Witness::Lifted(..) => panic!("OOD claim introduced before the lane rounds end"),
        };
        assert_eq!(b_new.len(), f.len());
        let (msg, h_new) = parallel::affine(|| round_msg_and_eval_lsb_ext(f, &b_new));
        self.pending.push((b_new, h_new, RoundQuad::from_msg(msg, h_new)));
        (msg, h_new)
    }

    /// Batch every claim introduced since the last glue into the running one
    /// with powers of the level's single batching challenge (PCS annex,
    /// Protocol 1 step 1): claim `tau` (counting from 1) contributes
    /// `combined_basis[j] += lambda^tau * b_new[j]`, `T_r += lambda^tau *
    /// h_new`. The running claim keeps `lambda^0 = 1`.
    fn glue_pending(&mut self, lambda: F192) {
        let pending = std::mem::take(&mut self.pending);
        assert!(!pending.is_empty(), "glue without introduce_new");
        let mut scalar = F192::ONE;
        for (b_new, h_new, quad_new) in pending {
            scalar *= lambda;
            assert_eq!(b_new.len(), self.combined_basis.len());
            const PAR_THRESHOLD: usize = 4096;
            if self.combined_basis.len() < PAR_THRESHOLD {
                for (acc, &v) in self.combined_basis.iter_mut().zip(b_new.iter()) {
                    *acc += scalar * v;
                }
            } else {
                let chunk = parallel::recommended_chunk_size(self.combined_basis.len());
                // In the next round's affine ranges ([`Self::fold`]).
                parallel::affine(|| {
                    parallel::chunks_mut_zip(&mut self.combined_basis, &b_new, chunk, |_, accs, news| {
                        // Four products at a time ([`mul4`]).
                        let (a4, a_rest) = accs.as_chunks_mut::<4>();
                        for (acc, v) in a4.iter_mut().zip(news.as_chunks::<4>().0) {
                            let p = mul4([scalar; 4], *v);
                            *acc = std::array::from_fn(|i| acc[i] + p[i]);
                        }
                        for (acc, &v) in a_rest.iter_mut().zip(&news[4 * a4.len()..]) {
                            *acc += scalar * v;
                        }
                    })
                });
            }
            self.t_r += scalar * h_new;
            self.quad = RoundQuad::fold(&self.quad, &quad_new, scalar);
        }
    }

    /// The folded witness (post-first-fold: always E). Panics if called
    /// before the first fold (the base phase never reaches a commit).
    fn f_ext(&self) -> &[F192] {
        match &self.f {
            Witness::Ext(f) => f,
            Witness::Base(_) | Witness::Lifted(..) => panic!("witness still in base phase (lane rounds not done)"),
        }
    }
}

/// Sample `count` query positions in transcript order: no dedup, no sort.
/// `block_len = 2^d`; each squeezed field element yields `⌊192/d⌋` positions as
/// its disjoint d-bit chunks (low bits first), matching the scheme the recursive guest derives (fixed `192/d` per
/// squeeze, dup-tolerant: soundness matches the deployed PCS with the same
/// `config.queries`). Duplicates are harmless, a repeated position re-opens the
/// same Merkle-authenticated row.
///
fn sample_queries_ordered(ch: &mut ProverState, block_len: usize, count: usize) -> Vec<usize> {
    let d = block_len.trailing_zeros() as usize;
    let per = 192 / d;
    let mut out = Vec::with_capacity(count);
    while out.len() < count {
        let v = ch.sample();
        for j in 0..per.min(count - out.len()) {
            let off = j * d;
            let limbs = [v.c0, v.c1, v.c2];
            let (li, sh) = (off / 64, off % 64);
            let mut chunk = limbs[li] >> sh;
            if sh + d > 64 {
                chunk |= limbs[li + 1] << (64 - sh);
            }
            out.push(chunk as usize & (block_len - 1));
        }
    }
    out
}

/// Prover side of the OOD claims taken right after a level's root enters the
/// transcript: sample `z`, evaluate the folded witness there, send the claim
/// and its intro message. The claim stays pending: the level's batching
/// challenge is drawn only once its query positions are fixed too, and
/// `glue_pending` then folds every claim of the level in with its own power.
/// A verifier replays it operation for operation.
fn send_ood(sc: &mut SumcheckProver<'_>, ps: &mut ProverState, n_vars: usize, count: usize) {
    for _ in 0..count {
        let z = ps.sample_vec(n_vars);
        let (intro, y) = sc.introduce_new_with_eval(build_eq_table_ext_parallel(&z));
        ps.add_scalar(y);
        send_msg(ps, intro, y);
    }
}

/// An `E` row as the `F64` words its Merkle leaf is hashed from.
fn ext_row_words(row: &[F192]) -> Vec<F64> {
    row.iter().flat_map(|v| [F64(v.c0), F64(v.c1), F64(v.c2)]).collect()
}

/// Prove `Σ_x witness(x) · b_initial(x) = target` against the L0 commitment
/// produced by [`commit`] (with `log_batch_size = config.initial_k` and
/// `log_inv_rate = config.log_inv_rates[0]`).
///
/// `witness` is borrowed: it is only READ (round-0 message + the first lane
/// fold, which lifts it into an owned E-vector), so callers with a large
/// committed stack pass the slice directly instead of paying a full copy.
///
/// PRECONDITION, and the reason `witness` may be shorter than `2^log_n`: it is a
/// whole number of lane blocks, and `b_initial` must be the weight restricted to
/// them, with the weight VANISHING at every boolean point of
/// `[witness.len(), 2^log_n)`. The lane rounds treat the absent blocks as zero
/// while a verifier evaluates the weight's closed form over the whole cube,
/// so a weight that is nonzero out there produces a proof that fails only at the
/// terminal check. `stack_open` discharges this by bounding every claim's support
/// by `stack.len()`; `ood_samples[0] == 0` is what keeps a full-tensor OOD weight
/// out of these rounds.
///
/// Scalars enter the shared transcript as they are transmitted, and authenticated Merkle openings travel as one phase per level. The caller has already bound the initial commitment and target.
pub fn recursive_prover_with_basis(
    config: &ProverConfig,
    log_n: usize,
    witness: &[F64],
    b_initial: Vec<F192>,
    target: F192,
    l0_codeword: &[F64],
    l0_tree: &[Hash],
    ps: &mut ProverState,
) {
    recursive_prover_with_prepared_basis(
        config,
        log_n,
        witness,
        b_initial,
        target,
        l0_codeword,
        l0_tree,
        None,
        ps,
    );
}

pub(crate) fn recursive_prover_with_prepared_basis(
    config: &ProverConfig,
    log_n: usize,
    witness: &[F64],
    b_initial: Vec<F192>,
    target: F192,
    l0_codeword: &[F64],
    l0_tree: &[Hash],
    initial_message: Option<SumcheckMessage>,
    ps: &mut ProverState,
) {
    assert_eq!(b_initial.len(), witness.len());
    recursive_prover(
        config,
        log_n,
        witness,
        Initial::Dense(b_initial, initial_message),
        target,
        Some(l0_codeword),
        l0_tree,
        ps,
    );
}

/// [`recursive_prover_with_basis`] on a weight that is a sum of lane tensors, `b(l, x) = Σ_c
/// weight[c].scales[l] · weight[c].low[x]`, never written out (see "Lane rounds on a weight that is a sum of
/// lane tensors"): the proof is the one the dense weight gives, byte for byte. Without `l0_codeword` (a
/// [`commit_tree`] commitment), the rows the L0 queries open are encoded again from `witness`. The witness and
/// the L0 tree are read last for those rows and their paths: owned ones (`Vec`s) are freed then, before the
/// deeper levels commit.
pub fn recursive_prover_with_lane_tensors(
    config: &ProverConfig,
    log_n: usize,
    witness: impl AsRef<[F64]>,
    weight: &[LaneTensor],
    target: F192,
    l0_codeword: Option<&[F64]>,
    l0_tree: impl AsRef<[Hash]>,
    ps: &mut ProverState,
) {
    recursive_prover_with_lane_tensors_known(
        config,
        log_n,
        witness,
        weight,
        &vec![None; weight.len()],
        target,
        l0_codeword,
        l0_tree,
        ps,
    );
}

/// [`recursive_prover_with_lane_tensors`], given some tensors' inner products with the committed lanes
/// (`known[c]`, one per committed lane: `Σ_x witness(l, x) · weight[c].low[x]`, as
/// [`dense_lane_inner_products`] gives them), which its lane rounds then do not compute. The proof is the same.
/// [Added here.]
#[allow(clippy::too_many_arguments)]
pub fn recursive_prover_with_lane_tensors_known(
    config: &ProverConfig,
    log_n: usize,
    witness: impl AsRef<[F64]>,
    weight: &[LaneTensor],
    known: &[Option<&[F192]>],
    target: F192,
    l0_codeword: Option<&[F64]>,
    l0_tree: impl AsRef<[Hash]>,
    ps: &mut ProverState,
) {
    recursive_prover(
        config,
        log_n,
        witness,
        Initial::Tensors(weight, known),
        target,
        l0_codeword,
        l0_tree,
        ps,
    );
}

/// [`recursive_prover_with_lane_tensors`] without a kept codeword, told which committed lanes are all zero
/// (`zero`, a flag a lane block of `witness`): the rows the L0 queries open are encoded again without them
/// ([`encoded_rows_skipping`]). The same proof.
#[allow(clippy::too_many_arguments)]
pub fn recursive_prover_with_lane_tensors_skipping(
    config: &ProverConfig,
    log_n: usize,
    witness: impl AsRef<[F64]>,
    weight: &[LaneTensor],
    target: F192,
    zero: &[bool],
    l0_tree: impl AsRef<[Hash]>,
    ps: &mut ProverState,
) {
    recursive_prover_rows(
        config,
        log_n,
        witness,
        Initial::Tensors(weight, &vec![None; weight.len()]),
        target,
        L0Rows::Skipping(zero),
        l0_tree,
        ps,
    );
}

/// Where the rows the L0 queries open come from.
#[derive(Clone, Copy)]
enum L0Rows<'c> {
    /// The kept codeword.
    Codeword(&'c [F64]),
    /// The kept codeword of the lanes not flagged all zero alone ([`commit_skipping`]). [Added here.]
    Compact(&'c [F64], &'c [bool]),
    /// Encoded again from the witness ([`encoded_rows`]).
    Encoded,
    /// Encoded again, the all-zero lanes flagged ([`encoded_rows_skipping`]).
    Skipping(&'c [bool]),
}

impl<'c> L0Rows<'c> {
    /// The committed lanes flagged all zero, if any are.
    fn zero(self) -> Option<&'c [bool]> {
        match self {
            L0Rows::Compact(_, zero) | L0Rows::Skipping(zero) => Some(zero),
            L0Rows::Codeword(_) | L0Rows::Encoded => None,
        }
    }

    /// The rows' source: the kept codeword (the flagged lanes left out of it when some are flagged), else encoded
    /// again, skipping the all-zero lanes when some are flagged.
    fn of(codeword: Option<&'c [F64]>, zero: Option<&'c [bool]>) -> Self {
        match (codeword, zero) {
            (Some(codeword), Some(zero)) if zero.contains(&true) => L0Rows::Compact(codeword, zero),
            (Some(codeword), _) => L0Rows::Codeword(codeword),
            (None, Some(zero)) if zero.contains(&true) => L0Rows::Skipping(zero),
            _ => L0Rows::Encoded,
        }
    }
}

/// The weight the lane rounds start from.
enum Initial<'w> {
    /// Written out over the committed lanes, with round 0's message if it is already known.
    Dense(Vec<F192>, Option<SumcheckMessage>),
    /// Lane tensors, and the inner products known of some.
    Tensors(&'w [LaneTensor], &'w [Option<&'w [F192]>]),
}

/// The level-0 shape [`recursive_prover`] checks: the committed lanes and the lane block's length.
fn l0_shape(
    config: &ProverConfig,
    log_n: usize,
    message_len: usize,
    l0_rows: L0Rows<'_>,
    l0_tree_len: usize,
) -> (usize, usize) {
    let r = config.level_steps;
    let initial_k = config.initial_k;

    assert_eq!(config.level_ks.len(), r);
    assert_eq!(config.log_inv_rates.len(), r + 1);
    assert!(r >= 1);
    assert!(initial_k >= 1);
    // L0 takes no OOD sample, and the padding-free truncation now depends on it:
    // the lane rounds are the only ones folding the truncated witness against a
    // weight over the whole `2^log_n` cube, and an OOD weight `eq(z, .)` is a full
    // tensor that does NOT vanish on the absent lanes, unlike every claim weight.
    assert_eq!(config.ood_samples.first().copied().unwrap_or(0), 0);

    let log_inv_rate_0 = config.log_inv_rates[0];
    let log_msg_cols_0 = log_n - initial_k;
    let block_len_0 = 1usize << (log_msg_cols_0 + log_inv_rate_0);
    let num_interleaved_0 = 1usize << initial_k;
    // The committed lanes: only the ones that carry data, so the witness is a
    // whole number of lane blocks but generally NOT `2^log_n` words.
    let lane_block = 1usize << log_msg_cols_0;
    let n_lanes = message_len / lane_block;
    assert_eq!(message_len, n_lanes * lane_block, "witness is whole lane blocks");
    assert!(
        n_lanes >= 1 && n_lanes <= num_interleaved_0,
        "at most 2^initial_k lanes"
    );
    match l0_rows {
        L0Rows::Codeword(l0_codeword) => assert_eq!(l0_codeword.len(), block_len_0 * n_lanes),
        L0Rows::Compact(l0_codeword, zero) => {
            assert_eq!(zero.len(), n_lanes, "a flag for every committed lane");
            assert_eq!(l0_codeword.len(), block_len_0 * zero.iter().filter(|&&z| !z).count());
        }
        L0Rows::Encoded | L0Rows::Skipping(_) => {}
    }
    assert_eq!(l0_tree_len, 2 * block_len_0 - 1);
    (n_lanes, lane_block)
}

#[allow(clippy::too_many_arguments)]
fn recursive_prover(
    config: &ProverConfig,
    log_n: usize,
    witness: impl AsRef<[F64]>,
    initial: Initial<'_>,
    target: F192,
    l0_codeword: Option<&[F64]>,
    l0_tree: impl AsRef<[Hash]>,
    ps: &mut ProverState,
) {
    let rows = l0_codeword.map_or(L0Rows::Encoded, L0Rows::Codeword);
    recursive_prover_rows(config, log_n, witness, initial, target, rows, l0_tree, ps);
}

#[allow(clippy::too_many_arguments)]
fn recursive_prover_rows(
    config: &ProverConfig,
    log_n: usize,
    witness: impl AsRef<[F64]>,
    initial: Initial<'_>,
    target: F192,
    l0_rows: L0Rows<'_>,
    l0_tree: impl AsRef<[Hash]>,
    ps: &mut ProverState,
) {
    let initial_k = config.initial_k;
    let (_, lane_block) = l0_shape(config, log_n, witness.as_ref().len(), l0_rows, l0_tree.as_ref().len());
    let message = witness.as_ref();

    // Nothing is absorbed on entry. The commitment was bound by the `add_root` that
    // transmitted it, and the target is `sum_i lambda^i * claim_i` over claim values bound by their
    // own reads, with lambda drawn from the state: the state already determines both. Every caller
    // must therefore have transmitted its root before opening against it, which is what makes the
    // fold challenges depend on the commitment.

    let sumcheck_span = tracing::info_span!("Sumcheck");
    let (sc_prover, r_lane_fold) = match initial {
        Initial::Dense(b_initial, initial_message) => {
            let (mut sc_prover, start_msg) =
                sumcheck_span.in_scope(|| SumcheckProver::new(message, b_initial, target, lane_block, initial_message));
            send_msg(ps, start_msg, target);

            let mut r_lane_fold = Vec::with_capacity(initial_k);
            for j in 0..initial_k {
                let r_j = ps.sample();
                let msg = sumcheck_span.in_scope(|| sc_prover.fold_lane(r_j, lane_block, j + 1 == initial_k));
                send_msg(ps, msg, sc_prover.claim());
                r_lane_fold.push(r_j);
            }
            (sc_prover.into_ext(), r_lane_fold)
        }
        Initial::Tensors(weight, known) => {
            let _entered = sumcheck_span.enter();
            let mut jobs = [LaneJob {
                tensors: (0..weight.len()).collect(),
                target,
                ps: &mut *ps,
            }];
            tensor_lane_rounds(message, lane_block, initial_k, weight, known, &mut jobs, l0_rows.zero())
                .pop()
                .expect("one job")
        }
    };
    drop(sumcheck_span);
    after_lane_rounds(config, log_n, witness, sc_prover, r_lane_fold, l0_rows, l0_tree, lean_ligero_bytes(), ps);
}

/// [`recursive_prover_with_lane_tensors`] of each of `jobs` (`known` as in
/// [`recursive_prover_with_lane_tensors_known`]), all on one commitment: each job's proof is the one it gives alone,
/// byte for byte, but the lane rounds of all of them read the message twice in all (the tensors' inner products in
/// one pass, the lanes' collapse in another) rather than twice each. Without `l0_codeword`, the rows the L0 queries
/// open are encoded again, skipping the all-zero lanes `zero_lanes` flags (as
/// [`recursive_prover_with_lane_tensors_skipping`]). The lanes `zero_lanes` flags must be all zero; they are left out
/// of the lane rounds' passes. [Added here.]
///
/// **`l0_codeword` with lanes flagged is compact**: when `zero_lanes` flags some lane (a `true`), `l0_codeword` must be
/// the codeword of the unflagged lanes alone, as [`commit_skipping`] keeps it (rows of as many words as lanes not
/// flagged), and the rows the queries open are spread back from it. A whole codeword with such flags is a misuse that
/// [`l0_shape`]'s length check rejects (a panic); pass no flags, or all `false`, with a whole codeword.
#[allow(clippy::too_many_arguments)]
pub fn recursive_prover_with_lane_tensors_batch(
    config: &ProverConfig,
    log_n: usize,
    witness: &[F64],
    weight: &[LaneTensor],
    known: &[Option<&[F192]>],
    jobs: &mut [LaneJob<'_>],
    l0_codeword: Option<&[F64]>,
    zero_lanes: Option<&[bool]>,
    l0_tree: &[Hash],
) {
    let l0_rows = L0Rows::of(l0_codeword, zero_lanes);
    let (_, lane_block) = l0_shape(config, log_n, witness.len(), l0_rows, l0_tree.len());
    let started = {
        let _span = tracing::info_span!("Sumcheck").entered();
        tensor_lane_rounds(witness, lane_block, config.initial_k, weight, known, jobs, zero_lanes)
    };
    // One opening after another: a batch's keep their level-1 codewords up to `LEAN_LIGERO_BYTES_IN_TURN`.
    let lean_bytes = if jobs.len() > 1 { lean_ligero_bytes_in_turn() } else { lean_ligero_bytes() };
    for (job, (sc_prover, r_lane_fold)) in jobs.iter_mut().zip(started) {
        after_lane_rounds(config, log_n, witness, sc_prover, r_lane_fold, l0_rows, l0_tree, lean_bytes, job.ps);
    }
}

/// The rows of the L0 codeword at `positions` (in order, repeats allowed): read from the kept codeword, else encoded
/// again from `witness`.
fn l0_images(
    config: &ProverConfig,
    log_n: usize,
    witness: &[F64],
    l0_rows: L0Rows<'_>,
    positions: &[usize],
) -> Vec<Vec<F64>> {
    let (initial_k, log_inv_rate_0) = (config.initial_k, config.log_inv_rates[0]);
    let n_lanes = witness.len() >> (log_n - initial_k);
    match l0_rows {
        L0Rows::Codeword(codeword) => positions
            .iter()
            .map(|&q| codeword[q * n_lanes..(q + 1) * n_lanes].to_vec())
            .collect(),
        L0Rows::Compact(codeword, zero) => {
            let indices: Vec<usize> = (0..n_lanes).filter(|&b| !zero[b]).collect();
            let k = indices.len();
            positions
                .iter()
                .map(|&q| {
                    let mut row = vec![F64::ZERO; n_lanes];
                    spread_rows(&codeword[q * k..(q + 1) * k], &indices, n_lanes, &mut row);
                    row
                })
                .collect()
        }
        L0Rows::Encoded => encoded_rows(witness, log_n, initial_k, log_inv_rate_0, positions),
        L0Rows::Skipping(zero) => encoded_rows_skipping(witness, log_n, initial_k, log_inv_rate_0, zero, positions),
    }
}

/// [`recursive_prover`] from the end of its lane rounds: level 1's commitment on.
#[allow(clippy::too_many_arguments)]
fn after_lane_rounds(
    config: &ProverConfig,
    log_n: usize,
    witness: impl AsRef<[F64]>,
    mut sc_prover: SumcheckProver<'static>,
    r_lane_fold: Vec<F192>,
    l0_rows: L0Rows<'_>,
    l0_tree: impl AsRef<[Hash]>,
    lean_bytes: usize,
    ps: &mut ProverState,
) {
    let r = config.level_steps;
    let initial_k = config.initial_k;
    let (n_lanes, _) = l0_shape(config, log_n, witness.as_ref().len(), l0_rows, l0_tree.as_ref().len());
    let log_inv_rate_0 = config.log_inv_rates[0];
    let block_len_0 = 1usize << (log_n - initial_k + log_inv_rate_0);
    let num_interleaved_0 = 1usize << initial_k;

    // L0 codeword + tree are borrowed (reused from `commit`); the root itself is never needed
    // here, the caller having transmitted it.
    // The codeword interleaves only the committed lanes, and its lane `t` is stack
    // block `n_lanes-1-t`, so a row IS the tail of the leaf image: the absent lanes
    // are the image's leading zeros (`MerkleBuilder` shares their hash prefix, and only
    // this tail rides the proof). Without the codeword, the queried rows are encoded again.
    // The same row for the induce, which folds a lane-ASCENDING row against the
    // lane eq table: reversing the image puts block `b` at index `b` and the absent
    // lanes' zeros at the end, where they contribute nothing.
    let l0_fold_row = |image: &[F64]| -> Vec<F64> {
        let mut row = vec![F64::ZERO; num_interleaved_0];
        for (t, &word) in image.iter().enumerate() {
            row[n_lanes - 1 - t] = word;
        }
        row
    };

    let ood_count = |lvl: usize| -> usize { config.ood_samples.get(lvl).copied().unwrap_or(0) };

    // Commit f^1 = folded (now E-valued) witness as wtns_1.
    let n1 = log_n - initial_k;
    let log_num_interleaved_1 = config.level_ks[0];
    assert!(n1 >= log_num_interleaved_1);
    let log_msg_cols_1 = n1 - log_num_interleaved_1;
    let log_inv_rate_1 = config.log_inv_rates[1];
    let span = tracing::info_span!("Commit", level = 1).entered();
    let ntt_1 = AdditiveNttF64::standard(log_msg_cols_1 + log_inv_rate_1);
    // Its codeword not kept from `lean_bytes` on.
    let wtns_1 = ligero_commit_ext_within(
        sc_prover.f_ext(),
        log_msg_cols_1,
        log_num_interleaved_1,
        log_inv_rate_1,
        &ntt_1,
        lean_bytes,
    );
    drop(span);
    ps.add_root(&wtns_1.root());

    // Bind the L1 Johnson list before drawing L0 queries. Each claimed random
    // MLE evaluation is introduced into the running sumcheck.
    send_ood(&mut sc_prover, ps, n1, ood_count(1));

    // Query-phase PoW grinding for L0 (`QUERY_GRINDING_BITS = 17` bits in the
    // production profile, as at every level; 0 bits, the canonical 0 nonce still
    // absorbed to keep the transcript in lockstep, only in the test-only
    // `default_config`). [Comment corrected here: leanVM's said 0 bits.]
    ps.grind(config.grinding_bits[0] as u32);

    // Open L0; lane-fold weights = r_lane_fold.
    let num_queries_0 = config.queries[0];
    let queries_0 = sample_queries_ordered(ps, block_len_0, num_queries_0);
    // One batching challenge for the whole level, drawn once every claim it
    // batches is fixed: the OOD claims above and these query positions.
    let lambda_0 = ps.sample();
    let weights_0 = powers(lambda_0, num_queries_0);
    let span = tracing::info_span!("Open", level = 0).entered();
    let images_0 = l0_images(config, log_n, witness.as_ref(), l0_rows, &queries_0);
    // The committed message is not read again.
    drop(witness);
    // Ordered (dup-possible) rows for the local induce math ...
    let opened_rows_0: Vec<Vec<F64>> = images_0.iter().map(|image| l0_fold_row(image)).collect();
    // ... but the stored proof carries the sorted-unique rows + one octopus over
    // the sorted-unique positions (the verifier re-fans them to ordered).
    let l0_row = row_at(&queries_0, &images_0);
    ps.hint_merkle(PrunedMerklePaths::prune(
        l0_tree.as_ref(),
        block_len_0,
        &queries_0,
        move |q| l0_row(q).to_vec(),
    ));
    drop((images_0, l0_tree));
    drop(span);

    // Induce basis_0 from the L0 opens. The dispatcher picks the sparse-prefix
    // transposed NTT wherever a level opens more queries than its blowup.
    let sks_vks_n1 = eval_sk_at_vks(n1);
    let span = tracing::info_span!("Induce", level = 0).entered();
    let (basis_0_induced, enforced_sum_0) = induce_sumcheck_poly_auto(
        n1,
        log_inv_rate_0,
        &sks_vks_n1,
        &opened_rows_0,
        &r_lane_fold,
        &queries_0,
        &weights_0,
    );
    drop(span);

    // Introduce basis_0, then batch the level's claims with powers of lambda_0.
    let span = tracing::info_span!("Introduce", level = 0).entered();
    let intro_msg_0 = sc_prover.introduce_new(basis_0_induced, enforced_sum_0);
    send_msg(ps, intro_msg_0, enforced_sum_0);
    sc_prover.glue_pending(lambda_0);
    drop(span);

    // Recursive levels.
    let mut wtns_prev = wtns_1;

    for i in 0..r {
        let k_i = config.level_ks[i];
        let mut level_rs = Vec::with_capacity(k_i);
        let sumcheck_span = tracing::info_span!("Sumcheck");
        for _ in 0..k_i {
            let ri = ps.sample();
            let msg = sumcheck_span.in_scope(|| sc_prover.fold(ri));
            send_msg(ps, msg, sc_prover.claim());
            level_rs.push(ri);
        }
        drop(sumcheck_span);

        if i == r - 1 {
            ps.add_scalars(sc_prover.f_ext());
            // PoW grinding for the last level before sampling its queries.
            ps.grind(config.grinding_bits[i + 1] as u32);
            let num_queries_last = config.queries[i + 1];
            let queries_last = sample_queries_ordered(ps, wtns_prev.block_len, num_queries_last);
            // The final level's batching challenge is drawn only after `yr`
            // and its queries are bound, matching the verifier exactly.
            let lambda_last = ps.sample();
            let weights_last = powers(lambda_last, num_queries_last);
            let span = tracing::info_span!("Final level").entered();
            // Final level: stored (sorted-unique) only, no local induce; the
            // verifier fans these to ordered for its last-level induce.
            let rows_last: Vec<Vec<F192>> = wtns_prev.rows(&queries_last);
            let row = row_at(&queries_last, &rows_last);
            ps.hint_merkle(PrunedMerklePaths::prune(
                &wtns_prev.tree,
                wtns_prev.block_len,
                &queries_last,
                |q| ext_row_words(row(q)),
            ));
            // Tie the last commitment into the running claim through the same
            // intro/glue step as every other level, then finish the remaining
            // sumcheck rounds. This closes on one weight evaluation instead of
            // a sweep over the residual cube.
            let enforced_sum_last = induce_sumcheck_enforced_sum(&rows_last, &level_rs, &queries_last, &weights_last);
            let n_res = sc_prover.f_ext().len().trailing_zeros() as usize;
            let basis_last = induce_sumcheck_evaluate_at_residual(
                n_res,
                &eval_sk_at_vks(n_res),
                &queries_last,
                &weights_last,
                &[],
                n_res,
            );
            let intro_msg_last = sc_prover.introduce_new(basis_last, enforced_sum_last);
            send_msg(ps, intro_msg_last, enforced_sum_last);
            sc_prover.glue_pending(lambda_last);
            for j in 0..n_res {
                let ri = ps.sample();
                let msg = sc_prover.fold(ri);
                // The last round's message is redundant: the verifier gets that
                // claim from `yr`, so it is never transmitted.
                if j + 1 < n_res {
                    send_msg(ps, msg, sc_prover.claim());
                }
            }
            drop(span);
            return;
        }

        let n_next = sc_prover.f_ext().len().trailing_zeros() as usize;
        let log_num_interleaved_next = config.level_ks[i + 1];
        assert!(n_next >= log_num_interleaved_next);
        let log_msg_cols_next = n_next - log_num_interleaved_next;
        let log_inv_rate_next = config.log_inv_rates[i + 2];
        let span = tracing::info_span!("Commit", level = i + 2).entered();
        let ntt_next = AdditiveNttF64::standard(log_msg_cols_next + log_inv_rate_next);
        let wtns_next = ligero_commit_ext(
            sc_prover.f_ext(),
            log_msg_cols_next,
            log_num_interleaved_next,
            log_inv_rate_next,
            &ntt_next,
        );
        drop(span);
        ps.add_root(&wtns_next.root());

        send_ood(&mut sc_prover, ps, n_next, ood_count(i + 2));

        // PoW grinding for this iteration's query phase.
        ps.grind(config.grinding_bits[i + 1] as u32);
        let num_queries_i = config.queries[i + 1];
        let queries_i = sample_queries_ordered(ps, wtns_prev.block_len, num_queries_i);
        let lambda_i = ps.sample();
        let weights_i = powers(lambda_i, num_queries_i);
        let span = tracing::info_span!("Open", level = i + 1).entered();
        // Ordered rows for the local induce; sorted-unique rows + octopus stored.
        let opened_rows_i: Vec<Vec<F192>> = wtns_prev.rows(&queries_i);
        let row = row_at(&queries_i, &opened_rows_i);
        ps.hint_merkle(PrunedMerklePaths::prune(
            &wtns_prev.tree,
            wtns_prev.block_len,
            &queries_i,
            |q| ext_row_words(row(q)),
        ));
        drop(span);

        let sks_vks_i = eval_sk_at_vks(n_next);
        let span = tracing::info_span!("Induce", level = i + 1).entered();
        let (basis_i_induced, enforced_sum_i) = induce_sumcheck_poly_auto(
            n_next,
            config.log_inv_rates[i + 1],
            &sks_vks_i,
            &opened_rows_i,
            &level_rs,
            &queries_i,
            &weights_i,
        );
        drop(span);

        let span = tracing::info_span!("Introduce", level = i + 1).entered();
        let intro_msg_i = sc_prover.introduce_new(basis_i_induced, enforced_sum_i);
        send_msg(ps, intro_msg_i, enforced_sum_i);
        sc_prover.glue_pending(lambda_i);
        drop(span);

        wtns_prev = wtns_next;
    }

    unreachable!()
}

#[cfg(test)]
mod adversarial;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::whir::QUERY_GRINDING_BITS;
    use crate::whir_config::test_config_for;
    use primitives::test_rng::Rng;

    /// Pin the production 128-bit Johnson/OOD profile rather than the small-
    /// size test fallback.
    #[test]
    fn configs_johnson_profile_shape() {
        let pc = config_for_rate(16, LOG_INV_RATE_0).expect("Johnson profile feasible at log_n = 16");
        assert_eq!(pc.initial_k, 6);
        assert!(pc.level_steps >= 1);
        assert_eq!(pc.ood_samples[0], 0);
        assert!(pc.ood_samples.iter().skip(1).all(|&s| s >= 1));
        assert!(pc.grinding_bits.iter().all(|&b| b == QUERY_GRINDING_BITS));
        // And log_n = 12 is below the production ladder's feasibility floor, so
        // the tests there use the default_config fallback.
        assert!(config_for_rate(12, LOG_INV_RATE_0).is_err());
    }

    /// The parallel eq builder must be byte-identical to the serial one, and
    /// the seeded variant must equal the seed-scaled table, at sizes on both
    /// sides of the internal parallel level floor (2^12 halves, so n = 15
    /// exercises parallel levels; n = 6 stays fully serial).
    #[test]
    fn eq_table_parallel_and_seeded_match_serial() {
        let mut rng = Rng::new(21);
        for n in [0usize, 1, 6, 13, 15] {
            let point: Vec<F192> = (0..n).map(|_| rng.ext()).collect();
            let serial = build_eq_table_ext(&point);
            assert_eq!(
                &*build_eq_table_ext_parallel(&point),
                &serial[..],
                "parallel mismatch at n={n}"
            );
            let g = rng.ext();
            let mut seeded = Box::new_uninit_slice(1 << n).into_vec();
            primitives::multilinear::fill_eq_table_uninit(&point, g, &mut seeded);
            // SAFETY: fill_eq_table_uninit initializes every entry.
            let seeded = unsafe { seeded.into_boxed_slice().assume_init() }.into_vec();
            let scaled: Vec<F192> = serial.iter().map(|&e| g * e).collect();
            assert_eq!(&*seeded, &scaled, "seeded mismatch at n={n}");
        }
    }

    /// At log_n = 18 the production profile's L0 has log_msg_cols = 12 and
    /// enough queries to trip the sparse transposed-NTT dispatch; the smaller
    /// shape stays on the dense path (cols < 12).
    #[test]
    fn induce_dispatch_follows_the_shape() {
        let pc = config_for_rate(18, LOG_INV_RATE_0).expect("Johnson profile feasible at log_n = 18");
        assert!(
            induce_use_ntt_heuristic(18 - pc.initial_k, pc.log_inv_rates[0], pc.queries[0]),
            "shape must select the sparse transposed-NTT induce at L0"
        );
        let pc16 = config_for_rate(16, LOG_INV_RATE_0).unwrap();
        assert!(!induce_use_ntt_heuristic(
            16 - pc16.initial_k,
            pc16.log_inv_rates[0],
            pc16.queries[0]
        ));
    }

    /// Committing only the lanes that carry data must be indistinguishable from
    /// committing the whole `2^log_n` witness with an explicit zero tail: same
    /// root and byte-identical stream, the stored L0 rows differing only by the
    /// zero prefix the truncated proof drops.
    #[test]
    fn truncated_lanes_match_an_explicit_zero_tail() {
        // `log_n = 18` puts the lane block over `ROUND_CHUNK`, so the fold runs several
        // x-chunks per block; at 13 it is one chunk per block. Both matter: the chunked
        // path is what production takes, and it is where a message pair could straddle
        // a task.
        for (log_n, lanes) in [(13usize, &[1usize, 5, 64][..]), (18, &[5, 64][..])] {
            let pc = test_config_for(log_n);
            let lane_block = 1usize << (log_n - pc.initial_k);
            for &n_lanes in lanes {
                let mut rng = Rng::new(0x5AFE + n_lanes as u64);
                let used = n_lanes * lane_block;
                let mut witness: Vec<F64> = (0..1usize << log_n).map(|_| F64(rng.next_u64())).collect();
                let mut b_initial: Vec<F192> = (0..1usize << log_n).map(|_| rng.ext()).collect();
                witness[used..].fill(F64::ZERO);
                b_initial[used..].fill(F192::ZERO);
                let target = inner_product_base_ext(&witness, &b_initial);

                let prove = |msg: &[F64], b: &[F192]| {
                    let (cm, pd) = commit(msg, log_n, pc.initial_k, pc.log_inv_rates[0]);
                    let mut ps = fiat_shamir::transcript::ProverState::from_label(b"whir-test");
                    recursive_prover_with_basis(
                        &pc,
                        log_n,
                        msg,
                        b.to_vec(),
                        target,
                        &pd.codeword,
                        &pd.merkle_tree,
                        &mut ps,
                    );
                    (cm.root, ps.into_proof())
                };
                let (root_trunc, fs_trunc) = prove(&witness[..used], &b_initial[..used]);
                let (root_full, fs_full) = prove(&witness, &b_initial);
                assert_eq!(root_trunc, root_full, "root differs at n_lanes = {n_lanes}");
                assert_eq!(
                    fs_trunc.stream, fs_full.stream,
                    "the protocol itself must not change at n_lanes = {n_lanes}"
                );

                // What the two proofs DO differ in, and the point of the exercise: the
                // truncated one stores each L0 row as the committed lanes alone, which is
                // exactly the full image with its leading padding zeros dropped.
                let leaf_words = 1usize << pc.initial_k;
                for (thin, full) in fs_trunc.merkle[0].leaf_data.iter().zip(&fs_full.merkle[0].leaf_data) {
                    assert_eq!(thin.len(), n_lanes);
                    assert_eq!(full.len(), leaf_words);
                    assert_eq!(thin[..], full[leaf_words - n_lanes..], "stored row is the image tail");
                    assert!(
                        full[..leaf_words - n_lanes].iter().all(|w| *w == F64::ZERO),
                        "the words the proof drops are the padding at n_lanes = {n_lanes}"
                    );
                }
            }
        }
    }

    /// Encoding one replica at a time commits to the same tree as encoding the whole codeword, and encodes the
    /// same rows again.
    #[test]
    fn replicas_encode_the_codeword() {
        let mut rng = Rng::new(0x2E91);
        let shapes = [
            (13usize, 1usize, &[1usize, 5, 64][..]),
            (14, 2, &[3][..]),
            (18, 1, &[37][..]),
            (21, 1, &[9][..]),
        ];
        for (log_n, log_inv_rate, lanes) in shapes {
            for &n_lanes in lanes {
                let message: Vec<F64> = (0..n_lanes << (log_n - 6)).map(|_| F64(rng.next_u64())).collect();
                let (commitment, data) = commit(&message, log_n, 6, log_inv_rate);
                let (lean, tree) = commit_tree(&message, log_n, 6, log_inv_rate);
                assert_eq!(lean.root, commitment.root, "log_n={log_n}, lanes={n_lanes}");
                assert_eq!(tree, data.merkle_tree, "log_n={log_n}, lanes={n_lanes}");
                let positions: Vec<usize> = (0..40)
                    .map(|_| rng.next_u64() as usize % (data.codeword.len() / n_lanes))
                    .chain([0, 0])
                    .collect();
                // One lane at a time, two (the last group short when the count is odd), and all at once.
                let lane_words = data.codeword.len() / n_lanes;
                for budget in [1, 2 * lane_words, REENCODE_WORDS] {
                    let rows = encoded_rows_within(&message, log_n, 6, log_inv_rate, &positions, budget);
                    for (row, &q) in rows.iter().zip(&positions) {
                        assert_eq!(row[..], data.codeword[q * n_lanes..(q + 1) * n_lanes], "row {q}");
                    }
                }
            }
        }
    }

    /// A commitment that skips its all-zero lanes has the tree of the whole codeword, and encodes its rows again
    /// alike: zero lanes leading, trailing, inside, alone, in runs; none, and all but one.
    #[test]
    fn skipped_zero_lanes_encode_the_codeword() {
        let mut rng = Rng::new(0x5C1F);
        let shapes: [(usize, usize, &[usize]); 5] = [
            (21, 41, &[9, 10, 11, 12, 13, 14, 15, 25, 26, 27, 28, 29, 30, 31]),
            (21, 45, &[13, 14, 15, 29, 30, 31]),
            (20, 33, &[0, 7, 31]),
            (19, 64, &[]),
            (19, 5, &[0, 1, 3, 4]),
        ];
        for (log_n, n_lanes, zero) in shapes {
            let lane = 1usize << (log_n - 6);
            let mut message: Vec<F64> = (0..n_lanes * lane).map(|_| F64(rng.next_u64())).collect();
            for &b in zero {
                message[b * lane..(b + 1) * lane].fill(F64::ZERO);
            }
            let flags: Vec<bool> = (0..n_lanes).map(|b| zero.contains(&b)).collect();
            let (commitment, data) = commit(&message, log_n, 6, 1);
            let (skipping, tree) = commit_tree_skipping_in(&message, log_n, 6, 1, &flags, Vec::new());
            assert_eq!(skipping.root, commitment.root, "log_n={log_n}, lanes={n_lanes}");
            assert_eq!(tree, data.merkle_tree, "log_n={log_n}, lanes={n_lanes}");
            let positions: Vec<usize> = (0..40)
                .map(|_| rng.next_u64() as usize % (data.codeword.len() / n_lanes))
                .chain([0, 0])
                .collect();
            let rows = encoded_rows_skipping(&message, log_n, 6, 1, &flags, &positions);
            for (row, &q) in rows.iter().zip(&positions) {
                assert_eq!(row[..], data.codeword[q * n_lanes..(q + 1) * n_lanes], "row {q}");
            }
        }
    }

    /// A deeper level committed one replica at a time, its message kept, has the tree and opens the rows of the
    /// level committed whole.
    #[test]
    fn lean_levels_open_the_codeword() {
        let mut rng = Rng::new(0x1E4);
        for (log_msg_cols, log_lanes, log_inv_rate) in [(6usize, 2usize, 1usize), (9, 4, 4), (12, 4, 3)] {
            let poly = rng.ext_vec(1 << (log_msg_cols + log_lanes));
            let ntt = AdditiveNttF64::standard(log_msg_cols + log_inv_rate);
            let whole = ligero_commit_ext_within(&poly, log_msg_cols, log_lanes, log_inv_rate, &ntt, usize::MAX);
            let lean = ligero_commit_ext_within(&poly, log_msg_cols, log_lanes, log_inv_rate, &ntt, 0);
            assert!(matches!(whole.rows, LigeroRows::Codeword(_)) && matches!(lean.rows, LigeroRows::Message { .. }));
            assert_eq!(lean.tree, whole.tree, "log_msg_cols={log_msg_cols}");
            let positions: Vec<usize> = (0..30).map(|_| rng.next_u64() as usize % whole.block_len).collect();
            assert_eq!(
                lean.rows(&positions),
                whole.rows(&positions),
                "log_msg_cols={log_msg_cols}"
            );
        }
    }

    /// The lane rounds on lane tensors, with the codeword or with the rows encoded again, prove what the dense
    /// weight proves, byte for byte, at every count of absent lanes.
    #[test]
    fn lane_tensors_prove_what_the_dense_weight_proves() {
        for (log_n, lanes) in [(13usize, &[1usize, 2, 5, 64][..]), (18, &[37][..])] {
            let pc = test_config_for(log_n);
            let lane_block = 1usize << (log_n - pc.initial_k);
            for &n_lanes in lanes {
                let mut rng = Rng::new(0x7E5 + n_lanes as u64);
                let witness: Vec<F64> = (0..n_lanes * lane_block).map(|_| F64(rng.next_u64())).collect();
                let weight: Vec<LaneTensor> = (0..3)
                    .map(|c| LaneTensor {
                        // A lane of zero scale, as a claim whose high coordinates miss it leaves.
                        scales: (0..n_lanes)
                            .map(|l| if l == c { F192::ZERO } else { rng.ext() })
                            .collect(),
                        // The third a sparse low weight, as a hidden layout's gadget: a few entries, in different
                        // chunks.
                        low: Low::Table(match c {
                            2 => (0..lane_block)
                                .map(|x| match x == 1 || x == lane_block / 2 + 3 || x == lane_block - 1 {
                                    true => rng.ext(),
                                    false => F192::ZERO,
                                })
                                .collect(),
                            _ => rng.ext_vec(lane_block),
                        }),
                    })
                    .collect();
                let dense: Vec<F192> = (0..witness.len())
                    .map(|i| {
                        weight.iter().fold(F192::ZERO, |acc, t| {
                            acc + t.scales[i / lane_block] * t.low.at(i % lane_block)
                        })
                    })
                    .collect();
                let target = inner_product_base_ext(&witness, &dense);
                let (cm, pd) = commit(&witness, log_n, pc.initial_k, pc.log_inv_rates[0]);
                let prove = |run: &dyn Fn(&mut ProverState)| {
                    let mut ps = ProverState::from_label(b"whir-test");
                    run(&mut ps);
                    ps.into_proof()
                };
                let expected = prove(&|ps| {
                    recursive_prover_with_basis(
                        &pc,
                        log_n,
                        &witness,
                        dense.clone(),
                        target,
                        &pd.codeword,
                        &pd.merkle_tree,
                        ps,
                    )
                });
                for codeword in [Some(&pd.codeword[..]), None] {
                    let actual = prove(&|ps| {
                        recursive_prover_with_lane_tensors(
                            &pc,
                            log_n,
                            &witness,
                            &weight,
                            target,
                            codeword,
                            &pd.merkle_tree,
                            ps,
                        )
                    });
                    assert_eq!(
                        actual,
                        expected,
                        "log_n={log_n}, lanes={n_lanes}, codeword={}",
                        codeword.is_some()
                    );
                }
                let _ = cm;
            }
        }
    }

    /// `eq` low weights (dense, and with all but three coordinates boolean: sparse), known inner products, and
    /// several openings on one commitment at once prove what written-out tables prove alone, byte for byte.
    #[test]
    fn eq_lows_known_products_and_batches_prove_what_tables_prove() {
        for (log_n, n_lanes) in [(13usize, 5usize), (13, 64), (18, 37)] {
            let pc = test_config_for(log_n);
            let lane_block = 1usize << (log_n - pc.initial_k);
            let log_lane = lane_block.trailing_zeros() as usize;
            let mut rng = Rng::new(0xE0 + n_lanes as u64);
            let witness: Vec<F64> = (0..n_lanes * lane_block).map(|_| F64(rng.next_u64())).collect();
            let (_, pd) = commit(&witness, log_n, pc.initial_k, pc.log_inv_rates[0]);
            let boolean: Vec<F192> = (0..log_lane)
                .map(|j| match j {
                    0..3 => rng.ext(),
                    _ if j % 2 == 0 => F192::ONE,
                    _ => F192::ZERO,
                })
                .collect();
            let points = [rng.ext_vec(log_lane), rng.ext_vec(log_lane), boolean];
            let scales: Vec<Vec<F192>> = (0..3).map(|_| rng.ext_vec(1 << pc.initial_k)).collect();
            let tensors = |eq: bool| -> Vec<LaneTensor> {
                points
                    .iter()
                    .zip(&scales)
                    .map(|(p, s)| LaneTensor {
                        scales: s.clone(),
                        low: if eq { Low::Eq(p.clone()) } else { Low::Table(build_eq_table_ext(p)) },
                    })
                    .collect()
            };
            let (tables, eqs) = (tensors(false), tensors(true));
            let targets = [rng.ext(), rng.ext()];
            let labels: [&[u8]; 2] = [b"job 0", b"job 1"];
            // Job `k` is the tensors `0` and `k + 1`, alone and on tables.
            let expected: Vec<fiat_shamir::transcript::Proof> = (0..2)
                .map(|k| {
                    let mut ps = ProverState::from_label(labels[k]);
                    recursive_prover_with_lane_tensors(
                        &pc,
                        log_n,
                        &witness,
                        &[tables[0].clone(), tables[k + 1].clone()],
                        targets[k],
                        Some(&pd.codeword),
                        &pd.merkle_tree,
                        &mut ps,
                    );
                    ps.into_proof()
                })
                .collect();
            let known = dense_lane_inner_products(&witness, lane_block, &[&eqs[0].low]);
            let mut states: Vec<ProverState> = labels.iter().map(|l| ProverState::from_label(l)).collect();
            let mut jobs: Vec<LaneJob<'_>> = states
                .iter_mut()
                .enumerate()
                .map(|(k, ps)| LaneJob {
                    tensors: vec![0, k + 1],
                    target: targets[k],
                    ps,
                })
                .collect();
            recursive_prover_with_lane_tensors_batch(
                &pc,
                log_n,
                &witness,
                &eqs,
                &[Some(&known[0]), None, None],
                &mut jobs,
                Some(&pd.codeword),
                None,
                &pd.merkle_tree,
            );
            drop(jobs);
            let actual: Vec<_> = states.into_iter().map(|ps| ps.into_proof()).collect();
            assert_eq!(actual, expected, "log_n={log_n}, lanes={n_lanes}");
        }
    }

    /// A batch's openings prove what each proves alone from the whole kept codeword, whatever their level-0 rows'
    /// source: encoded again (the lanes flagged all zero left out, or none flagged), or read from a kept codeword of
    /// the unflagged lanes alone ([`commit_skipping`]); the flagged lanes are left out of the lane passes too. [Added
    /// here.]
    #[test]
    fn batched_openings_skip_zero_lanes() {
        batched_openings_at(&[(8, 3), (13, 5), (18, 37)]);
    }

    /// [`batched_openings_skip_zero_lanes`] at a shape for Miri (`miri_`, as `adversarial.rs`'s): the lane passes'
    /// skipped lanes, the rows encoded again.
    #[test]
    fn miri_batched_openings() {
        batched_openings_at(&[(8, 3)]);
    }

    /// The smallest shape [`commit_skipping`] encodes (two sweeps of the unflagged lanes into the compact codeword, whose
    /// memory starts uninitialised; `2^12` rows, more than 32 lanes so that the first sweep has a layer), for Miri
    /// (`MIRIFLAGS=-Zmiri-ignore-leaks`, the pool's threads outliving the test): every word of the compact codeword is
    /// written and is the whole codeword's, the tree is the whole commitment's, and (but under Miri) an opening read
    /// through it ([`L0Rows::Compact`]) is the one read from the whole codeword. [Added here.]
    #[test]
    fn miri_compact_codeword() {
        let (log_n, n_lanes) = (18usize, 36usize);
        // The commitment's shape: 64 lanes at the first fold, rate 1/2 (the opening's configuration is not built
        // under Miri, whose `sqrt` is not IEEE-exact, which `whir_config`'s debug assertions check).
        let (initial_k, log_inv_rate) = (6usize, 1usize);
        let lane_block = 1usize << (log_n - initial_k);
        let mut rng = Rng::new(0xEC);
        let mut witness: Vec<F64> = (0..n_lanes * lane_block).map(|_| F64(rng.next_u64())).collect();
        for l in [2usize, 3, 20] {
            witness[l * lane_block..(l + 1) * lane_block].fill(F64::ZERO);
        }
        let zero: Vec<bool> = (0..n_lanes).map(|l| [2, 3, 20].contains(&l)).collect();
        let (whole, pd) = commit(&witness, log_n, initial_k, log_inv_rate);
        let (compact, data) =
            commit_skipping(&witness, log_n, initial_k, log_inv_rate, &zero).expect("a two-sweep shape");
        assert_eq!((compact.root, &data.merkle_tree), (whole.root, &pd.merkle_tree));
        let kept: Vec<usize> = (0..n_lanes).filter(|&l| !zero[l]).collect();
        let k = kept.len();
        assert_eq!(data.codeword.len() * n_lanes, pd.codeword.len() * k);
        for (row, full) in data.codeword.chunks_exact(k).zip(pd.codeword.chunks_exact(n_lanes)) {
            // Codeword lane `t` is lane block `n_lanes - 1 - t`'s, in both.
            let compact_row: Vec<F64> = kept.iter().rev().map(|&l| full[n_lanes - 1 - l]).collect();
            assert_eq!(row, &compact_row[..]);
        }
        if cfg!(miri) {
            return;
        }
        let pc = test_config_for(log_n);
        assert_eq!((pc.initial_k, pc.log_inv_rates[0]), (initial_k, log_inv_rate));
        let tensors: Vec<LaneTensor> = (0..2)
            .map(|_| LaneTensor {
                scales: rng.ext_vec(1 << pc.initial_k),
                low: Low::Eq(rng.ext_vec(lane_block.trailing_zeros() as usize)),
            })
            .collect();
        let target = rng.ext();
        let prove = |codeword: &[F64], flags: Option<&[bool]>| {
            let mut ps = ProverState::from_label(b"compact");
            let mut jobs = [LaneJob {
                tensors: vec![0, 1],
                target,
                ps: &mut ps,
            }];
            recursive_prover_with_lane_tensors_batch(
                &pc,
                log_n,
                &witness,
                &tensors,
                &[None, None],
                &mut jobs,
                Some(codeword),
                flags,
                &pd.merkle_tree,
            );
            ps.into_proof()
        };
        assert!(prove(&data.codeword, Some(&zero)) == prove(&pd.codeword, None));
    }

    fn batched_openings_at(shapes: &[(usize, usize)]) {
        for &(log_n, n_lanes) in shapes {
            let pc = test_config_for(log_n);
            let lane_block = 1usize << (log_n - pc.initial_k);
            let log_lane = lane_block.trailing_zeros() as usize;
            let mut rng = Rng::new(0xE7 + n_lanes as u64);
            let mut witness: Vec<F64> = (0..n_lanes * lane_block).map(|_| F64(rng.next_u64())).collect();
            // Lane 1 all zero, and lane 3 where there is one past it.
            for l in [1, 3].into_iter().filter(|&l| l + 1 < n_lanes) {
                witness[l * lane_block..(l + 1) * lane_block].fill(F64::ZERO);
            }
            let zero: Vec<bool> = (0..n_lanes).map(|l| witness[l * lane_block..(l + 1) * lane_block].iter().all(|w| w.is_zero())).collect();
            let (_, pd) = commit(&witness, log_n, pc.initial_k, pc.log_inv_rates[0]);
            let tensors: Vec<LaneTensor> = (0..3)
                .map(|_| LaneTensor {
                    scales: rng.ext_vec(1 << pc.initial_k),
                    low: Low::Eq(rng.ext_vec(log_lane)),
                })
                .collect();
            let targets = [rng.ext(), rng.ext()];
            let labels: [&[u8]; 2] = [b"job 0", b"job 1"];
            let expected: Vec<fiat_shamir::transcript::Proof> = (0..2)
                .map(|k| {
                    let mut ps = ProverState::from_label(labels[k]);
                    recursive_prover_with_lane_tensors(
                        &pc,
                        log_n,
                        &witness,
                        &[tensors[0].clone(), tensors[k + 1].clone()],
                        targets[k],
                        Some(&pd.codeword),
                        &pd.merkle_tree,
                        &mut ps,
                    );
                    ps.into_proof()
                })
                .collect();
            let compact = commit_skipping(&witness, log_n, pc.initial_k, pc.log_inv_rates[0], &zero);
            if let Some((c, data)) = &compact {
                assert_eq!(data.merkle_tree, pd.merkle_tree);
                assert_eq!(c.root, *pd.merkle_tree.last().expect("a root"));
            }
            let sources: Vec<(Option<&[F64]>, Option<&[bool]>)> = [(None, None), (None, Some(&zero[..]))]
                .into_iter()
                .chain(compact.as_ref().map(|(_, data)| (Some(&data.codeword[..]), Some(&zero[..]))))
                .collect();
            for (codeword, flags) in sources {
                let mut states: Vec<ProverState> = labels.iter().map(|l| ProverState::from_label(l)).collect();
                let mut jobs: Vec<LaneJob<'_>> = states
                    .iter_mut()
                    .enumerate()
                    .map(|(k, ps)| LaneJob {
                        tensors: vec![0, k + 1],
                        target: targets[k],
                        ps,
                    })
                    .collect();
                recursive_prover_with_lane_tensors_batch(
                    &pc,
                    log_n,
                    &witness,
                    &tensors,
                    &[None, None, None],
                    &mut jobs,
                    codeword,
                    flags,
                    &pd.merkle_tree,
                );
                drop(jobs);
                let actual: Vec<_> = states.into_iter().map(|ps| ps.into_proof()).collect();
                let kept = codeword.is_some();
                assert_eq!(actual, expected, "log_n={log_n}, lanes={n_lanes}, kept={kept}, flags={}", flags.is_some());
            }
        }
    }

    /// The sparse transposed-NTT induce must be byte-identical to the dense
    /// LCH-expansion induce (same guarantee the original pins). Covers both
    /// the windowed sparse-prefix path (log_block >= 12, k = 8) and the
    /// scatter + full-dense-transpose path (log_block < 12, k = 0).
    #[test]
    fn induce_via_ntt_matches_dense() {
        let mut rng = Rng::new(9);
        for (log_msg_cols, log_inv_rate, lanes_log, n_queries) in [(12usize, 1usize, 5usize, 130usize), (6, 2, 3, 40)] {
            let block_len = 1usize << (log_msg_cols + log_inv_rate);
            let lanes = 1usize << lanes_log;
            // Distinct sorted query positions plus one aligned random row each.
            let mut qs: Vec<usize> = Vec::new();
            let mut seen = std::collections::HashSet::new();
            while qs.len() < n_queries {
                let q = (rng.next_u64() as usize) % block_len;
                if seen.insert(q) {
                    qs.push(q);
                }
            }
            qs.sort_unstable();
            let rows: Vec<Vec<F64>> = (0..n_queries)
                .map(|_| (0..lanes).map(|_| F64(rng.next_u64())).collect())
                .collect();
            let v_challenges: Vec<F192> = (0..lanes_log).map(|_| rng.ext()).collect();
            let weights = powers(rng.ext(), n_queries);

            let sks_vks = eval_sk_at_vks(log_msg_cols);
            let dense = induce_sumcheck_poly(log_msg_cols, &sks_vks, &rows, &v_challenges, &qs, &weights);
            let via_ntt = induce_sumcheck_poly_via_ntt(log_msg_cols, log_inv_rate, &rows, &v_challenges, &qs, &weights);
            assert_eq!(dense.1, via_ntt.1, "enforced_sum mismatch");
            assert_eq!(&*dense.0, &*via_ntt.0, "basis_poly mismatch");
        }
    }

    /// The `E` round kernels four products at a time are the one-product-at-a-time forms, at lengths on both sides
    /// of the vectors and the chunks, on the calling thread or the pool (the round messages at powers of two alone,
    /// the lengths they take).
    #[test]
    fn vectored_ext_rounds_match_one_product_at_a_time() {
        let mut rng = Rng::new(0xe4e4);
        for n in [2usize, 4, 6, 8, 14, 16, 30, 4096, 1 << 14, 3 << 13] {
            let f = rng.ext_vec(n);
            let b = rng.ext_vec(n);
            let r = rng.ext();
            let half = n / 2;
            let pairs =
                |v: &[F192]| -> Vec<(F192, F192)> { v.as_chunks::<2>().0.iter().map(|x| (x[0], x[1])).collect() };
            let (fp, bp) = (pairs(&f), pairs(&b));

            let mut got = vec![F192::ZERO; half];
            fold_ext_into(&f, r, &mut got);
            let want: Vec<F192> = fp.iter().map(|&(x0, x1)| x0 + r * (x0 + x1)).collect();
            assert_eq!(got, want, "fold, {n}");

            let msg = |fp: &[(F192, F192)], bp: &[(F192, F192)]| {
                fp.iter()
                    .zip(bp)
                    .fold((F192::ZERO, F192::ZERO), |(u0, u2), (&(f0, f1), &(b0, b1))| {
                        (u0 + f0 * b0, u2 + (f0 + f1) * (b0 + b1))
                    })
            };
            let (u_0, u_2) = fold_msg_terms(&f, &b);
            assert_eq!((u_0.reduce(), u_2.reduce()), msg(&fp, &bp), "message terms, {n}");
            // The round kernels take a power of two words (their `debug_assert`s): the other lengths test the
            // folds' and the terms' tails alone.
            if !n.is_power_of_two() {
                continue;
            }
            let got = round_msg_lsb(&f, &b);
            assert_eq!((got.u_0, got.u_2), msg(&fp, &bp), "round message, {n}");

            let (got, y) = round_msg_and_eval_lsb_ext(&f, &b);
            assert_eq!(
                (got.u_0, got.u_2),
                msg(&fp, &bp),
                "round message with the evaluation, {n}"
            );
            assert_eq!(
                y,
                f.iter().zip(&b).fold(F192::ZERO, |a, (&x, &w)| a + x * w),
                "evaluation, {n}"
            );

            let (nf, nb, got) = fold_and_msg_lsb(&f, &b, r);
            let want_f: Vec<F192> = fp.iter().map(|&(x0, x1)| x0 + r * (x0 + x1)).collect();
            let want_b: Vec<F192> = bp.iter().map(|&(x0, x1)| x0 + r * (x0 + x1)).collect();
            assert_eq!((&nf, &nb), (&want_f, &want_b), "fold and message, {n}");
            assert_eq!(
                (got.u_0, got.u_2),
                msg(&pairs(&want_f), &pairs(&want_b)),
                "folded message, {n}"
            );
        }
    }

    /// The dense induce by chunks of the basis is the per-query one, entry for entry, at the shapes the deeper
    /// levels take (a few dozen queries, up to `2^14` entries), on the calling thread or the pool, and at the
    /// degenerate ones.
    #[test]
    fn chunked_induce_matches_the_per_query_one() {
        let mut rng = Rng::new(0x1d0c);
        for (log_msg_cols, lanes_log, n_queries) in [
            (0usize, 2usize, 3usize),
            (1, 1, 2),
            (5, 4, 7),
            (9, 4, 23),
            (13, 4, 32),
            (14, 4, 56),
        ] {
            let block_len = 1usize << (log_msg_cols + 7);
            let qs: Vec<usize> = (0..n_queries).map(|_| (rng.next_u64() as usize) % block_len).collect();
            let rows: Vec<Vec<F192>> = (0..n_queries).map(|_| rng.ext_vec(1 << lanes_log)).collect();
            let v_challenges: Vec<F192> = (0..lanes_log).map(|_| rng.ext()).collect();
            let weights = powers(rng.ext(), n_queries);
            let sks_vks = eval_sk_at_vks(log_msg_cols);
            let chunked = induce_sumcheck_poly(log_msg_cols, &sks_vks, &rows, &v_challenges, &qs, &weights);
            let by_query = crate::whir_induce::induce_sumcheck_poly_by_query(
                log_msg_cols,
                &sks_vks,
                &rows,
                &v_challenges,
                &qs,
                &weights,
            );
            assert_eq!(chunked, by_query, "2^{log_msg_cols} entries, {n_queries} queries");
        }
    }

    /// The second lane round must read the same folded witness from the base lanes
    /// as from the first round's stored fold, at every count of absent lanes.
    #[test]
    fn lifted_lane_fold_matches_the_stored_fold() {
        let mut rng = Rng::new(0x11F7);
        for block in [16, ROUND_CHUNK, 2 * ROUND_CHUNK] {
            for lanes in [1, 2, 3, 4, 5, 6, 7, 8, 37] {
                let f: Vec<F64> = (0..block * lanes).map(|_| F64(rng.next_u64())).collect();
                let b = rng.ext_vec(f.len());
                let (r0, r1) = (rng.ext(), rng.ext());
                let (nf, nb, msg) = fold_and_msg_blocks(lane_fold(&f, block, r0), &b, r0, block, false);
                assert_eq!(
                    fold_base_and_msg_blocks(&f, &b, r0, block),
                    (nb.clone(), msg),
                    "block={block}, lanes={lanes}"
                );
                for last in [false, lanes <= 4] {
                    let stored = fold_and_msg_blocks(lane_fold(&nf, block, r1), &nb, r1, block, last);
                    let lifted = fold_and_msg_blocks(lifted_lane_fold(&f, block, r0, r1), &nb, r1, block, last);
                    assert_eq!(lifted, stored, "block={block}, lanes={lanes}, last={last}");
                }
            }
        }
    }

    #[test]
    fn initial_basis_message_matches_materialized_weights() {
        let mut rng = Rng::new(0xBA515);
        for block in [1, 16, INITIAL_BASIS_CHUNK, 4 * INITIAL_BASIS_CHUNK] {
            for lanes in [1, 2, 3, 37] {
                let f: Vec<F64> = (0..block * lanes).map(|_| F64(rng.next_u64())).collect();
                let expected = rng.ext_vec(f.len());
                let expected_message = round_msg_blocks(&f, &expected, block);
                let (actual, message) = build_initial_basis(&f, block, |start, out| {
                    out.copy_from_slice(&expected[start..start + out.len()]);
                });
                assert_eq!(&*actual, expected, "block={block}, lanes={lanes}");
                assert_eq!(message, expected_message, "block={block}, lanes={lanes}");
            }
        }
    }
}
