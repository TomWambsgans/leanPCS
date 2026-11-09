// Part of this repository (not in leanVM). MIT OR Apache-2.0 (see LICENSE-MIT, LICENSE-APACHE and AGENTS.md at the
// repository root).
//! The commitment and opening of a stack of whole lanes, as the recursion's provers make them: `commit_tree_in` (the
//! tree alone, or `commit` keeping the codeword with `LANES_KEEP`), then `recursive_prover_with_lane_tensors` on one
//! lane tensor per claim. Times each phase per pass and prints medians.
//!
//! ```text
//! LANES_LOG_N   the stack's variables                        [default 28]
//! LANES_LANES   lanes carrying data, at most 64              [default 60: π2's Q]
//! LANES_CLAIMS  claims (lane tensors)                        [default 2]
//! LANES_KEEP    keep the codeword (`commit`) for the opening
//! LANES_SCHEDULE  the ladder's RS-domain schedule, `initial,subsequent[,min_log_block]`  [default 3,1: the deployed one]
//! BENCH_REPEAT, BENCH_TRACING
//!
//! cargo bench -p pcs --bench lanes
//! ```

use std::hint::black_box;
use std::time::Instant;

use bench::{Plan, env_usize};
use pcs::whir::{DomainSchedule, LaneTensor, commit, commit_tree_in, config_for_schedule, recursive_prover_with_lane_tensors};
use primitives::field::{F64, F192};
use primitives::test_rng::Rng;

#[global_allocator]
static ALLOCATOR: bench::Jemalloc = bench::Jemalloc;

fn main() {
    bench::init_tracing_from_env();
    parallel::init();
    let log_n = env_usize("LANES_LOG_N", 28);
    let lanes = env_usize("LANES_LANES", 60);
    let claims = env_usize("LANES_CLAIMS", 2);
    let keep = std::env::var_os("LANES_KEEP").is_some();
    let schedule = std::env::var("LANES_SCHEDULE").map_or(pcs::whir::DEPLOYED_SCHEDULE, |v| {
        let parts: Vec<usize> = v.split(',').map(|x| x.trim().parse().expect("a number")).collect();
        DomainSchedule {
            initial: parts[0],
            subsequent: parts[1],
            min_log_block: parts.get(2).copied().unwrap_or(0),
        }
    });
    let config = config_for_schedule(log_n, 1, schedule).expect("a WHIR shape");
    println!(
        "lanes: schedule {schedule:?}: rates {:?}, folds {} then {:?}, queries {:?}",
        config.log_inv_rates, config.initial_k, config.level_ks, config.queries
    );
    let log_lane = log_n - config.initial_k;
    let mut rng = Rng::new(0x1a7e5 ^ log_n as u64);
    let words: Vec<F64> = (0..lanes << log_lane).map(|_| F64(rng.next_u64())).collect();
    let weight: Vec<LaneTensor> = (0..claims)
        .map(|_| LaneTensor {
            scales: rng.ext_vec(lanes),
            low: primitives::multilinear::eq_table(&rng.ext_vec(log_lane)),
        })
        .collect();
    let target = F192::ZERO; // the proof need not verify: the work is the same
    let plan = Plan::from_env();
    if std::env::var_os("LANES_PARTS").is_some() {
        // The commitment's two parts alone: the encode, its rows dropped, and the leaves and tree of a codeword
        // as long.
        use pcs::ntt::{AdditiveNttF64, additive_ntt_f64::MsgLayout};
        let ntt = AdditiveNttF64::standard(log_lane + 1);
        let mut work = vec![F64::ZERO; words.len()];
        let codeword: Vec<F64> = (0..2 * words.len()).map(|i| words[i / 2]).collect();
        let (mut encodes, mut hashes) = (vec![], vec![]);
        for _ in 0..=plan.repeat {
            let t = Instant::now();
            ntt.encode_two_sweep_with(&mut work, &words, MsgLayout::LaneMajor, lanes, 1, &|_, rows| {
                black_box(rows);
            });
            encodes.push(t.elapsed().as_secs_f64());
            let t = Instant::now();
            let builder = pcs::merkle::MerkleBuilder::new(2 << log_lane, lanes, 64);
            let block = 1 << 10;
            parallel::for_each((2 << log_lane) / block, |b| {
                builder.absorb(b * block, &codeword[b * block * lanes..(b + 1) * block * lanes])
            });
            black_box(builder.finish());
            hashes.push(t.elapsed().as_secs_f64());
        }
        // The memory's pace: the message copied (read and written once), and read alone.
        let (mut copies, mut reads) = (vec![], vec![]);
        for _ in 0..=plan.repeat {
            let t = Instant::now();
            parallel::chunks_mut(&mut work, 1 << 16, |k, dst| {
                dst.copy_from_slice(&words[k << 16..][..dst.len()])
            });
            copies.push(t.elapsed().as_secs_f64());
            let t = Instant::now();
            let x = parallel::map_reduce(
                words.len() >> 16,
                || 0u64,
                |k| words[k << 16..][..1 << 16].iter().fold(0, |a, w| a ^ w.0),
                |a, b| a ^ b,
            );
            black_box(x);
            reads.push(t.elapsed().as_secs_f64());
        }
        copies.sort_by(f64::total_cmp);
        reads.sort_by(f64::total_cmp);
        let gb = (words.len() * 8) as f64 / 1e9;
        println!(
            "lanes: memory: copy {:.4} s ({:.0} GB/s each way), read {:.4} s ({:.0} GB/s)",
            copies[copies.len() / 2],
            gb / copies[copies.len() / 2],
            reads[reads.len() / 2],
            gb / reads[reads.len() / 2]
        );
        encodes.sort_by(f64::total_cmp);
        hashes.sort_by(f64::total_cmp);
        println!(
            "lanes: parts at 2^{log_n}, {lanes} lanes: encode {:.4} s, leaves and tree {:.4} s (medians)",
            encodes[encodes.len() / 2],
            hashes[hashes.len() / 2]
        );
        return;
    }
    let (mut commits, mut opens) = (vec![], vec![]);
    plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        let t = Instant::now();
        let (root, tree, codeword) = if keep {
            let (c, d) = commit(&words, log_n, config.initial_k, 1);
            (c.root, d.merkle_tree, Some(d.codeword))
        } else {
            let (c, tree) = commit_tree_in(&words, log_n, config.initial_k, 1, Vec::new());
            (c.root, tree, None)
        };
        commits.push(t.elapsed().as_secs_f64());
        let t = Instant::now();
        let mut ps = fiat_shamir::transcript::ProverState::from_label(b"lanes-bench");
        ps.add_root(&root);
        tracing::info_span!("open").in_scope(|| {
            recursive_prover_with_lane_tensors(
                &config,
                log_n,
                &words,
                &weight,
                target,
                codeword.as_deref(),
                &tree,
                &mut ps,
            )
        });
        opens.push(t.elapsed().as_secs_f64());
        black_box(ps.into_proof());
    });
    let median = |v: &mut Vec<f64>| {
        v.remove(0);
        v.sort_by(f64::total_cmp);
        v[v.len() / 2]
    };
    println!(
        "lanes: 2^{log_n}, {lanes} lanes, {claims} claims, keep {keep}: commit {:.4} s, open {:.4} s (medians of {}); peak RSS {:.2} GB",
        median(&mut commits),
        median(&mut opens),
        plan.repeat,
        bench::peak_rss_bytes() as f64 / 1e9
    );
}
