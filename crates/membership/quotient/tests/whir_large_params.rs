// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The WHIR parameters `formal/WhirBridge/WhirBridge/LargeParams.lean` decides at the stack sizes `2^24 ..= 2^28`
//! (rate `1/2`), against the Rust:
//!
//! * the prover's configuration (`pcs::whir::config_for_rate`, the per-level eta search of `whir_config.rs`): the
//!   folds, rate exponents, queries, grinding bits, out-of-domain samples and residual, level by level;
//! * the verifier's tabulated query counts (`WHIR_QUERIES` of `crates/vendor/leanvm-c445e3d5/verifier/src/whir.rs`, read from its source:
//!   the table is private) and its ladder rule;
//! * the Lean `largeLadder` (decided equal to leanerVM mumbai's `Whir.ladder`, `ladder_large`), its certified
//!   level-0 lists `largeList` (`listHi_large`) and the opening's query count `largeQueries` (`largeQueries_eq`),
//!   copied below.
//!
//! With `--nocapture` it also prints each level's slack `eta` from the code's search and the level-0 Johnson list it
//! implies, `1 / (2 eta sqrt(rho))`, next to leanerVM's certified list (the code's search omits the fold group's
//! row-union factor `2^(l-1)`, so its lists are smaller; `params/whir_params.py`).
//!
//!   cargo test --release -p quotient --test whir_large_params -- --nocapture
//!   cargo test --release -p quotient --test whir_large_params -- --ignored --nocapture large_public_openings

use pcs::whir_config::WhirSecurityConfig;
use pcs_claim::lean::bridge_vector;
use pcs_claim::{Codeword, commit, open};
use primitives::field::{F64, F192};
use primitives::test_rng::Rng;

/// A ladder: per level `(fold, log_inv_rate, queries)`.
type Ladder = &'static [(usize, usize, usize)];

/// `largeLadder` (`LargeParams.lean`).
const LEAN_LADDERS: [(usize, Ladder); 5] = [
    (24, &[(6, 1, 224), (4, 4, 56), (4, 7, 32), (4, 10, 23), (4, 13, 17)]),
    (25, &[(6, 1, 224), (4, 4, 56), (4, 7, 32), (4, 10, 23), (4, 13, 17)]),
    (26, &[(6, 1, 224), (4, 4, 56), (4, 7, 32), (4, 10, 23), (4, 13, 18)]),
    (27, &[(6, 1, 225), (4, 4, 56), (4, 7, 32), (4, 10, 23), (4, 13, 18)]),
    (
        28,
        &[
            (6, 1, 225),
            (4, 4, 56),
            (4, 7, 32),
            (4, 10, 23),
            (4, 13, 18),
            (4, 16, 14),
        ],
    ),
];

/// `residual_large`: the variables left after the folds.
const LEAN_RESIDUAL: [usize; 5] = [2, 3, 4, 5, 2];

/// `largeList` (`listHi_large`): leanerVM's certified level-0 lists.
const LEAN_LIST: [usize; 5] = [9952, 7908, 6296, 4473, 3564];

/// `largeQueries` (`largeQueries_eq`): the opening's queries to the two oracles.
const LEAN_QO: [usize; 5] = [7183, 7546, 7928, 8318, 9018];

/// `QUERY_GRINDING_BITS` (`grinding_large`).
const LEAN_GRINDING: usize = 17;

/// Row `log_inv_rate - 1`, entry `log_n - 15` of `WHIR_QUERIES`, parsed from the verifier's source.
fn verifier_queries(log_inv_rate: usize, log_n: usize) -> Vec<usize> {
    let source = include_str!("../../../vendor/leanvm-c445e3d5/verifier/src/whir.rs");
    let start = source.find("const WHIR_QUERIES").expect("WHIR_QUERIES in whir.rs");
    let row = source[start..].lines().nth(log_inv_rate).expect("a row per rate");
    let entries: Vec<Vec<usize>> = row
        .split("&[")
        .skip(1)
        .map(|e| {
            e.split(']')
                .next()
                .expect("an entry")
                .split(',')
                .map(|x| x.trim().parse().expect("a count"))
                .collect()
        })
        .collect();
    assert_eq!(entries.len(), 14, "14 stack sizes, 15 to 28");
    entries[log_n - 15].clone()
}

/// The verifier's ladder (`derive_config`, `whir.rs:34-60`): folds and rate exponents.
fn verifier_ladder(log_n: usize, log_inv_rate: usize) -> (Vec<usize>, Vec<usize>) {
    let (mut folds, mut rates, mut remaining) = (vec![6], vec![log_inv_rate], log_n - 6);
    while remaining > 5 {
        let reduction = if folds.len() == 1 { 3 } else { 1 };
        rates.push(rates[rates.len() - 1] + folds[folds.len() - 1] - reduction);
        let fold = remaining.min(4);
        remaining -= fold;
        folds.push(fold);
    }
    (folds, rates)
}

fn reduced_rate(log_inv_rate: usize, log_msg_cols: usize) -> f64 {
    ((log_msg_cols as f64).exp2() - 1.0) / ((log_msg_cols + log_inv_rate) as f64).exp2()
}

#[test]
fn whir_large_params_match_lean() {
    for (i, &(log_n, ladder)) in LEAN_LADDERS.iter().enumerate() {
        let folds: Vec<usize> = ladder.iter().map(|l| l.0).collect();
        let rates: Vec<usize> = ladder.iter().map(|l| l.1).collect();
        let queries: Vec<usize> = ladder.iter().map(|l| l.2).collect();

        // The prover's derived configuration.
        let cfg = pcs::whir::config_for_rate(log_n, 1).expect("a supported shape");
        let shapes = cfg.level_shapes(log_n);
        assert_eq!(shapes.ks, folds, "folds at log_n = {log_n}");
        assert_eq!(cfg.log_inv_rates, rates, "rates at log_n = {log_n}");
        assert_eq!(cfg.queries, queries, "queries at log_n = {log_n}");
        assert_eq!(
            cfg.grinding_bits,
            vec![LEAN_GRINDING; ladder.len()],
            "grinding at log_n = {log_n}"
        );
        let mut ood = vec![1; ladder.len()];
        ood[0] = 0;
        assert_eq!(
            cfg.ood_samples, ood,
            "out-of-domain samples at log_n = {log_n} (none at level 0)"
        );
        assert_eq!(shapes.yr_log_n, LEAN_RESIDUAL[i], "residual at log_n = {log_n}");

        // The verifier's table and ladder.
        assert_eq!(verifier_queries(1, log_n), queries, "WHIR_QUERIES at log_n = {log_n}");
        assert_eq!(
            verifier_ladder(log_n, 1),
            (folds.clone(), rates.clone()),
            "ladder at log_n = {log_n}"
        );

        // The code's own slack search, against the certified list.
        let sec = WhirSecurityConfig::derive_config_with_log_inv_rate(log_n + pcs::LOG_PACKING, 1)
            .expect("a supported shape");
        let l0 = &sec.levels[0];
        let code_list = 1.0 / (2.0 * l0.eta * reduced_rate(l0.log_inv_rate, l0.log_msg_cols).sqrt());
        println!(
            "log_n = {log_n}: folds {folds:?}, rates {rates:?}, queries {queries:?}, grinding {LEAN_GRINDING}, \
             residual {}; level-0 list: code's search {:.1} (2^{:.2}, eta {:.6e}), certified {} (2^{:.2}); \
             QO {}",
            LEAN_RESIDUAL[i],
            code_list,
            code_list.log2(),
            l0.eta,
            LEAN_LIST[i],
            (LEAN_LIST[i] as f64).log2(),
            LEAN_QO[i],
        );
        for (j, level) in sec.levels.iter().enumerate() {
            let list = 1.0 / (2.0 * level.eta * reduced_rate(level.log_inv_rate, level.log_msg_cols).sqrt());
            println!(
                "   L{j}: msg 2^{} rate 1/2^{} fold {} queries {} ood {} eta {:.6e} list {:.1}",
                level.log_msg_cols, level.log_inv_rate, level.k, level.queries, level.ood_samples, level.eta, list
            );
        }
        assert!(
            code_list < LEAN_LIST[i] as f64,
            "the code's list is below the certified one"
        );
    }
}

/// Openings at `2^24 ..= 2^MAX` words (`WHIR_LARGE_MAX`, default 26; the prover's memory grows with the table): the
/// prover's opening of one claim verifies and a changed value is rejected; each opening is written
/// (`target/whir_large_vector.txt`, or `$WHIR_LARGE_VECTOR`) for `formal/WhirBridge/Test/CheckLarge.lean`.
#[test]
#[ignore = "heavy: commits and opens tables of 2^24 words and more"]
fn large_public_openings() {
    let max: usize = std::env::var("WHIR_LARGE_MAX")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(26);
    let path = std::env::var("WHIR_LARGE_VECTOR")
        .unwrap_or_else(|_| concat!(env!("CARGO_MANIFEST_DIR"), "/../../../target/whir_large_vector.txt").to_string());
    let mut out = String::new();
    let mut rng = Rng::new(0x1a7e);
    for n in 24..=max {
        let start = std::time::Instant::now();
        let table: Vec<F64> = (0..1u64 << n)
            .map(|k| F64((k + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(17)))
            .collect();
        let committed = commit(table, false);
        let claim = committed.claim_at(rng.ext_vec(n));
        let proof = open(committed.words(), &committed, &claim, Codeword::Free);
        let proved = start.elapsed();
        let start = std::time::Instant::now();
        assert!(pcs_claim::verify(&claim.encode(), &pcs_claim::wire_proof(&proof)), "n = {n}");
        let verified = start.elapsed();
        let mut bad = claim.clone();
        bad.value += F192::ONE;
        assert!(!pcs_claim::verify(&bad.encode(), &pcs_claim::wire_proof(&proof)), "n = {n}: a wrong value");
        // `formal/WhirBridge/Test/CheckLarge.lean`'s vector.
        out += &bridge_vector(&format!("public{n}"), &claim, &proof);
        println!(
            "n = {n}: committed and opened in {:.1} s, verified in {:.1} ms; a wrong value rejected",
            proved.as_secs_f64(),
            verified.as_secs_f64() * 1e3
        );
    }
    std::fs::write(&path, out).expect("write the vectors");
    println!("wrote {path}");
}
