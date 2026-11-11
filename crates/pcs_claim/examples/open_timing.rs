// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! One commitment and one opening of `2^n` random words, timed, with the process's peak memory:
//! `cargo run --release -p pcs_claim --example open_timing -- <n>...` (default 26 28).

use std::time::Instant;

use primitives::field::{F64, F192};

fn main() {
    let ns: Vec<usize> = std::env::args().skip(1).map(|a| a.parse().expect("n")).collect();
    let ns = if ns.is_empty() { vec![26, 28] } else { ns };
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for n in ns {
        let words: Vec<F64> = (0..1usize << n).map(|_| F64(next())).collect();
        let point: Vec<F192> = (0..n).map(|_| F192::new(next(), next(), next())).collect();
        let start = Instant::now();
        let committed = pcs_claim::commit(words, false);
        let commit = start.elapsed().as_secs_f64();
        let claim = committed.claim_at(point);
        let start = Instant::now();
        let proof = pcs_claim::open(committed.words(), &committed, &claim, pcs_claim::Codeword::Free);
        let open = start.elapsed().as_secs_f64();
        assert!(pcs_claim::verify(&claim.encode(), &pcs_claim::wire_proof(&proof)));
        let peak = bench::peak_rss_bytes() as f64 / (1u64 << 30) as f64;
        println!("n = {n}: commit {commit:.3} s, open {open:.3} s, peak RSS {peak:.2} GiB");
    }
}
