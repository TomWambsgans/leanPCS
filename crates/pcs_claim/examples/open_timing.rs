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
        let committed = pcs_claim::commit(words);
        let commit = start.elapsed().as_secs_f64();
        let claim = committed.claim_at(point);
        let start = Instant::now();
        let proof = pcs_claim::open(&committed, &claim);
        let open = start.elapsed().as_secs_f64();
        assert!(pcs_claim::verify(&claim.encode(), &pcs_claim::wire_proof(&proof)));
        println!("n = {n}: commit {commit:.3} s, open {open:.3} s, peak RSS {:.2} GiB", peak_gib());
    }
}

fn peak_gib() -> f64 {
    let mut usage: libc_rusage = unsafe { std::mem::zeroed() };
    unsafe { getrusage(0, &mut usage) };
    // macOS reports bytes, Linux kilobytes.
    let bytes = if cfg!(target_os = "macos") { usage.ru_maxrss } else { usage.ru_maxrss * 1024 };
    bytes as f64 / (1u64 << 30) as f64
}

#[repr(C)]
struct libc_rusage {
    ru_utime: [i64; 2],
    ru_stime: [i64; 2],
    ru_maxrss: i64,
    rest: [i64; 13],
}

unsafe extern "C" {
    fn getrusage(who: i32, usage: *mut libc_rusage) -> i32;
}
