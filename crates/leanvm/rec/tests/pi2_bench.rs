// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! π2's prover timed alone on the real reference circuit (`keccak128_rec3.txt`, D16v): the circuit, its setup and the
//! witness once, then `prove` and `open` `PI2_REPEAT` times (default 5) after a warm-up pass, medians printed, and the
//! proof's fingerprints (`tests/pi2_real.rs`'s lines), checked equal across passes.
//!
//! `PI2_REPEAT=5 cargo test --release -p leanvm_rec --test pi2_bench -- --ignored --nocapture`

#[global_allocator]
static ALLOC: bench::Jemalloc = bench::Jemalloc;

#[path = "../../univariate/tests/vectors/mod.rs"]
mod vectors;

use std::time::Instant;

use leanvm_rec::circuit::compile::{Inputs, Layout, pi2};
use leanvm_rec::pi2::adapt;
use leanvm_rec::pi2::prover::{self, Setup, open, prove, verify_openings};
use leanvm_rec::pi2::verifier::Spec;
use leanvm_statement::shapes::PROGRAM_IV;
use leanvm_univariate::Claims;

/// The process's minor page faults so far (`/proc/self/stat`'s tenth field; 0 elsewhere).
fn minor_faults() -> u64 {
    std::fs::read_to_string("/proc/self/stat")
        .ok()
        .and_then(|s| s.rsplit_once(')').and_then(|(_, rest)| rest.split_whitespace().nth(7)?.parse().ok()))
        .unwrap_or(0)
}

fn median(x: &[f64]) -> f64 {
    let mut x = x.to_vec();
    x.sort_by(f64::total_cmp);
    x[x.len() / 2]
}

#[test]
#[ignore]
fn pi2_prover_timed() {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(run)
        .expect("a thread")
        .join()
        .expect("no panic");
}

fn run() {
    parallel::init();
    // `BENCH_TRACING=1`: the trace tree of every pass (WHIR's spans).
    bench::init_tracing_from_env();
    let repeat: usize = std::env::var("PI2_REPEAT").ok().map_or(5, |x| x.parse().expect("a count"));
    let path = format!(
        "{}/../univariate/tests/vectors/keccak128_rec3.txt",
        env!("CARGO_MANIFEST_DIR")
    );
    let v = vectors::read(&std::fs::read_to_string(&path).expect("a committed vector"));
    let roots = leanvm_univariate::contract::SetupRoots {
        f: v.whir_roots[2],
        ..leanvm_univariate::contract::SetupRoots::REFERENCE
    };
    let recorded =
        leanvm_univariate::contract::record_verifier_with(&v.shape, vectors::variant_of(&v.config), Claims::Point, &roots);
    let stream = v.calldata[4 + 32..].to_vec();
    let c = pi2(
        &recorded,
        Layout::D16v,
        &Inputs {
            program_iv: PROGRAM_IV,
            public: v.public,
            stream: &stream,
        },
    );
    let circuit = adapt::adapt(&c.finished.circuit);
    let witness = adapt::witness(&c.finished.witness);
    let (public_input, values) = adapt::public_values(&c.public);
    let pi1_iv = c.pi1_iv;
    drop(c);
    let spec = Spec::of(&circuit);
    let started = Instant::now();
    let setup = Setup::new(&circuit);
    let iv = prover::iv(&pi1_iv, &circuit.digest(), &setup.root(), circuit.log_n);
    println!(
        "setup {:.3} s; peak RSS {:.2} GB",
        started.elapsed().as_secs_f64(),
        bench::peak_rss_bytes() as f64 / 1e9
    );
    let hex = |b: &[u8]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
    let (mut proving, mut opening) = (vec![], vec![]);
    let mut first: Option<(Vec<u8>, Vec<u8>)> = None;
    for pass in 0..=repeat {
        let faults = minor_faults();
        let started = Instant::now();
        let proved = prove(&circuit, &spec, &setup, &iv, &public_input, &values, &witness);
        let p = started.elapsed().as_secs_f64();
        let steps = proved.timings.clone();
        let stream = proved.stream.clone();
        let started = Instant::now();
        let (reduced, roots, openings) = open(proved, &setup);
        let o = started.elapsed().as_secs_f64();
        let faults = minor_faults() - faults;
        let steps: Vec<String> = steps.iter().map(|(n, s)| format!("{s:.3} {n}")).collect();
        println!(
            "pass {pass}: prove {p:.3} s, open {o:.3} s, {faults} minor faults  [{}]",
            steps.join("; ")
        );
        assert_eq!(
            verify_openings(circuit.log_n, &reduced, &roots, &setup.root(), &openings),
            Ok(())
        );
        let opened = format!("{:?}", (&openings.witness, &openings.quotient, &openings.setup)).into_bytes();
        match &first {
            None => {
                println!("pi2 stream keccak {}", hex(&primitives::hash::hash(&stream)));
                println!("pi2 openings keccak {}", hex(&primitives::hash::hash(&opened)));
                first = Some((stream, opened));
            }
            Some((s, o2)) => assert!(s == &stream && o2 == &opened, "the proof is the first pass's"),
        }
        if pass > 0 {
            proving.push(p);
            opening.push(o);
        }
    }
    println!(
        "median of {repeat}: prove {:.3} s, open {:.3} s; peak RSS {:.2} GB",
        median(&proving),
        median(&opening),
        bench::peak_rss_bytes() as f64 / 1e9
    );
}
