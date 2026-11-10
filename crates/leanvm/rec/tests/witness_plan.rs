// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! π2's witness replayed from its plan (`circuit::plan::WitnessPlan`) is the compiler's (`circuit::compile::pi2`),
//! word for word, with the same public inputs: on the committed real π1-rec3 proofs
//! (`crates/leanvm/univariate/tests/vectors/keccak128_rec3.txt`, the reference shape, and `keccak_rec3.txt`, 400
//! signatures: another shape, another circuit) and on a sample stream, the plan made on a zero stream.
//!
//! `cargo test --release -p leanvm_rec --test witness_plan` (`-- --ignored --nocapture` for `replay_timing`).

#[global_allocator]
static ALLOC: bench::Jemalloc = bench::Jemalloc;

#[path = "../../univariate/tests/vectors/mod.rs"]
mod vectors;

use std::time::Instant;

use leanvm_rec::circuit::compile::{Inputs, Layout, pi2};
use leanvm_rec::circuit::plan::WitnessPlan;
use leanvm_rec::pi2::adapt;
use leanvm_rec::pi2::contract::sample_stream;
use leanvm_statement::shapes::PROGRAM_IV;
use leanvm_univariate::Claims;
use leanvm_univariate::contract::Recorded;

const STREAM_AT: usize = 4 + 32;

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

/// A committed vector's recorded verifier (π1's contract binds its setup root `F`), public input and stream.
fn real(name: &str) -> (Recorded, [u8; 32], Vec<u8>) {
    let path = format!("{}/../univariate/tests/vectors/{name}.txt", env!("CARGO_MANIFEST_DIR"));
    let v = vectors::read(&std::fs::read_to_string(&path).expect("a committed vector"));
    let roots = vectors::setup_roots(&v);
    let recorded = leanvm_univariate::contract::record_verifier_with(
        &v.shape,
        vectors::variant_of(&v.config),
        Claims::Point,
        &roots,
    );
    (recorded, v.public, v.calldata[STREAM_AT..].to_vec())
}

/// The plan's replay on `inputs` is the compiler's witness and public inputs.
fn check(plan: &WitnessPlan, recorded: &Recorded, layout: Layout, inputs: &Inputs) {
    let compiled = pi2(recorded, layout, inputs);
    let (witness, public) = plan.witness(inputs);
    assert!(public == compiled.public, "the public inputs are the compiler's");
    assert_eq!(witness.len(), compiled.finished.witness.len());
    let differ = witness
        .iter()
        .zip(&compiled.finished.witness)
        .filter(|(a, b)| a != b)
        .count();
    assert_eq!(differ, 0, "the witness is the compiler's");
    let (prover_witness, prover_public) = adapt::replay(plan, inputs);
    assert!(
        prover_witness == adapt::witness(&compiled.finished.witness),
        "the prover's witness is the adapted one"
    );
    assert!(prover_public == compiled.public);
}

#[test]
fn replay_is_the_compilers_d16v() {
    deep(|| {
        for name in ["keccak128_rec3", "keccak_rec3"] {
            let (recorded, public, stream) = real(name);
            let plan = WitnessPlan::new(&recorded, Layout::D16v, PROGRAM_IV);
            assert_eq!(plan.templates(), 1, "one Keccak-f template");
            let sample = sample_stream(stream.len(), 7);
            for (public, stream) in [(public, &stream), ([3; 32], &sample)] {
                let inputs = Inputs {
                    program_iv: PROGRAM_IV,
                    public,
                    stream,
                };
                check(&plan, &recorded, Layout::D16v, &inputs);
            }
        }
    });
}

/// The compiler's time and the replay's on the reference vector, D16v.
#[test]
#[ignore]
fn replay_timing() {
    deep(|| {
        parallel::init();
        let (recorded, public, stream) = real("keccak128_rec3");
        let inputs = Inputs {
            program_iv: PROGRAM_IV,
            public,
            stream: &stream,
        };
        let started = Instant::now();
        let (compiled, plan) = WitnessPlan::compile(&recorded, Layout::D16v, &inputs);
        println!("compile and plan: {:.3} s", started.elapsed().as_secs_f64());
        let reference = adapt::witness(&compiled.finished.witness);
        drop(compiled);
        let repeat: usize = std::env::var("REPEAT").map_or(10, |x| x.parse().expect("a count"));
        for _ in 0..3 {
            let started = Instant::now();
            let compiled = pi2(&recorded, Layout::D16v, &inputs);
            let witness = adapt::witness(&compiled.finished.witness);
            println!("compile + adapt: {:.4} s", started.elapsed().as_secs_f64());
            assert!(witness == reference);
        }
        let mut times = Vec::new();
        for _ in 0..repeat {
            let started = Instant::now();
            let (witness, _) = adapt::replay(&plan, &inputs);
            times.push(started.elapsed().as_secs_f64());
            assert!(witness == reference);
        }
        times.sort_by(f64::total_cmp);
        println!("replay: median {:.4} s, min {:.4} s", times[times.len() / 2], times[0]);
    });
}
