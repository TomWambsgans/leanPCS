// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! π2's witness replayed from its plan (`circuit::plan::WitnessPlan`) is the compiler's (`circuit::compile::pi2`),
//! word for word, with the same public inputs: on the committed real π1-rec3 proofs
//! (`crates/leanvm/univariate/tests/vectors/keccak128_rec3.txt`, the reference shape, and `keccak_rec3.txt`, 400
//! signatures: another shape, another circuit), the plan made on a sample stream.
//!
//! `cargo test --release -p leanvm_rec --test witness_plan` (`-- --ignored --nocapture` for `replay_timing`).

#[global_allocator]
static ALLOC: bench::Jemalloc = bench::Jemalloc;

#[path = "../../univariate/tests/vectors/mod.rs"]
mod vectors;

use std::time::Instant;

use leanvm_rec::circuit::compile::{Inputs, pi2};
use leanvm_rec::circuit::plan::WitnessPlan;
use leanvm_rec::pi2::adapt;
use leanvm_rec::pi2::contract::sample_stream;
use leanvm_statement::shapes::PROGRAM_IV;
use leanvm_univariate::contract::Recorded;

/// A committed vector's recorded verifier (π1's contract binds its setup root `F`), public input and stream.
fn real(name: &str) -> (Recorded, [u8; 32], Vec<u8>) {
    let v = vectors::committed(name);
    let roots = vectors::setup_roots(&v);
    let recorded = leanvm_univariate::contract::record_verifier_with(
        &v.shape,
        vectors::variant_of(&v.config),
        &roots,
    );
    (recorded, v.public, v.calldata[vectors::PI1_STREAM_AT..].to_vec())
}

/// The plan's replay on `inputs` is the compiler's witness and public inputs.
fn check(plan: &WitnessPlan, recorded: &Recorded, inputs: &Inputs) {
    let compiled = pi2(recorded, inputs);
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
    vectors::deep(|| {
        for name in [leanvm_rec::PI1_VECTOR_128, leanvm_rec::PI1_VECTOR_400] {
            let (recorded, public, stream) = real(name);
            // The plan of a compilation on a sample stream (which `WitnessPlan::compile` checks it replays), then
            // replayed on the real proof's.
            let sample = sample_stream(stream.len(), 7);
            let sample = Inputs {
                program_iv: PROGRAM_IV,
                public: [3; 32],
                stream: &sample,
            };
            let (_, plan) = WitnessPlan::compile(&recorded, &sample);
            // Keccak-f whole, and with the last round's planes of the lanes read: a digest's (1), a wide draw's (3, 4).
            assert_eq!(plan.templates(), 4, "four Keccak-f templates");
            let inputs = Inputs {
                program_iv: PROGRAM_IV,
                public,
                stream: &stream,
            };
            check(&plan, &recorded, &inputs);
        }
    });
}

/// The compiler's time and the replay's on the reference vector, D16v.
#[test]
#[ignore]
fn replay_timing() {
    vectors::deep(|| {
        parallel::init();
        let (recorded, public, stream) = real(leanvm_rec::PI1_VECTOR_128);
        let inputs = Inputs {
            program_iv: PROGRAM_IV,
            public,
            stream: &stream,
        };
        let started = Instant::now();
        let (compiled, plan) = WitnessPlan::compile(&recorded, &inputs);
        println!("compile and plan: {:.3} s", started.elapsed().as_secs_f64());
        let reference = adapt::witness(&compiled.finished.witness);
        drop(compiled);
        let repeat: usize = std::env::var("REPEAT").map_or(10, |x| x.parse().expect("a count"));
        for _ in 0..3 {
            let started = Instant::now();
            let compiled = pi2(&recorded, &inputs);
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
