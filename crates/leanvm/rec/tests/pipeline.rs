// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The recursion end to end, from a Keccak VM trace (leanVM 9d50c92a3, `crates/leanvm/univariate/src/prover/
//! dump_keccak`) to π2's proof and openings, timed: π1-rec3's proof (with its three openings), π2's witness (replayed
//! on π1's stream from the circuit's witness plan, `circuit::plan`), π2's proof and its three openings.
//!
//! What depends on the program and the shape only is computed once, before the timed passes, and reported apart (the
//! per-circuit setup): π1's setup root (its `F`), π1's recorded verifier, π2's circuit (adapted) and its witness plan,
//! its spec, its setup commitment (`σ`, `κ`) and its IV. The first pass checks (outside the timing) that the replayed
//! witness and public inputs are those of the circuit compiled on its stream (`circuit::compile::pi2`), and that
//! circuit the cached one; each pass, that π2's openings verify and that its proofs are the first pass's.
//!
//! `LEANVM_TRACE=<dir of one trace> cargo test --release -p leanvm_rec --test pipeline -- --ignored --nocapture`
//! (`PIPELINE_REPEAT`, default 3; `PIPELINE_COOLDOWN`, default 2 s).

#[global_allocator]
static ALLOC: bench::Jemalloc = bench::Jemalloc;

use std::time::Instant;

#[path = "../../univariate/tests/vectors/mod.rs"]
mod vectors;

use leanvm_rec::circuit::compile::{Inputs, Layout, pi2};
use leanvm_rec::circuit::plan::WitnessPlan;
use leanvm_rec::pi2::adapt;
use leanvm_rec::pi2::prover::{self, Setup, open, prove, verify_openings};
use leanvm_rec::pi2::verifier::Spec;
use leanvm_statement::shapes::PROGRAM_IV;
use leanvm_univariate::prover::prove::{Config, prove as prove_pi1, prove_streaming};
use leanvm_univariate::prover::trace::Trace;
use leanvm_univariate::{Claims, KECCAK_REC3};

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

fn median(x: &[f64]) -> f64 {
    let mut x = x.to_vec();
    x.sort_by(f64::total_cmp);
    x[x.len() / 2]
}

#[test]
#[ignore]
fn trace_to_recursion() {
    let Some(dir) = std::env::var_os("LEANVM_TRACE") else {
        println!("LEANVM_TRACE is not set: nothing to prove");
        return;
    };
    deep(move || {
        let repeat: usize = std::env::var("PIPELINE_REPEAT").ok().map_or(3, |x| x.parse().expect("a count"));
        let cooldown: u64 = std::env::var("PIPELINE_COOLDOWN").ok().map_or(2, |x| x.parse().expect("seconds"));
        parallel::init();

        // The per-circuit setup.
        let started = Instant::now();
        let mut trace = Trace::load(std::path::Path::new(&dir)).expect("a trace");
        trace.place();
        let loaded = started.elapsed().as_secs_f64();
        let started = Instant::now();
        let shape = trace.shape();
        let roots = leanvm_univariate::prover::setup::shape_roots(
            &shape,
            &leanvm_univariate::prover::columns::setup_polys(&trace),
        );
        let config = Config {
            variant: KECCAK_REC3,
            claims: Claims::Point,
            check: false,
            garbage: false,
            stand_in_roots: None,
            roots,
        };
        let recorded = leanvm_univariate::contract::record_verifier_with(&shape, KECCAK_REC3, Claims::Point, &roots);
        let pi1_setup = started.elapsed().as_secs_f64();
        let public = trace.public_input();
        // π2's circuit and its witness plan depend on π1's verifier only; a stream gives the compiler its values (any
        // proof's: the first).
        let (pi1_proof, _) = prove_pi1(&trace, trace.keccak_flock(), &PROGRAM_IV, config).expect("π1's proof");
        let started = Instant::now();
        let (compiled, plan) = WitnessPlan::compile(
            &recorded,
            Layout::D16v,
            &Inputs {
                program_iv: PROGRAM_IV,
                public,
                stream: &pi1_proof.stream,
            },
        );
        let planned = started.elapsed().as_secs_f64();
        let circuit = adapt::adapt(&compiled.finished.circuit);
        let spec = Spec::of(&circuit);
        let setup = Setup::new(&circuit);
        let digest = circuit.digest();
        let iv = prover::iv(&compiled.pi1_iv, &digest, &setup.root(), circuit.log_n);
        let pi2_setup = started.elapsed().as_secs_f64();
        drop((compiled, pi1_proof));
        println!(
            "{}: loaded and placed in {loaded:.2} s; per circuit: π1's setup root and recorded verifier {pi1_setup:.2} s, π2's circuit, witness plan, spec, setup commitment and IV {pi2_setup:.2} s (circuit and plan {planned:.2} s)",
            std::path::Path::new(&dir).display()
        );

        let mut phases: Vec<(&str, Vec<f64>)> = Vec::new();
        let mut first: Option<(Vec<u8>, Vec<u8>, Vec<u8>)> = None;
        for pass in 0..=repeat {
            std::thread::sleep(std::time::Duration::from_secs(cooldown));
            let mut laps: Vec<(&str, f64)> = Vec::new();
            let started = Instant::now();
            let mut clock = Instant::now();
            let mut lap = |name, laps: &mut Vec<(&str, f64)>| {
                laps.push((name, clock.elapsed().as_secs_f64()));
                clock = Instant::now();
            };
            // π2's witness is replayed on π1's stream while π1's openings run (`prove_streaming`).
            let (stream_tx, stream_rx) = std::sync::mpsc::channel::<Vec<u8>>();
            let plan = &plan;
            let (pi1_proof, ((witness, public2), replaying)) = std::thread::scope(|s| {
                let replayer = s.spawn(move || {
                    let stream = stream_rx.recv().expect("π1's stream");
                    let started = Instant::now();
                    let replayed = adapt::replay(
                        plan,
                        &Inputs {
                            program_iv: PROGRAM_IV,
                            public,
                            stream: &stream,
                        },
                    );
                    (replayed, started.elapsed().as_secs_f64())
                });
                let (proof, _) = prove_streaming(&trace, trace.keccak_flock(), &PROGRAM_IV, config, |stream| {
                    stream_tx.send(stream.to_vec()).expect("the replay waits")
                })
                .expect("π1's proof");
                (proof, replayer.join().expect("no panic"))
            });
            lap(
                "π1-rec3: proof and openings, with π2's witness replayed meanwhile",
                &mut laps,
            );
            let (public_input, values) = adapt::public_values(&public2);
            lap("π2: the rest of its witness", &mut laps);
            let proved = prove(&circuit, &spec, &setup, &iv, &public_input, &values, &witness);
            lap("π2: proof", &mut laps);
            let stream = proved.stream.clone();
            let (reduced, roots2, openings) = open(proved, &setup);
            lap("π2: openings", &mut laps);
            laps.push(("total", started.elapsed().as_secs_f64()));
            laps.push(("(π2's witness replay, overlapped with π1's openings)", replaying));

            // Outside the timing: the first pass's witness and public inputs are the compiler's on its stream, and its
            // circuit the cached one; π2's openings verify; the proofs are the first's.
            if pass == 0 {
                let compiled = pi2(
                    &recorded,
                    Layout::D16v,
                    &Inputs {
                        program_iv: PROGRAM_IV,
                        public,
                        stream: &pi1_proof.stream,
                    },
                );
                assert!(
                    adapt::adapt(&compiled.finished.circuit).digest() == digest,
                    "the circuit is the cached one"
                );
                assert!(
                    witness == adapt::witness(&compiled.finished.witness) && public2 == compiled.public,
                    "the replayed witness is the compiler's"
                );
            }
            assert_eq!(
                verify_openings(circuit.log_n, &reduced, &roots2, &setup.root(), &openings),
                Ok(())
            );
            let opened = format!("{:?}", (&openings.witness, &openings.quotient, &openings.setup)).into_bytes();
            match &first {
                None => first = Some((pi1_proof.stream.clone(), stream, opened)),
                Some((s1, s2, o2)) => {
                    assert_eq!(s1, &pi1_proof.stream, "π1's proof is the first pass's");
                    assert!(s2 == &stream && o2 == &opened, "π2's proof is the first pass's");
                }
            }
            drop((pi1_proof, witness));
            if pass == 0 {
                continue;
            }
            for (k, (name, secs)) in laps.into_iter().enumerate() {
                if phases.len() <= k {
                    phases.push((name, Vec::new()));
                }
                phases[k].1.push(secs);
            }
        }
        println!("{repeat} warm passes ({cooldown} s cooldown), medians:");
        for (name, secs) in &phases {
            println!(
                "  {:7.3} s  {name}   (passes {:?})",
                median(secs),
                secs.iter().map(|t| format!("{t:.3}")).collect::<Vec<_>>()
            );
        }
        // The proofs' fingerprints: at the reference trace, π1's stream is the committed vector's
        // (`keccak128_rec3.txt`) and π2's lines are `tests/pi2_real.rs`'s.
        let (s1, s2, o2) = first.expect("a pass");
        let reference = vectors::read(
            &std::fs::read_to_string(format!(
                "{}/../univariate/tests/vectors/keccak128_rec3.txt",
                env!("CARGO_MANIFEST_DIR")
            ))
            .expect("the committed vector"),
        );
        if reference.shape == shape && reference.public == public {
            assert_eq!(reference.calldata[4 + 32..], s1[..], "π1's stream is the committed vector's");
            println!("π1's stream is the committed vector keccak128_rec3's");
        }
        let hex = |b: &[u8]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
        println!("pi1 stream keccak {}", hex(&primitives::hash::hash(&s1)));
        println!("pi2 stream keccak {}", hex(&primitives::hash::hash(&s2)));
        println!("pi2 openings keccak {}", hex(&primitives::hash::hash(&o2)));
        println!("peak RSS {:.2} GB", bench::peak_rss_bytes() as f64 / 1e9);
    });
}
