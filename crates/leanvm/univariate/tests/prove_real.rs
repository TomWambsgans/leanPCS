// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The prover on real Keccak VM traces (leanVM 9d50c92a3, written by `src/prover/dump_keccak`; KECCAK.md): SPEC.md's
//! identities on the domain, the quotients' degrees, every combined relation at `t`, the Rust verifier's and the EVM
//! contract's acceptance of the proof (the claims the contract checks declared being exactly those the WHIR openings
//! prove), and the rejection of mutated proofs.
//!
//! `LEANVM_TRACE=<dir of one trace>` (the directory `trace_dump.rs` wrote), then, built with
//! `RUSTFLAGS="-C target-cpu=native"` as leanVM is,
//! `cargo test --release -p leanvm_univariate --test prove_real -- --ignored --nocapture --test-threads 1`.
//! `WRITE_VECTORS=<dir>` writes the proof's Rust→EVM vector (`tests/vectors/`) to `<dir>/<config>.txt`, or to
//! `<dir>/<VECTOR_FILE>.txt`.

use leanvm_statement::evm::codegen::word;
use leanvm_statement::evm::machine::{PcsFrame, call};
use leanvm_statement::shapes::PROGRAM_IV;
use leanvm_univariate::claims::Commitment;
use leanvm_univariate::contract::{SetupRoots, calldata, compile_verifier, record_verifier_with};
use leanvm_univariate::prover::check::on_domain;
use leanvm_univariate::prover::prove::{Config, OpeningProof, Proof, prove, verify};
use leanvm_univariate::prover::trace::Trace;
use leanvm_univariate::{Claims, KECCAK_MAIN, KECCAK_REC3, KECCAK_REC4, Variant};
use primitives::field::F192;

fn dir() -> Option<std::path::PathBuf> {
    std::env::var("LEANVM_TRACE").ok().map(std::path::PathBuf::from)
}

/// The trace, its rows placed at the verifier's positions (`Trace::place`), and the placement's time.
fn trace() -> Option<(Trace, f64)> {
    let dir = dir()?;
    let started = std::time::Instant::now();
    let mut trace = Trace::load(&dir).expect("a trace");
    let loaded = started.elapsed().as_secs_f64();
    let started = std::time::Instant::now();
    parallel::init();
    trace.place();
    let placed = started.elapsed().as_secs_f64();
    println!(
        "trace {}: loaded in {loaded:.2} s, placed in {placed:.2} s, rows {:?}, heights {:?}, memory 2^{}, bytecode 2^{}",
        dir.display(),
        trace.rows,
        trace.heights,
        trace.log_memory,
        trace.log_bytecode
    );
    Some((trace, placed))
}

mod vectors;
use vectors::name_of as vector_name;

/// The allocator leanVM's own CLI and benches run on (jemalloc, freed pages kept: `bench::Jemalloc`), so that the
/// prover is measured as leanVM's is; on glibc's every large buffer faults its pages in again.
#[global_allocator]
static ALLOCATOR: bench::Jemalloc = bench::Jemalloc;

/// The root of the trace's contract: its program's and shape's `F`.
fn contract_roots(trace: &Trace) -> SetupRoots {
    leanvm_univariate::prover::setup::shape_roots(&trace.shape(), &leanvm_univariate::prover::columns::setup_polys(trace))
}

/// Run `f` on a thread with a deep stack: the code generator recurses along the graph.
fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

fn copy(proof: &Proof, stream: Vec<u8>) -> Proof {
    Proof {
        stream,
        openings: proof
            .openings
            .iter()
            .map(|o| OpeningProof {
                commitment: o.commitment,
                root: o.root,
                ood: o.ood,
                vars: o.vars,
                point: o.point.clone(),
                value: o.value,
                proof: o.proof.clone(),
            })
            .collect(),
    }
}

#[test]
#[ignore]
fn identities_hold_on_the_domain() {
    let Some((mut trace, _)) = trace() else {
        println!("LEANVM_TRACE is not set: nothing to check");
        return;
    };
    // q_flock: one Keccak-f block a SHA3 row.
    trace.qflock = trace.keccak_flock().z.into_iter().map(primitives::field::F64).collect();
    let alphas = [F192::new(3, 1, 4), F192::new(1, 5, 9), F192::new(2, 6, 5), F192::new(3, 5, 8)];
    let checks = on_domain(&trace, &alphas, F192::new(9, 7, 9));
    let mut failed = false;
    for c in &checks {
        println!("{:>9} / {:>9} fail: {}", c.failures, c.tested, c.name);
        failed |= c.failures > 0 && !c.name.contains("informative");
    }
    assert!(!failed, "an identity fails on the domain");
}

/// Prove, verify (Rust and EVM), mutate.
fn end_to_end(variant: Variant) {
    let Some((trace, mut placing)) = trace() else {
        println!("LEANVM_TRACE is not set: nothing to prove");
        return;
    };
    // q_flock and Flock's witness built from the placed SHA3 rows, one Keccak-f block a row.
    let flock = {
        let started = std::time::Instant::now();
        let witness = trace.keccak_flock();
        println!("  {:8.3} s  the Keccak-f blocks: q_flock and Flock's witness", started.elapsed().as_secs_f64());
        placing += started.elapsed().as_secs_f64();
        witness
    };
    let roots = contract_roots(&trace);
    let config = Config {
        variant,
        claims: Claims::Point,
        check: true,
        garbage: false,
        roots,
    };
    let _ = leanvm_univariate::prover::prove::MEMORY_PROBE.set(bench::peak_rss_bytes);
    let started = std::time::Instant::now();
    let (proof, report) = prove(&trace, flock, &PROGRAM_IV, config).expect("a proof");
    let total = started.elapsed().as_secs_f64();
    println!("  {placing:8.3} s  placement: the rows at the verifier's positions, and Flock's witness");
    for (k, (phase, secs)) in report.phases.iter().enumerate() {
        match report.peaks.get(k) {
            Some((_, peak)) => println!("  {secs:8.3} s  {phase} (peak RSS so far {:.2} GB)", *peak as f64 / 1e9),
            None => println!("  {secs:8.3} s  {phase}"),
        }
    }
    for note in &report.notes {
        println!("  note: {note}");
    }
    println!(
        "  {:8.3} s  total ({total:.3} s and the placement); peak RSS {:.2} GB",
        total + placing,
        bench::peak_rss_bytes() as f64 / 1e9
    );
    for (name, degree, count, m) in &report.quotients {
        println!(
            "  quotient {name}: degree {degree}, the verifier's count {count} (2^{:.3}), extension 2^{m}",
            (*count as f64).log2()
        );
    }
    for (c, placed, vars) in &report.stacks {
        println!("  stack {c:?}: {placed} words placed (2^{:.3}), 2^{vars}", (*placed as f64).log2());
    }
    for (name, ok) in &report.checks {
        println!("  check {}: {name}", if *ok { "ok  " } else { "FAIL" });
    }
    println!("  stream {} bytes; openings {:?} bytes", report.stream_bytes, report.opening_bytes);
    // The proof's fingerprint: a change of the prover that keeps the proof keeps this line.
    println!(
        "  stream keccak {}",
        leanvm_univariate::prover::setup::hex(&leanvm_statement::transcript::keccak256(&proof.stream))
    );
    // The openings' fingerprint (their Debug form: the WHIR streams and Merkle paths), for prover changes that must
    // keep the proof byte for byte.
    println!(
        "  openings keccak {}",
        leanvm_univariate::prover::setup::hex(&leanvm_statement::transcript::keccak256(
            format!("{:?}", proof.openings.iter().map(|o| (&o.root, &o.proof)).collect::<Vec<_>>()).as_bytes()
        ))
    );
    assert!(report.checks.iter().all(|(_, ok)| *ok));
    let shape = trace.shape();
    let public = trace.public_input();
    let started = std::time::Instant::now();
    verify(&shape, &PROGRAM_IV, &roots, &public, &proof, variant).expect("the verifier accepts");
    println!(
        "  verified (reduce + 3 WHIR openings) in {:.3} s; the contract binds F {}",
        started.elapsed().as_secs_f64(),
        leanvm_univariate::prover::setup::hex(&roots.f)
    );
    // The claims the openings prove, from the prover's output: each WHIR opening's first two scalars are its
    // commitment's root's (`hash_to_scalars`), and the stream carries C1's and C2's roots as they are, each followed by
    // its out-of-domain answer, so that the contract passes them as the claims encode them.
    let order: Vec<Commitment> = proof.openings.iter().map(|o| o.commitment).collect();
    assert_eq!(order, [Commitment::C1, Commitment::C2, Commitment::Setup], "the claims' order");
    for o in &proof.openings {
        let scalars = fiat_shamir::merkle::hash_to_scalars(&o.root);
        assert_eq!(o.proof.stream[..2], scalars, "{:?}: the WHIR opening's first two scalars are its root's", o.commitment);
    }
    // After the six row counts: C1's root, then its out-of-domain answer.
    let c1 = &proof.openings[0];
    assert_eq!(proof.stream[24..56], c1.root, "C1's root in the stream");
    assert_eq!(proof.stream[56..80], pcs_claim::element_bytes(c1.ood), "C1's out-of-domain answer in the stream");
    assert_eq!(proof.openings[2].root, roots.f, "the setup claim's root is the contract's F");
    let inputs: Vec<Vec<u8>> = proof.openings.iter().map(|o| o.claim().encode()).collect();
    let data = calldata(&public, &proof.stream);
    let stream = proof.stream.clone();
    // π1-rec4 has no contract (its wide draws are no `KECCAK256`): the Rust verifier's claims are the openings'.
    let wide = variant.fs.wide();
    if wide {
        let (reduced, zero, nonzero) = leanvm_univariate::contract::rust_verifier_with(
            &shape,
            &PROGRAM_IV,
            &roots,
            &public,
            &stream,
            variant,
            Claims::Point,
        )
        .expect("the Rust verifier accepts");
        assert!(zero.iter().all(|x| *x == Default::default()) && nonzero.iter().all(|x| *x != Default::default()));
        let recorded = deep(move || record_verifier_with(&shape, variant, Claims::Point, &roots));
        let claims: Vec<Vec<u8>> = leanvm_univariate::contract::expected_claims(&recorded, &reduced, &proof.stream)
            .iter()
            .map(|c| c.encode())
            .collect();
        assert_eq!(claims, inputs, "the Rust verifier's claims are the openings'");
        println!("  π1-rec4: no contract; the Rust verifier's claims are the openings'");
    }
    let (accepted, rejected, gas, calls) = if wide {
        (Some(word([1, 0, 0]).to_vec()), 0, 0, inputs.clone())
    } else {
        deep(move || {
        let recorded = record_verifier_with(&shape, variant, Claims::Point, &roots);
        assert_eq!(recorded.stream_len, stream.len(), "the contract's stream is the proof's");
        // The measuring build, word for word against the Rust verifier, on this accepting stream.
        leanvm_univariate::contract::parity_with(&shape, &PROGRAM_IV, &roots, &public, &stream, variant, Claims::Point);
        let contract = compile_verifier(&recorded, &PROGRAM_IV, false);
        // The claims the contract checks, its frame declaring those the openings prove, are those.
        let calls = call(&contract.code, &[], &data, &PcsFrame::of(inputs.iter().cloned())).claims;
        assert_eq!(calls.len(), inputs.len(), "one claim per opening");
        for (k, (made, proven)) in calls.iter().zip(&inputs).enumerate() {
            assert_eq!(made, proven, "call {k}: the opening's claim");
        }
        let attesting = |skip: Option<usize>| {
            let mut pcs = PcsFrame::default();
            for (k, input) in calls.iter().enumerate() {
                if Some(k) != skip {
                    pcs.declare(input.clone());
                }
            }
            pcs
        };
        let blocks: Vec<PcsFrame> = std::iter::once(attesting(None)).chain((0..calls.len()).map(|k| attesting(Some(k)))).collect();
        let accepts = |data: &[u8], block: &PcsFrame| call(&contract.code, &[], data, block).attests();
        let ok = call(&contract.code, &[], &data, &blocks[0]);
        let mut bad = data.clone();
        // The stream's last byte, before the frame's.
        let last = bad.len() - 2;
        bad[last] ^= 1;
        let mut rejected = accepts(&bad, &blocks[0]) as usize;
        // Every claim must be declared.
        rejected += blocks[1..].iter().filter(|b| accepts(&data, b)).count();
        (ok.output.clone(), rejected, ok.execution, calls)
    })
    };
    if wide {
        println!("  π1-rec4 has no contract: checked against the Rust verifier (its claims, the openings' above)");
    } else {
        println!(
            "  the contract returns {:?} on the real proof, {gas} gas of execution; parity with the Rust verifier",
            accepted.as_ref().map(|o| o[31]),
        );
        assert_eq!(accepted.as_deref(), Some(&word([1, 0, 0])[..]), "the contract accepts the real proof");
    }
    // The Rust→EVM test vector (tests/vectors/): the proof's calldata, the claims declared, the verdict and the gas.
    if let Ok(out) = std::env::var("WRITE_VECTORS") {
        let name = vector_name(variant);
        let text = vectors::write(&vectors::Vector {
            config: name.to_string(),
            shape,
            public,
            calldata: [&vectors::SELECTOR[..], &public, &proof.stream].concat(),
            claims: calls.clone(),
            accepts: true,
            gas_straight: gas,
            note: format!(
                "the Keccak VM (leanVM 9d50c92a3, KECCAK.md), its run without the fill blocks: rows {:?}",
                trace.rows
            ),
        });
        let file = std::env::var("VECTOR_FILE").unwrap_or_else(|_| name.to_string());
        // `cargo test` runs in the crate's directory: a relative WRITE_VECTORS is relative to it.
        let dir = std::path::Path::new(&out);
        std::fs::create_dir_all(dir).unwrap_or_else(|e| panic!("WRITE_VECTORS={}: cannot create it: {e}", dir.display()));
        let path = dir.join(format!("{file}.txt"));
        std::fs::write(&path, text).unwrap_or_else(|e| panic!("the vector file {}: {e}", path.display()));
        println!("  test vector written to {}", path.display());
    }
    assert_eq!(rejected, 0, "the contract rejects a mutated proof, and a proof with one call not attested");

    // Mutations: a root, a value early on, the middle, a final value, a sumcheck round.
    let mut refused = 0;
    let len = proof.stream.len();
    for &at in &[0usize, 40, len / 2, len - 30, len - 100] {
        let mut bad = proof.stream.clone();
        bad[at] ^= 1;
        let verdict = verify(&trace.shape(), &PROGRAM_IV, &roots, &public, &copy(&proof, bad), variant);
        println!(
            "  stream byte {at} flipped: {}",
            verdict.as_ref().err().map_or("ACCEPTED".to_string(), |e| e.clone())
        );
        refused += verdict.is_err() as usize;
    }
    assert_eq!(refused, 5, "every mutation is rejected");
}

/// The Keccak VM (KECCAK.md): leanVM 9d50c92a3's `SHA3` table, Flock on the Keccak-f block at a skip of 3, the
/// structured lincheck terminal, three claims (`KECCAK_MAIN`). On a trace `dump_keccak` wrote.
#[test]
#[ignore]
fn proves_and_verifies_keccak() {
    end_to_end(KECCAK_MAIN);
}

/// The Keccak VM's π1-rec3, the recursion's inner proof (`crates/leanvm/rec`): `KECCAK_MAIN` with π1-rec3's Fiat–Shamir
/// shape (`FsShape::Rec3`: α and the zerocheck's eq point as squares, the batch two variables a round).
#[test]
#[ignore]
fn proves_and_verifies_keccak_rec3() {
    end_to_end(KECCAK_REC3);
}

/// The Keccak VM's π1-rec4, the recursion's inner proof (`docs/leanvm/univariate/SPEC.md` §14.4): π1-rec3 with the
/// challenges no message separates drawn from one Keccak-f each (`FsShape::Rec4`). It has no contract: the Rust
/// verifier's claims are checked against the openings'.
#[test]
#[ignore]
fn proves_and_verifies_keccak_rec4() {
    end_to_end(KECCAK_REC4);
}

/// The setup commitment a contract for this trace's program and shape is generated with (SPEC.md §13, F2): `F`'s root
/// and out-of-domain answer, from the program and the shape (at the reference trace, `SetupRoots::REFERENCE`).
#[test]
#[ignore]
fn setup_roots() {
    let Some((trace, _)) = trace() else {
        println!("LEANVM_TRACE is not set: no program");
        return;
    };
    let started = std::time::Instant::now();
    let setup = leanvm_univariate::prover::columns::setup_polys(&trace);
    let f = leanvm_univariate::prover::setup::shape_roots(&trace.shape(), &setup);
    println!("  shape {:?}", trace.shape());
    println!("  F  {}", leanvm_univariate::prover::setup::hex(&f.f));
    println!("  F's out-of-domain answer, limbs {:#018x} {:#018x} {:#018x}", f.f_ood.c0, f.f_ood.c1, f.f_ood.c2);
    if trace.shape() == leanvm_univariate::Shape::of(&leanvm_statement::shapes::reference().shape) {
        assert_eq!(f, leanvm_univariate::contract::SetupRoots::REFERENCE, "the reference shape's F");
    }
    println!("  in {:.2} s", started.elapsed().as_secs_f64());
}

/// The prover's timings, warm, as leanVM's own benchmark measures it (a warm-up pass, then `PI1_REPEAT` passes, 3 by
/// default, each after `PI1_COOLDOWN` idle seconds, 2 by default, as leanVM's `--cooldown`; the median of each phase): the Keccak VM's main line (`PI1_VARIANT=rec3`: π1-rec3) on a `dump_keccak`
/// trace, from the placed trace to the openings, the Keccak-f blocks' witness included, no test checks. Each pass's
/// proof is checked to be the first's, byte for byte.
#[test]
#[ignore]
fn keccak_prover_benchmark() {
    let Some((trace, _)) = trace() else {
        println!("LEANVM_TRACE is not set: nothing to prove");
        return;
    };
    let variant = match std::env::var("PI1_VARIANT").as_deref() {
        Ok("rec3") => KECCAK_REC3,
        Ok("rec4") => KECCAK_REC4,
        _ => KECCAK_MAIN,
    };
    let repeat: usize = std::env::var("PI1_REPEAT").ok().map_or(3, |x| x.parse().expect("a count"));
    let cooldown: u64 = std::env::var("PI1_COOLDOWN").ok().map_or(2, |x| x.parse().expect("seconds"));
    let config = Config {
        variant,
        claims: Claims::Point,
        check: false,
        garbage: false,
        roots: contract_roots(&trace),
    };
    let mut phases: Vec<(String, Vec<f64>)> = Vec::new();
    let mut totals = Vec::new();
    let mut first: Option<Vec<u8>> = None;
    for pass in 0..=repeat {
        if pass > 0 {
            std::thread::sleep(std::time::Duration::from_secs(cooldown));
        }
        let started = std::time::Instant::now();
        let witness = trace.keccak_flock();
        let blocks = started.elapsed().as_secs_f64();
        let (proof, report) = prove(&trace, witness, &PROGRAM_IV, config).expect("a proof");
        let total = started.elapsed().as_secs_f64();
        match &first {
            None => first = Some(proof.stream.clone()),
            Some(stream) => assert_eq!(stream, &proof.stream, "the same proof every pass"),
        }
        if pass == 0 {
            continue;
        }
        totals.push(total);
        let all = std::iter::once(("the Keccak-f blocks: q_flock and Flock's witness", blocks)).chain(report.phases.iter().copied());
        for (k, (name, secs)) in all.enumerate() {
            if phases.len() <= k {
                phases.push((name.to_string(), Vec::new()));
            }
            phases[k].1.push(secs);
        }
    }
    let median = |x: &[f64]| {
        let mut x = x.to_vec();
        x.sort_by(f64::total_cmp);
        x[x.len() / 2]
    };
    println!("{variant:?}, rows {:?}: {repeat} warm passes, medians", trace.rows);
    for (name, secs) in &phases {
        println!("  {:8.3} s  {name}", median(secs));
    }
    println!(
        "  {:8.3} s  total (passes {:?}); peak RSS {:.2} GB",
        median(&totals),
        totals.iter().map(|t| format!("{t:.3}")).collect::<Vec<_>>(),
        bench::peak_rss_bytes() as f64 / 1e9
    );
}

/// The verifier relies on nothing in the stacks' words past their blocks: filled with pseudo-random words, the
/// proof is accepted all the same.
#[test]
#[ignore]
fn unused_words_are_not_relied_on() {
    let Some((trace, _)) = trace() else {
        println!("LEANVM_TRACE is not set: nothing to prove");
        return;
    };
    let config = Config {
        variant: KECCAK_MAIN,
        claims: Claims::Point,
        check: true,
        garbage: true,
        roots: contract_roots(&trace),
    };
    let witness = trace.keccak_flock();
    let (proof, report) = prove(&trace, witness, &PROGRAM_IV, config).expect("a proof");
    for (c, placed, vars) in &report.stacks {
        println!("  stack {c:?}: words {placed}.. up to its last lane pseudo-random (2^{vars})");
    }
    assert!(report.checks.iter().all(|(_, ok)| *ok));
    // F's unused words hold garbage too: the contract that accepts is the one built for that F.
    let roots = report.roots.expect("the proof's roots");
    verify(&trace.shape(), &PROGRAM_IV, &roots, &trace.public_input(), &proof, KECCAK_MAIN).expect("accepted");
    println!("  accepted");
}
