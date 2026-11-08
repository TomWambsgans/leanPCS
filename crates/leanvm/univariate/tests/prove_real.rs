// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The prover on real Keccak VM traces (leanVM 9d50c92a3, written by `src/prover/dump_keccak`; KECCAK.md): SPEC.md's
//! identities on the domain, the quotients' degrees, every combined relation at `t`, the Rust verifier's and the EVM
//! contract's acceptance of the proof (the contract's `PCS_OPEN` calls being exactly the claims the WHIR openings
//! prove), and the rejection of mutated proofs.
//!
//! `LEANVM_TRACE=<dir of one trace>` (the directory `trace_dump.rs` wrote), then, built with
//! `RUSTFLAGS="-C target-cpu=native"` as leanVM is,
//! `cargo test --release -p leanvm_univariate --test prove_real -- --ignored --nocapture --test-threads 1`.
//! `WRITE_VECTORS=<dir>` writes the proof's Rust→EVM vector (`tests/vectors/`) to `<dir>/<config>.txt`, or to
//! `<dir>/<VECTOR_FILE>.txt`.

use leanvm_statement::evm::codegen::word;
use leanvm_statement::evm::machine::{PcsOpen, call, element_word, root_of_word};
use leanvm_statement::shapes::PROGRAM_IV;
use leanvm_univariate::claims::Commitment;
use leanvm_univariate::contract::{SetupRoots, calldata, compile_verifier, record_verifier_with};
use leanvm_univariate::prover::check::on_domain;
use leanvm_univariate::prover::poly::to_v;
use leanvm_univariate::prover::prove::{Config, OpeningProof, Proof, prove, verify};
use leanvm_univariate::prover::trace::Trace;
use leanvm_univariate::{Claims, KECCAK_MAIN, KECCAK_REC3, Variant};
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
use vectors::{deployable, name_of as vector_name};

/// The allocator leanVM's own CLI and benches run on (jemalloc, freed pages kept: `bench::Jemalloc`), so that the
/// prover is measured as leanVM's is; on glibc's every large buffer faults its pages in again.
#[global_allocator]
static ALLOCATOR: bench::Jemalloc = bench::Jemalloc;

/// The roots of the trace's contract: its program's and shape's `F`, and the two fixed words.
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
                layout: o.layout,
                vars: o.vars,
                placed: o.placed,
                point: o.point.clone(),
                value: o.value,
                proof: o.proof.clone(),
            })
            .collect(),
    }
}

/// `PCS_OPEN`'s root word (`crates/evm/src/machine.rs`: `s_0 · 2^128 + s_1`) of the root a WHIR opening is of, read
/// off the opening itself: its first two scalars, each 128 bits.
fn whir_word(opening_stream: &[F192]) -> [u8; 32] {
    let mut word = [0u8; 32];
    for (h, s) in opening_stream[..2].iter().enumerate() {
        assert_eq!(s.c2, 0, "a root scalar is 128-bit");
        word[16 * h..16 * h + 8].copy_from_slice(&s.c1.to_be_bytes());
        word[16 * h + 8..16 * h + 16].copy_from_slice(&s.c0.to_be_bytes());
    }
    word
}

fn number(n: u64) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[24..].copy_from_slice(&n.to_be_bytes());
    b
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
        stand_in_roots: None,
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
    // The roots the openings are of, from the prover's output: each WHIR opening's first two scalars are its
    // commitment's root's (`hash_to_scalars`), and the stream carries C1's and C2's as those scalars, so that the
    // stream's 32 bytes are the root's `PCS_OPEN` word (machine.rs: `s_0 · 2^128 + s_1`).
    let order: Vec<Commitment> = proof.openings.iter().map(|o| o.commitment).collect();
    assert_eq!(order, [Commitment::C1, Commitment::C2, Commitment::Setup], "the calls' order");
    let mut whir_roots: Vec<[u8; 32]> = Vec::new();
    for o in &proof.openings {
        let scalars = fiat_shamir::merkle::hash_to_scalars(&o.root);
        assert_eq!(o.proof.stream[..2], scalars, "{:?}: the WHIR opening's first two scalars are its root's", o.commitment);
        if o.commitment == Commitment::C1 {
            // After the six row counts.
            assert_eq!(proof.stream[24..56], whir_word(&o.proof.stream), "C1's root word in the stream");
        }
        whir_roots.push(o.root);
    }

    // The contract on the real calldata: its PCS_OPEN mock attests exactly the claims the openings prove (C1's and
    // C2's root words their WHIR openings' first two scalars, the setup's root the contract's constant, the hash as it
    // is; the layout words the contract's).
    let mut inputs: Vec<Vec<u8>> = Vec::new();
    for o in &proof.openings {
        let root = match o.commitment {
            Commitment::Setup => roots.f,
            _ => whir_word(&o.proof.stream),
        };
        let mut input = root.to_vec();
        input.extend(o.layout);
        input.extend(number(1));
        for &x in o.point.iter().chain([&o.value]) {
            input.extend(element_word(to_v(x)));
        }
        inputs.push(input);
    }
    let data = calldata(&public, &proof.stream);
    let stream = proof.stream.clone();
    let opened = whir_roots.clone();
    let (accepted, rejected, gas, linked, calls) = deep(move || {
        let recorded = record_verifier_with(&shape, variant, Claims::Point, &roots);
        assert_eq!(recorded.stream_len, stream.len(), "the contract's stream is the proof's");
        // The measuring build, word for word against the Rust verifier, on this accepting stream.
        leanvm_univariate::contract::parity_with(&shape, &PROGRAM_IV, &roots, &public, &stream, variant, Claims::Point);
        let contract = compile_verifier(&recorded, &PROGRAM_IV, false);
        // The calls the contract makes are the claims the openings prove.
        let calls = call(&contract.code, &[], &data, &PcsOpen::attesting_all(0)).pcs_calls;
        assert_eq!(calls.len(), inputs.len(), "one call per claim the openings prove");
        for (k, (made, proven)) in calls.iter().zip(&inputs).enumerate() {
            assert_eq!(made, proven, "call {k}: the opening's claim");
        }
        // C1's and C2's calls, read as a decoding PCS_OPEN reads them (machine.rs: the root word, then the root it
        // names), are of the roots the prover committed. The setup's constants are the hashes as they are (π1's own
        // contract; π2 passes their root words).
        for (k, (made, root)) in calls.iter().zip(&opened).enumerate().take(2) {
            let word: [u8; 32] = made[..32].try_into().expect("a root word");
            assert_eq!(&root_of_word(&word), root, "call {k}: PCS_OPEN reads the root the opening is of");
        }
        let attesting = |skip: Option<usize>| {
            let mut pcs = PcsOpen::default();
            for (k, input) in calls.iter().enumerate() {
                if Some(k) != skip {
                    pcs.register(input.clone());
                }
            }
            pcs
        };
        let blocks: Vec<PcsOpen> = std::iter::once(attesting(None)).chain((0..calls.len()).map(|k| attesting(Some(k)))).collect();
        let one = word([1, 0, 0]);
        let accepts = |data: &[u8], block: &PcsOpen| call(&contract.code, &[], data, block).output.as_deref() == Some(&one[..]);
        let ok = call(&contract.code, &[], &data, &blocks[0]);
        let mut bad = data.clone();
        let last = bad.len() - 1;
        bad[last] ^= 1;
        let mut rejected = accepts(&bad, &blocks[0]) as usize;
        // Every call must be attested.
        rejected += blocks[1..].iter().filter(|b| accepts(&data, b)).count();
        // The deployable verifying build (crates/evm_link, contracts of at most 24,576 bytes), likewise.
        let deployed = deployable(&recorded);
        let linked = |data: &[u8], block: &PcsOpen| deployed.chain.call(deployed.address, data, block);
        let linked_run = linked(&data, &blocks[0]);
        let linked_ok = linked_run.output.as_deref() == Some(&one[..])
            && linked(&bad, &blocks[0]).output.is_none()
            && blocks[1..].iter().all(|b| linked(&data, b).output.is_none());
        let deployed_gas = linked_run.execution;
        (ok.output.clone(), rejected, ok.execution, (deployed.contracts.len(), linked_ok, deployed_gas), calls)
    });
    println!(
        "  the contract returns {:?} on the real proof, {gas} gas of execution; parity with the Rust verifier; the \
         deployable build ({} contracts) accepts it: {}, {} gas of execution",
        accepted.as_ref().map(|o| o[31]),
        linked.0,
        linked.1,
        linked.2
    );
    assert_eq!(accepted.as_deref(), Some(&word([1, 0, 0])[..]), "the contract accepts the real proof");
    // The Rust→EVM test vector (tests/vectors/): the calldata, the calls PCS_OPEN attests, the verdict and the gas.
    if let Ok(out) = std::env::var("WRITE_VECTORS") {
        let name = vector_name(variant);
        let text = vectors::write(&vectors::Vector {
            config: name.to_string(),
            shape,
            public,
            calldata: calldata(&public, &proof.stream),
            calls: calls.clone(),
            whir_roots,
            accepts: true,
            gas_straight: gas,
            gas_deployed: linked.2,
            contracts: linked.0,
            note: format!(
                "the Keccak VM (leanVM 9d50c92a3, KECCAK.md), its run without the fill blocks: rows {:?}",
                trace.rows
            ),
        });
        let file = std::env::var("VECTOR_FILE").unwrap_or_else(|_| name.to_string());
        let path = std::path::Path::new(&out).join(format!("{file}.txt"));
        std::fs::write(&path, text).expect("the vector file");
        println!("  test vector written to {}", path.display());
    }
    assert_eq!(rejected, 0, "the contract rejects a mutated proof, and a proof with one call not attested");
    assert!(linked.1, "the deployable build accepts the real proof, and rejects the mutations");

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

/// The Keccak VM's π1-rec3, the recursion's inner proof (`crates/leanvm_rec`): `KECCAK_MAIN` with π1-rec3's Fiat–Shamir
/// shape (`FsShape::Rec3`: α and the zerocheck's eq point as squares, the batch two variables a round).
#[test]
#[ignore]
fn proves_and_verifies_keccak_rec3() {
    end_to_end(KECCAK_REC3);
}

/// The setup root a contract for this trace's program and shape is generated with (SPEC.md §13, F2): `F` from the
/// program and the shape.
#[test]
#[ignore]
fn setup_roots() {
    let Some((trace, _)) = trace() else {
        println!("LEANVM_TRACE is not set: no program");
        return;
    };
    let started = std::time::Instant::now();
    let setup = leanvm_univariate::prover::columns::setup_polys(&trace);
    let f = leanvm_univariate::prover::setup::f_root(&trace.shape(), &setup);
    println!("  shape {:?}", trace.shape());
    println!("  F  {}", leanvm_univariate::prover::setup::hex(&f));
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
        _ => KECCAK_MAIN,
    };
    let repeat: usize = std::env::var("PI1_REPEAT").ok().map_or(3, |x| x.parse().expect("a count"));
    let cooldown: u64 = std::env::var("PI1_COOLDOWN").ok().map_or(2, |x| x.parse().expect("seconds"));
    let config = Config {
        variant,
        claims: Claims::Point,
        check: false,
        garbage: false,
        stand_in_roots: None,
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
        stand_in_roots: None,
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
