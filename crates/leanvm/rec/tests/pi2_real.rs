// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! π2 on the real instance (PI2.md): the circuit compiled from π1's recorded verifier with the witness of a real
//! Keccak VM π1-rec4 proof (`leanvm_rec::PI1`; `crates/leanvm/univariate/tests/vectors/keccak128_rec4.txt`, the
//! reference shape, 128 signatures, the default; `keccak_rec4.txt`, 400), through the adapter (`pi2::adapt`):
//!
//! - `real_gas`: the contract's gas on the real circuits, D16v (the verifier's gas depends on the circuit alone),
//!   parity with the Rust verifier;
//! - `real_end_to_end` (`PI2_VECTOR=keccak128_rec4|keccak_rec4`, default `keccak128_rec4`): π2's prover on the real
//!   witness, its five openings verified (`pcs_claim::verify_claim`, the EIP draft's `pcs_verify`: what the block's
//!   openings prove), and the contract accepting the proof with its frame of PCS claims declaring exactly its claims:
//!   π1's three (the vector's, which π1's openings prove) and π2's five; flipped calldata bytes and the frame's
//!   attacks are rejected (`frame_and_calldata_attacks`). Its gas is the frame transaction's (EIP-8141, EIP-7976's
//!   floor; without `FRAME_TX_INTRINSIC_COST` and the per-frame costs).
//!
//! `cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture --test-threads 1`

#![allow(clippy::needless_range_loop)]

#[global_allocator]
static ALLOC: bench::Jemalloc = bench::Jemalloc;

#[path = "../../univariate/tests/vectors/mod.rs"]
mod vectors;

use leanvm_statement::shapes::PROGRAM_IV;
use leanvm_rec::circuit::compile::{Compiled, Inputs, Layout, pi2};
use leanvm_rec::pi2::adapt;
use pcs_claim::PcsClaim;
use leanvm_rec::pi2::contract::{self, Instance, calldata, record_verifier, sample_stream};
use leanvm_rec::pi2::prover::{self, Setup, claims_hold, open, prove, public_scalars, verify_openings};
use leanvm_rec::pi2::verifier::Spec;
use primitives::field::F192;

const STREAM_AT: usize = 4 + 32;

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

fn vector(name: &str) -> vectors::Vector {
    let path = format!(
        "{}/../univariate/tests/vectors/{name}.txt",
        env!("CARGO_MANIFEST_DIR")
    );
    vectors::read(&std::fs::read_to_string(&path).expect("a committed vector"))
}

/// The real circuit and witness, and π1's contract IV. π1's contract binds the vector's setup commitment `F` (its
/// third claim's, its program's and shape's own), as the proof's does.
fn real(name: &str, layout: Layout) -> (vectors::Vector, Compiled, [u8; 32]) {
    let v = vector(name);
    let roots = vectors::setup_roots(&v);
    let recorded = leanvm_univariate::contract::record_verifier_with(
        &v.shape,
        vectors::variant_of(&v.config),
        &roots,
    );
    let stream = v.calldata[STREAM_AT..].to_vec();
    let c = pi2(
        &recorded,
        layout,
        &Inputs {
            program_iv: PROGRAM_IV,
            public: v.public,
            stream: &stream,
        },
    );
    let iv = c.pi1_iv;
    (v, c, iv)
}

fn peak_memory() -> String {
    format!("peak RSS {:.2} GB", bench::peak_rss_bytes() as f64 / 1e9)
}

fn gas(name: &str, layout: Layout) {
    let (_, c, pi1_iv) = real(name, layout);
    let circuit = adapt::adapt(&c.finished.circuit);
    let spec = Spec::of(&circuit);
    let terms: usize = spec
        .groups
        .iter()
        .map(|g| g.formula.lin.terms.len() + 2 * g.formula.products.len())
        .sum();
    let products: usize = spec.groups.iter().map(|g| g.formula.products.len()).sum();
    println!(
        "{name} × {layout:?}: 2^{} positions, {} pairs ({} pull-less, the holes), {} groups ({} formula terms, {} products), blocks up to 2^{} rows, {} public terms, {} reads; π1: {} calls",
        circuit.log_n,
        circuit.pairs.len(),
        spec.pull_less.len(),
        spec.groups.len(),
        terms,
        products,
        spec.max_log_rows(),
        circuit.public.len(),
        circuit.reads.len(),
        c.finished.circuit.calls.len()
    );
    // The setup commitment does not change the gas: a placeholder, as the univariate contract's reports.
    let inst = Instance::new(&circuit, &spec, [0x44; 32], F192::new(5, 6, 7), &pi1_iv, &c.finished.circuit.calls);
    let recorded = record_verifier(&spec);
    let report = contract::measure(&inst, &recorded);
    print!("{}", report.table(&format!("{name} × {layout:?} (real circuit)")));
    let stream = sample_stream(recorded.stream_len, 13);
    contract::parity(&inst, &recorded, &[0x5a; 32], &contract::sample_hashed(&inst), &stream);
    println!("parity\n");
}

#[test]
#[ignore]
fn real_gas() {
    deep(|| {
        gas("keccak128_rec4", Layout::D16v);
        gas("keccak_rec4", Layout::D16v);
    });
}

/// The contract against its frame and its calldata, on the real proof (`data`, its frame declaring `block`): it
/// rejects a frame of another mode or scheme, swapped payloads, any claim's value, point or out-of-domain answer
/// changed, a claim missing, a frame index naming a non-PCS frame, a PCS-scheme frame of another mode, calldata one
/// byte longer or shorter, and every calldata byte flipped at bits 0 and 7; it accepts a ninth claim appended (the frame
/// may declare more) and the right index past a frame before it.
fn frame_and_calldata_attacks(inst: &Instance, recorded: &contract::Recorded, data: &[u8], block: &[PcsClaim]) {
    use leanvm_statement::evm::codegen::word;
    use leanvm_statement::evm::machine::{Frame, PcsFrame, call};
    let code = contract::compile_verifier(inst, recorded, false).code;
    let ok = |d: &[u8], f: &PcsFrame| call(&code, &[], d, f).output.as_deref() == Some(&word([1, 0, 0])[..]);
    let honest = contract::block(block);
    assert!(ok(data, &honest), "the honest frame");
    let mut f = contract::block(block);
    f.mode = 3;
    assert!(!ok(data, &f), "another mode");
    let mut f = contract::block(block);
    f.scheme = 0x11;
    assert!(!ok(data, &f), "another scheme");
    for (i, j) in [(0, 1), (1, 2), (0, 2), (3, 4), (5, 6), (6, 7), (2, 3)] {
        let mut b = block.to_vec();
        b.swap(i, j);
        assert!(!ok(data, &contract::block(&b)), "payloads {i} and {j} swapped");
    }
    for k in 0..block.len() {
        let mut b = block.to_vec();
        b[k].value += F192::ONE;
        assert!(!ok(data, &contract::block(&b)), "claim {k}'s value changed");
        let mut b = block.to_vec();
        b[k].point[3] += F192::ONE;
        assert!(!ok(data, &contract::block(&b)), "claim {k}'s point changed");
        let mut b = block.to_vec();
        b[k].ood += F192::ONE;
        assert!(!ok(data, &contract::block(&b)), "claim {k}'s out-of-domain answer changed");
    }
    assert!(!ok(data, &contract::block(&block[..block.len() - 1])), "a claim missing");
    let mut b = block.to_vec();
    b.push(block[0].clone());
    assert!(ok(data, &contract::block(&b)), "a ninth claim appended");
    // A frame before the PCS frame: the index byte must name the PCS frame.
    let mut f = contract::block(block);
    f.before = vec![Frame {
        mode: 4,
        data: [&[0x13u8][..], &[7u8; 64]].concat(),
    }];
    assert!(!ok(data, &f), "index 0 names a non-PCS frame");
    let mut moved = data.to_vec();
    *moved.last_mut().expect("the index") = 1;
    assert!(ok(&moved, &f), "index 1 names the PCS frame");
    // A frame of the PCS scheme and the right payloads, but not a dependency verification frame.
    let mut f = contract::block(block);
    f.before = vec![Frame {
        mode: 1,
        data: contract::block(block).data(),
    }];
    let mut first = data.to_vec();
    *first.last_mut().expect("the index") = 0;
    assert!(!ok(&first, &f), "a mode-1 frame with the right payloads");
    let longer = [data, &[0]].concat();
    assert!(!ok(&longer, &honest), "one byte more");
    assert!(!ok(&data[..data.len() - 1], &honest), "one byte less");
    // Every calldata byte but the frame's index (above), at bits 0 and 7.
    for at in 0..data.len() - 1 {
        for bit in [0, 7] {
            let mut bad = data.to_vec();
            bad[at] ^= 1 << bit;
            assert!(!ok(&bad, &honest), "calldata byte {at} flipped at bit {bit}");
        }
    }
    println!(
        "frame and calldata attacks rejected; every one of {} calldata bytes flipped at 2 bits rejected",
        data.len() - 1
    );
}

#[test]
#[ignore]
fn real_end_to_end() {
    bench::init_tracing_from_env();
    deep(|| {
        let layout = Layout::D16v;
        let name = std::env::var("PI2_VECTOR").unwrap_or_else(|_| leanvm_rec::PI1_VECTOR_128.into());
        let start = std::time::Instant::now();
        let (v, c, pi1_iv) = real(&name, layout);
        let compiled = start.elapsed().as_secs_f64();
        assert_eq!(c.finished.circuit.check(&c.finished.witness, &c.public), Ok(()));
        // π1's claims as the block proves them: the vector's, on the commitments π1's prover made (written from its
        // output), not on whatever a contract encodes.
        let pi1_claims: Vec<PcsClaim> =
            v.claims.iter().map(|c| PcsClaim::decode(c).expect("a well-formed claim")).collect();
        let circuit = adapt::adapt(&c.finished.circuit);
        let witness = adapt::witness(&c.finished.witness);
        let (public_input, values) = adapt::public_values(&c.public);
        drop(c.expanded);
        let calls = c.finished.circuit.calls.clone();
        circuit
            .check(&witness, &public_scalars(&public_input, &values), F192::new(3, 5, 7))
            .expect("the adapted circuit holds");
        let spec = Spec::of(&circuit);
        println!(
            "{name} × {layout:?}: compiled, adapted, checked in {:.1} s (the compile, which a proof's witness needs, {compiled:.2} s); {}",
            start.elapsed().as_secs_f64(),
            peak_memory()
        );
        let start = std::time::Instant::now();
        let setup = Setup::new(&circuit);
        let inst = Instance::new(&circuit, &spec, setup.root(), setup.ood(), &pi1_iv, &calls);
        let iv = inst.iv;
        assert_eq!(iv, prover::iv(&pi1_iv, &circuit.digest(), &setup.root(), setup.ood(), circuit.log_n));
        println!("setup committed in {:.1} s", start.elapsed().as_secs_f64());

        let start = std::time::Instant::now();
        let proved = prove(&circuit, &spec, &setup, &iv, &public_input, &values, &witness);
        let proving = start.elapsed().as_secs_f64();
        for (step, s) in &proved.timings {
            println!("   {s:>7.2} s  {step}");
        }
        assert_eq!(claims_hold(&proved, &setup), [true; 5], "the claims hold on the stacks");
        let stream = proved.stream.clone();
        let start = std::time::Instant::now();
        let (reduced, roots, openings) = open(proved, &setup);
        let opening = start.elapsed().as_secs_f64();
        println!("prove {proving:.1} s, open {opening:.1} s; {}", peak_memory());
        // The proof's fingerprint: a change of the prover that keeps the proof keeps these lines.
        let hex = |b: &[u8]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
        println!("pi2 stream keccak {}", hex(&primitives::hash::hash(&stream)));
        println!("pi2 roots {} {}", hex(&roots[0]), hex(&roots[1]));
        println!(
            "pi2 openings keccak {}",
            hex(&primitives::hash::hash(
                format!("{:?}", &openings.proofs).as_bytes()
            ))
        );
        // The openings' sizes: the scalars (24 bytes) and the Merkle rows and siblings.
        let bytes = |p: &fiat_shamir::transcript::Proof| {
            24 * p.stream.len()
                + (p.merkle.iter())
                    .map(|m| m.leaf_data.iter().map(|r| 8 * r.len()).sum::<usize>() + 32 * m.sibling_hashes.len())
                    .sum::<usize>()
        };
        println!(
            "pi2 openings W, setup, Q (identity, pushes, sum): {:?} bytes",
            openings.proofs.iter().map(bytes).collect::<Vec<_>>()
        );
        assert_eq!(
            verify_openings(circuit.log_n, &reduced, &roots, &setup.root(), setup.ood(), &openings),
            Ok(())
        );

        // The contract: π1's three claims (the vector's, which π1's openings prove) and π2's five (the proof's
        // commitments, its reduction's claims), declared exactly, in order, in its frame of PCS claims.
        let recorded = record_verifier(&spec);
        // The frame: π1's claims (payloads 0, 1, 2), then π2's five. The contract encodes those at `payloads` from π2's
        // public data and its reduction; it reads the others (π1's claims hashed in the circuit) as public words.
        let pi2_claims = prover::claims(circuit.log_n, &reduced, &roots, &setup.root(), setup.ood());
        let block: Vec<PcsClaim> = pi1_claims.iter().chain(&pi2_claims).cloned().collect();
        let expected = contract::expected_claims(&inst, &recorded, &reduced, &stream);
        let payloads = contract::payloads(&inst);
        assert_eq!(expected.len(), payloads.len());
        for (&p, claim) in payloads.iter().zip(&expected) {
            assert_eq!(block[p], *claim, "payload {p}: the claim from π2's public data and reduction is the frame's");
        }
        let hashed: Vec<Vec<u8>> =
            contract::frame_payloads(&spec).iter().map(|&p| block[p as usize].encode()).collect();
        let words = prover::frame_words(&values);
        assert_eq!(
            hashed.iter().map(|c| leanvm_statement::transcript::keccak256(c)).collect::<Vec<_>>(),
            words,
            "π2's public claim hashes are the Keccak-256s of the vector's claims"
        );
        println!(
            "π1's claims hashed in π2's circuit: payloads {:?}; the contract encodes payloads {payloads:?}",
            contract::frame_payloads(&spec)
        );
        let data = calldata(&public_input, &stream);
        println!("pi2 calldata keccak {}", hex(&primitives::hash::hash(&data)));
        let (accepted, made) = contract::run(&inst, &recorded, &data, &block);
        assert!(accepted, "the contract accepts π2's proof of π1's real proof");
        assert_eq!(
            made,
            payloads.iter().map(|&p| block[p].encode()).collect::<Vec<_>>(),
            "the claims the contract checks"
        );
        // The roots are the commitments' bytes as they are: π1's claims with each half of a root reversed (the former
        // root word) name other commitments, which the frame does not declare.
        let reversed: Vec<PcsClaim> = block
            .iter()
            .enumerate()
            .map(|(k, c)| {
                let mut c = c.clone();
                if k < 2 {
                    c.root[..16].reverse();
                    c.root[16..].reverse();
                }
                c
            })
            .collect();
        assert!(!contract::run(&inst, &recorded, &data, &reversed).0, "π1's claims on other roots: rejected");
        // A flipped byte anywhere: the public input, π1's roots, its elements, W's and Q's commitments, every value
        // sent.
        let n_roots = recorded.roots_at.len();
        let (w_at, q_at) = (recorded.roots_at[n_roots - 2], recorded.roots_at[n_roots - 1]);
        let values_at = q_at + 32 + 24;
        let s = contract::STREAM_AT;
        let mut flips = vec![0, 31, s + 5, s + 40, s + 64, s + 64 + 20 * 14 + 11, s + w_at - 1];
        flips.extend([s + w_at, s + w_at + 31, s + w_at + 32 + 5, s + q_at + 7, s + q_at + 32 + 20]);
        flips.extend((0..spec.values()).step_by(4).map(|k| s + values_at + 24 * k + k % 24));
        // The last values, and the frame's index.
        flips.extend([data.len() - 49, data.len() - 26, data.len() - 2, data.len() - 1]);
        assert!(flips.len() >= 13);
        for &at in &flips {
            let mut bad = data.clone();
            bad[at] ^= 1;
            assert!(
                !contract::run(&inst, &recorded, &bad, &block).0,
                "calldata byte {at} flipped"
            );
        }
        contract::parity(&inst, &recorded, &public_input, &hashed, &stream);
        frame_and_calldata_attacks(&inst, &recorded, &data, &block);
        // The transaction on the real calldata (its zero bytes are the proof's): a frame
        // transaction (EIP-8141, EIP-7976's floor), without `FRAME_TX_INTRINSIC_COST` and the per-frame costs.
        let (ok, execution) = contract::verifying_execution(&inst, &recorded, &data, &block);
        assert!(ok);
        let zero = data.iter().filter(|&&b| b == 0).count();
        let alone = contract::transaction_of(&data, execution, &[]);
        println!(
            "the real calldata: {} B ({zero} zero); execution {execution} (the verifying build); standard {}, floor {}: {}",
            data.len(),
            alone.standard,
            alone.floor,
            alone.total
        );
        let frame = contract::block(&block).data();
        let with = contract::transaction_of(&data, execution, &block);
        println!(
            "with its frame of PCS claims ({} B, {} claims) and pcs_gas ({}): standard {}, floor {}: {}",
            frame.len(),
            block.len(),
            leanvm_statement::evm::machine::dependency_gas(block.len()),
            with.standard,
            with.floor,
            with.total
        );
        println!(
            "end to end: π1's real proof → π2's proof ({} B of calldata) → the contract accepts, its frame declaring its {} claims; {} flipped bytes rejected",
            data.len(),
            block.len(),
            flips.len()
        );
    });
}
