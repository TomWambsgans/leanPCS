// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! π2 on the real instance (PI2.md): the circuit compiled from π1's recorded verifier with the witness of a real
//! Keccak VM π1-rec3 proof (`crates/leanvm/univariate/tests/vectors/keccak128_rec3.txt`, the reference shape, 128
//! signatures; `keccak_rec3.txt`, 400), through the adapter (`pi2::adapt`):
//!
//! - `real_gas`: the contract's gas on the real circuits, D16v (the verifier's gas depends on the circuit alone),
//!   parity with the Rust verifier;
//! - `real_end_to_end` (`PI2_VECTOR=keccak128_rec3|keccak_rec3`): π2's prover on the real witness, its five openings
//!   verified (`pcs_claim::verify_claim`, the EIP draft's `pcs_verify`: what the block's openings prove), and the
//!   contract accepting the proof with its frame of PCS claims declaring exactly its claims: π1's three (the vector's,
//!   which π1's openings prove) and π2's five; a flipped calldata byte is rejected. Its gas is the frame transaction's
//!   (EIP-8141, EIP-7976's floor; without `FRAME_TX_INTRINSIC_COST` and the per-frame costs).
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
use leanvm_univariate::Claims;
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
        Claims::Point,
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
        gas("keccak128_rec3", Layout::D16v);
        gas("keccak_rec3", Layout::D16v);
    });
}

#[test]
#[ignore]
fn real_end_to_end() {
    bench::init_tracing_from_env();
    deep(|| {
        let layout = Layout::D16v;
        let name = std::env::var("PI2_VECTOR").unwrap_or_else(|_| "keccak128_rec3".into());
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
        assert!(accepted, "the contract accepts π2's proof of π1-rec3's real proof");
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
        // The transaction on the real calldata (its zero bytes are the proof's: π1-rec3's narrow challenges): a frame
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
