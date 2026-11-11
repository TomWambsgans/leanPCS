// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The Keccak VM's π1 (docs/leanvm/univariate/KECCAK.md) under π2: its verifier recorded with π1-rec4's Fiat–Shamir
//! shape, counted, and compiled into π2's circuit (D16v) on a sample stream, at the reference shape (128 signatures)
//! and at 400: whether π2 holds it in `2^24` positions, and the recursion's contract's gas.
//!
//! `cargo test --release -p leanvm_rec --test keccak_vm_rec -- --ignored --nocapture`

use leanvm_statement::shapes::PROGRAM_IV;
use leanvm_rec::REFERENCE;
use leanvm_rec::circuit::compile::{Inputs, Layout, pi2};
use leanvm_rec::count::count;
use leanvm_rec::pi2::adapt;
use leanvm_rec::pi2::contract::{self as pi2_contract, Instance};
use leanvm_rec::pi2::verifier::Spec;
use leanvm_univariate::contract::{record_verifier, sample_stream};
use leanvm_rec::PI1;
use leanvm_univariate::{Claims, Shape};

/// leanVM 9d50c92a3 at 400 signatures (`crates/leanvm/univariate/tests/keccak_vm.rs`).
const KECCAK_400: Shape = Shape {
    log_memory: 22,
    log_bytecode: 18,
    table_rows: [73288, 110893, 75762, 109932, 48157, 55316],
};

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

fn report(name: &str, shape: &Shape) -> usize {
    let recorded = record_verifier(shape, PI1, Claims::Point);
    let c = count(&recorded);
    let stream = sample_stream(recorded.stream_len, 7);
    let compiled = pi2(
        &recorded,
        Layout::D16v,
        &Inputs {
            program_iv: PROGRAM_IV,
            public: [3; 32],
            stream: &stream,
        },
    );
    let s = &compiled.finished.stats;
    println!(
        "  π2: {} rows used, {} blocks, {} selector pairs, {} regions",
        s.rows_used,
        s.blocks,
        s.pairs,
        s.rows.len()
    );
    println!("  π2 regions (rows): {:?}", s.rows);
    println!(
        "{name}: stream {} B, Keccak-256 {} calls, Keccak-f {}, E products {} / linear {} (kernels expanded); \
         π2 D16v N = 2^{}, {} positions used ({:.1}%)",
        recorded.stream_len,
        c.hash_lengths.len(),
        c.permutations,
        c.total_ops.products(),
        c.total_ops.linear(),
        s.log_n,
        s.positions_used,
        100.0 * s.fill(),
    );
    // The recursion's contract: π2's verifier, whose gas depends on the circuit alone (`tests/pi2_real.rs`); the setup
    // root a placeholder.
    let circuit = adapt::adapt(&compiled.finished.circuit);
    let spec = Spec::of(&circuit);
    let inst = Instance::new(
        &circuit,
        &spec,
        [0x44; 32],
        primitives::field::F192::new(5, 6, 7),
        &compiled.pi1_iv,
        &compiled.finished.circuit.calls,
    );
    let pi2_recorded = pi2_contract::record_verifier(&spec);
    let gas = pi2_contract::measure(&inst, &pi2_recorded);
    print!("{}", gas.table(&format!("{name}: the recursion's contract (π2 D16v)")));
    let pi2_stream = pi2_contract::sample_stream(pi2_recorded.stream_len, 13);
    pi2_contract::parity(&inst, &pi2_recorded, &[0x5a; 32], &pi2_contract::sample_hashed(&inst), &pi2_stream);
    s.log_n as usize
}

#[test]
#[ignore]
fn keccak_vm_under_pi2() {
    deep(|| {
        report("Keccak VM π1-rec4, 128 signatures (REFERENCE)", &REFERENCE);
        report("Keccak VM π1-rec4, 400 signatures", &KECCAK_400);
    });
}
