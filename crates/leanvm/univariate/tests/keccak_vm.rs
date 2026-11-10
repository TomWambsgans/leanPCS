// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The Keccak VM (docs/leanvm/univariate/KECCAK.md): leanVM 9d50c92a3's tables, proved by Flock on the Keccak-f
//! block with its structured terminal. Its contract against its Rust verifier, its stacks against WHIR's `2^28` words,
//! and its gas.
//!
//! `cargo test --release -p leanvm_univariate --test keccak_vm`
//! `cargo test --release -p leanvm_univariate --test keccak_vm -- --ignored --nocapture keccak_gas_report`

use leanvm_statement::shapes::{PROGRAM_IV, WORKLOADS, by_xmss};
use leanvm_univariate::claims::Commitment;
use leanvm_univariate::contract::{GasReport, measure, parity, record_verifier, sample_stream};
use leanvm_univariate::verifier::layouts;
use leanvm_univariate::{Claims, KECCAK_MAIN, Shape};

/// The largest proof stack (`C1`, `C2`) of `shape`, in variables: WHIR takes at most 28.
fn largest_stack(shape: &Shape) -> usize {
    layouts(shape)
        .iter()
        .filter(|(c, _)| *c != Commitment::Setup)
        .map(|(_, l)| l.vars)
        .max()
        .expect("stacks")
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

/// The contract computes what the Rust verifier computes, word for word, on sample streams: the claims it checks
/// declared and every value it checks (point claims, the PCS claims a contract checks; the smallest Keccak shape).
#[test]
fn keccak_contract_is_the_rust_verifier() {
    deep(|| {
        let shape = Shape::of(&by_xmss(32).shape);
        for mode in [Claims::Point] {
            let recorded = record_verifier(&shape, KECCAK_MAIN, mode);
            for seed in [1u64, 2] {
                let stream = sample_stream(recorded.stream_len, seed);
                parity(&shape, &PROGRAM_IV, &[0x5a; 32], &stream, KECCAK_MAIN, mode);
            }
        }
    });
}

/// The Keccak VM's stacks: `q_flock` is `2^11` words a permutation (one Keccak-f block a `SHA3` row), so `C1` fits
/// WHIR's `2^28` words up to `2^16` permutations: 400 signatures fit, 1,000 (138,266 permutations, `2^29` words of
/// `q_flock` alone) do not.
#[test]
fn keccak_stacks_against_whir() {
    for workload in &WORKLOADS {
        let vars = largest_stack(&Shape::of(&workload.shape));
        println!("xmss {}: largest proof stack 2^{vars}", workload.xmss);
        assert_eq!(vars <= 28, workload.xmss <= 400, "xmss {}", workload.xmss);
    }
}

fn row(label: &str, xmss: usize, report: &GasReport, stack: usize) -> String {
    let alone = report.transaction(false);
    let with = report.transaction(true);
    format!(
        "| {label} | {xmss} | 2^{stack} | {} | {} | {} | {} | {} / {} | {} / {} |",
        report.calldata_bytes,
        report.execution,
        report.field_muls,
        report.claims,
        alone.standard,
        alone.floor,
        with.standard,
        with.floor,
    )
}

fn phases(report: &GasReport) {
    for phase in &report.phases {
        println!("  {:>8}  {}", phase.gas, phase.phase);
    }
    for &(phase, bytes) in &report.stream_by_phase {
        println!("  stream {:>6} B  {}", bytes, phase);
    }
}

/// `cargo test --release -p leanvm_univariate --test keccak_vm -- --ignored --nocapture keccak_gas_report`
#[test]
#[ignore]
fn keccak_gas_report() {
    deep(|| {
        println!(
            "| configuration | signatures | largest stack | calldata B | execution | FIELD_MUL | claims | \
             standard / floor | with the frame of PCS claims and pcs_gas | (EIP-8141 frame transaction, EIP-7976 floor, \
             without FRAME_TX_INTRINSIC_COST and per-frame costs)"
        );
        println!("|---|---:|---:|---:|---:|---:|---:|---:|---:|");
        let mut details = Vec::new();
        // Above 400 signatures C1 exceeds 2^28 (measured all the same: the gas of a contract that no WHIR opening
        // could serve).
        for workload in &WORKLOADS {
            let shape = Shape::of(&workload.shape);
            let report = measure(&shape, &PROGRAM_IV, KECCAK_MAIN, Claims::Point);
            let stack = largest_stack(&shape);
            let label = if stack <= 28 {
                "Keccak VM, Flock Keccak-f"
            } else {
                "Keccak VM, Flock Keccak-f [C1 over 2^28: infeasible]"
            };
            println!("{}", row(label, workload.xmss, &report, stack));
            if [128, 400].contains(&workload.xmss) {
                details.push((workload.xmss, report));
            }
        }
        for (name, report) in &details {
            println!(
                "\n### Keccak VM, {name} signatures: execution {} (code {} B)",
                report.execution, report.code_bytes
            );
            phases(report);
        }
    });
}
