// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The contract computes what the Rust verifier computes, and what a call of it costs.

use leanvm_flock_gas::evm::codegen::MAX_CODE;
use leanvm_flock_gas::evm::contract::{
    DeployableReport, GasReport, category, measure, measure_deployable, parity,
    parity_deployable, record_verifier, sample_stream,
};
use leanvm_flock_gas::shapes::{PROGRAM_IV, WORKLOADS, benchmark};
use leanvm_flock_gas::LincheckTerminal;

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

/// On streams of the benchmark's shape, the contract (without its calls, returning the claims and every value it
/// checks) and the Rust verifier on the Keccak chain agree word for word: the claims for `PCS_OPEN`, and every
/// identity's residual.
#[test]
fn contract_is_the_rust_verifier() {
    deep(|| {
        let shape = benchmark().shape;
        let recorded = record_verifier(&shape, LincheckTerminal::Matrices);
        for seed in [1, 2, 3] {
            let stream = sample_stream(&shape, &recorded, seed);
            let public_input: [u8; 32] = std::array::from_fn(|i| (seed as u8).wrapping_mul(31) ^ i as u8);
            parity(&shape, &PROGRAM_IV, &public_input, &stream, LincheckTerminal::Matrices);
        }
    });
}

/// The contract reads leanVM's PIOP stream (the real proofs' length, `shapes.rs`) and what it adds: the bytecode's
/// value, the matrices' reduction (12 rounds of two scalars, then two values) and the stack's batching sumcheck (two
/// scalars a round, then the value). A root is 32 bytes, a scalar 24.
#[test]
fn stream_is_leanvms_and_the_additions() {
    deep(|| {
        for workload in &WORKLOADS {
            for (lincheck, matrices) in [(LincheckTerminal::Matrices, 2 * 12 + 2), (LincheckTerminal::Walk, 0)] {
                let recorded = record_verifier(&workload.shape, lincheck);
                let stack_log = recorded.reduced.layout_stack_log;
                let scalars = workload.piop_elements - 2 + 1 + matrices + 2 * stack_log + 1;
                assert_eq!(recorded.stream_len, 32 + 24 * scalars, "{} {lincheck:?}", workload.name);
            }
        }
    });
}

/// The same with the lincheck's terminal walked in the contract, as leanVM's verifier does.
#[test]
#[ignore]
fn walking_contract_is_the_rust_verifier() {
    deep(|| {
        let shape = benchmark().shape;
        let recorded = record_verifier(&shape, LincheckTerminal::Walk);
        let stream = sample_stream(&shape, &recorded, 7);
        parity(&shape, &PROGRAM_IV, &[0x42; 32], &stream, LincheckTerminal::Walk);
    });
}

fn grouped(n: u64) -> String {
    let digits = n.to_string();
    let mut out = String::new();
    for (i, digit) in digits.chars().enumerate() {
        if i > 0 && (digits.len() - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(digit);
    }
    out
}

fn print_report(name: &str, report: &GasReport) {
    println!("\n### {name}");
    println!(
        "calldata {} bytes ({} zero), stream {} bytes; code {} bytes; FIELD_MUL {}, XOR {}, KECCAK256 {} ({} bytes), \
         checks {}, memory {} words; PCS_OPEN {} claims in {} calls",
        grouped(report.calldata_bytes as u64),
        report.calldata_zero_bytes,
        grouped(report.stream_bytes as u64),
        grouped(report.code_bytes as u64),
        grouped(report.field_muls as u64),
        grouped(report.xors as u64),
        report.hashes,
        grouped(report.hashed_bytes as u64),
        report.checks,
        grouped(report.memory_words as u64),
        report.claims,
        report.calls,
    );
    println!("| part | execution gas |");
    println!("|---|---:|");
    for phase in &report.phases {
        println!("| {} | {} |", phase.phase, grouped(phase.gas));
    }
    println!("| **execution** | **{}** |", grouped(report.execution));
    println!("| calldata (16/4 a byte) | {} |", grouped(report.calldata_gas()));
    println!();
    println!("| c | execution | tx EIP-7623 (−21,000) | tx EIP-7976 (−21,000) |");
    println!("|---:|---:|---:|---:|");
    for c in [0, 2_000, 5_000, 20_000] {
        println!(
            "| {} | {} | {} | {} |",
            grouped(c),
            grouped(report.execution_at(c)),
            grouped(report.transaction(c, 40)),
            grouped(report.transaction(c, 64))
        );
    }
    println!();
    println!("| stream read by | bytes | scalars (24 B; a root 32 B) |");
    println!("|---|---:|---:|");
    for &(phase, bytes) in &report.stream_by_phase {
        let phase = if phase == "setup" {
            "announced sizes, stack root"
        } else {
            phase
        };
        println!("| {phase} | {} | {} |", grouped(bytes as u64), bytes / 24);
    }
    println!(
        "| selector, public input | {} | |",
        report.calldata_bytes - report.stream_bytes
    );
}

fn print_categories(report: &GasReport) {
    let mut categories: Vec<(&str, u64)> = Vec::new();
    for phase in &report.phases {
        let name = category(phase.phase);
        match categories.iter_mut().find(|(c, _)| *c == name) {
            Some((_, gas)) => *gas += phase.gas,
            None => categories.push((name, phase.gas)),
        }
    }
    categories.sort_by_key(|(_, gas)| std::cmp::Reverse(*gas));
    println!("| category | execution gas | share |");
    println!("|---|---:|---:|");
    for (name, gas) in categories {
        println!(
            "| {name} | {} | {:.1}% |",
            grouped(gas),
            100.0 * gas as f64 / report.execution as f64
        );
    }
    println!("| **execution** | **{}** | |", grouped(report.execution));
}

/// What a call costs: `cargo test --release -p leanvm_flock_gas --test evm -- --ignored --nocapture gas_report`.
#[test]
#[ignore]
fn gas_report() {
    deep(|| {
        let mut rows = Vec::new();
        for workload in &WORKLOADS {
            for lincheck in [LincheckTerminal::Matrices, LincheckTerminal::Walk] {
                let report = measure(&workload.shape, &PROGRAM_IV, lincheck);
                if workload.xmss == benchmark().xmss {
                    print_report(&format!("{} ({:?})", workload.name, lincheck), &report);
                    print_categories(&report);
                }
                rows.push((workload, lincheck, report));
            }
        }
        println!("\n### Over the proofs (transaction gas without the 21,000 base)");
        println!(
            "| signatures | cycles | log heights (XOR MUL SET DEREF JUMP BLAKE2S), memory | committed | stack vars | \
             GKR depth | stack claims | lincheck terminal | calldata bytes | execution (c = 0) | claims / calls | \
             tx EIP-7623, c = 0 / 2,000 / 5,000 / 20,000 | tx EIP-7976, c = 0 / 20,000 |"
        );
        println!("|---:|---:|---|---:|---:|---:|---:|---|---:|---:|---:|---|---|");
        for (workload, lincheck, report) in &rows {
            let heights: Vec<String> = workload
                .shape
                .table_rows
                .iter()
                .map(|&rows| (64 - (rows - 1).leading_zeros()).to_string())
                .collect();
            let tx = |c, floor| grouped(report.transaction(c, floor));
            println!(
                "| {} | {} | {}, {} | 2^{:.2} | {} | {} | {} | {} | {} | {} | {} / {} | {} / {} / {} / {} | {} / {} |",
                grouped(workload.xmss as u64),
                grouped(workload.cycles),
                heights.join(" "),
                workload.shape.log_memory,
                workload.log2_committed,
                report.stack_log,
                report.bus_depth,
                report.stack_claims,
                match lincheck {
                    LincheckTerminal::Matrices => "A0, B0 claims",
                    LincheckTerminal::Walk => "walk in contract",
                },
                grouped(report.calldata_bytes as u64),
                grouped(report.execution),
                report.claims,
                report.calls,
                tx(0, 40),
                tx(2_000, 40),
                tx(5_000, 40),
                tx(20_000, 40),
                tx(0, 64),
                tx(20_000, 64),
            );
        }
    });
}

/// The deployable verifier (contracts of at most EIP-170's 24,576 bytes, each deployed by a transaction) computes what
/// the Rust verifier computes, word for word, on streams of the benchmark's shape; reverts exactly when it rejects;
/// and calls `PCS_OPEN` exactly as the one straight-line contract does.
#[test]
fn deployable_is_the_rust_verifier() {
    deep(|| {
        let shape = benchmark().shape;
        let recorded = record_verifier(&shape, LincheckTerminal::Matrices);
        for seed in [4, 5] {
            let stream = sample_stream(&shape, &recorded, seed);
            let public_input: [u8; 32] = std::array::from_fn(|i| (seed as u8).wrapping_mul(29) ^ i as u8);
            let contracts = parity_deployable(
                &shape,
                &PROGRAM_IV,
                &public_input,
                &stream,
                LincheckTerminal::Matrices,
                MAX_CODE,
            );
            assert!(contracts > 1, "117 KB of straight-line code is more than one contract");
        }
    });
}

/// What the deployable verifier costs against the straight-line contract, and its deployment:
/// `cargo test --release -p leanvm_flock_gas --test evm -- --ignored --nocapture deployable_report`.
#[test]
#[ignore]
fn deployable_report() {
    deep(|| {
        for workload in &WORKLOADS {
            for lincheck in [LincheckTerminal::Matrices, LincheckTerminal::Walk] {
                if workload.xmss != benchmark().xmss && lincheck == LincheckTerminal::Walk {
                    continue;
                }
                let deployable = measure_deployable(&workload.shape, &PROGRAM_IV, lincheck, MAX_CODE);
                print_deployable(&format!("{} ({lincheck:?})", workload.name), &deployable);
            }
        }
    });
}

fn print_deployable(name: &str, d: &DeployableReport) {
    let r = &d.report;
    let added = r.execution - d.straight;
    println!("\n### {name}: deployable, contracts of at most 24,576 bytes");
    println!(
        "straight-line: {} bytes, execution {}; deployable: {} contracts, {} bytes, execution {} (+{}, +{:.2}%)",
        grouped(d.straight_code as u64),
        grouped(d.straight),
        d.contracts.len(),
        grouped(r.code_bytes as u64),
        grouped(r.execution),
        grouped(added),
        100.0 * added as f64 / d.straight as f64
    );
    println!(
        "tx (−21,000), EIP-7623: straight {} / deployable {}; EIP-7976: {} / {}",
        grouped(r.transaction_for(d.straight, 40)),
        grouped(r.transaction(0, 40)),
        grouped(r.transaction_for(d.straight, 64)),
        grouped(r.transaction(0, 64)),
    );
    println!(
        "| contract | code bytes | init bytes | deployment execution | deployment tx EIP-7623 (−21,000) | memory words \
         | items | values in / out | stack in / out |"
    );
    println!("|---|---:|---:|---:|---:|---:|---|---:|---:|");
    let (mut execution, mut tx) = (0, 0);
    for (k, c) in d.contracts.iter().enumerate() {
        execution += c.deployment_execution;
        tx += c.deployment_tx;
        println!(
            "| {} | {} | {} | {} | {} | {} | {}..{} | {} / {} | {} / {} |",
            if k == 0 {
                "driver".to_string()
            } else {
                format!("part {k}")
            },
            grouped(c.code_bytes as u64),
            grouped(c.init_bytes as u64),
            grouped(c.deployment_execution),
            grouped(c.deployment_tx),
            grouped(c.memory_words as u64),
            c.items.start,
            c.items.end,
            c.imports,
            c.exports,
            c.stack_in,
            c.stack_out
        );
    }
    println!(
        "| **all** | {} | | {} | **{}** | | | values region: {} words | |",
        grouped(r.code_bytes as u64),
        grouped(execution),
        grouped(tx),
        d.values
    );
    println!("| phase | execution gas |");
    println!("|---|---:|");
    for phase in &r.phases {
        println!("| {} | {} |", phase.phase, grouped(phase.gas));
    }
}
