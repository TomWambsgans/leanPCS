// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The Keccak VM (`KECCAK.md`): leanVM's `SHA3` table in BLAKE2S's place, proved by Flock on the Keccak-f block with
//! its structured terminal. Its contract against its Rust verifier, its stacks against WHIR's `2^28` words, and its gas
//! next to the BLAKE2s VM's.
//!
//! `cargo test --release -p leanvm_univariate --test keccak_vm`
//! `cargo test --release -p leanvm_univariate --test keccak_vm -- --ignored --nocapture keccak_gas_report`

use leanvm_statement::layout::N_TABLES;
use leanvm_statement::shapes::{PROGRAM_IV, WORKLOADS};
use leanvm_univariate::claims::Commitment;
use leanvm_univariate::contract::{GasReport, measure, measure_deployable, parity, record_verifier, sample_stream};
use leanvm_univariate::verifier::layouts_for;
use leanvm_univariate::{Blake2s, Claims, FLOCK_MAIN, KECCAK_MAIN, Shape};

/// One run of leanVM's Keccak VM (commit `9d50c92a3`, the last before its switch to GKR): `cargo leanvm aggregate
/// --xmss N --log-inv-rate 1`, the executed rows of each table (`Stats::base_counts`), the memory cells used and the
/// bytecode's instructions (`2^17.54`, padded to `2^18`). Run on a Mac (M-series), 2026-11-08.
struct KeccakRun {
    xmss: usize,
    rows: [u64; N_TABLES],
    memory_cells: u64,
}

/// Table rows in leanVM's order: XOR, MUL, SET, DEREF, JUMP, SHA3.
const KECCAK_RUNS: [KeccakRun; 4] = [
    KeccakRun {
        xmss: 32,
        rows: [6956, 9877, 6578, 9652, 3995, 4440],
        memory_cells: 184_479,
    },
    KeccakRun {
        xmss: 128,
        rows: [24260, 36229, 24626, 35812, 15509, 17712],
        memory_cells: 721_598,
    },
    KeccakRun {
        xmss: 400,
        rows: [73288, 110893, 75762, 109932, 48157, 55316],
        memory_cells: 2_243_324,
    },
    KeccakRun {
        xmss: 1000,
        rows: [181438, 275593, 188562, 273432, 120085, 138266],
        memory_cells: 5_600_312,
    },
];

const KECCAK_LOG_BYTECODE: usize = 18;

impl KeccakRun {
    fn shape(&self) -> Shape {
        Shape {
            log_memory: 64 - (self.memory_cells - 1).leading_zeros() as usize,
            log_bytecode: KECCAK_LOG_BYTECODE,
            table_rows: self.rows,
        }
    }
}

/// The largest proof stack (`C1`, `C2`) of `shape` under `blake2s`, in variables: WHIR takes at most 28.
fn largest_stack(shape: &Shape, blake2s: Blake2s) -> usize {
    layouts_for(shape, blake2s)
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

/// The contract computes what the Rust verifier computes, word for word, on sample streams: the claims it hands
/// `PCS_OPEN` and every value it checks (both modes, the smallest Keccak shape).
#[test]
fn keccak_contract_is_the_rust_verifier() {
    deep(|| {
        let shape = KECCAK_RUNS[0].shape();
        for mode in [Claims::Point, Claims::Weighted] {
            let recorded = record_verifier(&shape, Blake2s::Keccak(KECCAK_MAIN), mode);
            for seed in [1u64, 2] {
                let stream = sample_stream(recorded.stream_len, seed);
                parity(
                    &shape,
                    &PROGRAM_IV,
                    &[0x5a; 32],
                    &stream,
                    Blake2s::Keccak(KECCAK_MAIN),
                    mode,
                );
            }
        }
    });
}

/// The Keccak VM's stacks: `q_flock` is `2^11` words a permutation (one Keccak-f block a `SHA3` row), so `C1` fits
/// WHIR's `2^28` words up to `2^16` permutations: 400 signatures fit, 1,000 (138,266 permutations, `2^29` words of
/// `q_flock` alone) do not.
#[test]
fn keccak_stacks_against_whir() {
    for run in &KECCAK_RUNS {
        let vars = largest_stack(&run.shape(), Blake2s::Keccak(KECCAK_MAIN));
        println!("xmss {}: largest proof stack 2^{vars}", run.xmss);
        assert_eq!(vars <= 28, run.xmss <= 400, "xmss {}", run.xmss);
    }
}

fn row(label: &str, xmss: usize, report: &GasReport, stack: usize) -> String {
    format!(
        "| {label} | {xmss} | 2^{stack} | {} | {} | {} | {} / {} | {} | {} |",
        report.calldata_bytes,
        report.execution,
        report.field_muls,
        report.claims,
        report.calls,
        report.transaction(0, 40),
        report.transaction(5_000, 40),
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
            "| VM, hash argument | signatures | largest stack | calldata B | execution | FIELD_MUL | claims / calls | \
             tx EIP-7623 c = 0 | c = 5,000 |"
        );
        println!("|---|---:|---:|---:|---:|---:|---:|---:|---:|");
        let mut details = Vec::new();
        // The BLAKE2s VM, leanVM 42422001's measured shapes (the main line, Flock (a')).
        for workload in WORKLOADS.iter().filter(|w| [32, 128, 400, 1000].contains(&w.xmss)) {
            let shape = Shape::of(&workload.shape);
            let report = measure(&shape, &PROGRAM_IV, Blake2s::Flock(FLOCK_MAIN), Claims::Point);
            let stack = largest_stack(&shape, Blake2s::Flock(FLOCK_MAIN));
            println!(
                "{}",
                row("BLAKE2s VM (42422001), Flock (a')", workload.xmss, &report, stack)
            );
            if workload.xmss == 400 {
                details.push(("BLAKE2s VM, 400", report));
            }
        }
        // The Keccak VM, leanVM 9d50c92a3's shapes. Above 400 signatures C1 exceeds 2^28 (measured all the same: the
        // gas of a contract that no WHIR opening could serve).
        for run in &KECCAK_RUNS {
            let shape = run.shape();
            let report = measure(&shape, &PROGRAM_IV, Blake2s::Keccak(KECCAK_MAIN), Claims::Point);
            let stack = largest_stack(&shape, Blake2s::Keccak(KECCAK_MAIN));
            let label = if stack <= 28 {
                "Keccak VM (9d50c92a3 shapes), Flock Keccak-f"
            } else {
                "Keccak VM, Flock Keccak-f [C1 over 2^28: infeasible]"
            };
            println!("{}", row(label, run.xmss, &report, stack));
            // Isolating the hash argument: the same shape with the BLAKE2S table and BLAKE2s's Flock, and with none.
            let blake = measure(&shape, &PROGRAM_IV, Blake2s::Flock(FLOCK_MAIN), Claims::Point);
            let stack_b = largest_stack(&shape, Blake2s::Flock(FLOCK_MAIN));
            println!(
                "{}",
                row(
                    "  same shape, BLAKE2S table + its Flock (a')",
                    run.xmss,
                    &blake,
                    stack_b
                )
            );
            let none = measure(&shape, &PROGRAM_IV, Blake2s::Omitted, Claims::Point);
            println!(
                "{}",
                row(
                    "  same shape, BLAKE2S table, no hash argument",
                    run.xmss,
                    &none,
                    stack_b
                )
            );
            if run.xmss == 400 {
                details.push(("Keccak VM, 400", report));
                details.push(("Keccak shape 400, BLAKE2s argument", blake));
            }
        }
        for (name, report) in &details {
            println!(
                "\n### {name}: execution {} (code {} B)",
                report.execution, report.code_bytes
            );
            phases(report);
        }
        // Deployable: the Keccak contract cut into EIP-170 contracts.
        let shape = KECCAK_RUNS[2].shape();
        let deployable = measure_deployable(&shape, &PROGRAM_IV, Blake2s::Keccak(KECCAK_MAIN), Claims::Point, 24_576);
        println!(
            "\nKeccak VM, 400 signatures, deployable: {} contracts, execution {} (straight {}), tx EIP-7623 c = 0: {}",
            deployable.contracts.len(),
            deployable.report.execution,
            deployable.straight,
            deployable.report.transaction(0, 40),
        );
    });
}
