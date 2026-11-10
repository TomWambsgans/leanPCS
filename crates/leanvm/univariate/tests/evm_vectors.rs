// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The Rust→EVM test vectors, replayed with no prover and no trace: each file of `tests/vectors/` holds a real Keccak
//! VM proof's calldata, the claims the contract checks (which the proof's WHIR openings prove), and the verdict and
//! gas it was recorded with. The straight contract and the deployable one (its parts of at most 24,576 bytes) are
//! built from the verifier for the vector's shape and configuration, then, the proof's calldata followed by the
//! frame byte ([`PCS_FRAME`]):
//!
//! - both accept the calldata, at the recorded gas, when its frame of PCS claims declares exactly the recorded claims,
//!   in order, and check exactly those;
//! - both revert on mutations: a byte of the stream flipped (a root, a Flock scalar, a value at `t`, a round of the
//!   batching sumcheck, the last byte), a row count changed, the public input changed, one claim left undeclared, a
//!   byte of a declared claim flipped.
//!
//! `cargo test --release -p leanvm_univariate --test evm_vectors -- --nocapture`; with `UPDATE_VECTOR_GAS=1` it
//! rewrites the vectors' two gas lines to what it measures, and nothing else.

mod vectors;

use leanvm_statement::evm::codegen::word;
use leanvm_statement::evm::machine::{PCS_FRAME, PcsFrame, call, root_of_word};
use leanvm_univariate::Claims;
use leanvm_univariate::contract::{SetupRoots, compile_verifier, record_verifier_with};
use vectors::{PROGRAM_IV, Vector, deployable, read, variant_of};

/// Run `f` on a thread with a deep stack: the code generator recurses along the graph.
fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

fn attesting(calls: &[Vec<u8>]) -> PcsFrame {
    let mut pcs = PcsFrame::default();
    for input in calls {
        pcs.declare(input.clone());
    }
    pcs
}

/// Calldata after the selector (4 bytes) and the public input (32): the stream.
const STREAM_AT: usize = 4 + 32;

/// Replay `v`: the gas it measures, straight and deployed.
fn replay(v: Vector) -> (u64, u64) {
    let variant = variant_of(&v.config);
    // The contract binds the proof's setup root `F` (the third call's: its program's and shape's own).
    let roots = SetupRoots {
        f: v.whir_roots[2],
    };
    let recorded = record_verifier_with(&v.shape, variant, Claims::Point, &roots);
    assert_eq!(STREAM_AT + recorded.stream_len, v.calldata.len(), "{}: the calldata is the shape's", v.config);
    let straight = compile_verifier(&recorded, &PROGRAM_IV, false);
    let deployed = deployable(&recorded);
    assert_eq!(deployed.contracts.len(), v.contracts, "{}: the deployable build's contracts", v.config);
    let one = word([1, 0, 0]);
    let block = attesting(&v.calls);
    let framed = |data: &[u8]| [data, &[PCS_FRAME]].concat();
    let run_straight = |data: &[u8], block: &PcsFrame| call(&straight.code, &[], &framed(data), block);
    let run_deployed = |data: &[u8], block: &PcsFrame| deployed.chain.call(deployed.address, &framed(data), block);

    let update = std::env::var_os("UPDATE_VECTOR_GAS").is_some();
    let mut measured = Vec::new();
    for (build, outcome, gas) in [
        ("straight", run_straight(&v.calldata, &block), v.gas_straight),
        ("deployed", run_deployed(&v.calldata, &block), v.gas_deployed),
    ] {
        assert_eq!(outcome.output.as_deref() == Some(&one[..]), v.accepts, "{} {build}: the verdict", v.config);
        assert_eq!(outcome.claims, v.calls, "{} {build}: the claims checked are the recorded ones", v.config);
        if !update {
            assert_eq!(outcome.execution, gas, "{} {build}: the gas of execution", v.config);
        }
        println!("{} {build}: accepts, {} gas of execution, {} claims", v.config, outcome.execution, v.calls.len());
        measured.push(outcome.execution);
    }
    // The roots the calls name, against the vector's committed roots (its
    // `whir_root`s, the prover's): `C1`'s and `C2`'s words, the stream's bytes, are their claims' root words
    // (`machine.rs` decodes them to those roots); the setup root's word is the hash as it is, which π2's
    // contract passes as its root word (`pi1_abi`).
    assert_eq!(v.whir_roots.len(), v.calls.len(), "{}: the vector has the committed roots", v.config);
    for (k, (input, root)) in v.calls.iter().zip(&v.whir_roots).enumerate() {
        let word: [u8; 32] = input[..32].try_into().expect("a root word");
        match k {
            0 | 1 => assert_eq!(&root_of_word(&word), root, "{}: call {k}'s word is its root's", v.config),
            _ => assert_eq!(&word, root, "{}: call {k}'s word is the setup's hash", v.config),
        }
        let abi: [u8; 32] = vectors::pi1_abi(input)[..32].try_into().expect("a root word");
        assert_eq!(&root_of_word(&abi), root, "{}: call {k} in machine.rs's ABI is of its root", v.config);
    }

    // Mutations, each of which both builds must revert on.
    let stream_len = recorded.stream_len;
    let mut mutants: Vec<(String, Vec<u8>, PcsFrame)> = Vec::new();
    let flip = |at: usize| {
        let mut data = v.calldata.clone();
        data[at] ^= 1;
        data
    };
    for (what, at) in [
        ("a row count", STREAM_AT + 3),
        ("C1's root", STREAM_AT + 24 + 5),
        ("a scalar a third in", STREAM_AT + stream_len / 3),
        ("a scalar half way", STREAM_AT + stream_len / 2),
        ("a batching round", STREAM_AT + stream_len - 200),
        ("the last byte", STREAM_AT + stream_len - 1),
        ("the public input", 4 + 7),
    ] {
        mutants.push((format!("{what} flipped"), flip(at), attesting(&v.calls)));
    }
    for k in 0..v.calls.len() {
        let mut calls = v.calls.clone();
        calls.remove(k);
        mutants.push((format!("claim {k} not declared"), v.calldata.clone(), attesting(&calls)));
        let mut calls = v.calls.clone();
        let last = calls[k].len() - 1;
        calls[k][last] ^= 1;
        mutants.push((format!("claim {k}'s declared value flipped"), v.calldata.clone(), attesting(&calls)));
    }
    for (what, data, block) in &mutants {
        assert!(run_straight(data, block).output.is_none(), "{} straight: {what} must revert", v.config);
        assert!(run_deployed(data, block).output.is_none(), "{} deployed: {what} must revert", v.config);
    }
    println!("{}: {} mutations revert on both builds", v.config, mutants.len());
    (measured[0], measured[1])
}

/// Every vector file, replayed.
#[test]
fn vectors_replay_on_both_builds() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/vectors");
    let mut files: Vec<_> = std::fs::read_dir(&dir)
        .expect("tests/vectors")
        .map(|e| e.expect("an entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "txt"))
        .collect();
    files.sort();
    assert!(!files.is_empty(), "the vectors are committed");
    for path in files {
        let text = std::fs::read_to_string(&path).expect("a vector");
        let v = read(&text);
        println!("{}: {} calldata bytes", path.display(), v.calldata.len());
        let (straight, deployed) = deep(move || replay(v));
        if std::env::var_os("UPDATE_VECTOR_GAS").is_some() {
            // The two gas lines only: the proof, its claims and its roots are the prover's.
            let text: String = text
                .lines()
                .map(|line| match line.split_once(' ') {
                    Some(("gas_straight", _)) => format!("gas_straight {straight}\n"),
                    Some(("gas_deployed", _)) => format!("gas_deployed {deployed}\n"),
                    _ => format!("{line}\n"),
                })
                .collect();
            std::fs::write(&path, text).expect("the vector rewritten");
        }
    }
}
