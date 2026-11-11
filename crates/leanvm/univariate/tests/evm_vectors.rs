// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The Rust→EVM test vectors, replayed with no prover and no trace: each file of `tests/vectors/` holds a real Keccak
//! VM proof's calldata, the claims the contract checks (which the proof's WHIR openings prove), and the verdict and
//! gas it was recorded with. The contract is built from the verifier for the vector's shape and configuration, then,
//! the proof's calldata followed by the frame byte ([`PCS_FRAME`]):
//!
//! - it accepts the calldata, at the recorded gas, when its frame of PCS claims declares exactly the recorded claims,
//!   in order, and checks exactly those; their commitments are the stream's (`C1`'s and `C2`'s roots and
//!   out-of-domain answers) and the contract's (`F`);
//! - it reverts on mutations: a byte of the stream flipped (a root, an out-of-domain answer, a Flock scalar, a value at
//!   `t`, a round of the batching sumcheck, the last byte), a row count changed, the public input changed, one claim
//!   left undeclared, a byte of a declared claim flipped.
//!
//! A π1-rec4 vector (`keccak*_rec4`, `FsShape::Rec4`: no EVM contract of its own, its wide draws are no `KECCAK256`;
//! π2's circuit runs its verifier) is replayed by the Rust verifier instead: it gives exactly the recorded claims, and
//! the stream's mutations change them or are rejected. A vector holds no opening proofs (nor does π1's contract check
//! any: the frame declares the claims, the block proves them), so the claims' three WHIR openings are verified where
//! the vector is written: `tests/prove_real.rs` (`prover::prove::verify`: the reduction and each opening's WHIR proof
//! against its claim, the claims the openings' own), on the real trace; π2's by `leanvm_rec`'s `tests/pi2_real.rs`.
//!
//! `cargo test --release -p leanvm_univariate --test evm_vectors -- --nocapture`; with `UPDATE_VECTOR_GAS=1` it
//! rewrites the vectors' `gas_straight` line to what it measures, and nothing else.

mod vectors;

use leanvm_statement::evm::machine::{PCS_FRAME, PcsFrame, call};
use leanvm_univariate::Claims;
use leanvm_univariate::contract::{compile_verifier, expected_claims, record_verifier_with, rust_verifier_with};
use vectors::{PROGRAM_IV, Vector, read, setup_roots, variant_of};

/// Run `f` on a thread with a deep stack: the code generator recurses along the graph.
fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

fn attesting(claims: &[Vec<u8>]) -> PcsFrame {
    PcsFrame::of(claims.iter().cloned())
}

/// A vector's calldata after its selector (4 bytes, [`vectors::SELECTOR`]) and the public input (32): the stream.
const STREAM_AT: usize = 4 + 32;

/// Replay `v`: the gas it measures.
fn replay(v: Vector) -> u64 {
    let variant = variant_of(&v.config);
    // The contract binds the proof's setup commitment `F` (the third claim's: its program's and shape's own).
    let roots = setup_roots(&v);
    let recorded = record_verifier_with(&v.shape, variant, Claims::Point, &roots);
    assert_eq!(STREAM_AT + recorded.stream_len, v.calldata.len(), "{}: the calldata is the shape's", v.config);
    if variant.fs.wide() {
        // π1-rec4: the Rust verifier, its checks held to account, gives the recorded claims; a flipped stream byte or
        // public input byte fails a check or changes a claim.
        let claims_of = |data: &[u8]| -> Option<Vec<Vec<u8>>> {
            let public: [u8; 32] = data[4..36].try_into().unwrap();
            let stream = &data[STREAM_AT..];
            let (reduced, zero, nonzero) =
                rust_verifier_with(&v.shape, &PROGRAM_IV, &roots, &public, stream, variant, Claims::Point).ok()?;
            let holds = zero.iter().all(|x| *x == Default::default()) && nonzero.iter().all(|x| *x != Default::default());
            holds.then(|| expected_claims(&recorded, &reduced, stream).iter().map(|c| c.encode()).collect())
        };
        assert_eq!(claims_of(&v.calldata), Some(v.claims.clone()), "{}: the Rust verifier's claims", v.config);
        let len = recorded.stream_len;
        let ats = [3, 24 + 5, 24 + 32 + 3, len / 3, len / 2, len - 200, len - 80, len - 1].map(|at| STREAM_AT + at);
        for at in ats.into_iter().chain([4 + 7]) {
            let mut data = v.calldata.clone();
            data[at] ^= 1;
            assert_ne!(claims_of(&data), Some(v.claims.clone()), "{}: calldata byte {at} flipped", v.config);
        }
        println!("{}: the Rust verifier gives its {} claims; 9 mutations change them", v.config, v.claims.len());
        assert_eq!(v.gas_straight, 0, "{}: no contract, no gas", v.config);
        return 0;
    }
    let straight = compile_verifier(&recorded, &PROGRAM_IV, false);
    let block = attesting(&v.claims);
    // The contract's calldata: the vector's after its selector, then the frame's index.
    let framed = |data: &[u8]| {
        assert_eq!(data[..4], vectors::SELECTOR);
        [&data[4..], &[PCS_FRAME]].concat()
    };
    let run_straight = |data: &[u8], block: &PcsFrame| call(&straight.code, &[], &framed(data), block);

    let update = std::env::var_os("UPDATE_VECTOR_GAS").is_some();
    let outcome = run_straight(&v.calldata, &block);
    assert_eq!(outcome.attests(), v.accepts, "{}: the verdict", v.config);
    assert_eq!(outcome.claims, v.claims, "{}: the claims checked are the recorded ones", v.config);
    if !update {
        assert_eq!(outcome.execution, v.gas_straight, "{}: the gas of execution", v.config);
    }
    println!("{}: accepts, {} gas of execution, {} claims", v.config, outcome.execution, v.claims.len());
    // The claims' commitments: `C1`'s and `C2`'s roots are the stream's 32 bytes as they are, their out-of-domain
    // answers the stream's 24 bytes after them (the prover's commitments); the setup's is `F`'s.
    assert_eq!(v.claims.len(), 3, "{}: one claim per commitment", v.config);
    for (k, claim) in v.claims.iter().enumerate() {
        let decoded = pcs_claim::PcsClaim::decode(claim).expect("a well-formed claim");
        if k < 2 {
            let at = STREAM_AT + recorded.roots_at[k];
            assert_eq!(&v.calldata[at..at + 32], &decoded.root, "{}: claim {k}'s root is the stream's", v.config);
            assert_eq!(
                &v.calldata[at + 32..at + 56],
                &pcs_claim::element_bytes(decoded.ood),
                "{}: claim {k}'s out-of-domain answer is the stream's",
                v.config
            );
        } else {
            assert_eq!(decoded.root, roots.f, "{}: the setup claim's root is F's", v.config);
        }
    }

    // Mutations, each of which it must revert on.
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
        ("C1's out-of-domain answer", STREAM_AT + 24 + 32 + 3),
        ("a scalar a third in", STREAM_AT + stream_len / 3),
        ("a scalar half way", STREAM_AT + stream_len / 2),
        ("a batching round", STREAM_AT + stream_len - 200),
        ("the last byte", STREAM_AT + stream_len - 1),
        ("the public input", 4 + 7),
    ] {
        mutants.push((format!("{what} flipped"), flip(at), attesting(&v.claims)));
    }
    for k in 0..v.claims.len() {
        let mut claims = v.claims.clone();
        claims.remove(k);
        mutants.push((format!("claim {k} not declared"), v.calldata.clone(), attesting(&claims)));
        let mut claims = v.claims.clone();
        let last = claims[k].len() - 1;
        claims[k][last] ^= 1;
        mutants.push((format!("claim {k}'s declared value flipped"), v.calldata.clone(), attesting(&claims)));
        let mut claims = v.claims.clone();
        claims[k][34] ^= 1;
        mutants.push((format!("claim {k}'s declared out-of-domain answer flipped"), v.calldata.clone(), attesting(&claims)));
    }
    for (what, data, block) in &mutants {
        assert!(run_straight(data, block).output.is_none(), "{}: {what} must revert", v.config);
    }
    println!("{}: {} mutations revert", v.config, mutants.len());
    outcome.execution
}

/// Every vector file, replayed.
#[test]
fn vectors_replay() {
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
        let straight = deep(move || replay(v));
        if std::env::var_os("UPDATE_VECTOR_GAS").is_some() {
            // The gas line only: the proof, its claims and its roots are the prover's.
            let text: String = text
                .lines()
                .map(|line| match line.split_once(' ') {
                    Some(("gas_straight", _)) => format!("gas_straight {straight}\n"),
                    _ => format!("{line}\n"),
                })
                .collect();
            std::fs::write(&path, text).expect("the vector rewritten");
        }
    }
}
