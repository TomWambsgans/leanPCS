// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The Rust→EVM test vectors (`tests/vectors/*.txt`): a real proof's calldata (without the frame byte a verifying call
//! appends), the PCS claims the contract checks declared (which the proof's openings prove), the verdict and the gas.
//! Written by `tests/prove_real.rs` (`WRITE_VECTORS=<dir>`), replayed by `tests/evm_vectors.rs` with no prover and no
//! trace.
//!
//! The format is lines of `key value`, the bytes in lowercase hex: `config`, `shape` (`log_memory log_bytecode` and
//! the six row counts), `public`, `calldata`, one `claim` line per claim in order (the EIP draft's PCS claim as
//! encoded, `crates/pcs_claim`: its commitment's root and out-of-domain answer, as the prover committed them, the
//! point and the value; written by the prover's run, the claims its openings prove), `accepts`, `gas_straight` (the
//! contract's execution gas); `#` starts a comment.

#![allow(dead_code)]

use leanvm_univariate::{KECCAK_MAIN, KECCAK_REC3, KECCAK_REC4, Shape, Variant};

/// The program's IV the vectors' contracts are built with (`leanvm_statement::shapes::PROGRAM_IV`).
#[allow(unused_imports)]
pub use leanvm_statement::shapes::PROGRAM_IV;

pub struct Vector {
    pub config: String,
    pub shape: Shape,
    pub public: [u8; 32],
    pub calldata: Vec<u8>,
    /// The PCS claims, encoded, in the contract's order (`C1`, `C2`, the setup `F`).
    pub claims: Vec<Vec<u8>>,
    pub accepts: bool,
    pub gas_straight: u64,
    /// What the proof is of, written as a comment line under the header (not read back).
    pub note: String,
}

/// The configurations by name: `keccak` the Keccak VM's main line (`KECCAK_MAIN`), `keccak_rec3` its π1-rec3
/// (`KECCAK_REC3`), `keccak_rec4` its π1-rec4 (`KECCAK_REC4`, the recursion's (`docs/leanvm/univariate/SPEC.md` §14.4)).
pub fn variant_of(config: &str) -> Variant {
    match config {
        "keccak" => KECCAK_MAIN,
        "keccak_rec3" => KECCAK_REC3,
        "keccak_rec4" => KECCAK_REC4,
        other => panic!("no configuration {other}"),
    }
}

pub fn name_of(variant: Variant) -> &'static str {
    match variant {
        v if v == KECCAK_MAIN => "keccak",
        v if v == KECCAK_REC3 => "keccak_rec3",
        v if v == KECCAK_REC4 => "keccak_rec4",
        _ => "keccak_other",
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn unhex(text: &str) -> Vec<u8> {
    assert!(text.len().is_multiple_of(2), "whole bytes");
    (0..text.len() / 2)
        .map(|i| u8::from_str_radix(&text[2 * i..2 * i + 2], 16).expect("hex"))
        .collect()
}

pub fn write(v: &Vector) -> String {
    let mut out = String::new();
    if v.note.is_empty() {
        out.push_str("# leanvm_univariate Rust->EVM test vector (tests/vectors/mod.rs): a real proof, 1,000 leanXMSS signatures\n");
    } else {
        out.push_str("# leanvm_univariate Rust->EVM test vector (tests/vectors/mod.rs): a real proof\n");
        out.push_str(&format!("# {}\n", v.note));
    }
    out.push_str(&format!("config {}\n", v.config));
    let rows: Vec<String> = v.shape.table_rows.iter().map(u64::to_string).collect();
    out.push_str(&format!("shape {} {} {}\n", v.shape.log_memory, v.shape.log_bytecode, rows.join(" ")));
    out.push_str(&format!("public {}\n", hex(&v.public)));
    out.push_str(&format!("calldata {}\n", hex(&v.calldata)));
    for claim in &v.claims {
        out.push_str(&format!("claim {}\n", hex(claim)));
    }
    out.push_str(&format!("accepts {}\n", v.accepts));
    out.push_str(&format!("gas_straight {}\n", v.gas_straight));
    out
}

pub fn read(text: &str) -> Vector {
    let mut v = Vector {
        config: String::new(),
        shape: Shape {
            log_memory: 0,
            log_bytecode: 0,
            table_rows: [0; 6],
        },
        public: [0; 32],
        calldata: Vec::new(),
        claims: Vec::new(),
        accepts: false,
        gas_straight: 0,
        note: String::new(),
    };
    for line in text.lines().filter(|l| !l.starts_with('#') && !l.is_empty()) {
        let (key, value) = line.split_once(' ').expect("key value");
        match key {
            "config" => v.config = value.to_string(),
            "shape" => {
                let n: Vec<u64> = value.split(' ').map(|x| x.parse().expect("a number")).collect();
                v.shape = Shape {
                    log_memory: n[0] as usize,
                    log_bytecode: n[1] as usize,
                    table_rows: n[2..8].try_into().expect("six counts"),
                };
            }
            "public" => v.public = unhex(value).try_into().expect("32 bytes"),
            "calldata" => v.calldata = unhex(value),
            "claim" => v.claims.push(unhex(value)),
            "accepts" => v.accepts = value == "true",
            "gas_straight" => v.gas_straight = value.parse().expect("a number"),
            other => panic!("no key {other}"),
        }
    }
    v
}

/// The setup commitment a vector's contract binds: its setup claim's (the third), `F`'s root and out-of-domain
/// answer, its program's and shape's own.
pub fn setup_roots(v: &Vector) -> leanvm_univariate::contract::SetupRoots {
    let claim = pcs_claim::PcsClaim::decode(&v.claims[2]).expect("a well-formed setup claim");
    leanvm_univariate::contract::SetupRoots {
        f: claim.root,
        f_ood: leanvm_statement::field::E::new(claim.ood.c0, claim.ood.c1, claim.ood.c2),
    }
}
