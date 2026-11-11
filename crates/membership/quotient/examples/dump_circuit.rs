// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The membership circuit as bytes, for the differential test against its Lean transcription
//! (`formal/Circuit`, `lake exe dump-circuit`, which writes the same format): `cargo run --release -p quotient
//! --example dump_circuit -- OUT`, then compare the two files' SHA-256.
//!
//! The format, little-endian `u32`s: the number of rows, the rows used, the number of inputs; each row's `X, Y, C`
//! sources (`0` zero, `1` one, `2` three, `3` free, `4 + r` row `r`); the input rows; σ. It then prints the public
//! words the circuit computes for a fixed secret (its anchors' cells), next to the statement's.

use quotient::circuit::{PUBLIC_WORDS, Src, anchor_cell, membership, membership_inputs};
use quotient::statement::Secret;

fn code(src: Src) -> u32 {
    match src {
        Src::Zero => 0,
        Src::One => 1,
        Src::Three => 2,
        Src::Free => 3,
        Src::Row(r) => r + 4,
    }
}

fn main() {
    let path = std::env::args().nth(1).expect("usage: dump_circuit OUT");
    let circuit = membership();
    println!(
        "rows {} used {} inputs {} sigma {}",
        circuit.rows.len(),
        circuit.used_rows,
        circuit.inputs.len(),
        circuit.sigma.len()
    );
    let mut out: Vec<u8> =
        Vec::with_capacity(4 * (3 + 3 * circuit.rows.len() + circuit.inputs.len() + circuit.sigma.len()));
    let mut push = |x: u32| out.extend_from_slice(&x.to_le_bytes());
    push(circuit.rows.len() as u32);
    push(circuit.used_rows as u32);
    push(circuit.inputs.len() as u32);
    for row in &circuit.rows {
        push(code(row.x));
        push(code(row.y));
        push(code(row.c));
    }
    for &r in &circuit.inputs {
        push(r);
    }
    for &s in &circuit.sigma {
        push(s);
    }
    std::fs::write(&path, &out).expect("write");

    // The secret `CircuitTest/Dump.lean` uses.
    let secret = Secret {
        x: std::array::from_fn(|i| (i * 37 + 11) as u8),
        siblings: std::array::from_fn(|l| std::array::from_fn(|i| (l * 101 + i * 13 + 5) as u8)),
        directions: 0xA5C3_1E77,
    };
    let cells = circuit.cells(&membership_inputs(&secret));
    let words = secret.statement().words();
    for (k, word) in words.iter().enumerate().take(PUBLIC_WORDS) {
        println!("word {k}: circuit {:016x} statement {:016x}", cells[anchor_cell(k)].0, word.0);
    }
}
