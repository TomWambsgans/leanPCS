// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The vectors of `formal/UniStatement/UniStatementTest/KeccakTables.lean`: the Keccak VM's six tables
//! (`layout::tables_keccak`) as the verifier reads them, their columns, their flushes' forms term by term in the
//! map's order, and each column's `q_flock` word (`keccak_slot`) and offset (`keccak_slot_offset`). One record a line:
//! `table <opcode> <width>`, `col <name> <slot or -> <offset hex>`, `push <k> <form> ; <form> ; …` and
//! `pull <k> …`, a form `<monomial>=<c0>:<c1>:<c2>` (hex limbs, the monomial's columns joined by `.`, `c` the
//! constant), terms separated by one space, `0` the empty form.
//!
//! `cargo test --release -p leanvm_statement --test lean_keccak_tables -- --nocapture`

use leanvm_statement::layout::{Form, keccak_slot, keccak_slot_offset, tables};

fn form_text(f: &Form) -> String {
    let terms: Vec<String> = f
        .terms()
        .map(|(mono, c)| {
            let m = if mono.is_empty() {
                "c".to_string()
            } else {
                mono.iter().map(|i| i.to_string()).collect::<Vec<_>>().join(".")
            };
            format!("{m}={:x}:{:x}:{:x}", c.c0, c.c1, c.c2)
        })
        .collect();
    if terms.is_empty() { "0".into() } else { terms.join(" ") }
}

#[test]
fn vectors() {
    let mut lines = Vec::new();
    for t in tables() {
        lines.push(format!("table {} {}", t.opcode, t.width()));
        for name in t.columns {
            let slot = keccak_slot(name).map_or("-".to_string(), |s| s.to_string());
            lines.push(format!("col {name} {slot} {:x}", keccak_slot_offset(name)));
        }
        for (side, tuples) in [("push", &t.flushes.push), ("pull", &t.flushes.pull)] {
            for (k, tuple) in tuples.iter().enumerate() {
                let forms: Vec<String> = tuple.iter().map(form_text).collect();
                lines.push(format!("{side} {k} {}", forms.join(" ; ")));
            }
        }
    }
    for l in &lines {
        println!("{l}");
    }
}
