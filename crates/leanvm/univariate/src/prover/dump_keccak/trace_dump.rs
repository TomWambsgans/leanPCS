// Part of PCS-openings-aggregation (crates/leanvm/univariate/src/prover/dump_keccak), not of leanVM, and not a module
// of that crate: `apply.sh` copies it into a leanVM (https://github.com/leanEthereum/leanVM) tree at commit 9d50c92a3
// (the Keccak VM, docs/leanvm/univariate/KECCAK.md) as crates/leanvm_core/src/cpu/trace_dump.rs. MIT OR Apache-2.0;
// see NOTICE.md.
//! The execution trace of a run, written for the univariate prover's Keccak VM (`docs/leanvm/univariate/KECCAK.md`):
//! when `LEANVM_TRACE_DUMP` names a directory, [`maybe_dump`] runs the program again **without the fill blocks**
//! (`cpu::filler`), writes the run's rows, memory and counts there, and exits the process.
//!
//! **The fill.** leanVM 9d50c92a3 brings every table to a power of two by executing fill cycles after the program
//! halts, `SHA3` to a quarter rule with a dummy zero-state step on every fourth row (its three-steps-a-block Flock
//! layout). The univariate PIOP handles padding rows itself (they sit at `domain::active_positions`' complement, their
//! leaves are 1), so the dump is the run of the program alone: `program.filler` emptied, the interpreter halts at the
//! sentinel and stops. The memory's and the bytecode's final counts are then the counts of exactly the rows dumped,
//! and the fill cycles' frames are never allocated. The interpreter still reorders the `SHA3` rows
//! (`hash_flock::interleave_dummies`, when their count is a multiple of four): a permutation of executed rows, which the
//! bus, a multiset, does not see.
//!
//! - `meta.txt`: `vm keccak-9d50c92a3`, `log_mem`, `log_bytecode`, `rows` (six: the executed rows), `taus` (six:
//!   `ceil(log2(rows))`), `pi` (the two public cells, three limbs each), `columns n`, then `column i len committed`;
//! - `columns.bin`: the columns, each its `len` words, 8 little-endian bytes a word: the memory's three limbs and its
//!   final counts (`2^log_mem` each), the bytecode's final counts (`2^log_bytecode`), then each table's columns
//!   (`leanvm_core::tables` order, `SHA3`'s fifty lanes included), its executed rows only;
//! - `bytecode.bin`: the stacked bytecode (`layout::bytecode_table`), 8 little-endian bytes a word.
//!
//! `q_flock` is not written: the prover builds it from the `SHA3` rows (one Keccak-f block a row,
//! `lv42_flock::keccak`).

use std::fmt::Write as _;
use std::io::Write as _;

use primitives::field::{F64, F192};

use super::Program;

pub(crate) fn maybe_dump(program: &Program, public_input: [F192; 2]) {
    let Some(dir) = std::env::var_os("LEANVM_TRACE_DUMP") else {
        return;
    };
    let started = std::time::Instant::now();
    let dir = std::path::PathBuf::from(dir);
    std::fs::create_dir_all(&dir).expect("the dump directory");
    // The program without its fill blocks: the run stops at the halt.
    let mut bare = program.clone();
    bare.filler = Vec::new();
    let exec = bare.execute(public_input).expect("the program runs without its fill blocks");
    assert!(exec.unconstrained_reads.is_empty(), "the run reads cells nothing wrote");
    let tr = &exec.trace;
    let rows = tr.row_counts();
    assert_eq!(rows, exec.base_counts, "no fill ran: the rows are the program's own");
    let cells = exec.mem.len();
    let log_mem = crate::log2_strict_usize(cells);
    let log_bytecode = crate::log2_strict_usize(program.prog.len());
    let gpow = primitives::field::g_powers(cells.max(program.prog.len()));

    let mut columns: Vec<Vec<F64>> = Vec::new();
    columns.push(exec.mem.iter().map(|w| F64(w.c0)).collect());
    columns.push(exec.mem.iter().map(|w| F64(w.c1)).collect());
    columns.push(exec.mem.iter().map(|w| F64(w.c2)).collect());
    columns.push(tr.mem_count.clone());
    columns.push(tr.bytecode_count.clone());
    assert_eq!(tr.mem_count.len(), cells);
    assert_eq!(tr.bytecode_count.len(), program.prog.len());
    for (t, table) in crate::tables::tables().iter().enumerate() {
        let n = table.n_committed_columns();
        let mut out: Vec<Vec<F64>> = (0..n).map(|_| vec![F64::ZERO; rows[t]]).collect();
        let mut windows: Vec<&mut [F64]> = out.iter_mut().map(|c| &mut c[..]).collect();
        let ctx = crate::tables::FillCtx::new(tr, &exec.mem, &gpow, &program.prog, rows[t]);
        crate::tables::fill_table(*table, &ctx, &mut windows);
        columns.extend(out);
    }

    let join = |v: &[usize]| v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ");
    let taus = rows.map(|r| r.next_power_of_two().trailing_zeros() as usize);
    let mut meta = String::new();
    writeln!(meta, "vm keccak-9d50c92a3").unwrap();
    writeln!(meta, "log_mem {log_mem}").unwrap();
    writeln!(meta, "log_bytecode {log_bytecode}").unwrap();
    writeln!(meta, "rows {}", join(&rows)).unwrap();
    writeln!(meta, "taus {}", join(&taus)).unwrap();
    let [a, b] = [exec.mem[0], exec.mem[1]];
    assert_eq!([a, b], public_input, "memory cells 0 and 1 are the public input");
    writeln!(meta, "pi {} {} {} {} {} {}", a.c0, a.c1, a.c2, b.c0, b.c1, b.c2).unwrap();
    writeln!(meta, "cycles {}", exec.cycles).unwrap();
    writeln!(meta, "mem_used {}", exec.mem_used).unwrap();
    writeln!(meta, "columns {}", columns.len()).unwrap();
    for (i, column) in columns.iter().enumerate() {
        writeln!(meta, "column {i} {} committed", column.len()).unwrap();
    }
    std::fs::write(dir.join("meta.txt"), meta).expect("meta.txt");
    let mut out = std::io::BufWriter::with_capacity(1 << 24, std::fs::File::create(dir.join("columns.bin")).unwrap());
    for column in &columns {
        for chunk in column.chunks(1 << 16) {
            let bytes: Vec<u8> = chunk.iter().flat_map(|x| x.0.to_le_bytes()).collect();
            out.write_all(&bytes).expect("columns.bin");
        }
    }
    out.flush().expect("columns.bin");
    let table = super::layout::bytecode_table(&program.prog);
    let bytes: Vec<u8> = table.iter().flat_map(|x| x.0.to_le_bytes()).collect();
    std::fs::write(dir.join("bytecode.bin"), bytes).expect("bytecode.bin");
    eprintln!(
        "trace dumped to {} in {:.2} s: rows {rows:?}, memory 2^{log_mem}, bytecode 2^{log_bytecode}, {} cycles",
        dir.display(),
        started.elapsed().as_secs_f64(),
        exec.cycles
    );
    std::process::exit(0);
}
