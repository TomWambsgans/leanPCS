// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The workloads: leaf aggregates of leanXMSS signatures by leanVM's Keccak VM (commit `9d50c92a3`, the last before its
//! switch to GKR), `cargo leanvm aggregate --xmss N --log-inv-rate 1`, and the shapes their proofs announce. The
//! reference is 128 signatures ([`reference`]).

use crate::layout::BUS_BITS;
use crate::{N_TABLES, Shape};

/// The aggregation program's bytecode: `2^17.54` instructions, padded to `2^18`.
pub const LOG_BYTECODE: usize = 18;

/// The program IV the contracts and the committed vectors are built with. A contract parameter (any 32 bytes binds
/// the program); this value is leanVM 42422001's aggregation guest's Fiat–Shamir IV, kept so that the committed
/// vectors replay.
pub const PROGRAM_IV: [u8; 32] = [
    0xb5, 0x41, 0x04, 0x5c, 0x98, 0x65, 0x5d, 0xb5, 0xa8, 0xaa, 0xc6, 0x1e, 0xfd, 0xb0, 0xad, 0xea, 0x1e, 0xaf, 0xab,
    0x5f, 0x51, 0x02, 0xa4, 0xe3, 0xf9, 0x3d, 0xf9, 0xc7, 0x53, 0x27, 0x1e, 0x1e,
];

/// One run of the Keccak VM: the executed rows of each table (`Stats::base_counts`), the memory cells used. Run on a
/// Mac (M-series), 2026-11-08.
#[derive(Clone, Copy, Debug)]
pub struct Workload {
    pub name: &'static str,
    pub xmss: usize,
    pub shape: Shape,
    pub memory_cells: u64,
}

const fn workload(name: &'static str, xmss: usize, rows: [u64; N_TABLES], memory_cells: u64) -> Workload {
    Workload {
        name,
        xmss,
        shape: Shape {
            log_memory: 64 - (memory_cells - 1).leading_zeros() as u64,
            table_rows: rows,
            log_inv_rate: 1,
            bytecode_len: 1 << (LOG_BYTECODE + BUS_BITS),
        },
        memory_cells,
    }
}

/// Table rows in leanVM's order: XOR, MUL, SET, DEREF, JUMP, SHA3.
pub const WORKLOADS: [Workload; 4] = [
    workload("xmss32", 32, [6956, 9877, 6578, 9652, 3995, 4440], 184_479),
    workload("xmss128", 128, [24260, 36229, 24626, 35812, 15509, 17712], 721_598),
    workload("xmss400", 400, [73288, 110893, 75762, 109932, 48157, 55316], 2_243_324),
    workload("xmss1000", 1000, [181438, 275593, 188562, 273432, 120085, 138266], 5_600_312),
];

/// The reference workload: 128 signatures (memory `2^20`, bytecode `2^18`).
pub fn reference() -> &'static Workload {
    by_xmss(128)
}

/// The workload of `xmss` signatures.
pub fn by_xmss(xmss: usize) -> &'static Workload {
    WORKLOADS.iter().find(|w| w.xmss == xmss).expect("a workload")
}
