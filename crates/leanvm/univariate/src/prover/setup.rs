// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The setup commitment `F` (SPEC.md §3), computed from what it is fixed by: the program (leanVM's stacked bytecode)
//! and the shape (the memory's and the bytecode's sizes). Its commitment (root and out-of-domain answer) is what a
//! contract is generated with (SPEC.md §13, F2): [`shape_roots`].
//!
//! It is committed as every stack is (`opening::commit`: the EIP draft's PCS version 1, `crates/pcs_claim`).

use fiat_shamir::merkle::Hash;
use primitives::field::F64;
use quotient::ntt::Fill;

use super::columns::SetupPolys;
use super::opening;
use super::stack::{Stack, setup_columns};
use crate::claims::Column;
use crate::stacks::StackLayout;
use crate::verifier::Shape;

/// `F`'s stack: the 16 tuple slots interleaved (word `slot + 16 k`, `k` a basis-`B` coefficient), the addresses.
pub fn f_stack(shape: &Shape, setup: &SetupPolys) -> Stack {
    let n = 1usize << shape.log_bytecode;
    let tuple: Vec<F64> = parallel::map_collect(16 * n, |i| setup.slots[i % 16].b[i / 16]);
    Stack::filled(
        StackLayout::new(&setup_columns(shape)),
        &[
            (Column::BytecodeTuple, 0, Fill::Words(&tuple)),
            (Column::Address, 0, Fill::Words(&setup.address.b)),
        ],
    )
}

/// The roots a contract is built with (the contract's type: its IV binds them, SPEC.md §13, F2).
pub use crate::contract::SetupRoots;

/// `F`'s root for `shape` and the program whose setup polynomials are `setup`.
pub fn f_root(shape: &Shape, setup: &SetupPolys) -> Hash {
    shape_roots(shape, setup).f
}

/// The setup commitment of `shape`'s contract: `F`'s root and out-of-domain answer.
pub fn shape_roots(shape: &Shape, setup: &SetupPolys) -> SetupRoots {
    let f = f_stack(shape, setup);
    let committed = opening::commit(&f.words, f.layout.vars);
    SetupRoots {
        f: committed.root,
        f_ood: super::poly::to_v(committed.ood),
    }
}

/// A root as 64 hex digits.
pub fn hex(root: &Hash) -> String {
    root.iter().map(|b| format!("{b:02x}")).collect()
}
