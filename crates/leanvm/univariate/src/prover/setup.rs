// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The setup commitment `F` (SPEC.md §3), computed from what it is fixed by: the program (leanVM's stacked bytecode)
//! and the shape (the memory's and the bytecode's sizes). Its root is what a contract is generated with (SPEC.md §13,
//! F2): [`shape_roots`].
//!
//! They are committed as every stack is (`opening::commit`: leanVM's WHIR at `c445e3d5`, rate `1/2`, 64 lanes).

use fiat_shamir::merkle::Hash;
use primitives::field::F64;

use super::columns::SetupPolys;
use super::opening;
use super::stack::{Stack, setup_columns};
use crate::claims::Column;
use crate::stacks::StackLayout;
use crate::verifier::Shape;

/// `F`'s stack: the 16 tuple slots interleaved (word `slot + 16 k`, `k` a basis-`B` coefficient), the addresses.
pub fn f_stack(shape: &Shape, setup: &SetupPolys) -> Stack {
    let mut stack = Stack::new(StackLayout::new(&setup_columns(shape)));
    let n = 1usize << shape.log_bytecode;
    let tuple: Vec<F64> = (0..16 * n).map(|i| setup.slots[i % 16].b[i / 16]).collect();
    stack.put_k(Column::BytecodeTuple, &tuple);
    stack.put_k(Column::Address, &setup.address.b);
    stack
}

/// The roots a contract is built with (the contract's type: its IV binds them, SPEC.md §13, F2).
pub use crate::contract::SetupRoots;

/// `F`'s root for `shape` and the program whose setup polynomials are `setup`.
pub fn f_root(shape: &Shape, setup: &SetupPolys) -> Hash {
    let f = f_stack(shape, setup);
    opening::commit(&f.words, f.layout.vars, f.placed()).root
}

/// The roots of `shape`'s contract: `F`'s, and the two fixed words (`SetupRoots::REFERENCE`'s, the same for every
/// shape).
pub fn shape_roots(shape: &Shape, setup: &SetupPolys) -> SetupRoots {
    SetupRoots {
        f: f_root(shape, setup),
        ..SetupRoots::REFERENCE
    }
}

/// A root as 64 hex digits.
pub fn hex(root: &Hash) -> String {
    root.iter().map(|b| format!("{b:02x}")).collect()
}
