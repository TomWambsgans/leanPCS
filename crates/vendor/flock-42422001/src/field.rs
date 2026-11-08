// Part of this repository. The GF(2^8) field and its embedding φ₈ into F192, the two modules of leanVM's
// (https://github.com/leanEthereum/leanVM) `crates/primitives/src/field` at commit 42422001 that leanVM c445e3d5's
// `primitives` (crates/vendor/leanvm-c445e3d5), which this crate runs on, does not have; these lines are that
// `field/mod.rs`'s. MIT OR Apache-2.0 (see LICENSE-MIT, LICENSE-APACHE and AGENTS.md at the repository root).
//! - [`F8`]: GF(2^8) with AES polynomial x^8 + x^4 + x^3 + x + 1
//! - [`phi8_192`]: `φ₈: GF(2⁸) → F64 ⊂ F192`, and its table

pub mod gf2_8;
pub mod phi8_tower;

pub use gf2_8::F8;
pub use phi8_tower::{PHI_8_TABLE_192, phi8_192};
