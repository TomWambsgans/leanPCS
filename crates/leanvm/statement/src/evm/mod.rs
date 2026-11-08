// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The EVM toolchain: a verifier run on the recorder's symbolic scalar ([`record::Sym`]) gives its graph, compiled
//! to straight-line EVM code ([`codegen`], through `evm_link`), run on revm with `FIELD_MUL` and a mock `PCS_OPEN`
//! ([`machine`]), deployed or installed ([`deploy`]).

pub mod codegen;
pub mod deploy;
pub mod kernel;
pub mod machine;
pub mod record;
