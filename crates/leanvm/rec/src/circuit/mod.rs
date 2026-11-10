// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! `π2`'s circuit (SPEC-REC.md §2.3–§2.5, milestone R2): the PIOP-facing description ([`spec`]), the layout framework
//! ([`layout`]), Keccak-f and Keccak-256 ([`keccak`]: the sponge; [`keccak16`]: D16v's template), the small units ([`units`]).
//! The compiler ([`compile`]) makes the circuit and its witness; [`plan`] replays the witness on any stream, made once
//! per circuit.

pub mod compile;
pub mod keccak;
pub mod keccak16;
pub mod layout;
pub mod plan;
pub mod spec;
pub mod units;

#[cfg(test)]
mod tests;
