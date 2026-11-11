// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The EIP draft's PCS claim on the wire (`eip-draft_leanPCS.md`, `docs/PCS_CLAIM.md`): `version || n || root || ood
//! || point || value`, `82 + 24 n` bytes, an element of `E` in 24 bytes. The contracts pack claims in this format
//! ([`crate::Item::DeclaredClaim`]); `crates/pcs_claim` encodes, decodes and opens them.

/// The PCS version a claim's first byte names (the EIP draft's version `1`: leanVM's WHIR, `crates/pcs_claim`).
pub const VERSION: u8 = 1;

/// The EIP's bound on a claim's variables `n` (`MAX_PCS_VARIABLES`): a claim with more is not well-formed.
pub const MAX_PCS_VARIABLES: usize = 32;

/// The bytes of an element of `E`: the low 24 bytes of the word `FIELD_MUL` takes, big-endian.
pub const ELEMENT_BYTES: usize = 24;

/// The bytes of a claim on `n` variables: `82 + 24 n` (the version, `n`, the root, the out-of-domain answer, the
/// point, the value).
pub const fn claim_len(n: usize) -> usize {
    2 + 32 + ELEMENT_BYTES * (n + 2)
}

/// Whether `bytes` are a well-formed claim: version [`VERSION`], `1 <= n <= MAX_PCS_VARIABLES`, exactly
/// [`claim_len`]`(n)` bytes.
pub fn well_formed(bytes: &[u8]) -> bool {
    match bytes {
        [version, n, ..] => {
            let n = *n as usize;
            *version == VERSION && (1..=MAX_PCS_VARIABLES).contains(&n) && bytes.len() == claim_len(n)
        }
        _ => false,
    }
}
