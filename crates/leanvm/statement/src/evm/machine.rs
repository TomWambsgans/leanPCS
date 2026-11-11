// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The EVM the contracts run on: `evm_link`'s (revm with `FIELD_MUL`, EIP-8141's frame introspection over a frame of
//! PCS claims, per-instruction gas), and an element of [`E`] as a contract holds it.

pub use evm_link::machine::*;

use crate::field::E;

/// A field element as a contract holds it: limb 0 lowest, the top 64 bits zero (a claim encodes its low 24 bytes).
pub fn element_word(x: E) -> [u8; 32] {
    evm_link::op::word([x.c0, x.c1, x.c2])
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::field::F192;

    /// The machine's `FIELD_MUL` (`primitives`' product in `GF(2^192)`) is `E`'s product.
    #[test]
    fn field_mul_is_the_product_in_e() {
        let mut state = 0x2545_F491_4F6C_DD1Du64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for _ in 0..1000 {
            let (a, b) = ([next(), next(), next()], [next(), next(), next()]);
            let e = E::new(a[0], a[1], a[2]) * E::new(b[0], b[1], b[2]);
            let f = F192::new(a[0], a[1], a[2]) * F192::new(b[0], b[1], b[2]);
            assert_eq!([e.c0, e.c1, e.c2], [f.c0, f.c1, f.c2]);
        }
    }
}
