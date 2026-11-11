// Part of this repository. Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch
// PCS-openings-aggregation, commit 651453c6, crates/flock/src/membership.rs (`Statement`, `Secret`),
// with the Keccak-256 statement (new here). MIT OR Apache-2.0; see AGENTS.md.
//! The statement: `y = H(x | 0x11^32)`, and a Merkle path of depth [`DEPTH`] from `H(x | 0x22^32)` up to
//! `root`, with `H` = Keccak-256 (Ethereum's `keccak256`) of a 64-byte block.

use primitives::field::F64;
use primitives::hash::hash as keccak256;

pub const DEPTH: usize = 32;

/// The domain constants the leaf and `y` are hashed with.
pub const Y_PAD: u8 = 0x11;
pub const LEAF_PAD: u8 = 0x22;

/// `H(left | right)`.
pub fn pair(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    keccak256(&[*left, *right].concat())
}

/// The public values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Statement {
    pub y: [u8; 32],
    pub root: [u8; 32],
}

impl Statement {
    /// `y` then `root`, each as its four [`words`]: the eight `K`-words the circuit packs its public bits into and
    /// the verifier pins (`quotient::protocol`).
    pub fn words(&self) -> [F64; 8] {
        let ([a, b, c, d], [e, f, g, h]) = (words(&self.y), words(&self.root));
        [a, b, c, d, e, f, g, h]
    }
}

/// What the prover knows. Bit `i` of `directions` says the sibling is on the left at level `i`.
#[derive(Clone, Debug)]
pub struct Secret {
    pub x: [u8; 32],
    pub siblings: [[u8; 32]; DEPTH],
    pub directions: u32,
}

impl Secret {
    /// The statement this secret proves, by hashing natively.
    pub fn statement(&self) -> Statement {
        let leaf = pair(&self.x, &[LEAF_PAD; 32]);
        let root = self.siblings.iter().enumerate().fold(leaf, |node, (i, sibling)| {
            if (self.directions >> i) & 1 == 1 {
                pair(sibling, &node)
            } else {
                pair(&node, sibling)
            }
        });
        Statement {
            y: pair(&self.x, &[Y_PAD; 32]),
            root,
        }
    }
}

/// A 32-byte value as four `K`-words, eight bytes each read as a big-endian number: bit `j` of word `k` is bit
/// `j % 8` of byte `8 k + 7 - j / 8`.
pub fn words(bytes: &[u8; 32]) -> [F64; 4] {
    std::array::from_fn(|k| F64(u64::from_be_bytes(bytes[8 * k..8 * k + 8].try_into().unwrap())))
}
