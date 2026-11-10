// Part of this repository. The round constants, rotations and lane permutation are Keccak's (FIPS 202), as in this
// repository's crates/vendor/leanvm-c445e3d5/primitives/src/hash.rs (vendored from leanVM) and used by crates/membership/quotient/src/circuit.rs, whose
// Keccak-f wiring (lane `x + 5y`, bit `z` at index `z`, lane `i` rotated by `RHO[i]` to `PI[i]`) this follows. MIT OR
// Apache-2.0; see AGENTS.md.
//! Keccak-f\[1600\] and Keccak-256 as rows (SPEC-REC.md §2.4.1, §2.4.2): the round constants, the [`Permutation`]
//! interface D16v's template implements (`keccak16`), and [`Sponge`], Keccak-256 over any [`Permutation`]: the first
//! block's rate from the input bits and the padding (fresh constants), its capacity known zero; later blocks XORed
//! into the rate; the digest the first four lanes.

use leanvm_statement::field::K;

use super::layout::{Builder, PolyBuilder, Units, Value, forwards};
use super::spec::{Formula, Poly};

/// The round constants.
pub const RC: [u64; 24] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808A,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808B,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008A,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000A,
    0x0000_0000_8000_808B,
    0x8000_0000_0000_008B,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800A,
    0x8000_0000_8000_000A,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

/// ρ's left rotation of lane `x + 5y`.
pub const RHO: [usize; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

/// Where π sends lane `x + 5y`: lane `y + 5·((2x + 3y) mod 5)`.
pub const PI: [usize; 25] = {
    let mut p = [0usize; 25];
    let mut i = 0;
    while i < 25 {
        let (x, y) = (i % 5, i / 5);
        p[i] = y + 5 * ((2 * x + 3 * y) % 5);
        i += 1;
    }
    p
};

/// Keccak-256's rate, in lanes and bits.
pub const RATE_LANES: usize = 17;
pub const RATE_BITS: usize = 64 * RATE_LANES;

/// Keccak-f\[1600\] in rows.
pub trait Permutation {
    /// The permutation of `input` (index `64·lane + z`), whose constant bits it makes from `constants` (after
    /// offering its rows' spare slots to it). Returns the output's 1600 values.
    fn permute(&mut self, b: &mut Builder, constants: &mut Constants, input: &[Bit]) -> Vec<Value>;
}

/// Fresh constants: one expression slot each, pushing `κ` (its pull is a free end). The slots are other regions'
/// spare roles (formula 0) when offered, else rows of their own.
pub struct Constants {
    units: Option<Units>,
    spare: Vec<(u32, usize)>,
    /// Constants made, and the rows of their own.
    pub made: usize,
    pub own_rows: usize,
}

/// A spare role: an expression slot pushing 0, which a constant may take (`κ`) or which stays dead.
pub fn spare() -> Formula {
    Formula::Expr(Poly::default())
}

impl Constants {
    pub fn new() -> Self {
        Self {
            units: None,
            spare: Vec::new(),
            made: 0,
            own_rows: 0,
        }
    }

    /// Offer a spare role (its formula [`spare`]).
    pub fn offer(&mut self, row: u32, role: usize) {
        self.spare.push((row, role));
    }

    /// A new value of word `k`.
    pub fn fresh(&mut self, b: &mut Builder, k: K) -> Value {
        self.made += 1;
        let (row, role) = match self.spare.pop() {
            Some(slot) => slot,
            None => {
                let units = self.units.get_or_insert_with(|| {
                    let w = b.width();
                    let r = b.region("const", (0..w).map(|_| spare()).collect());
                    Units::new(r, 1, w)
                });
                let (row, role) = units.next(b);
                if role == 0 {
                    self.own_rows += 1;
                }
                (row, role)
            }
        };
        b.set_kappa(row, role, k);
        b.produce(row, role)
    }
}

impl Default for Constants {
    fn default() -> Self {
        Self::new()
    }
}

/// One input bit of a Keccak-256 call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Bit {
    /// A value that may end at the permutation's slot (it has no other slot placement).
    V(Value),
    Zero,
    One,
}

/// XOR units for the later blocks: `a ⊕ b` at the slot reading its own pull `a` and the forward `b`.
pub struct Xors {
    units: Units,
}

impl Xors {
    pub fn new(b: &mut Builder) -> Self {
        let w = b.width();
        let mut roles = forwards(w);
        for u in 0..w / 2 {
            roles[2 * u] = Formula::Expr(PolyBuilder::new().linear(2 * u, 1).linear(2 * u + 1, 1).build());
        }
        let r = b.region("xor", roles);
        Self {
            units: Units::new(r, 2, w / 2),
        }
    }

    /// `a ⊕ b`: `a` ends here, `b` is forwarded.
    pub fn xor(&mut self, bld: &mut Builder, a: Value, b: Value) -> Value {
        let (row, base) = self.units.next(bld);
        bld.place(row, base, a);
        bld.place(row, base + 1, b);
        bld.produce(row, base)
    }
}

/// Keccak-256's sponge on rows.
pub struct Sponge<P: Permutation> {
    pub permutation: P,
    pub constants: Constants,
    pub xors: Xors,
    /// Permutations run.
    pub permutations: usize,
    /// Each permutation run: its rows, input and output (for the witness plan, `super::plan`).
    pub runs: Vec<Run>,
}

/// A permutation run: the creation rows `rows` it made (consecutive), its input and its output values.
#[derive(Clone, Debug)]
pub struct Run {
    pub rows: std::ops::Range<u32>,
    pub input: Vec<Bit>,
    pub output: Vec<Value>,
}

impl<P: Permutation> Sponge<P> {
    pub fn new(b: &mut Builder, permutation: P) -> Self {
        Self {
            permutation,
            constants: Constants::new(),
            xors: Xors::new(b),
            permutations: 0,
            runs: Vec::new(),
        }
    }

    /// Keccak-256 of `message` (bits in byte order, low bit first): the digest's 256 bits, likewise.
    pub fn keccak256(&mut self, b: &mut Builder, message: &[Bit]) -> Vec<Value> {
        assert!(message.len().is_multiple_of(8), "whole bytes");
        let blocks = message.len() / RATE_BITS + 1;
        let padded_len = blocks * RATE_BITS;
        // pad10*1: 0x01 after the message, 0x80 in the last byte.
        let bit_of = |i: usize| -> Bit {
            if i < message.len() {
                message[i]
            } else if i == message.len() || i == padded_len - 1 {
                Bit::One
            } else {
                Bit::Zero
            }
        };
        let mut state: Vec<Value> = Vec::new();
        for block in 0..blocks {
            let mut input: Vec<Bit> = vec![Bit::Zero; 1600];
            for (i, slot) in input.iter_mut().enumerate().take(RATE_BITS) {
                let bit = bit_of(block * RATE_BITS + i);
                *slot = if block == 0 {
                    bit
                } else {
                    Bit::V(match bit {
                        Bit::V(v) => self.xors.xor(b, state[i], v),
                        Bit::Zero => state[i],
                        Bit::One => {
                            let one = self.constants.fresh(b, K(1));
                            self.xors.xor(b, state[i], one)
                        }
                    })
                };
            }
            if block > 0 {
                for i in RATE_BITS..1600 {
                    input[i] = Bit::V(state[i]);
                }
            }
            let first_row = b.rows() as u32;
            state = self.permutation.permute(b, &mut self.constants, &input);
            self.runs.push(Run {
                rows: first_row..b.rows() as u32,
                input,
                output: state.clone(),
            });
            self.permutations += 1;
        }
        state[..256].to_vec()
    }
}

/// Keccak-f\[1600\] on lanes, the reference.
pub fn keccak_f(a: &mut [u64; 25]) {
    for &rc in &RC {
        let c: [u64; 5] = std::array::from_fn(|x| (0..5).fold(0, |acc, y| acc ^ a[x + 5 * y]));
        for i in 0..25 {
            a[i] ^= c[(i + 4) % 5] ^ c[(i + 1) % 5].rotate_left(1);
        }
        let mut b = [0u64; 25];
        for i in 0..25 {
            b[PI[i]] = a[i].rotate_left(RHO[i] as u32);
        }
        for y in 0..5 {
            for x in 0..5 {
                a[x + 5 * y] = b[x + 5 * y] ^ (!b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]);
            }
        }
        a[0] ^= rc;
    }
}
