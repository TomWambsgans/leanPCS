// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! Keccak-256 as rows (SPEC-REC.md §2.4.1, §2.4.2): [`Sponge`], Keccak-256 over D16v's Keccak-f\[1600\] template
//! (`keccak16`): the first block's rate from the input bits and the padding (fresh constants), its capacity known zero;
//! later blocks XORed into the rate; the digest the first four lanes.

use leanvm_statement::field::K;

use super::keccak16::D16;
use super::layout::{Builder, PolyBuilder, Units, Value, forwards};
use super::spec::{Formula, Poly};

/// Keccak-256's rate, in lanes and bits.
pub const RATE_LANES: usize = 17;
pub const RATE_BITS: usize = 64 * RATE_LANES;

/// An output bit a permutation did not make (its lane is not read).
pub const UNMADE: Value = u32::MAX;

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
pub struct Sponge {
    pub permutation: D16,
    pub constants: Constants,
    pub xors: Xors,
    /// Permutations run.
    pub permutations: usize,
    /// The last rounds' planes not made, over the permutations (a last block whose caller reads fewer lanes than 25:
    /// D16v's 64 `k1` rows a plane).
    pub planes_unmade: usize,
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

impl Sponge {
    /// The sponge on D16v's permutation template, its rows' regions made first.
    pub fn new(b: &mut Builder) -> Self {
        Self {
            permutation: D16::new(b),
            constants: Constants::new(),
            xors: Xors::new(b),
            permutations: 0,
            planes_unmade: 0,
            runs: Vec::new(),
        }
    }

    /// Keccak-256 of `message` (bits in byte order, low bit first): the digest's 256 bits, likewise.
    pub fn keccak256(&mut self, b: &mut Builder, message: &[Bit]) -> Vec<Value> {
        self.keccak256_lanes(b, message, 4)
    }

    /// Keccak-256's sponge on `message`: its first `lanes` lanes after the last permutation (`4 ≤ lanes ≤ 17`: the
    /// digest, then the rest of the rate, `transcript::keccak256_rate`), `64 · lanes` bits in byte order.
    pub fn keccak256_lanes(&mut self, b: &mut Builder, message: &[Bit], lanes: usize) -> Vec<Value> {
        assert!((4..=RATE_LANES).contains(&lanes), "the digest's lanes and the rate's");
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
            // A later block reads the whole state; the last, the lanes asked for.
            let read = if block + 1 == blocks { lanes } else { 25 };
            state = self.permutation.permute(b, &mut self.constants, &input, read);
            self.runs.push(Run {
                rows: first_row..b.rows() as u32,
                input,
                output: state.clone(),
            });
            self.permutations += 1;
            self.planes_unmade += 5 - read.div_ceil(5);
        }
        let out = state[..64 * lanes].to_vec();
        assert!(!out.contains(&UNMADE), "the lanes asked for are made");
        out
    }
}
