// Part of this repository. Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch
// PCS-openings-aggregation, commit 651453c6, crates/flock/src/quotient/circuit.rs: the wiring is the same; the
// gate (one χ on bits instead of a full adder on GF(4)), the Keccak-256 statement, the anchors with the packing of
// the public words and the random rows' shapes are new; the gate's roles swapped (`docs/membership/PROTOCOL.md`, so
// that the verifier needs three of the row's values at `t`, not four). MIT OR Apache-2.0; see AGENTS.md.
//! Rows of one gate and the permutation that wires them, and the circuit of the membership statement.
//!
//! **The gate.** A row has four cells, `X, Y, C, V`, and says `V = Y + C + X·C`. On bits that is
//! `Y ⊕ (C ∧ ¬X)`: Keccak's χ when `(X, Y, C)` are `(a[x+1], a[x], a[x+2])`, an XOR when `X = 0`, a NOT when
//! `X = 0, Y = 1`. A free input bit is a row whose three inputs are wired to its own output, so the gate reads
//! `v = v + v + v^2`, that is `v^2 = v`. Every other row reads constants or rows before it, and the gate sends
//! bits to bits: by induction every cell is a bit, and the one the circuit computes.
//!
//! The product is of the row's first cell `X` (role 0, the cell the copy argument reads at `t`) and `C` (role 2), the
//! rest is `V + Y`: the verifier needs the row's values at `t` only through `X`, `C` and `V + Y`, three linear forms
//! of the row's four polynomials that one claim of the witness table binds ([`crate::protocol`]).
//!
//! **The public values** are eight `K`-words ([`crate::statement::Statement::words`]), each packed from its 64
//! bits by 63 rows of Horner's rule (`(X, Y, C) = (3, b, acc)`: `V = b + 2 acc`, `2` the generator of `K`'s
//! polynomial basis, so the word is the number its bits spell), built after every other row. The first
//! [`PUBLIC_ROWS`] rows are **anchors**: anchor `k` is `(0, 0, s_k)`, its `C` cell on the cycle of `s_k`, the
//! packed word `k` for `k < 8`, then the constants `0`, `1` and `3`, whose anchors read their constant as `Y` too:
//! `(0, 1, 1)` and `(0, 3, 3)`. The verifier pins the anchors' `C` cells to those values ([`anchor_cell`],
//! `crate::protocol`), which pins every cell on their cycles.
//!
//! **Every cycle of more than one cell holds a cell that is neither a row's first (`X`) cell nor a pinned one**,
//! outside the random rows ([`Circuit::errors_have_their_own_poles`], which [`crate::protocol::Index::new`]
//! asserts): the protocol's soundness needs it. A row's output cycle holds its `V` cell; the zero's holds the anchors'
//! `Y` cells; the one's and the three's hold their anchors' `Y` cells, which is why those anchors read their constant
//! twice. No random row carries the condition.

use primitives::field::F64;
use primitives::hash::{PI, RC, RHO, ROUNDS, STATE_LANES};

use crate::statement::{DEPTH, LEAF_PAD, Secret, Y_PAD};

/// The anchor rows, the first rows of the circuit: one a public word, then one a constant (`0`, `1`, `3`).
pub const PUBLIC_ROWS: usize = PUBLIC_WORDS + 3;
/// The public `K`-words, of [`WORD_BITS`] bits each.
pub const PUBLIC_WORDS: usize = 8;
pub const WORD_BITS: usize = 64;
/// The constant the packing rows read as `X`: `V = Y + C + 3 C = Y + 2 C`.
pub const THREE: F64 = F64(3);

/// The cell the verifier pins for anchor `k`: its `C` cell (`X` cells are the gate's rows, which the pins avoid).
pub const fn anchor_cell(k: usize) -> usize {
    4 * k + 2
}

/// The values of the anchors' cells: the public words, then the constants `0`, `1`, `3`.
pub fn anchor_values(words: &[F64; PUBLIC_WORDS]) -> [F64; PUBLIC_ROWS] {
    std::array::from_fn(|k| match k {
        _ if k < PUBLIC_WORDS => words[k],
        8 => F64::ZERO,
        9 => F64::ONE,
        _ => THREE,
    })
}
/// The membership circuit's rows: `2^LOG_ROWS`.
pub const LOG_ROWS: usize = 22;

/// The **random rows**: idle rows the builder turns into rows of two free cells ([`Src::Free`], each its own cycle),
/// the last ones of the circuit, of three shapes in turn ([`RandomShape`]): `(0, r, s, r +
/// s)`, `(s, r, 0, r)`, `(1, r, s, r)`. A witness leaves them zero; the prover fills each with two fresh random
/// values ([`Circuit::randomize`], `PROTOCOL.md`, "Zero knowledge"), which every cell of the row depends on affinely: they make the
/// witness table's evaluations and out-of-domain answer uniform, and its root hide.
pub const RANDOM_ROWS: usize = 16;
/// The random words a proof draws for them.
pub const RANDOM_WORDS: usize = 2 * RANDOM_ROWS;

/// The shapes of the random rows, `(X, Y, C, V)` for the words `(r, s)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RandomShape {
    /// `(0, r, s, r + s)`.
    Sum,
    /// `(s, r, 0, r)`.
    Select,
    /// `(1, r, s, r)`.
    Pass,
}

impl RandomShape {
    /// The shape of the `k`-th random row.
    pub fn of(k: usize) -> Self {
        [Self::Sum, Self::Select, Self::Pass][k % 3]
    }

    fn row(self) -> Row {
        let (x, y, c) = match self {
            Self::Sum => (Src::Zero, Src::Free, Src::Free),
            Self::Select => (Src::Free, Src::Free, Src::Zero),
            Self::Pass => (Src::One, Src::Free, Src::Free),
        };
        Row { x, y, c }
    }

    /// The row's four cells for its words.
    pub fn cells(self, r: F64, s: F64) -> [F64; 4] {
        match self {
            Self::Sum => [F64::ZERO, r, s, r + s],
            Self::Select => [s, r, F64::ZERO, r],
            Self::Pass => [F64::ONE, r, s, r],
        }
    }
}

/// What a cell reads: a constant, row `r`'s `V` cell, or nothing (a free cell, its own cycle).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Src {
    Zero,
    One,
    /// The constant [`THREE`], which the packing rows read.
    Three,
    Row(u32),
    /// A cell on a cycle of its own: any value (the random rows').
    Free,
}

/// One gate: `V = Y + C + X·C`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Row {
    pub x: Src,
    pub y: Src,
    pub c: Src,
}

const IDLE: Row = Row {
    x: Src::Zero,
    y: Src::Zero,
    c: Src::Zero,
};

/// The gate on bits: `y ⊕ (c ∧ ¬x)`.
pub fn gate_bits(x: u8, y: u8, c: u8) -> u8 {
    y ^ (c & !x & 1)
}

/// A lane of 64 wires, bit `z` at index `z`.
type Lane = [Src; 64];
type State = [Lane; STATE_LANES];

pub struct Circuit {
    pub log_rows: usize,
    /// Rows the gates use, the public ones included; the rest are idle.
    pub used_rows: usize,
    pub rows: Vec<Row>,
    /// The rows that are free input bits, in the order [`Circuit::cells`] takes them.
    pub inputs: Vec<u32>,
    /// Each cell's successor on its cycle. Cell `4 r + role`, the roles `X, Y, C, V`.
    pub sigma: Vec<u32>,
    /// The packing rows `[start, start + len)`: `K`-valued, evaluated by [`Circuit::cells`] over `K`.
    pub packing: (usize, usize),
}

pub struct Builder {
    rows: Vec<Row>,
    inputs: Vec<u32>,
}

impl Default for Builder {
    fn default() -> Self {
        Self::new()
    }
}

impl Builder {
    pub fn new() -> Self {
        Self::with_capacity(PUBLIC_ROWS)
    }

    /// A builder with room for `rows` rows, so that a large circuit's rows are not copied as they grow.
    pub fn with_capacity(rows: usize) -> Self {
        let mut all = Vec::with_capacity(rows.max(PUBLIC_ROWS));
        all.resize(PUBLIC_ROWS, IDLE);
        Self {
            rows: all,
            inputs: Vec::new(),
        }
    }

    /// Rows used so far, the public ones included.
    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    pub fn row(&mut self, x: Src, y: Src, c: Src) -> Src {
        self.rows.push(Row { x, y, c });
        Src::Row(self.rows.len() as u32 - 1)
    }

    /// A free bit: a row reading its own output three times, which the gate then makes `0` or `1`.
    pub fn input(&mut self) -> Src {
        let at = Src::Row(self.rows.len() as u32);
        self.inputs.push(self.rows.len() as u32);
        self.row(at, at, at)
    }

    pub fn not(&mut self, a: Src) -> Src {
        match a {
            Src::Zero => Src::One,
            Src::One => Src::Zero,
            _ => self.row(Src::Zero, Src::One, a),
        }
    }

    pub fn xor(&mut self, a: Src, b: Src) -> Src {
        match (a, b) {
            (Src::Zero, v) | (v, Src::Zero) => v,
            (Src::One, v) | (v, Src::One) => self.not(v),
            _ => self.row(Src::Zero, a, b),
        }
    }

    /// `a ⊕ (¬b ∧ c)`, Keccak's χ, in one row unless a constant makes it cheaper.
    pub fn chi(&mut self, a: Src, b: Src, c: Src) -> Src {
        match (b, c) {
            (Src::One, _) | (_, Src::Zero) => a,
            (Src::Zero, _) => self.xor(a, c),
            (_, Src::One) => {
                let not_b = self.not(b);
                self.xor(a, not_b)
            }
            _ => self.row(b, a, c),
        }
    }

    /// Keccak-f\[1600\]: lane `x + 5y`, bit `z` of a lane at index `z`.
    pub fn keccak_f(&mut self, mut a: State) -> State {
        for &rc in RC.iter().take(ROUNDS) {
            // θ: the column parities, then each lane XORed with its two neighbours' columns.
            let mut c = [[Src::Zero; 64]; 5];
            for x in 0..5 {
                for z in 0..64 {
                    let mut acc = a[x][z];
                    for y in 1..5 {
                        acc = self.xor(acc, a[x + 5 * y][z]);
                    }
                    c[x][z] = acc;
                }
            }
            let mut d = [[Src::Zero; 64]; 5];
            for x in 0..5 {
                for z in 0..64 {
                    d[x][z] = self.xor(c[(x + 4) % 5][z], c[(x + 1) % 5][(z + 63) % 64]);
                }
            }
            for (i, lane) in a.iter_mut().enumerate() {
                for z in 0..64 {
                    lane[z] = self.xor(lane[z], d[i % 5][z]);
                }
            }
            // ρ and π: wiring only. Lane `i`, rotated left by `RHO[i]`, goes to `PI[i]`.
            let mut b = [[Src::Zero; 64]; STATE_LANES];
            for i in 0..STATE_LANES {
                let r = RHO[i] as usize;
                for z in 0..64 {
                    b[PI[i]][(z + r) % 64] = a[i][z];
                }
            }
            // χ: one row a bit.
            for y in 0..5 {
                for x in 0..5 {
                    for z in 0..64 {
                        a[x + 5 * y][z] =
                            self.chi(b[x + 5 * y][z], b[(x + 1) % 5 + 5 * y][z], b[(x + 2) % 5 + 5 * y][z]);
                    }
                }
            }
            // ι: a NOT where the round constant has a one.
            for z in 0..64 {
                if (rc >> z) & 1 == 1 {
                    a[0][z] = self.not(a[0][z]);
                }
            }
        }
        a
    }

    /// Keccak-256 of a 64-byte block, its bits in byte order and low bit first; the digest likewise.
    pub fn keccak256_64(&mut self, message: &[Src]) -> Vec<Src> {
        assert_eq!(message.len(), 512);
        let mut state: State = [[Src::Zero; 64]; STATE_LANES];
        for (b, &bit) in message.iter().enumerate() {
            state[b / 64][b % 64] = bit;
        }
        // Keccak's padding of a 64-byte message in one 136-byte block: 0x01 at byte 64, 0x80 at byte 135.
        state[8][0] = Src::One;
        state[16][63] = Src::One;
        let out = self.keccak_f(state);
        (0..256).map(|b| out[b / 64][b % 64]).collect()
    }

    /// Close the circuit on `2^log_rows` rows, `public[J][j]` being bit `j` of public word `J`: the packing rows
    /// after every row built, the anchors in the first [`PUBLIC_ROWS`] rows, the random rows last.
    pub fn finish(mut self, log_rows: usize, public: &[Vec<Src>; PUBLIC_WORDS]) -> Circuit {
        assert!(public.iter().all(|word| word.len() == WORD_BITS));
        let n = 1 << log_rows;
        let packing_start = self.rows.len();
        let mut words = [Src::Zero; PUBLIC_WORDS];
        for (word, bits) in words.iter_mut().zip(public) {
            let mut acc = bits[WORD_BITS - 1];
            for &bit in bits[..WORD_BITS - 1].iter().rev() {
                acc = self.row(Src::Three, bit, acc);
            }
            *word = acc;
        }
        let packing = (packing_start, self.rows.len() - packing_start);
        let used_rows = self.rows.len();
        assert!(used_rows <= n, "{used_rows} rows");
        let sources = [&words[..], &[Src::Zero, Src::One, Src::Three]].concat();
        for (row, &c) in self.rows[..PUBLIC_ROWS].iter_mut().zip(&sources) {
            // A constant's anchor reads it as `Y` too, a cell of its cycle that is neither an `X` cell nor pinned.
            let y = if matches!(c, Src::One | Src::Three) { c } else { Src::Zero };
            *row = Row { x: Src::Zero, y, c };
        }
        assert!(used_rows + RANDOM_ROWS <= n, "room for the random rows");
        self.rows.resize(n, IDLE);
        for (k, r) in (n - RANDOM_ROWS..n).rev().enumerate() {
            self.rows[r] = RandomShape::of(k).row();
        }

        // A cycle is a source and the cells reading it, in cell order.
        const NONE: u32 = u32::MAX;
        let slot = |src: Src| match src {
            Src::Zero => Some(0),
            Src::One => Some(1),
            Src::Three => Some(2),
            Src::Row(r) => Some(3 + r as usize),
            Src::Free => None,
        };
        let mut first = vec![NONE; n + 3];
        let mut last = vec![NONE; n + 3];
        let mut sigma: Vec<u32> = (0..4 * n as u32).collect();
        let mut join = |at: usize, cell: u32, sigma: &mut Vec<u32>| {
            if first[at] == NONE {
                first[at] = cell;
            } else {
                sigma[last[at] as usize] = cell;
            }
            last[at] = cell;
            sigma[cell as usize] = first[at];
        };
        for r in 0..n {
            join(3 + r, 4 * r as u32 + 3, &mut sigma);
        }
        for (r, row) in self.rows.iter().enumerate() {
            for (role, src) in [row.x, row.y, row.c].into_iter().enumerate() {
                if let Some(at) = slot(src) {
                    join(at, (4 * r + role) as u32, &mut sigma);
                }
            }
        }
        Circuit {
            log_rows,
            used_rows,
            rows: self.rows,
            inputs: self.inputs,
            sigma,
            packing,
        }
    }
}

/// The bit a source holds, given every row's output (a free cell and the constant three read as `0`: the bits
/// are not the packing rows' values, which [`Circuit::cells`] takes over `K`).
pub fn read(v: &[u8], src: Src) -> u8 {
    match src {
        Src::Zero | Src::Three | Src::Free => 0,
        Src::One => 1,
        Src::Row(r) => v[r as usize],
    }
}

impl Circuit {
    /// The [`RANDOM_ROWS`] rows, from the last: the `k`-th is of shape [`RandomShape::of`]`(k)`.
    pub fn random_rows(&self) -> Vec<usize> {
        (self.rows.len() - RANDOM_ROWS..self.rows.len()).rev().collect()
    }

    /// Whether every cycle of the wiring but a lone cell's holds a cell that is neither a row's first (`X`) cell nor
    /// a pinned one ([`anchor_cell`]), nor a cell of a random row: what the protocol's soundness asks of the circuit,
    /// independently of the rows that make it zero knowledge. The protocol's identity sets the sum's polynomial, at
    /// the `X` cells and the pinned ones, to the logarithmic derivative plus a multiple of the gate's or the pin's
    /// error over `d d'`; walking a cycle from a cell of neither kind, each error is then the only term with a pole on
    /// the line of its cell, so the sum vanishes identically in `α, β` only if every error is zero
    /// (`crate::protocol`, `docs/membership/PROTOCOL.md`).
    pub fn errors_have_their_own_poles(&self) -> bool {
        let pinned = |cell: usize| cell % 4 == 2 && cell / 4 < PUBLIC_ROWS;
        let mut random = vec![false; self.rows.len()];
        self.random_rows().into_iter().for_each(|r| random[r] = true);
        let mut seen = vec![false; self.sigma.len()];
        for start in 0..self.sigma.len() {
            if seen[start] {
                continue;
            }
            let (mut at, mut len, mut free) = (start, 0, false);
            while !seen[at] {
                seen[at] = true;
                len += 1;
                free |= at % 4 != 0 && !pinned(at) && !random[at / 4];
                at = self.sigma[at] as usize;
            }
            if len > 1 && !free {
                return false;
            }
        }
        true
    }

    /// Fill the random rows of `cells` with `words`, two a row (`PROTOCOL.md`, "Zero knowledge").
    pub fn randomize(&self, cells: &mut [F64], words: &[F64; RANDOM_WORDS]) {
        for (k, r) in self.random_rows().into_iter().enumerate() {
            let row = RandomShape::of(k).cells(words[2 * k], words[2 * k + 1]);
            cells[4 * r..4 * r + 4].copy_from_slice(&row);
        }
    }

    pub fn n_inputs(&self) -> usize {
        self.inputs.len()
    }

    /// Every row's output bit, from the free inputs (the packing rows' and the anchors' are not bits: see
    /// [`Circuit::cells`]).
    pub fn outputs(&self, inputs: &[bool]) -> Vec<u8> {
        assert_eq!(inputs.len(), self.inputs.len());
        let mut v = vec![0u8; self.rows.len()];
        for (&row, &input) in self.inputs.iter().zip(inputs) {
            v[row as usize] = input as u8;
        }
        // A row reads rows before it, or itself; the public rows read the outputs.
        for r in (PUBLIC_ROWS..self.rows.len()).chain(0..PUBLIC_ROWS) {
            let row = self.rows[r];
            v[r] = gate_bits(read(&v, row.x), read(&v, row.y), read(&v, row.c));
        }
        v
    }

    /// Every cell's value, from the free inputs: the rows' bits, then the packing rows and the anchors over `K`.
    pub fn cells(&self, inputs: &[bool]) -> Vec<F64> {
        let bits = self.outputs(inputs);
        let mut v: Vec<F64> = parallel::map_collect(bits.len(), |r| F64(bits[r] as u64));
        let (start, len) = self.packing;
        for r in (start..start + len).chain(0..PUBLIC_ROWS) {
            let row = self.rows[r];
            v[r] = gate_k(read_k(&v, row.x), read_k(&v, row.y), read_k(&v, row.c));
        }
        self.cells_k(&v)
    }
}

/// The `K` value a source holds, given every row's output (a free cell's is the witness's `0`).
pub fn read_k(v: &[F64], src: Src) -> F64 {
    match src {
        Src::Zero | Src::Free => F64::ZERO,
        Src::One => F64::ONE,
        Src::Three => THREE,
        Src::Row(r) => v[r as usize],
    }
}

/// The gate over `K`: `y + c + x·c`.
pub fn gate_k(x: F64, y: F64, c: F64) -> F64 {
    y + c + x * c
}

impl Circuit {
    /// Every cell's value over `K`, from every row's output.
    pub fn cells_k(&self, v: &[F64]) -> Vec<F64> {
        assert_eq!(v.len(), self.rows.len());
        parallel::map_collect(4 * self.rows.len(), |cell| {
            let row = self.rows[cell / 4];
            match cell % 4 {
                0 => read_k(v, row.x),
                1 => read_k(v, row.y),
                2 => read_k(v, row.c),
                _ => v[cell / 4],
            }
        })
    }

    /// Whether `cells` satisfy every row's gate and are constant on every cycle of the wiring; else the first
    /// row whose gate fails, or the first cell that differs from its successor.
    pub fn check_k(&self, cells: &[F64]) -> Result<(), CheckError> {
        assert_eq!(cells.len(), 4 * self.rows.len());
        if let Some(r) = (0..self.rows.len()).find(|&r| {
            let [x, y, c, v] = std::array::from_fn(|role| cells[4 * r + role]);
            gate_k(x, y, c) != v
        }) {
            return Err(CheckError::Gate(r));
        }
        if let Some(cell) = (0..cells.len()).find(|&i| cells[self.sigma[i] as usize] != cells[i]) {
            return Err(CheckError::Wiring(cell));
        }
        Ok(())
    }
}

/// Why cells are not a witness of a circuit ([`Circuit::check_k`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CheckError {
    /// The row's gate fails.
    Gate(usize),
    /// The cell differs from its successor on its cycle.
    Wiring(usize),
}

/// The 256 wires of `y` and of `root` (32 bytes each, bit `i` bit `i % 8` of byte `i / 8`) to the eight public
/// words they are read as ([`crate::statement::words`]): a word is eight bytes, big-endian.
pub fn public_words(y: &[Src], root: &[Src]) -> [Vec<Src>; PUBLIC_WORDS] {
    std::array::from_fn(|word| {
        let (bytes, chunk) = (if word < 4 { y } else { root }, word % 4);
        (0..WORD_BITS)
            .map(|j| bytes[8 * (8 * chunk + 7 - j / 8) + j % 8])
            .collect()
    })
}

fn constant_block(byte: u8) -> Vec<Src> {
    (0..256)
        .map(|i| {
            if (byte >> (i % 8)) & 1 == 1 {
                Src::One
            } else {
                Src::Zero
            }
        })
        .collect()
}

/// The membership statement: `y = H(x | 0x11..)`, and the path from `H(x | 0x22..)` up to `root`.
pub fn membership() -> Circuit {
    let mut b = Builder::new();
    let x: Vec<Src> = (0..256).map(|_| b.input()).collect();
    let y = b.keccak256_64(&[&x[..], &constant_block(Y_PAD)].concat());
    let mut node = b.keccak256_64(&[&x[..], &constant_block(LEAF_PAD)].concat());
    for _ in 0..DEPTH {
        let sibling: Vec<Src> = (0..256).map(|_| b.input()).collect();
        let direction = b.input();
        // χ negates its middle input, so `left = node ⊕ (direction ∧ differ)` reads `¬direction` there.
        let keep = b.not(direction);
        let (mut left, mut right) = (Vec::with_capacity(256), Vec::with_capacity(256));
        for i in 0..256 {
            let differ = b.xor(node[i], sibling[i]);
            let l = b.chi(node[i], keep, differ);
            right.push(b.xor(l, differ));
            left.push(l);
        }
        node = b.keccak256_64(&[left, right].concat());
    }
    b.finish(LOG_ROWS, &public_words(&y, &node))
}

/// The free inputs of [`membership`] for a secret.
pub fn membership_inputs(secret: &Secret) -> Vec<bool> {
    let bits = |bytes: &[u8; 32]| -> Vec<bool> { (0..256).map(|i| (bytes[i / 8] >> (i % 8)) & 1 == 1).collect() };
    let mut inputs = bits(&secret.x);
    for (level, sibling) in secret.siblings.iter().enumerate() {
        inputs.extend(bits(sibling));
        inputs.push((secret.directions >> level) & 1 == 1);
    }
    inputs
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// The circuit's Keccak-256 is Ethereum's, on random blocks.
    #[test]
    fn keccak_matches() {
        let mut b = Builder::new();
        let message: Vec<Src> = (0..512).map(|_| b.input()).collect();
        let digest = b.keccak256_64(&message);
        let rows = b.len() - PUBLIC_ROWS - 512;
        let circuit = b.finish(18, &std::array::from_fn(|_| vec![Src::Zero; WORD_BITS]));
        let mut rng = Rng::new(0x4B);
        for _ in 0..4 {
            let bytes: Vec<u8> = (0..64).map(|_| rng.next_u64() as u8).collect();
            let inputs: Vec<bool> = (0..512).map(|i| (bytes[i / 8] >> (i % 8)) & 1 == 1).collect();
            let v = circuit.outputs(&inputs);
            let got: Vec<u8> = (0..32)
                .map(|byte| (0..8).fold(0u8, |acc, i| acc | read(&v, digest[8 * byte + i]) << i))
                .collect();
            let expected = {
                use sha3::Digest;
                sha3::Keccak256::digest(&bytes).to_vec()
            };
            assert_eq!(got, expected);
            assert_eq!(got, primitives::hash::hash(&bytes).to_vec());
        }
        println!("rows per Keccak-256 of a 64-byte block: {rows}");
    }

    /// The membership circuit computes the statement, fits its rows, and is what the soundness argument
    /// assumes: an input row reads its own output three times, every other row reads constants or rows of lower
    /// rank (the anchors ranked last, nothing reading them; the packing rows read only bits, `3` and the packing
    /// rows before them), every reading cell is on the cycle of the output cell it reads, the cells reading a
    /// constant are one cycle that holds its anchor, and the anchors' cells hold the statement's words and the
    /// constants.
    #[test]
    fn membership_is_a_wired_loop_free_circuit() {
        let circuit = membership();
        let n = circuit.rows.len();
        let mut rng = Rng::new(0x3E);
        let secret = Secret {
            x: std::array::from_fn(|_| rng.next_u64() as u8),
            siblings: std::array::from_fn(|_| std::array::from_fn(|_| rng.next_u64() as u8)),
            directions: rng.next_u64() as u32,
        };
        let statement = secret.statement();
        let cells = circuit.cells(&membership_inputs(&secret));
        assert_eq!(circuit.check_k(&cells), Ok(()));
        assert!(circuit.errors_have_their_own_poles());
        let pinned = anchor_values(&statement.words());
        for (k, &value) in pinned.iter().enumerate() {
            assert_eq!(cells[anchor_cell(k)], value, "anchor {k}");
        }

        let rank = |r: usize| if r < PUBLIC_ROWS { n + r } else { r };
        let (start, len) = circuit.packing;
        assert_eq!(len, PUBLIC_WORDS * (WORD_BITS - 1));
        let packing = |r: usize| (start..start + len).contains(&r);
        let mut is_input = vec![false; n];
        circuit.inputs.iter().for_each(|&r| is_input[r as usize] = true);
        let random = circuit.random_rows();
        assert_eq!(random, (n - RANDOM_ROWS..n).rev().collect::<Vec<_>>());
        for (r, row) in circuit.rows.iter().enumerate() {
            let sources = [row.x, row.y, row.c];
            if is_input[r] {
                assert_eq!(sources, [Src::Row(r as u32); 3]);
                continue;
            }
            if let Some(k) = random.iter().position(|&q| q == r) {
                assert_eq!(*row, RandomShape::of(k).row());
                continue;
            }
            assert!(!sources.contains(&Src::Free), "row {r} has a free cell");
            assert!(packing(r) || r < PUBLIC_ROWS || !sources.contains(&Src::Three), "row {r} reads 3");
            for src in sources {
                if let Src::Row(from) = src {
                    assert!(from as usize >= PUBLIC_ROWS, "row {r} reads an anchor");
                    assert!(rank(from as usize) < rank(r), "row {r} reads row {from}");
                    assert!(
                        packing(from as usize) <= (packing(r) || r < PUBLIC_ROWS),
                        "row {r} reads the packing row {from}"
                    );
                }
            }
        }
        // Cycles of the wiring, each named by its least cell.
        let mut cycle = vec![u32::MAX; 4 * n];
        for start in 0..4 * n {
            if cycle[start] != u32::MAX {
                continue;
            }
            let mut at = start;
            while cycle[at] == u32::MAX {
                cycle[at] = start as u32;
                at = circuit.sigma[at] as usize;
            }
            assert_eq!(at, start, "the wiring is not a permutation");
        }
        let anchors = [anchor_cell(PUBLIC_WORDS), anchor_cell(PUBLIC_WORDS + 1), anchor_cell(PUBLIC_WORDS + 2)];
        for (r, row) in circuit.rows.iter().enumerate() {
            for (role, src) in [row.x, row.y, row.c].into_iter().enumerate() {
                let source = match src {
                    Src::Zero => anchors[0],
                    Src::One => anchors[1],
                    Src::Three => anchors[2],
                    Src::Row(from) => 4 * from as usize + 3,
                    Src::Free => {
                        assert_eq!(circuit.sigma[4 * r + role] as usize, 4 * r + role, "a free cell's own cycle");
                        continue;
                    }
                };
                assert_eq!(cycle[4 * r + role], cycle[source], "cell {role} of row {r}");
            }
        }
        for (i, &a) in anchors.iter().enumerate() {
            for &b in &anchors[i + 1..] {
                assert_ne!(cycle[a], cycle[b]);
            }
        }
        assert!((0..n).all(|r| anchors.iter().all(|&a| cycle[4 * r + 3] != cycle[a])));
        // The anchors: `(0, 0, word or zero)` and `(0, c, c)` for the constants one and three, each word the last of
        // its 63 packing rows.
        for (k, row) in circuit.rows[..PUBLIC_ROWS].iter().enumerate() {
            let y = if k > PUBLIC_WORDS { row.c } else { Src::Zero };
            assert_eq!([row.x, row.y], [Src::Zero, y]);
            match k {
                _ if k < PUBLIC_WORDS => {
                    assert_eq!(row.c, Src::Row((start + (k + 1) * (WORD_BITS - 1) - 1) as u32))
                }
                8 => assert_eq!(row.c, Src::Zero),
                9 => assert_eq!(row.c, Src::One),
                _ => assert_eq!(row.c, Src::Three),
            }
        }
    }
}
