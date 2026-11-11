// Adapted from leanVM (https://github.com/leanEthereum/leanVM), commit 42422001, file crates/verifier/src/layout.rs:
// the same tables, flushes and constraints (not its stacking, which `leanvm_univariate` replaces with its own); a
// `Form` is generic over its coefficients' `Scalar`, and a table's constraints a method on any `Scalar`. New here: the
// Keccak VM's `SHA3` table (leanVM 9d50c92a3), which replaces leanVM 42422001's BLAKE2S table in its opcode slot.
// MIT OR Apache-2.0; see AGENTS.md.
//! The instruction tables, their bus flushes and constraints.

use crate::field::{E, GEN, ONE, ZERO};
use crate::scalar::Scalar;
use std::collections::BTreeMap;
use std::ops::Add;

pub const BUS_BITS: usize = 4; // bus communicates tuples of 2^BUS_BITS field elements

/// A polynomial of degree at most 2 in a table's columns.
#[derive(Clone, Debug)]
pub struct Form<S = E> {
    terms: BTreeMap<Vec<usize>, S>, // monomial -> coefficient; [] is 1, [i] is x_i, [i, j] is x_i*x_j
}

impl<S> Default for Form<S> {
    fn default() -> Self {
        Self { terms: BTreeMap::new() }
    }
}

impl<S: Scalar> Form<S> {
    pub fn term(monomial: Vec<usize>, coefficient: S) -> Self {
        Self {
            terms: BTreeMap::from([(monomial, coefficient)]),
        }
    }

    /// `self += weight * other`, `other` having constant coefficients.
    pub fn add_scaled(&mut self, other: &Form<E>, weight: S) {
        for (monomial, &coefficient) in &other.terms {
            let entry = self.terms.entry(monomial.clone()).or_insert(S::zero());
            *entry += weight * S::constant(coefficient);
        }
    }

    /// The monomials and their coefficients: `[]` is 1, `[i]` is `x_i`, `[i, j]` is `x_i x_j`.
    pub fn terms(&self) -> impl Iterator<Item = (&[usize], &S)> {
        self.terms.iter().map(|(monomial, coefficient)| (monomial.as_slice(), coefficient))
    }

    pub fn evaluate(&self, column: &[S]) -> S {
        S::sum(
            self.terms
                .iter()
                .map(|(monomial, &c)| monomial.iter().fold(c, |acc, &index| acc * column[index])),
        )
    }
}

impl Form<E> {
    /// `Σ forms`, the empty sum being the zero polynomial.
    fn sum(forms: impl IntoIterator<Item = Form>) -> Form {
        forms.into_iter().fold(Form::default(), |acc, form| acc + form)
    }
}

impl Add for Form<E> {
    type Output = Form;
    fn add(mut self, other: Form) -> Form {
        self.add_scaled(&other, ONE);
        self
    }
}

pub const K_BITS: usize = 64;

fn cols<const N: usize>(columns: &[&str], names: [&str; N]) -> [usize; N] {
    names.map(|name| {
        columns
            .iter()
            .position(|&column| column == name)
            .expect("unknown column")
    })
}

pub fn gpow(index: u64) -> E {
    GEN.pow(index)
}

pub fn constant(value: E) -> Form {
    Form::term(vec![], value)
}

fn col(index: usize, exponent: u64) -> Form {
    Form::term(vec![index], gpow(exponent))
}

fn prod(a: usize, b: usize, exponent: u64) -> Form {
    Form::term(vec![a.min(b), a.max(b)], gpow(exponent))
}

pub const SEP_STATE: E = ONE;
pub const SEP_MEM: E = GEN;
pub const SEP_BYTECODE: E = E::new(4, 0, 0); // GEN^2

#[derive(Clone, Debug, Default)]
pub struct Flushes {
    pub push: Vec<Vec<Form>>,
    pub pull: Vec<Vec<Form>>,
}

impl Flushes {
    fn pair(&mut self, push: Vec<Form>, pull: Vec<Form>) {
        self.push.push(push);
        self.pull.push(pull);
    }

    fn state_derived(&mut self, pc: usize, fp: usize, npc: Form, nfp: Form) {
        self.pair(
            vec![constant(SEP_STATE), npc, nfp],
            vec![constant(SEP_STATE), col(pc, 0), col(fp, 0)],
        );
    }

    fn state_step(&mut self, pc: usize, fp: usize) {
        self.state_derived(pc, fp, col(pc, 1), col(fp, 0));
    }

    fn counted(&mut self, prefix: [Form; 2], count: usize, suffix: Vec<Form>) {
        let side = |counter: Form| [prefix.to_vec(), vec![counter], suffix.clone()].concat();
        self.pair(side(col(count, 1)), side(col(count, 0)));
    }

    fn bytecode(&mut self, pc: usize, count: usize, opcode: usize, operands: Vec<Form>) {
        let suffix = [vec![constant(gpow(opcode as u64))], operands].concat();
        self.counted([constant(SEP_BYTECODE), col(pc, 0)], count, suffix);
    }

    fn memory(&mut self, address: Form, count: usize, values: [Form; 3]) {
        self.counted([constant(SEP_MEM), address], count, values.to_vec());
    }

    /// The cell's limbs are the named columns, the missing top ones zero.
    fn memory_cols(&mut self, address: Form, count: usize, columns: &[usize]) {
        let values = std::array::from_fn(|limb| columns.get(limb).map_or(constant(ZERO), |&column| col(column, 0)));
        self.memory(address, count, values);
    }
}

/// One instruction's table: its columns, its bus flushes, its constraints.
pub struct Table {
    pub opcode: usize, // also its index in the table list, so g^opcode is its bytecode tag
    pub columns: &'static [&'static str],
    pub padding: Vec<E>, // the row a padding row holds
    pub flushes: Flushes,
}

impl Table {
    /// The constraints the table's rows satisfy (leanVM's per-table `constraints` function).
    pub fn constraints<S: Scalar>(&self, columns: &[S]) -> Vec<S> {
        if self.opcode == OP_JUMP {
            jump_constraints(columns)
        } else {
            vec![]
        }
    }

    pub fn width(&self) -> usize {
        self.columns.len()
    }

    pub fn count_columns(&self) -> impl Iterator<Item = usize> {
        (0..self.width()).filter(|&i| self.columns[i].starts_with("cnt"))
    }
}

fn flushes_arith(opcode: usize, multiply: bool) -> Flushes {
    let [pc, fp, o_a, o_b, o_c, cnt_a, cnt_b, cnt_c, cnt_bc] = cols(
        ARITH_COLUMNS,
        ["pc", "fp", "o_a", "o_b", "o_c", "cnt_a", "cnt_b", "cnt_c", "cnt_bc"],
    );
    let va = cols(ARITH_COLUMNS, ["va_0", "va_1", "va_2"]);
    let vb = cols(ARITH_COLUMNS, ["vb_0", "vb_1", "vb_2"]);
    let mut flushes = Flushes::default();
    flushes.state_step(pc, fp);
    let operands = vec![col(o_a, 0), col(o_b, 0), col(o_c, 0), constant(ZERO), constant(ZERO)];
    flushes.bytecode(pc, cnt_bc, opcode, operands);
    flushes.memory_cols(prod(fp, o_a, 0), cnt_a, &va);
    flushes.memory_cols(prod(fp, o_b, 0), cnt_b, &vb);
    const TOWER_LANES: [&[(usize, usize)]; 3] = [
        &[(0, 0), (1, 2), (2, 1)],
        &[(0, 1), (1, 0), (1, 2), (2, 1), (2, 2)],
        &[(0, 2), (1, 1), (2, 0), (2, 2)],
    ];
    let result = if multiply {
        TOWER_LANES.map(|lane| Form::sum(lane.iter().map(|&(j, k)| prod(va[j], vb[k], 0))))
    } else {
        std::array::from_fn(|i| col(va[i], 0) + col(vb[i], 0))
    };
    flushes.memory(prod(fp, o_c, 0), cnt_c, result);
    flushes
}

fn flushes_set() -> Flushes {
    let [pc, fp, o, cnt, cnt_bc] = cols(SET_COLUMNS, ["pc", "fp", "o", "cnt", "cnt_bc"]);
    let k = cols(SET_COLUMNS, ["k_0", "k_1", "k_2"]);
    let mut flushes = Flushes::default();
    flushes.state_step(pc, fp);
    let operands = vec![col(o, 0), col(k[0], 0), col(k[1], 0), col(k[2], 0), constant(ZERO)];
    flushes.bytecode(pc, cnt_bc, OP_SET, operands);
    flushes.memory_cols(prod(fp, o, 0), cnt, &k);
    flushes
}

fn flushes_deref() -> Flushes {
    let [pc, fp, o1, o2, o3, f_pc, f_fp, ptr] =
        cols(DEREF_COLUMNS, ["pc", "fp", "o1", "o2", "o3", "f_pc", "f_fp", "ptr"]);
    let [cnt_ptr, cnt_target, cnt_local, cnt_bc] =
        cols(DEREF_COLUMNS, ["cnt_ptr", "cnt_target", "cnt_local", "cnt_bc"]);
    let v3 = cols(DEREF_COLUMNS, ["v3_0", "v3_1", "v3_2"]);

    let gated = |lane: usize| [col(lane, 0), prod(f_pc, lane, 0), prod(f_fp, lane, 0)];

    // v2 = (1 + f_pc + f_fp)*v3 + f_pc*(g^2*pc) + f_fp*fp, lane-wise: only the low lane takes the two K-valued sources.
    let store = [
        Form::sum(gated(v3[0]).into_iter().chain([prod(f_pc, pc, 2), prod(f_fp, fp, 0)])),
        Form::sum(gated(v3[1])),
        Form::sum(gated(v3[2])),
    ];
    let mut flushes = Flushes::default();
    flushes.state_step(pc, fp);
    let operands = vec![col(o1, 0), col(o2, 0), col(o3, 0), col(f_pc, 0), col(f_fp, 0)];
    flushes.bytecode(pc, cnt_bc, OP_DEREF, operands);
    flushes.memory_cols(prod(fp, o1, 0), cnt_ptr, &[ptr]);
    flushes.memory(prod(ptr, o2, 0), cnt_target, store);
    flushes.memory_cols(prod(fp, o3, 0), cnt_local, &v3);
    flushes
}

fn flushes_jump() -> Flushes {
    let [pc, fp, o_c, o_d, o_f, cond, dest, frame, b] = cols(
        JUMP_COLUMNS,
        ["pc", "fp", "o_c", "o_d", "o_f", "v_cond", "v_pc", "v_fp", "b"],
    );
    let [cnt_c, cnt_d, cnt_f, cnt_bc] = cols(JUMP_COLUMNS, ["cnt_c", "cnt_d", "cnt_f", "cnt_bc"]);
    let mut flushes = Flushes::default();
    // next_pc = b*dest + (b+1)*g*pc, next_fp = b*frame + (b+1)*fp, both derived.
    flushes.state_derived(
        pc,
        fp,
        prod(b, dest, 0) + prod(b, pc, 1) + col(pc, 1),
        prod(b, frame, 0) + prod(b, fp, 0) + col(fp, 0),
    );
    let operands = vec![col(o_c, 0), col(o_d, 0), col(o_f, 0), constant(ZERO), constant(ZERO)];
    flushes.bytecode(pc, cnt_bc, OP_JUMP, operands);
    flushes.memory_cols(prod(fp, o_c, 0), cnt_c, &[cond]);
    flushes.memory_cols(prod(fp, o_d, 0), cnt_d, &[dest]);
    flushes.memory_cols(prod(fp, o_f, 0), cnt_f, &[frame]);
    flushes
}

fn jump_constraints<S: Scalar>(columns: &[S]) -> Vec<S> {
    let [condition, inverse, flag] = cols(JUMP_COLUMNS, ["v_cond", "w", "b"]).map(|index| columns[index]);
    vec![flag + condition * inverse, condition * (flag + S::one())]
}

/// The `SHA3` table of leanVM's Keccak branch before its switch to GKR (commit `9d50c92a3`,
/// `crates/leanvm_core/src/tables.rs` there, `Sha3Table`): one Keccak-f step over a thirteen-cell state. Its flushes are
/// that table's: the state step, the bytecode read (seven operands: four independently addressed `m` cells, the `tail`,
/// `cap` and output bases), thirteen cells read and thirteen written, each two lanes and a zero top (`memory_128`)
/// but for the lone lane-16 cell (`memory_k`). No constraint of its own: the permutation is Flock's.
fn flushes_sha3() -> Flushes {
    let [pc, fp, cnt_bc] = cols(SHA3_COLUMNS, ["pc", "fp", "cnt_bc"]);
    let o_m = cols(SHA3_COLUMNS, ["o_m0", "o_m1", "o_m2", "o_m3"]);
    let [o_tail, o_cap, o_out] = cols(SHA3_COLUMNS, ["o_tail", "o_cap", "o_out"]);
    let mut flushes = Flushes::default();
    flushes.state_step(pc, fp);
    let operands = [o_m[0], o_m[1], o_m[2], o_m[3], o_tail, o_cap, o_out];
    flushes.bytecode(pc, cnt_bc, OP_SHA3, operands.map(|i| col(i, 0)).to_vec());
    let input_address = |c: usize| match c {
        0..4 => prod(fp, o_m[c], 0),
        4..8 => prod(fp, o_tail, (c - 4) as u64),
        _ => prod(fp, o_cap, (c - 8) as u64),
    };
    for (side, prefix) in [(0, "in"), (1, "out")] {
        for (c, &(lo, hi)) in SHA3_CELL_LANES.iter().enumerate() {
            let address = if side == 0 { input_address(c) } else { prod(fp, o_out, c as u64) };
            let count = cols(SHA3_COLUMNS, [&*format!("cnt_{}", side * SHA3_STATE_CELLS + c)])[0];
            let lo = cols(SHA3_COLUMNS, [&*format!("{prefix}_{lo}")])[0];
            match hi {
                Some(hi) => {
                    let hi = cols(SHA3_COLUMNS, [&*format!("{prefix}_{hi}")])[0];
                    flushes.memory_cols(address, count, &[lo, hi]);
                }
                None => flushes.memory_cols(address, count, &[lo]),
            }
        }
    }
    flushes
}

/// Cells a sponge state occupies (leanVM `9d50c92a3`, `hash_flock::STATE_CELLS`).
pub const SHA3_STATE_CELLS: usize = 13;

/// The lanes each state cell holds, `(lo, hi)`, `None` a literal zero (leanVM `9d50c92a3`, `hash_flock::CELL_LANES`):
/// lanes 0..16 two to a cell, then lane 16 alone, then the capacity lanes 17..25.
pub const SHA3_CELL_LANES: [(usize, Option<usize>); SHA3_STATE_CELLS] = {
    let mut t = [(0usize, None); SHA3_STATE_CELLS];
    let mut c = 0;
    while c < SHA3_STATE_CELLS {
        t[c] = if c < 8 {
            (2 * c, Some(2 * c + 1))
        } else if c == 8 {
            (16, None)
        } else {
            (2 * c - 1, Some(2 * c))
        };
        c += 1;
    }
    t
};

/// `log2` of the Keccak-f Flock block's slots (`crate::keccak_flock`, `flock::keccak`): one permutation a block,
/// so one `SHA3` row a block, `2^(17 - 6)` words of `q_flock` a row.
pub const KECCAK_R1CS_LOG_SIZE: usize = crate::keccak_flock::LOG_SIZE;

/// Where `q_flock` keeps the `SHA3` table's value lanes, within a row's block (word index): input lane `l` is the
/// block's input port word, output lane `l` its output port word (`keccak_flock::state_word(-1, l)` and
/// `state_word(23, l)`).
pub fn keccak_slot(name: &str) -> Option<usize> {
    let lane = |prefix: &str| name.strip_prefix(prefix).and_then(|l| l.parse::<usize>().ok());
    if let Some(l) = lane("in_") {
        return Some(crate::keccak_flock::state_word(-1, l));
    }
    lane("out_").map(|l| crate::keccak_flock::state_word(23, l))
}

/// leanVM `9d50c92a3`'s `SHA3` step is `Keccak-f(in ⊕ END_BIT · e_16)` (`primitives::hash::step` there: SHA3's last
/// padding bit, `0x80 << 56`, in rate lane 16). The Keccak-f block proves `Keccak-f` of its input port, so the port of
/// input lane 16 holds `in_16 ⊕ END_BIT`: the `SHA3` column `in_16` is its port word plus this constant.
pub const SHA3_END_BIT: u64 = 0x80 << 56;

/// The constant a `SHA3` value column differs from its `q_flock` word by ([`SHA3_END_BIT`] for `in_16`, else 0).
pub fn keccak_slot_offset(name: &str) -> u64 {
    if name == "in_16" { SHA3_END_BIT } else { 0 }
}

pub const OP_XOR: usize = 0;
pub const OP_MUL: usize = 1;
pub const OP_SET: usize = 2;
pub const OP_DEREF: usize = 3;
pub const OP_JUMP: usize = 4;
/// The Keccak VM's `SHA3` table: opcode 5, its bytecode tag `g^5`.
pub const OP_SHA3: usize = 5;
pub const N_TABLES: usize = 6;
pub const TABLE_NAMES: [&str; N_TABLES] = ["XOR", "MUL", "SET", "DEREF", "JUMP", "SHA3"];

#[rustfmt::skip]
const ARITH_COLUMNS: &[&str] = &["pc", "fp", "o_a", "o_b", "o_c", "va_0", "va_1", "va_2", "vb_0", "vb_1", "vb_2", "cnt_a", "cnt_b", "cnt_c", "cnt_bc"];
const SET_COLUMNS: &[&str] = &["pc", "fp", "o", "k_0", "k_1", "k_2", "cnt", "cnt_bc"];
#[rustfmt::skip]
const DEREF_COLUMNS: &[&str] = &["pc", "fp", "o1", "o2", "o3", "f_pc", "f_fp", "ptr", "v3_0", "v3_1", "v3_2", "cnt_ptr", "cnt_target", "cnt_local", "cnt_bc"];
#[rustfmt::skip]
const JUMP_COLUMNS: &[&str] = &["pc", "fp", "o_c", "o_d", "o_f", "v_cond", "v_pc", "v_fp", "cnt_c", "cnt_d", "cnt_f", "cnt_bc", "w", "b"];
/// leanVM `9d50c92a3`'s `SHA3` columns (`sha3t` there): the operands, the 25 input and 25 output lanes (`q_flock`'s
/// words, committed again as the univariate copies), one read count a cell in flush order, and the bytecode count.
#[rustfmt::skip]
const SHA3_COLUMNS: &[&str] = &[
    "pc", "fp", "o_m0", "o_m1", "o_m2", "o_m3", "o_tail", "o_cap", "o_out", "in_0", "in_1", "in_2", "in_3", "in_4",
    "in_5", "in_6", "in_7", "in_8", "in_9", "in_10", "in_11", "in_12", "in_13", "in_14", "in_15", "in_16", "in_17",
    "in_18", "in_19", "in_20", "in_21", "in_22", "in_23", "in_24", "out_0", "out_1", "out_2", "out_3", "out_4",
    "out_5", "out_6", "out_7", "out_8", "out_9", "out_10", "out_11", "out_12", "out_13", "out_14", "out_15",
    "out_16", "out_17", "out_18", "out_19", "out_20", "out_21", "out_22", "out_23", "out_24", "cnt_0", "cnt_1",
    "cnt_2", "cnt_3", "cnt_4", "cnt_5", "cnt_6", "cnt_7", "cnt_8", "cnt_9", "cnt_10", "cnt_11", "cnt_12", "cnt_13",
    "cnt_14", "cnt_15", "cnt_16", "cnt_17", "cnt_18", "cnt_19", "cnt_20", "cnt_21", "cnt_22", "cnt_23", "cnt_24",
    "cnt_25", "cnt_bc",
];

/// The Keccak VM's tables: leanVM 42422001's five (XOR, MUL, SET, DEREF, JUMP), and the `SHA3` table
/// ([`flushes_sha3`]). A padding row is zero: the univariate PIOP's padding rows' leaves are 1 whatever they hold.
pub fn tables() -> Vec<Table> {
    let table = |opcode, columns: &'static [&'static str], flushes| Table {
        opcode,
        columns,
        padding: vec![ZERO; columns.len()],
        flushes,
    };
    vec![
        table(OP_XOR, ARITH_COLUMNS, flushes_arith(OP_XOR, false)),
        table(OP_MUL, ARITH_COLUMNS, flushes_arith(OP_MUL, true)),
        table(OP_SET, SET_COLUMNS, flushes_set()),
        table(OP_DEREF, DEREF_COLUMNS, flushes_deref()),
        table(OP_JUMP, JUMP_COLUMNS, flushes_jump()),
        table(OP_SHA3, SHA3_COLUMNS, flushes_sha3()),
    ]
}
