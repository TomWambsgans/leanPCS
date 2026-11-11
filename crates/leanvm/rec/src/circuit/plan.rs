// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! `π2`'s witness replayed from a plan (the compiler's witness, [`super::compile`], without the compiler).
//!
//! The circuit depends on `π1`'s recorded verifier only; a proof's stream and public input change the words. A
//! [`WitnessPlan`] is made once per circuit from one compilation's layout ([`super::layout::Internals`]) and records
//! how every word is computed; [`WitnessPlan::witness`] replays it on any stream, word for word the compiler's:
//!
//! 1. **The sequential words** (one thread): every value outside the Keccak-f permutations' rows (free bits and
//!    limbs given by the inputs, XORs, nonzero constants, packings, `E` units; a copy is its operand's word, a zero
//!    constant the zero word), in value order, and each permutation's 1600 output bits, computed natively
//!    ([`super::keccak::keccak_f`]) where its first output was made. The Keccak-256 chain is so computed first, at
//!    the cost of its native permutations (116 at the reference shape).
//! 2. **The permutations' words** (in parallel): every permutation's rows are one *template*'s (checked when the
//!    plan is made: the same local program on its inputs, its *leaves*: D16v has one template), a program on bits
//!    (coefficients 1, `κ` bits) that the plan compiles and runs on 64 permutations at once, bit `b` of a word
//!    permutation `b`'s.
//! 3. **The witness** (in parallel, a final row a task): each position's word, from the template (a permutation's
//!    row), the row's sources (another row), or zero (no row). A free end's pull, which is anywhere, is a source.
//!
//! The plan is checked against the compiler (`tests/witness_plan.rs`): on the real streams, on a sample stream,
//! made on a zero stream.

use std::collections::{BTreeMap, HashMap};

use leanvm_statement::field::{E, K};
use leanvm_univariate::contract::Recorded;

use super::compile::{Compiled, Given, Inputs, Layout, compile_keeping};
use super::keccak::{Bit, UNMADE, keccak_f};
use super::spec::{Formula, PublicInputs, Witness};

const NONE: u32 = u32::MAX;

/// Where a word is read: a slot of the sequential words, a permutation's local word (`LOCAL | perm << 32 | index`),
/// or zero.
type Src = u64;
const LOCAL: u64 = 1 << 63;
const ZERO: Src = u64::MAX;

/// A template's content at a hole (a position whose pull is no value placed there): `HOLE | ordinal`.
const HOLE: u32 = 1 << 31;

/// A permutation's constant input bits, in [`Perm::input`].
const IN_ZERO: u32 = u32::MAX;
const IN_ONE: u32 = u32::MAX - 1;

/// A row formula on an op's reads (the cells `role_reads` lists, in order).
#[derive(Clone, Debug)]
struct KPoly {
    reads: usize,
    linear: Vec<(u8, K)>,
    quadratic: Vec<(u8, u8, K)>,
}

/// The sequential slot that holds zero (every zero constant's). A copy (a slot pushing one cell) has its operand's
/// slot, so neither is a step.
const ZERO_SLOT: u32 = 0;

/// A sequential step.
#[derive(Clone, Copy, Debug)]
enum Op {
    Given {
        slot: u32,
        source: Given,
    },
    /// Bit `bit` of the word at slot `from` (a hashed claim's element unpacked: `Given::Bit`).
    Bit {
        slot: u32,
        from: u32,
        bit: u8,
    },
    /// A constant `κ`.
    Const {
        slot: u32,
        word: K,
    },
    /// The sum of the slots `reads .. reads + n`.
    Sum {
        slot: u32,
        reads: u32,
        n: u32,
    },
    /// `poly` on the slots `reads .. reads + poly.reads`, plus `κ`.
    Eval {
        slot: u32,
        poly: u32,
        kappa: K,
        reads: u32,
    },
    /// Permutation `perm`'s outputs, at the slots `out .. out + 1600`.
    Permute {
        perm: u32,
        out: u32,
    },
}

/// A row formula on bits, coefficients 1: its cells.
#[derive(Clone, Debug, PartialEq, Eq)]
struct BitPoly {
    linear: Vec<u8>,
    quadratic: Vec<(u8, u8)>,
}

/// A local value of a template: `poly` on its row's cells, plus `κ`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct BitOp {
    row: u32,
    poly: u16,
    kappa: u8,
}

/// A permutation's rows: their local program and their contents.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Template {
    rows: u32,
    leaves: u32,
    /// The local values, in value order: local index `leaves + k`.
    ops: Vec<BitOp>,
    /// Per local position (`row · W + role`): the local index of the value placed there, or `HOLE | ordinal`.
    contents: Vec<u32>,
    /// The program compiled ([`Template::compile`]).
    code: Vec<u32>,
}

/// A compiled op's header: `κ` (bit 0), a product of two sums (bit 1, else a sum of products), the linear terms'
/// count (bits 8..16), the two sums' sizes or the products' count (bits 16..24, 24..32).
const PRODUCT_OF_SUMS: u32 = 2;

impl Template {
    /// Each op as its header and its reads' local indices: the linear terms', then the quadratic part's (the two sums'
    /// terms, `(Σ_S)(Σ_T)` when the products are exactly `S × T`, else each product's two).
    fn compile(&mut self, polys: &[BitPoly], w: usize) {
        let mut code = Vec::new();
        for op in &self.ops {
            let poly = &polys[op.poly as usize];
            let cell = |c: u8| self.contents[op.row as usize * w + c as usize];
            let factors = factor(&poly.quadratic);
            // Each count in its byte of the header.
            let counts = match &factors {
                Some((s, t)) => [poly.linear.len(), s.len(), t.len()],
                None => [poly.linear.len(), poly.quadratic.len(), 0],
            };
            assert!(counts.iter().all(|&c| c <= 0xff), "a row formula of at most 255 terms a part");
            let mut header = op.kappa as u32 | (poly.linear.len() as u32) << 8;
            match &factors {
                Some((s, t)) => header |= PRODUCT_OF_SUMS | (s.len() as u32) << 16 | (t.len() as u32) << 24,
                None => header |= (poly.quadratic.len() as u32) << 16,
            }
            code.push(header);
            code.extend(poly.linear.iter().map(|&c| cell(c)));
            match factors {
                Some((s, t)) => code.extend(s.iter().chain(&t).map(|&c| cell(c))),
                None => code.extend(poly.quadratic.iter().flat_map(|&(a, b)| [cell(a), cell(b)])),
            }
        }
        self.code = code;
    }

    /// The program on 64 permutations at once (bit `b` of a word is lane `b`'s), from the leaves' words.
    fn run(&self, leaves: Vec<u64>) -> Vec<u64> {
        let mut local = leaves;
        local.reserve(self.ops.len());
        let code = &self.code;
        let mut i = 0;
        while i < code.len() {
            let header = code[i];
            i += 1;
            let mut acc = 0u64.wrapping_sub((header & 1) as u64);
            let (n, a, b) = (
                (header >> 8 & 0xff) as usize,
                (header >> 16 & 0xff) as usize,
                (header >> 24) as usize,
            );
            for &x in &code[i..i + n] {
                acc ^= local[x as usize];
            }
            i += n;
            if header & PRODUCT_OF_SUMS != 0 {
                let (mut s, mut t) = (0u64, 0u64);
                for &x in &code[i..i + a] {
                    s ^= local[x as usize];
                }
                for &x in &code[i + a..i + a + b] {
                    t ^= local[x as usize];
                }
                acc ^= s & t;
                i += a + b;
            } else {
                for pair in code[i..i + 2 * a].as_chunks::<2>().0 {
                    acc ^= local[pair[0] as usize] & local[pair[1] as usize];
                }
                i += 2 * a;
            }
            local.push(acc);
        }
        local
    }
}

/// `(S, T)` with the products exactly `{s·t : s ∈ S, t ∈ T}`, `S` and `T` disjoint, if so.
fn factor(products: &[(u8, u8)]) -> Option<(Vec<u8>, Vec<u8>)> {
    let &(a, b) = products.first()?;
    let has = |x: u8, y: u8| products.contains(&(x.min(y), x.max(y)));
    let s: Vec<u8> = (0..=u8::MAX).filter(|&x| has(x, b)).collect();
    let t: Vec<u8> = (0..=u8::MAX).filter(|&y| has(a, y)).collect();
    let exact = s.len() * t.len() == products.len() && s.iter().all(|&x| t.iter().all(|&y| x != y && has(x, y)));
    exact.then_some((s, t))
}

/// Permutations of one template, at most 64, run together: permutation `perms[b]` is bit `b`.
#[derive(Clone, Debug)]
struct Group {
    template: u32,
    perms: Vec<u32>,
}

/// One permutation run.
#[derive(Clone, Debug)]
struct Perm {
    template: u32,
    /// Its group and its bit there.
    group: u32,
    bit: u32,
    /// The leaves' slots (local indices `0 .. leaves`).
    leaves: Vec<u32>,
    /// The input bits' slots (`IN_ZERO`, `IN_ONE`: constants), index `64·lane + z`.
    input: Vec<u32>,
    /// Each hole's source, by ordinal.
    holes: Vec<Src>,
}

/// A final row: a permutation's (`kind` the permutation, `index` its local row), another row's (`OUTER`, `index`
/// into [`WitnessPlan::outer`] by rows), or none.
#[derive(Clone, Copy, Debug)]
struct RowSrc {
    kind: u32,
    index: u32,
}
const OUTER: u32 = u32::MAX - 1;
const EMPTY: u32 = u32::MAX;

/// How to compute `π2`'s witness and public inputs on any stream, for one circuit (see the module's description).
pub struct WitnessPlan {
    log_n: u8,
    log_width: u8,
    program_iv: [u8; 32],
    stream_len: usize,
    roots_at: Vec<usize>,
    slots: usize,
    ops: Vec<Op>,
    kpolys: Vec<KPoly>,
    reads: Vec<u32>,
    templates: Vec<Template>,
    perms: Vec<Perm>,
    groups: Vec<Group>,
    rows: Vec<RowSrc>,
    /// The sources of the rows outside the permutations, `W` a row.
    outer: Vec<Src>,
    /// The public elements' limbs' slots.
    elements: Vec<[u32; 3]>,
    /// The hashed claims' digests' limbs' slots.
    claim_hashes: Vec<[u32; 4]>,
}

impl WitnessPlan {
    /// Compile `recorded` in `layout` on `inputs` ([`super::compile::pi2`]), and the plan of its circuit (for any
    /// stream of `recorded` with `inputs.program_iv`), checked to replay this compilation. Needs the compiler's deep
    /// stack, as `pi2` does; not from inside a `parallel` task (the replay dispatches), as [`WitnessPlan::witness`].
    pub fn compile(recorded: &Recorded, layout: Layout, inputs: &Inputs) -> (Compiled, WitnessPlan) {
        let (compiled, trace) = match layout {
            Layout::D16v => compile_keeping(recorded, 4, super::keccak16::D16::new, inputs, true),
        };
        let trace = trace.expect("kept");
        let plan = Self::of(&compiled, trace, recorded, inputs.program_iv);
        // The plan replays the compilation it was made from (its native permutations are the circuit's).
        let (witness, public) = plan.witness(inputs);
        assert!(
            witness == compiled.finished.witness && public == compiled.public,
            "the plan replays its compilation"
        );
        (compiled, plan)
    }

    /// The plan of `recorded`'s circuit in `layout`, for π1's program IV `program_iv` (compiled on a zero stream).
    pub fn new(recorded: &Recorded, layout: Layout, program_iv: [u8; 32]) -> WitnessPlan {
        let stream = vec![0u8; recorded.stream_len];
        Self::compile(
            recorded,
            layout,
            &Inputs {
                program_iv,
                public: [0; 32],
                stream: &stream,
            },
        )
        .1
    }

    fn of(compiled: &Compiled, trace: super::compile::Trace, recorded: &Recorded, program_iv: [u8; 32]) -> Self {
        let it = &trace.internals;
        let w = it.width;
        let log_width = compiled.finished.circuit.log_width;
        assert_eq!(1usize << log_width, w);
        let rows = it.row_region.len();
        let values = it.producer.len();
        let formula = |p: usize| -> &Formula { &it.roles[it.row_region[p / w] as usize][p % w] };
        let reads_of = |p: usize| -> &[u8] { &it.role_reads[it.row_region[p / w] as usize][p % w] };
        let kappa = |p: usize| it.kappa.get(&(p as u32)).copied().unwrap_or(K(0));

        let given: HashMap<u32, Given> = trace.given.iter().copied().collect();
        assert_eq!(given.len(), it.given.len(), "every given word has a source");
        for v in &it.given {
            assert!(given.contains_key(v), "every given word has a source");
        }

        // Each creation row's permutation.
        let mut perm_of_row = vec![NONE; rows];
        for (i, run) in trace.runs.iter().enumerate() {
            for r in run.rows.clone() {
                assert_eq!(perm_of_row[r as usize], NONE, "a row of one permutation");
                perm_of_row[r as usize] = i as u32;
            }
        }
        // A permutation's local value: produced in its rows by a formula that reads cells (a constant, which reads
        // none, is a sequential word: the permutations' spare roles hold any constant).
        let perm_of: Vec<u32> = (0..values as u32)
            .map(|v| {
                let p = it.producer[v as usize];
                if p == NONE || given.contains_key(&v) || reads_of(p as usize).is_empty() {
                    NONE
                } else {
                    perm_of_row[p as usize / w]
                }
            })
            .collect();
        let perm_of_value = |v: u32| perm_of[v as usize];

        // The templates.
        let mut local_index = vec![NONE; values];
        let mut templates: Vec<Template> = Vec::new();
        let mut bitpolys: Vec<BitPoly> = Vec::new();
        let mut bitpoly_of: BTreeMap<(u16, usize), u16> = BTreeMap::new();
        let mut perms: Vec<Perm> = Vec::new();
        // Per permutation: its leaves' and holes' values, resolved to slots and sources once all are known.
        let mut pending: Vec<(Vec<u32>, Vec<u32>)> = Vec::new();
        for (i, run) in trace.runs.iter().enumerate() {
            let (r0, r1) = (run.rows.start as usize, run.rows.end as usize);
            let positions = r0 * w..r1 * w;
            let mut locals: Vec<u32> = positions
                .clone()
                .map(|p| it.produced[p])
                .filter(|&v| v != NONE && perm_of_value(v) == i as u32)
                .collect();
            locals.sort_unstable();
            let mut leaf_of: HashMap<u32, u32> = HashMap::new();
            let mut leaves: Vec<u32> = Vec::new();
            for p in positions.clone() {
                let v = it.cell[p];
                if v != NONE && perm_of_value(v) != i as u32 {
                    leaf_of.entry(v).or_insert_with(|| {
                        leaves.push(v);
                        leaves.len() as u32 - 1
                    });
                }
            }
            let n_leaves = leaves.len() as u32;
            for (k, &v) in locals.iter().enumerate() {
                local_index[v as usize] = n_leaves + k as u32;
            }
            let mut holes: Vec<u32> = Vec::new();
            let contents: Vec<u32> = positions
                .clone()
                .map(|p| {
                    let v = it.cell[p];
                    if v == NONE {
                        holes.push(it.pulled_at_free_end.get(&(p as u32)).copied().unwrap_or(NONE));
                        HOLE | (holes.len() as u32 - 1)
                    } else if perm_of_value(v) == i as u32 {
                        local_index[v as usize]
                    } else {
                        leaf_of[&v]
                    }
                })
                .collect();
            let ops: Vec<BitOp> = locals
                .iter()
                .map(|&v| {
                    let p = it.producer[v as usize] as usize;
                    let (region, role) = (it.row_region[p / w], p % w);
                    let poly = *bitpoly_of.entry((region, role)).or_insert_with(|| {
                        let Formula::Expr(poly) = formula(p) else {
                            panic!("a local value is an expression slot's")
                        };
                        assert!(
                            poly.linear.iter().all(|&(_, k)| k == K(1))
                                && poly.quadratic.iter().all(|&(_, _, k)| k == K(1)),
                            "a permutation's formulas have coefficients 1"
                        );
                        bitpolys.push(BitPoly {
                            linear: poly.linear.iter().map(|&(c, _)| c).collect(),
                            quadratic: poly.quadratic.iter().map(|&(a, b, _)| (a, b)).collect(),
                        });
                        bitpolys.len() as u16 - 1
                    });
                    let k = kappa(p);
                    assert!(k.0 <= 1, "a permutation's κ is a bit");
                    BitOp {
                        row: (p / w - r0) as u32,
                        poly,
                        kappa: k.0 as u8,
                    }
                })
                .collect();
            // The program reads earlier local values and leaves.
            for (k, op) in ops.iter().enumerate() {
                let b = &bitpolys[op.poly as usize];
                for c in b.linear.iter().chain(b.quadratic.iter().flat_map(|(a, b)| [a, b])) {
                    let x = contents[op.row as usize * w + *c as usize];
                    assert!(x < n_leaves + k as u32, "a local value reads earlier ones");
                }
            }
            let template = Template {
                rows: (r1 - r0) as u32,
                leaves: n_leaves,
                ops,
                contents,
                code: Vec::new(),
            };
            let t = match templates.iter().position(|t| *t == template) {
                Some(t) => t,
                None => {
                    templates.push(template);
                    templates.len() - 1
                }
            };
            perms.push(Perm {
                template: t as u32,
                group: 0,
                bit: 0,
                leaves: Vec::new(),
                input: Vec::new(),
                holes: Vec::new(),
            });
            pending.push((leaves, holes));
        }
        for t in &mut templates {
            t.compile(&bitpolys, w);
        }
        let mut groups: Vec<Group> = Vec::new();
        for t in 0..templates.len() as u32 {
            let of_t: Vec<u32> = (0..perms.len() as u32)
                .filter(|&i| perms[i as usize].template == t)
                .collect();
            for chunk in of_t.chunks(64) {
                for (bit, &i) in chunk.iter().enumerate() {
                    (perms[i as usize].group, perms[i as usize].bit) = (groups.len() as u32, bit as u32);
                }
                groups.push(Group {
                    template: t,
                    perms: chunk.to_vec(),
                });
            }
        }

        // The sequential words: the values outside the permutations, in value order, each permutation where its
        // first output was made.
        let mut keyed: Vec<(u32, Option<u32>)> = (0..values as u32)
            .filter(|&v| perm_of_value(v) == NONE)
            .map(|v| (v, None))
            .collect();
        for (i, run) in trace.runs.iter().enumerate() {
            let first = *run.output.iter().min().expect("outputs");
            assert_eq!(perm_of_value(first), i as u32, "a permutation's outputs are its own");
            keyed.push((first, Some(i as u32)));
        }
        keyed.sort_unstable();
        let mut slot_of = vec![NONE; values];
        let mut slots = ZERO_SLOT + 1;
        let mut ops: Vec<Op> = Vec::with_capacity(keyed.len());
        let mut kpolys: Vec<KPoly> = Vec::new();
        let mut kpoly_of: BTreeMap<(u16, usize), u32> = BTreeMap::new();
        let mut reads: Vec<u32> = Vec::new();
        for (v, perm) in keyed {
            if let Some(i) = perm {
                let run = &trace.runs[i as usize];
                perms[i as usize].input = run
                    .input
                    .iter()
                    .map(|&bit| match bit {
                        Bit::V(u) => {
                            assert_ne!(slot_of[u as usize], NONE, "a permutation's input is computed before it");
                            slot_of[u as usize]
                        }
                        Bit::Zero => IN_ZERO,
                        Bit::One => IN_ONE,
                    })
                    .collect();
                assert_eq!(run.output.len(), 1600);
                ops.push(Op::Permute { perm: i, out: slots });
                // The native permutation writes all 1600 bits; the unmade lanes' (`keccak::UNMADE`: a last round
                // that makes the lanes read alone) are no value's.
                for &u in &run.output {
                    if u != UNMADE {
                        slot_of[u as usize] = slots;
                    }
                    slots += 1;
                }
                continue;
            }
            if let Some(&source) = given.get(&v) {
                slot_of[v as usize] = slots;
                ops.push(match source {
                    Given::Bit { value, bit } => {
                        assert_ne!(slot_of[value as usize], NONE, "a bit of a word computed before it");
                        Op::Bit {
                            slot: slots,
                            from: slot_of[value as usize],
                            bit,
                        }
                    }
                    source => Op::Given { slot: slots, source },
                });
                slots += 1;
                continue;
            }
            let p = it.producer[v as usize] as usize;
            let (region, role) = (it.row_region[p / w], p % w);
            let cells = reads_of(p);
            let poly = *kpoly_of.entry((region, role)).or_insert_with(|| {
                let Formula::Expr(poly) = formula(p) else {
                    panic!("a value is an expression slot's")
                };
                let at = |c: u8| cells.iter().position(|&x| x == c).expect("a read") as u8;
                kpolys.push(KPoly {
                    reads: cells.len(),
                    linear: poly.linear.iter().map(|&(c, k)| (at(c), k)).collect(),
                    quadratic: poly.quadratic.iter().map(|&(a, b, k)| (at(a), at(b), k)).collect(),
                });
                kpolys.len() as u32 - 1
            });
            let read_slots: Vec<u32> = cells
                .iter()
                .map(|&c| {
                    let u = it.cell[p / w * w + c as usize];
                    assert_ne!(slot_of[u as usize], NONE, "a word reads words computed before it");
                    slot_of[u as usize]
                })
                .collect();
            let k = kappa(p);
            let kp = &kpolys[poly as usize];
            let sum = kp.quadratic.is_empty() && kp.linear.iter().all(|&(_, c)| c == K(1)) && k == K(0);
            if read_slots.is_empty() && k == K(0) {
                // A zero constant: the zero slot.
                slot_of[v as usize] = ZERO_SLOT;
                continue;
            }
            if sum && kp.linear.len() == 1 {
                // A copy: its operand's slot.
                slot_of[v as usize] = read_slots[kp.linear[0].0 as usize];
                continue;
            }
            let slot = slots;
            slots += 1;
            slot_of[v as usize] = slot;
            let at = reads.len() as u32;
            if read_slots.is_empty() {
                ops.push(Op::Const { slot, word: k });
            } else if sum {
                reads.extend(kp.linear.iter().map(|&(c, _)| read_slots[c as usize]));
                ops.push(Op::Sum {
                    slot,
                    reads: at,
                    n: kp.linear.len() as u32,
                });
            } else {
                reads.extend(read_slots);
                ops.push(Op::Eval {
                    slot,
                    poly,
                    kappa: k,
                    reads: at,
                });
            }
        }

        // Every value's source, once the slots and the local indices are known.
        let src = |v: u32| -> Src {
            if v == NONE {
                ZERO
            } else if slot_of[v as usize] != NONE {
                slot_of[v as usize] as u64
            } else {
                let perm = perm_of_value(v);
                assert_ne!(perm, NONE, "a value is computed");
                LOCAL | (perm as u64) << 32 | local_index[v as usize] as u64
            }
        };
        for (perm, (leaves, holes)) in perms.iter_mut().zip(pending) {
            perm.leaves = leaves
                .iter()
                .map(|&v| {
                    assert_ne!(slot_of[v as usize], NONE, "a leaf is a sequential word");
                    slot_of[v as usize]
                })
                .collect();
            perm.holes = holes.into_iter().map(src).collect();
        }

        // The final rows, and the other rows' sources.
        let n_rows = 1usize << (compiled.finished.circuit.log_n - log_width);
        let mut row_src = vec![RowSrc { kind: EMPTY, index: 0 }; n_rows];
        let mut outer: Vec<Src> = Vec::new();
        for r in 0..rows {
            let f = it.row_map[r] as usize;
            let perm = perm_of_row[r];
            row_src[f] = if perm != NONE {
                RowSrc {
                    kind: perm,
                    index: r as u32 - trace.runs[perm as usize].rows.start,
                }
            } else {
                let index = (outer.len() / w) as u32;
                for p in r * w..(r + 1) * w {
                    outer.push(match it.cell[p] {
                        NONE => src(it.pulled_at_free_end.get(&(p as u32)).copied().unwrap_or(NONE)),
                        v => src(v),
                    });
                }
                RowSrc { kind: OUTER, index }
            };
        }
        let elements = trace
            .elements
            .iter()
            .map(|l| {
                l.map(|v| {
                    assert_ne!(slot_of[v as usize], NONE, "an element is a sequential word");
                    slot_of[v as usize]
                })
            })
            .collect();
        let claim_hashes = trace
            .claim_hashes
            .iter()
            .map(|l| {
                l.map(|v| {
                    assert_ne!(slot_of[v as usize], NONE, "a claim hash's limb is a sequential word");
                    slot_of[v as usize]
                })
            })
            .collect();
        WitnessPlan {
            log_n: compiled.finished.circuit.log_n,
            log_width,
            program_iv,
            stream_len: recorded.stream_len,
            roots_at: compiled.roots_at.clone(),
            slots: slots as usize,
            ops,
            kpolys,
            reads,
            templates,
            perms,
            groups,
            rows: row_src,
            outer,
            elements,
            claim_hashes,
        }
    }

    /// How many permutation templates the plan holds (one for D16v).
    pub fn templates(&self) -> usize {
        self.templates.len()
    }

    /// The circuit's `log N`: the witness has `2^log_n` words.
    pub fn log_n(&self) -> u8 {
        self.log_n
    }

    /// The sequential words on these inputs.
    fn sequential(&self, public: &[u8; 32], stream: &[u8]) -> Vec<u64> {
        let mut words = vec![0u64; self.slots];
        // `k · x`, which most often is `k` or 0 (a bit times a packing's power).
        let scaled = |k: K, x: K| {
            if k == K(1) {
                x
            } else if x.0 <= 1 {
                K(k.0 & 0u64.wrapping_sub(x.0))
            } else {
                k * x
            }
        };
        for op in &self.ops {
            match *op {
                Op::Given { slot, source } => words[slot as usize] = source.word(public, stream).0,
                Op::Bit { slot, from, bit } => words[slot as usize] = words[from as usize] >> bit & 1,
                Op::Const { slot, word } => words[slot as usize] = word.0,
                Op::Sum { slot, reads, n } => {
                    let reads = &self.reads[reads as usize..(reads + n) as usize];
                    words[slot as usize] = reads.iter().fold(0, |acc, &s| acc ^ words[s as usize]);
                }
                Op::Eval {
                    slot,
                    poly,
                    kappa,
                    reads,
                } => {
                    let poly = &self.kpolys[poly as usize];
                    let reads = &self.reads[reads as usize..reads as usize + poly.reads];
                    let cell = |i: u8| K(words[reads[i as usize] as usize]);
                    let mut out = kappa;
                    for &(c, k) in &poly.linear {
                        out = out + scaled(k, cell(c));
                    }
                    for &(a, b, k) in &poly.quadratic {
                        out = out + scaled(k, cell(a) * cell(b));
                    }
                    words[slot as usize] = out.0;
                }
                Op::Permute { perm, out } => {
                    let mut lanes = [0u64; 25];
                    for (i, &s) in self.perms[perm as usize].input.iter().enumerate() {
                        let bit = match s {
                            IN_ZERO => 0,
                            IN_ONE => 1,
                            s => words[s as usize],
                        };
                        assert!(bit <= 1, "a permutation's input is bits");
                        lanes[i / 64] |= bit << (i % 64);
                    }
                    keccak_f(&mut lanes);
                    for (i, word) in words[out as usize..out as usize + 1600].iter_mut().enumerate() {
                        *word = lanes[i / 64] >> (i % 64) & 1;
                    }
                }
            }
        }
        words
    }

    /// Group `g`'s local words (its leaves, then its local values), bit `b` its permutation `b`'s.
    fn group(&self, g: usize, words: &[u64]) -> Vec<u64> {
        let group = &self.groups[g];
        let t = &self.templates[group.template as usize];
        let mut leaves = vec![0u64; t.leaves as usize];
        for (b, &i) in group.perms.iter().enumerate() {
            for (leaf, &s) in leaves.iter_mut().zip(&self.perms[i as usize].leaves) {
                let bit = words[s as usize];
                assert!(bit <= 1, "a permutation's leaves are bits");
                *leaf |= bit << b;
            }
        }
        t.run(leaves)
    }

    /// The witness, a final row (of `W` positions) a task.
    fn fill<const W: usize, T: Send>(
        &self,
        locals: &[Vec<u64>],
        read: &(impl Fn(Src) -> u64 + Sync),
        to: &(impl Fn(K) -> T + Sync),
    ) -> Vec<T> {
        assert_eq!(W, 1 << self.log_width);
        assert_eq!(self.rows.len() * W, 1 << self.log_n);
        parallel::map_collect(self.rows.len(), |r| -> [T; W] {
            let row = self.rows[r];
            let at = row.index as usize * W;
            match row.kind {
                EMPTY => std::array::from_fn(|_| to(K(0))),
                OUTER => {
                    let sources = &self.outer[at..at + W];
                    std::array::from_fn(|role| to(K(read(sources[role]))))
                }
                perm => {
                    let p = &self.perms[perm as usize];
                    let contents = &self.templates[p.template as usize].contents[at..at + W];
                    let (local, bit) = (&locals[p.group as usize], p.bit);
                    std::array::from_fn(|role| {
                        let c = contents[role];
                        to(K(if c & HOLE == 0 {
                            local[c as usize] >> bit & 1
                        } else {
                            read(p.holes[(c & !HOLE) as usize])
                        }))
                    })
                }
            }
        })
        .into_flattened()
    }

    /// The witness (each word mapped by `to`) and the public inputs on `inputs`, as the compiler's.
    pub fn witness_with<T: Send>(&self, inputs: &Inputs, to: impl Fn(K) -> T + Sync) -> (Vec<T>, PublicInputs) {
        assert_eq!(inputs.program_iv, self.program_iv, "the plan's program IV");
        let stream = inputs.stream;
        assert_eq!(stream.len(), self.stream_len);
        let words = self.sequential(&inputs.public, stream);
        let locals: Vec<Vec<u64>> = parallel::map_collect(self.groups.len(), |g| self.group(g, &words));
        let read = |s: Src| -> u64 {
            if s == ZERO {
                0
            } else if s & LOCAL != 0 {
                let p = &self.perms[(s >> 32 & 0x7fff_ffff) as usize];
                locals[p.group as usize][s as u32 as usize] >> p.bit & 1
            } else {
                words[s as usize]
            }
        };
        let witness = match self.log_width {
            4 => self.fill::<16, T>(&locals, &read, &to),
            5 => self.fill::<32, T>(&locals, &read, &to),
            l => panic!("rows of 2^{l}"),
        };
        let public = PublicInputs {
            statement: inputs.public,
            roots: self
                .roots_at
                .iter()
                .map(|&at| stream[at..at + 32].try_into().expect("32 bytes"))
                .collect(),
            elements: self
                .elements
                .iter()
                .map(|l| E::new(words[l[0] as usize], words[l[1] as usize], words[l[2] as usize]))
                .collect(),
            claim_hashes: self
                .claim_hashes
                .iter()
                .map(|l| {
                    let mut hash = [0u8; 32];
                    for (k, &s) in l.iter().enumerate() {
                        hash[8 * k..8 * k + 8].copy_from_slice(&words[s as usize].to_be_bytes());
                    }
                    hash
                })
                .collect(),
        };
        (witness, public)
    }

    /// The witness and the public inputs on `inputs`, as [`super::compile::pi2`]'s.
    pub fn witness(&self, inputs: &Inputs) -> (Witness, PublicInputs) {
        self.witness_with(inputs, |k| k)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A compiled op's counts fit their bytes of its header: 255 linear terms compile and run, 256 are refused
    /// (rather than spill into the next count).
    #[test]
    fn compile_refuses_counts_past_a_byte() {
        let w = 256;
        let template = Template {
            rows: 1,
            leaves: 256,
            ops: vec![BitOp {
                row: 0,
                poly: 0,
                kappa: 1,
            }],
            contents: (0..256).collect(),
            code: Vec::new(),
        };
        let poly = |terms: usize| BitPoly {
            linear: (0..terms).map(|c| c as u8).collect(),
            quadratic: Vec::new(),
        };
        let mut fits = template.clone();
        fits.compile(&[poly(255)], w);
        let leaves: Vec<u64> = (0..256u64).map(|i| i.wrapping_mul(0x9E37_79B9_7F4A_7C15)).collect();
        let want = !leaves[..255].iter().fold(0, |a, &x| a ^ x);
        assert_eq!(fits.run(leaves)[256], want);
        let wide = std::panic::catch_unwind(|| template.clone().compile(&[poly(256)], w));
        assert!(wide.is_err());
    }
}
