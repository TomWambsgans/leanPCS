// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The prover (SPEC.md §3–§8), phase by phase, on a Keccak VM trace: `C1`, the challenges, Flock, the heap
//! and the quotients, `C2`, the values at `t`, the batching sumcheck, and the openings.
//!
//! It writes the stream the verifier reads (`crate::verifier::reduce`, through the contract's Keccak-256 chain) and
//! one WHIR opening per claim (`crates/pcs_claim`). Before the batching sumcheck it runs the verifier itself on the stream so far
//! (weighted mode, which reads nothing after `ρ`) to learn the combined claims, as any prover may.

use std::time::Instant;

use fiat_shamir::merkle::Hash;
use leanvm_statement::field::E;
use leanvm_statement::layout::{Form, OP_JUMP, OP_SHA3, SEP_MEM, Table, tables};
use leanvm_statement::transcript::{FsShape, KeccakWriter, keccak_seed, squares};
use primitives::field::{F64, F192};
use quotient::ntt::Fill;

use super::bus::{Bus, expected_root, heap_of};
use super::columns::{c1_polys, setup_polys};
use super::flock::FlockWitness;
use super::replay::Replay;
use super::opening::{self, Committed};
use super::poly::{eval_k, eval_limbs, from_v, novel_limbs, novel_limbs_many, to_v};
use super::quotients::{self, Quotient};
use super::stack::{Stack, c1_columns, c2_columns};
use super::trace::Trace;
use super::weight::Weight;
use crate::claims::{Column, Combined, Commitment};
use crate::contract::{NAME, SetupRoots, contract_iv};
use crate::heap::Leaves;
use crate::stacks::StackLayout;
use crate::verifier::{Claims, Opening, Shape, Variant, chunks, degree, reduce, sent_columns};

/// What a proof is: the verifier's stream (calldata after the selector and the public input) and one WHIR opening
/// per claim, with the PCS claim it proves.
pub struct Proof {
    pub stream: Vec<u8>,
    pub openings: Vec<OpeningProof>,
}

/// One claim (the EIP draft's PCS claim, `crates/pcs_claim`: the stack in `vars` variables committed as `(root,
/// ood)`, at `point`, of value `value`) and its opening.
pub struct OpeningProof {
    pub commitment: Commitment,
    pub root: Hash,
    pub ood: F192,
    pub vars: usize,
    pub point: Vec<F192>,
    pub value: F192,
    pub proof: fiat_shamir::transcript::Proof,
}

impl OpeningProof {
    /// The PCS claim it proves.
    pub fn claim(&self) -> pcs_claim::PcsClaim {
        pcs_claim::PcsClaim {
            n: self.vars as u8,
            root: self.root,
            ood: self.ood,
            point: self.point.clone(),
            value: self.value,
        }
    }
}

/// Every quotient's degree against the count the verifier declares, every stack's size, and the time of each phase.
#[derive(Default, Debug)]
pub struct Report {
    pub phases: Vec<(&'static str, f64)>,
    /// (name, actual degree, the verifier's count, the extension's variables).
    pub quotients: Vec<(String, i64, u64, usize)>,
    /// (commitment, words placed, stack variables).
    pub stacks: Vec<(Commitment, u64, usize)>,
    /// Per relation family checked at `t` directly: (name, holds).
    pub checks: Vec<(String, bool)>,
    pub stream_bytes: usize,
    pub opening_bytes: Vec<usize>,
    /// Finer timings inside a phase, as text.
    pub notes: Vec<String>,
    /// The setup root the proof's contract binds.
    pub roots: Option<SetupRoots>,
    /// The process's peak resident memory at the end of each phase, in bytes, when [`MEMORY_PROBE`] is set.
    pub peaks: Vec<(&'static str, u64)>,
}

/// A reader of the process's peak resident memory (a test's `bench::peak_rss_bytes`): when set, each phase's end
/// records it in [`Report::peaks`].
pub static MEMORY_PROBE: std::sync::OnceLock<fn() -> u64> = std::sync::OnceLock::new();

struct Clock {
    last: Instant,
    faults: u64,
}

impl Clock {
    fn lap(&mut self, report: &mut Report, name: &'static str) {
        let now = Instant::now();
        report.phases.push((name, (now - self.last).as_secs_f64()));
        if let Some(probe) = MEMORY_PROBE.get() {
            report.peaks.push((name, probe()));
        }
        if std::env::var_os("PI1_PROFILE").is_some() {
            let faults = minor_faults();
            let hwm = std::fs::read_to_string("/proc/self/status")
                .ok()
                .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM:")).map(|l| l.to_string()))
                .unwrap_or_default();
            eprintln!(
                "    {name}: {:.4} s, {} minor faults, {hwm}",
                (now - self.last).as_secs_f64(),
                faults - self.faults
            );
            self.faults = faults;
        }
        self.last = Instant::now();
    }
}

/// The process's minor page faults so far (`/proc/self/stat`, field 10), 0 where unreadable: for `PI1_PROFILE`.
fn minor_faults() -> u64 {
    std::fs::read_to_string("/proc/self/stat")
        .ok()
        .and_then(|s| s.rsplit_once(')').and_then(|(_, rest)| rest.split_whitespace().nth(7)?.parse().ok()))
        .unwrap_or(0)
}

/// The root's two 128-bit halves as the stream carries them (`Channel::next_root`: each 16-byte half big-endian, `c1`
/// then `c0`), so that the stream's 32 bytes are the root's bytes as they are: the root a PCS claim encodes, which the
/// contract passes as it is.
pub fn halves(root: &Hash) -> [E; 2] {
    let word = |at: usize| u64::from_be_bytes(root[at..at + 8].try_into().expect("8 bytes"));
    [E::new(word(8), word(0), 0), E::new(word(24), word(16), 0)]
}

/// `tuple`'s fingerprint needs a sent value: one of its monomials reads an unsent column (`verifier::linearise`).
fn reads_unsent(tuple: &[Form], sent: &[bool]) -> bool {
    tuple.iter().any(|form| {
        form.terms()
            .any(|(monomial, c)| *c != E::default() && monomial.iter().any(|&i| !sent[i]))
    })
}

/// The degree of a tuple's fingerprint in the columns (`verifier::tuple_degree`).
fn tuple_degree(tuple: &[Form]) -> usize {
    tuple
        .iter()
        .flat_map(|form| form.terms().filter(|(_, c)| **c != E::default()).map(|(m, _)| m.len()))
        .max()
        .unwrap_or(0)
        .max(1)
}

/// The verifier's count of a table block's leaf quotient coefficients: sized for the height's fewest rows
/// (`Shape::least_rows`, SPEC.md §13, F1).
pub fn table_leaf_count(t: usize, r: usize) -> u64 {
    table_leaf_count_for(&tables()[t], r)
}

/// [`table_leaf_count`] of a table of either VM (`verifier::vm_tables`).
pub fn table_leaf_count_for(table: &Table, r: usize) -> u64 {
    let n = 1u64 << r;
    let pull = 1 + table.flushes.pull.iter().map(|tu| tuple_degree(tu)).sum::<usize>();
    let push: usize = table.flushes.push.iter().map(|tu| tuple_degree(tu)).sum();
    degree(pull.max(push) as u64 * (n - 1) + (n - Shape::least_rows(r)), n) + 1
}

/// The verifier's count of the constraint quotient's coefficients (`verifier::reduce`, step 5).
pub fn constraint_count(trace: &Trace) -> u64 {
    let mut most = 0u64;
    for table in tables() {
        let r = trace.heights[table.opcode];
        let n = 1u64 << r;
        if table.opcode == OP_JUMP {
            most = most.max(degree(n, 2));
        }
        let counts = table.count_columns().count() as u64;
        most = most.max(degree((n - 1) * (1 + counts), n));
        if table.opcode == OP_SHA3 {
            most = most.max(degree(r as u64 * (n / 2), n));
        }
    }
    most.max(degree(1u64 << trace.log_memory, 3)) + 1
}

/// The prover's configuration.
#[derive(Clone, Copy, Debug)]
pub struct Config {
    /// Flock's variant (with it, the Fiat–Shamir shape): `KECCAK_MAIN` or `KECCAK_REC3`.
    pub variant: Variant,
    pub claims: Claims,
    /// Check every combined claim against the committed stacks (slower).
    pub check: bool,
    /// Fill every stack's words past its blocks with pseudo-random words instead of zeros (a test that the verifier
    /// relies on nothing there).
    pub garbage: bool,
    /// The setup commitment the contract's IV binds (SPEC.md §13, F2): `F`'s, which must be this program's and shape's
    /// (`setup::shape_roots`; at the reference shape `SetupRoots::REFERENCE`).
    pub roots: SetupRoots,
}

/// Prove `trace`'s execution (its rows placed: [`Trace::place`]) for the contract of the program's IV `iv` (the
/// contract's own binds the setup root, the shape and the variant: `contract::contract_iv`), from the Flock witness of
/// its placed `SHA3` rows (`Trace::keccak_flock`).
pub fn prove(trace: &Trace, flock: FlockWitness, iv: &[u8; 32], config: Config) -> Result<(Proof, Report), String> {
    prove_streaming(trace, flock, iv, config, |_| {})
}

/// [`prove`], handing the stream to `on_stream` as soon as it is final (after the batching sumcheck, before the
/// openings, which write nothing to it): a recursion can start compiling π2's witness while the openings run.
pub fn prove_streaming(
    trace: &Trace,
    flock: FlockWitness,
    iv: &[u8; 32],
    config: Config,
    on_stream: impl FnOnce(&[u8]),
) -> Result<(Proof, Report), String> {
    let mut report = Report::default();
    let mut clock = Clock {
        last: Instant::now(),
        faults: minor_faults(),
    };
    if !trace.placed {
        return Err("the trace's rows are leanVM's order: place them first (Trace::place)".into());
    }
    let shape = trace.shape();
    if shape.heights() != trace.heights {
        return Err(format!("leanVM's heights {:?} are not the verifier's {:?}", trace.heights, shape.heights()));
    }
    shape.validate().map_err(|e| format!("the shape: {e:?}"))?;
    let public = trace.public_input();

    // 1. C1: every column in basis B, q_flock as values.
    let c1 = c1_polys(trace);
    let setup = setup_polys(trace);
    clock.lap(&mut report, "C1 and setup: inverse NTTs to basis B");
    // q_flock: the Flock witness's packed words (`Trace::keccak_flock`), which the trace does not keep; every other
    // column's subset sums, all in the same dispatches.
    let mut fills: Vec<(Column, usize, Fill)> = vec![(Column::Qflock, 0, Fill::Raw(&flock.z))];
    for (t, columns) in c1.tables.iter().enumerate() {
        for (c, column) in columns.iter().enumerate() {
            fills.push((Column::Table { table: t, column: c }, 0, Fill::Sums(&column.novel)));
        }
        fills.push((Column::Inverse(t), 0, Fill::Sums(&c1.inverses[t].novel)));
    }
    for (k, column) in c1.memory.iter().enumerate() {
        fills.push((Column::Memory(k), 0, Fill::Sums(&column.novel)));
    }
    fills.push((Column::BytecodeFinal, 0, Fill::Sums(&c1.bytecode_final.novel)));
    let mut stack1 = Stack::filled(StackLayout::new(&c1_columns(&shape)), &fills);
    drop(fills);
    let mut stack_f = super::setup::f_stack(&shape, &setup);
    if config.garbage {
        stack1.fill_unused(0xC1);
        stack_f.fill_unused(0xF0);
    }
    // `PI1_LOW_MEMORY=1`: C1's codeword (twice its stack) is not kept until its opening, which encodes the rows its
    // queries open again: the prover's peak (C2's commitment) falls by it. The proof is the same.
    let low_memory = std::env::var_os("PI1_LOW_MEMORY").is_some_and(|v| v != "0");
    let committed1 = if low_memory {
        opening::commit(&stack1.words, stack1.layout.vars)
    } else {
        opening::commit_keeping_codeword(&stack1.words, stack1.layout.vars)
    };
    let committed_f = opening::commit_keeping_codeword(&stack_f.words, stack_f.layout.vars);
    // The contract binds F's commitment (and its claim on F is against it): it must be this program's and shape's.
    // Garbage in the unused words makes another F, which only a contract built for it accepts: that contract's is used.
    let roots = if config.garbage {
        SetupRoots {
            f: committed_f.root,
            f_ood: to_v(committed_f.ood),
        }
    } else {
        config.roots
    };
    if committed_f.root != roots.f || to_v(committed_f.ood) != roots.f_ood {
        return Err("the contract's F commitment is not this program's and shape's (prover::setup::shape_roots)".into());
    }
    report.roots = Some(roots);
    report.stacks.push((Commitment::C1, stack1.placed(), stack1.layout.vars));
    report.stacks.push((Commitment::Setup, stack_f.placed(), stack_f.layout.vars));
    clock.lap(&mut report, "C1 and setup: WHIR commits");

    // 0. The seed (the contract's IV binds the setup root), then the six row counts (SPEC.md §13, F1), absorbed with
    // C1's root.
    let seed = keccak_seed(&NAME, &contract_iv(&shape, config.variant, iv, &roots), &public);
    let mut writer = KeccakWriter::new(seed);
    for &rows in &trace.rows {
        writer.send_integer(rows, 4);
    }
    // C1's commitment: its root, then its out-of-domain answer, which binds the root to one polynomial before any
    // challenge (docs/PCS_CLAIM.md).
    writer.send_root(halves(&committed1.root));
    writer.send(to_v(committed1.ood));

    // 2. The bus's and the constraints' challenges; with π1-rec (`FsShape::Rec`, SPEC-REC.md §1.4) α is (c, c², c⁴,
    // c⁸) of one challenge c, squared in E as the verifier squares it.
    let alphas: Vec<F192> = match config.variant.fs {
        FsShape::Main => (0..4).map(|_| from_v(writer.sample())).collect(),
        FsShape::Rec | FsShape::Rec2 | FsShape::Rec3 => squares(writer.sample(), 4).into_iter().map(from_v).collect(),
    };
    let beta = from_v(writer.sample());
    let gamma = from_v(writer.sample());

    // 3. Flock on the Keccak-f block, one block a SHA3 row (`flock.rs`), the walked (structured) terminal.
    {
        let log_n = leanvm_statement::layout::KECCAK_R1CS_LOG_SIZE + trace.heights[OP_SHA3];
        let out = super::flock::prove(&mut writer, &flock, config.variant, log_n)?;
        drop(flock);
        report.notes.push(format!("Flock's zerocheck and lincheck: {:.3} s", out.reduction_secs));
        for (stage, secs) in std::mem::take(&mut *flock::zerocheck::skip::STAGES.lock().expect("the stages")) {
            report.notes.push(format!("  the skip's zerocheck, {stage}: {secs:.3} s"));
        }
        if std::env::var_os("PI1_PROFILE").is_some() {
            report.notes.iter().for_each(|note| eprintln!("    {note}"));
        }
        clock.lap(&mut report, "Flock: zerocheck, lincheck, slices");
    }

    // 4. The heap.
    let bus = Bus::new(&alphas, beta);
    let layout = shape.heap();
    let heap_values = heap_of(trace, &bus, &layout)?;
    let root = expected_root(&bus, trace.log_bytecode);
    report.checks.push(("bus: the heap's root is the state boundary's ratio (push = pull)".into(), heap_values[1] == root));
    if heap_values[1] != root {
        return Err("the bus does not balance: the heap's root is not fp(final) / fp(initial)".into());
    }
    let heap_novel = novel_limbs(&heap_values);
    // Every block's heap (`R`, its leaves) as novel coefficients, the blocks of one height in the same dispatches.
    let blocks: Vec<(usize, Leaves, usize)> = layout
        .blocks
        .iter()
        .enumerate()
        .filter(|(_, b)| b.leaves != Leaves::Unused)
        .map(|(i, b)| (i, b.leaves, b.r))
        .collect();
    let r_novels: Vec<[Vec<F64>; 3]> = novel_limbs_many(
        &blocks
            .iter()
            .map(|&(i, _, r)| {
                let at = layout.blocks[i].position as usize;
                &heap_values[at..at + (1 << r)]
            })
            .collect::<Vec<_>>(),
    );
    drop(heap_values);
    clock.lap(&mut report, "heap: leaves, products, inverse NTT");

    // 5. The quotients.
    let tree = quotients::tree(&heap_novel);
    report.quotients.push(("tree".into(), tree.degree, tree.count, layout.h + 1));
    clock.lap(&mut report, "quotient: tree");
    // The tables' leaves and `Q_W`'s tables' parts, every stage of all of them in the same dispatches; then the
    // memory's and the bytecode's leaves and `Q_W`'s public part, whose columns are long.
    let parts = quotients::constraint_parts(trace, stack1.k(Column::Qflock), &c1, gamma);
    let mut jobs: Vec<Box<dyn quotients::Numerator + '_>> = Vec::new();
    for (&(_, kind, r), r_novel) in blocks.iter().zip(&r_novels) {
        if let Leaves::Table(t) = kind {
            let count = table_leaf_count_for(&tables()[t], r);
            jobs.push(quotients::table_leaf_numerator(trace, t, &c1, &bus, r_novel, count));
        }
    }
    jobs.extend(parts.tables.iter().map(|p| p.numerator(&c1)));
    let mut batched = quotients::prefix_quotients(&jobs.iter().map(|j| &**j).collect::<Vec<_>>()).into_iter();
    drop(jobs);
    clock.lap(&mut report, "quotients: the tables' leaves and Q_W's parts");
    let mut leaf_quotients: Vec<(usize, Quotient)> = Vec::new();
    for (&(index, kind, r), r_novel) in blocks.iter().zip(&r_novels) {
        let n = 1u64 << r;
        let (name, q) = match kind {
            Leaves::Memory => ("leaf: memory".to_string(), quotients::memory_leaf(trace, &c1, &setup, &bus, r_novel, n - 1)),
            Leaves::Bytecode => (
                "leaf: bytecode".to_string(),
                quotients::bytecode_leaf(trace, &c1, &setup, &bus, r_novel, n - 1),
            ),
            Leaves::Table(t) => (
                format!("leaf: {}", leanvm_statement::TABLE_NAMES[t]),
                batched.next().expect("a table's leaf"),
            ),
            Leaves::Unused => unreachable!(),
        };
        report
            .quotients
            .push((name, q.degree, q.count, quotients::extension_vars(q.count, r)));
        leaf_quotients.push((index, q));
    }
    debug_assert_eq!(batched.len(), parts.tables.len());
    drop(r_novels);
    clock.lap(&mut report, "quotients: memory and bytecode leaves");
    let r_w = shape.constraint_vars();
    let lines = {
        let [a, b] = trace.public;
        [(F64(a[0]), F64(b[0])), (F64(a[1]), F64(b[1])), (F64::ZERO, F64::ZERO)]
    };
    let mut constraint_parts: Vec<Quotient> = batched.collect();
    constraint_parts.push(quotients::public_part(trace, &c1, parts.publics, lines));
    let constraint = quotients::sum_parts(constraint_parts, constraint_count(trace));
    report
        .quotients
        .push(("constraints Q_W".into(), constraint.degree, constraint.count, quotients::extension_vars(constraint.count, r_w)));
    clock.lap(&mut report, "quotient: constraints");
    for (name, degree, count, _) in &report.quotients {
        if *degree >= *count as i64 {
            return Err(format!("{name}: degree {degree} is not below the verifier's count {count}"));
        }
    }
    // Past the quotients, C1's polynomials are not read again (the values at t read the stacks): freed
    // before C2's commitment, the prover's peak (the columns' variables kept, for the values at t).
    let table_vars: Vec<Vec<usize>> = c1.tables.iter().map(|t| t.iter().map(|c| c.vars()).collect()).collect();
    drop(c1);

    // 6. C2.
    let constraint_sizes = chunks(constraint.count);
    let leaf_sizes: Vec<(usize, Vec<usize>)> = leaf_quotients.iter().map(|(b, q)| (*b, chunks(q.count))).collect();
    let mut stack2 = {
        // The heap's limbs and every quotient's chunks' limbs: all their subset sums in the same dispatches.
        let mut fills: Vec<(Column, usize, Fill)> = Vec::new();
        for (limb, novel) in heap_novel.iter().enumerate() {
            fills.push((Column::Heap, limb, Fill::Sums(novel)));
        }
        let tree_sizes = [layout.h, 0];
        type ColumnOf<'a> = Box<dyn Fn(usize) -> Column + 'a>;
        let mut all: Vec<(&Quotient, &[usize], ColumnOf)> = vec![
            (&tree, &tree_sizes[..], Box::new(Column::TreeQuotient)),
            (&constraint, &constraint_sizes[..], Box::new(Column::ConstraintQuotient)),
        ];
        for ((block, q), (_, sizes)) in leaf_quotients.iter().zip(&leaf_sizes) {
            all.push((q, sizes, Box::new(move |chunk| Column::LeafQuotient { block: *block, chunk })));
        }
        for (q, sizes, column) in &all {
            for chunk in 0..sizes.len() {
                for limb in 0..3 {
                    fills.push((column(chunk), limb, Fill::Sums(q.chunk_novel(sizes, chunk, limb))));
                }
            }
        }
        Stack::filled(StackLayout::new(&c2_columns(layout.h, &constraint_sizes, &leaf_sizes)), &fills)
    };
    drop((heap_novel, tree, constraint, leaf_quotients));
    clock.lap(&mut report, "C2: chunks in basis B");
    if config.garbage {
        stack2.fill_unused(0xC2);
    }
    let committed2 = opening::commit_keeping_codeword(&stack2.words, stack2.layout.vars);
    report.stacks.push((Commitment::C2, stack2.placed(), stack2.layout.vars));
    clock.lap(&mut report, "C2: WHIR commit");
    writer.send_root(halves(&committed2.root));
    writer.send(to_v(committed2.ood));

    // 7. The point and the values at it, in the verifier's order.
    let t = from_v(writer.sample());
    let digit_count = layout.h.max(r_w + 4) + 2;
    let w: Vec<F192> = std::iter::successors(Some(t), |&x| Some(x * x + x)).take(digit_count).collect();
    let mut sent_values: Vec<F192> = Vec::new();
    let weights = &bus.weights;
    for table in tables() {
        let tvars = &table_vars[table.opcode];
        let b = |c: usize| stack1.k(Column::Table { table: table.opcode, column: c });
        let at: Vec<F192> = parallel::map_collect(tvars.len(), |c| primitives::multilinear::mle_eval(b(c), &w[..tvars[c]]));
        let mut sent = vec![false; table.width()];
        for c in sent_columns(&table) {
            sent_values.push(at[c]);
            sent[c] = true;
        }
        for (pulled, pushed) in table.flushes.pull.iter().zip(&table.flushes.push) {
            let fp = |tuple: &[Form]| super::fingerprint::Fingerprint::new(tuple, weights, beta).at_e(|c| at[c]);
            if reads_unsent(pulled, &sent) {
                sent_values.push(fp(pulled));
            }
            let difference: Vec<Form> = pushed
                .iter()
                .zip(pulled)
                .map(|(a, b)| {
                    let mut d = a.clone();
                    d.add_scaled(b, E::new(1, 0, 0));
                    d
                })
                .collect();
            if reads_unsent(&difference, &sent) {
                sent_values.push(fp(pushed));
            }
        }
    }
    let lm = trace.log_memory;
    let lb = trace.log_bytecode;
    let mem_at: Vec<F192> = (0..4).map(|k| eval_k(stack1.k(Column::Memory(k)), &w[..lm])).collect();
    let address_at = eval_k(&setup.address.b, &w[..lm]);
    let memory_pull = beta
        + weights[0] * from_v(SEP_MEM)
        + weights[1] * address_at
        + weights[2] * mem_at[3]
        + (0..3).fold(F192::ZERO, |acc, k| acc + weights[3 + k] * mem_at[k]);
    sent_values.extend([mem_at[3], address_at, memory_pull]);
    let bytecode_final_at = eval_k(stack1.k(Column::BytecodeFinal), &w[..lb]);
    let slots_at: Vec<F192> = setup.slots.iter().map(|s| eval_k(&s.b, &w[..lb])).collect();
    let bytecode_pull = beta
        + weights[2] * bytecode_final_at
        + (0..16).filter(|&s| s != 2).fold(F192::ZERO, |acc, s| acc + weights[s] * slots_at[s]);
    sent_values.extend([bytecode_final_at, bytecode_pull]);
    let heap_at = eval_limbs(stack2.limbs(Column::Heap), &w);
    let constraint_at = {
        let mut factor = F192::ONE;
        let mut sum = F192::ZERO;
        for (c, &e) in constraint_sizes.iter().enumerate() {
            sum += factor * eval_limbs(stack2.limbs(Column::ConstraintQuotient(c)), &w);
            factor *= w[e];
        }
        sum
    };
    sent_values.extend([heap_at, constraint_at]);
    for &v in &sent_values {
        writer.send(to_v(v));
    }
    clock.lap(&mut report, "values at t");

    // Past the values at t, the proof reads the stacks and their commitments alone (the heap and the quotients are
    // in C2's stack since step 6).
    drop(setup);

    // 8. ρ, and the combined claims: the verifier's own, on the stream so far, in weighted mode (which reads nothing
    // after ρ).
    let rho = writer.sample();
    let combined: Vec<(Commitment, Combined<E>)> = {
        let mut channel = Replay::new(seed, &writer.stream);
        let words: [E; 4] = std::array::from_fn(|k| E::new(u64::from_be_bytes(public[8 * k..8 * k + 8].try_into().unwrap()), 0, 0));
        let reduced = reduce(&shape, words, &mut channel, config.variant, Claims::Weighted).map_err(|e| format!("{e:?}"))?;
        channel.finish().map_err(|e| format!("the verifier reads the stream so far: {e}"))?;
        report.checks.push(("the verifier's checks on the stream so far (weighted mode)".into(), channel.checks_hold()));
        for (commitment, vars) in &reduced.stack_vars {
            let mine = match commitment {
                Commitment::C1 => stack1.layout.vars,
                Commitment::C2 => stack2.layout.vars,
                Commitment::Setup => stack_f.layout.vars,
            };
            if mine != *vars {
                return Err(format!("{commitment:?}: the verifier's stack has {vars} variables, the prover's {mine}"));
            }
        }
        reduced
            .openings
            .into_iter()
            .map(|(c, o)| match o {
                Opening::Weighted(claim) => (c, claim),
                Opening::Point { .. } => unreachable!("weighted mode"),
            })
            .collect()
    };
    let _ = rho;
    clock.lap(&mut report, "claims: the verifier's combination");

    let stacks_of = |c: Commitment| -> (&Stack, &Committed) {
        match c {
            Commitment::C1 => (&stack1, &committed1),
            Commitment::C2 => (&stack2, &committed2),
            Commitment::Setup => (&stack_f, &committed_f),
        }
    };
    let weights: Vec<Weight> = combined
        .iter()
        .map(|(c, claim)| Weight::with_slot_bits(claim, &stacks_of(*c).0.layout, crate::verifier::QFLOCK_ROW_BITS))
        .collect();
    clock.lap(&mut report, "claims: weights");
    if config.check {
        for ((c, claim), weight) in combined.iter().zip(&weights) {
            let sum = weight.sum(&stacks_of(*c).0.words);
            report
                .checks
                .push((format!("{c:?}: its {} relations, combined by ρ, hold", claim.relations), sum == from_v(claim.value)));
        }
        clock.lap(&mut report, "claims: the combined-claims check (test only)");
    }

    // 9. The point claims: the batching sumcheck.
    let mut openings = Vec::new();
    match config.claims {
        Claims::Point => {
            let lambda = from_v(writer.sample());
            let stacks: Vec<(&[F64], usize)> = combined
                .iter()
                .map(|(c, _)| {
                    let (s, _) = stacks_of(*c);
                    (&s.words[..], s.layout.vars)
                })
                .collect();
            let fs = config.variant.fs;
            let narrow = matches!(fs, FsShape::Rec2 | FsShape::Rec3);
            let (point, values) = if fs == FsShape::Rec3 {
                // π1-rec3: the batch two variables a round (SPEC-POINTS.md), its claim the combined claims' values.
                let target: F192 = combined
                    .iter()
                    .rev()
                    .fold(F192::ZERO, |acc, (_, claim)| acc * lambda + from_v(claim.value));
                super::batch::prove_pairs(&mut writer, &stacks, weights, lambda, target)?
            } else {
                super::batch::prove(&mut writer, &stacks, weights, lambda, narrow)?
            };
            clock.lap(&mut report, "batching sumcheck");
            on_stream(&writer.stream);
            for ((c, _), &value) in combined.iter().zip(&values) {
                let (stack, committed) = stacks_of(*c);
                let p = point[..stack.layout.vars].to_vec();
                let proof = opening::open(&stack.words, committed, &p, value);
                openings.push(OpeningProof {
                    commitment: *c,
                    root: committed.root,
                    ood: committed.ood,
                    vars: committed.n,
                    point: p,
                    value,
                    proof,
                });
            }
            clock.lap(&mut report, "openings: WHIR");
        }
        Claims::Weighted => return Err("weighted claims (extension W) have no opening here: use Claims::Point".into()),
    }
    report.stream_bytes = writer.stream.len();
    report.opening_bytes = openings
        .iter()
        .map(|o| 24 * o.proof.stream.len() + o.proof.merkle.iter().map(merkle_bytes).sum::<usize>())
        .collect();
    Ok((
        Proof {
            stream: writer.stream,
            openings,
        },
        report,
    ))
}

fn merkle_bytes(paths: &fiat_shamir::merkle::PrunedMerklePaths) -> usize {
    paths.leaf_data.iter().map(|row| 8 * row.len()).sum::<usize>() + 32 * paths.sibling_hashes.len()
}

/// Verify a proof: the verifier's `reduce` on the stream (its zero and nonzero checks held to account) and every
/// opening's WHIR proof (`pcs_verify` of its PCS claim), its claim the one the verifier leaves.
///
/// The contract binds `roots` in its IV (`contract::rust_verifier_with`), and the setup claim's commitment must be its
/// `F`.
pub fn verify(
    trace_shape: &crate::verifier::Shape,
    iv: &[u8; 32],
    roots: &SetupRoots,
    public: &[u8; 32],
    proof: &Proof,
    variant: Variant,
) -> Result<(), String> {
    let (reduced, zero, nonzero) =
        crate::contract::rust_verifier_with(trace_shape, iv, roots, public, &proof.stream, variant, Claims::Point)
            .map_err(|e| format!("reduce: {e:?}"))?;
    if let Some(i) = zero.iter().position(|x| *x != E::default()) {
        return Err(format!("check {i} of {} required zero is not", zero.len()));
    }
    if let Some(i) = nonzero.iter().position(|x| *x == E::default()) {
        return Err(format!("check {i} required nonzero is zero"));
    }
    if reduced.openings.len() != proof.openings.len() {
        return Err("one opening per commitment".into());
    }
    for ((commitment, opening), mine) in reduced.openings.iter().zip(&proof.openings) {
        let Opening::Point { point, value } = opening else {
            return Err("point claims".into());
        };
        if *commitment != mine.commitment || from_v(*value) != mine.value || point.iter().map(|&x| from_v(x)).collect::<Vec<_>>() != mine.point {
            return Err(format!("{commitment:?}: the opening is not of the verifier's claim"));
        }
        // The commitment: the stream's for C1 and C2 (its root and out-of-domain answer); the setup's is the
        // contract's constant.
        let commitment_ok = match commitment {
            Commitment::C1 => reduced.roots[0] == halves(&mine.root) && reduced.oods[0] == to_v(mine.ood),
            Commitment::C2 => reduced.roots[1] == halves(&mine.root) && reduced.oods[1] == to_v(mine.ood),
            Commitment::Setup => mine.root == roots.f && to_v(mine.ood) == roots.f_ood,
        };
        if !commitment_ok {
            return Err(format!("{commitment:?}: the claim's commitment is not the stream's (or the contract's)"));
        }
        let stack_vars = reduced.stack_vars.iter().find(|(c, _)| c == commitment).map(|&(_, v)| v);
        if stack_vars != Some(mine.vars) {
            return Err(format!("{commitment:?}: the claim's variables are not the stack's"));
        }
        opening::verify(&mine.claim(), &opening::wire_proof(&mine.proof))
            .map_err(|e| format!("{commitment:?}: WHIR rejects: {e:?}"))?;
    }
    Ok(())
}
