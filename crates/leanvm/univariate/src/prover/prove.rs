// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The prover (SPEC.md §3–§8), phase by phase, on a Keccak VM trace: `C1`, the challenges, Flock, the heap
//! and the quotients, `C2`, the values at `t`, the batching sumcheck, and the openings.
//!
//! It writes the stream the verifier reads (`crate::verifier::reduce`, through the contract's Keccak-256 chain) and
//! one WHIR opening per claim (`crates/pcs_claim`). Before the batching sumcheck it runs the verifier itself on the
//! stream so far (`reduce_combined`, which reads nothing after `ρ`) to learn the combined claims, as any prover may.

use std::time::Instant;

use fiat_shamir::merkle::Hash;
use leanvm_statement::field::E;
use leanvm_statement::layout::{Form, SEP_MEM, tables};
use leanvm_statement::transcript::{Checks, KeccakChannel, KeccakWriter, keccak_seed, root_halves, statement_words};
use primitives::field::{F64, F192};
use quotient::ntt::Fill;

use super::bus::{Bus, expected_root, heap_of};
use super::columns::{c1_polys, setup_polys};
use super::flock::FlockWitness;
use super::opening::{self, Committed};
use super::poly::{eval_k, eval_limbs, novel_limbs, novel_limbs_many};
use super::quotients::{self, Quotient};
use super::stack::Stack;
use super::trace::Trace;
use super::weight::Weight;
use crate::claims::{Column, Combined, Commitment};
use crate::contract::{NAME, SetupRoots, contract_iv};
use crate::heap::Leaves;
use crate::stacks::StackLayout;
use crate::verifier::{
    Variant, bus_challenges, c1_columns, c2_columns, chunks, constraint_count, expand_ring, flush_difference,
    late_challenges, point_challenge, reduce_combined, sent_columns, table_leaf_count,
};

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
}

impl Clock {
    fn lap(&mut self, report: &mut Report, name: &'static str) {
        let now = Instant::now();
        report.phases.push((name, (now - self.last).as_secs_f64()));
        if let Some(probe) = MEMORY_PROBE.get() {
            report.peaks.push((name, probe()));
        }
        self.last = Instant::now();
    }
}

/// `tuple`'s fingerprint needs a sent value: one of its monomials reads an unsent column (`verifier::linearise`).
fn reads_unsent(tuple: &[Form], sent: &[bool]) -> bool {
    tuple.iter().any(|form| {
        form.terms()
            .any(|(monomial, c)| *c != E::default() && monomial.iter().any(|&i| !sent[i]))
    })
}

/// The prover's configuration.
#[derive(Clone, Copy, Debug)]
pub struct Config {
    /// Flock's variant (with it, the Fiat–Shamir shape): `KECCAK_MAIN`, `KECCAK_REC3` or `KECCAK_REC4`.
    pub variant: Variant,
    /// Check every combined claim against the committed stacks (slower).
    pub check: bool,
    /// Fill every stack's words past its blocks with pseudo-random words instead of zeros (a test that the verifier
    /// relies on nothing there).
    pub garbage: bool,
    /// The setup commitment the contract's IV binds (SPEC.md §13, F2): `F`'s, which must be this program's and shape's
    /// (`setup::shape_roots`; at the reference shape `SetupRoots::REFERENCE`).
    pub roots: SetupRoots,
    /// Commit `C1` without keeping its codeword (twice its stack) until its opening, which then encodes the rows its
    /// queries open again: the prover's peak (`C2`'s commitment) falls by it. The proof is the same.
    pub low_memory: bool,
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
    let mut clock = Clock { last: Instant::now() };
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
    let committed1 = if config.low_memory {
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
            f_ood: committed_f.ood.into(),
        }
    } else {
        config.roots
    };
    if committed_f.root != roots.f || E::from(committed_f.ood) != roots.f_ood {
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
    writer.send_root(&committed1.root);
    writer.send(committed1.ood.into());

    // 2. The bus's and the constraints' challenges, as the verifier draws them (`verifier::bus_challenges`, squared in
    // E as the verifier squares them).
    let fs = config.variant.fs;
    let (alphas, beta, gamma, eq_first) = bus_challenges(fs, &mut writer);
    let alphas: Vec<F192> = alphas.into_iter().map(F192::from).collect();
    let (beta, gamma) = (F192::from(beta), F192::from(gamma));

    // 3. Flock on the Keccak-f block, one block a SHA3 row (`flock.rs`), the walked (structured) terminal.
    {
        let log_n = leanvm_statement::layout::KECCAK_R1CS_LOG_SIZE + trace.heights[leanvm_statement::layout::OP_SHA3];
        let out = super::flock::prove(&mut writer, &flock, config.variant, log_n, eq_first)?;
        drop(flock);
        report.notes.push(format!("Flock's zerocheck and lincheck: {:.3} s", out.reduction_secs));
        for (stage, secs) in std::mem::take(&mut *flock::zerocheck::skip::STAGES.lock().expect("the stages")) {
            report.notes.push(format!("  the skip's zerocheck, {stage}: {secs:.3} s"));
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
            let count = table_leaf_count(&tables()[t], r);
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
    let constraint = quotients::sum_parts(constraint_parts, constraint_count(&shape));
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
    writer.send_root(&committed2.root);
    writer.send(committed2.ood.into());

    // 7. The point and the values at it, in the verifier's order. π1-rec4: t with the ring switch's map's f_0 … f_3
    // (the verifier's; the prover's batch weights take the map from the verifier's replay below).
    let t = F192::from(point_challenge(fs, &mut writer).0);
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
            if reads_unsent(&flush_difference(pushed, pulled), &sent) {
                sent_values.push(fp(pushed));
            }
        }
    }
    let lm = trace.log_memory;
    let lb = trace.log_bytecode;
    let mem_at: Vec<F192> = (0..4).map(|k| eval_k(stack1.k(Column::Memory(k)), &w[..lm])).collect();
    let address_at = eval_k(&setup.address.b, &w[..lm]);
    let memory_pull = beta
        + weights[0] * F192::from(SEP_MEM)
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
        writer.send(v.into());
    }
    clock.lap(&mut report, "values at t");

    // Past the values at t, the proof reads the stacks and their commitments alone (the heap and the quotients are
    // in C2's stack since step 6).
    drop(setup);

    // 8. ρ (π1-rec4: with the batch's λ and the map's f_4, f_5), then the combined claims: the verifier's own, on the
    // stream so far (`reduce_combined`, which reads nothing after ρ), the ring switch's weight as its 64 twisted terms.
    let drawn_lambda = if fs.wide() {
        Some(late_challenges(&mut writer).1)
    } else {
        writer.sample();
        None
    };
    let combined: Vec<(Commitment, Combined<E>)> = {
        let mut channel = KeccakChannel::new(seed, &writer.stream, Checks::collect());
        let c = reduce_combined(&shape, statement_words(&public), &mut channel, config.variant)
            .map_err(|e| format!("{e:?}"))?;
        channel.finish().map_err(|e| format!("the verifier reads the stream so far: {e:?}"))?;
        report.checks.push(("the verifier's checks on the stream so far".into(), channel.checks.hold()));
        for (commitment, layout) in &c.layouts {
            let mine = match commitment {
                Commitment::C1 => stack1.layout.vars,
                Commitment::C2 => stack2.layout.vars,
                Commitment::Setup => stack_f.layout.vars,
            };
            if mine != layout.vars {
                return Err(format!("{commitment:?}: the verifier's stack has {} variables, the prover's {mine}", layout.vars));
            }
        }
        c.combined.iter().map(|(commitment, claim)| (*commitment, expand_ring(claim, &c.ring_map))).collect()
    };
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
                .push((format!("{c:?}: its {} relations, combined by ρ, hold", claim.relations), sum == F192::from(claim.value)));
        }
        clock.lap(&mut report, "claims: the combined-claims check (test only)");
    }

    // 9. The point claims: the batching sumcheck.
    let lambda = F192::from(drawn_lambda.unwrap_or_else(|| writer.sample()));
    let stacks: Vec<(&[F64], usize)> = combined
        .iter()
        .map(|(c, _)| {
            let (s, _) = stacks_of(*c);
            (&s.words[..], s.layout.vars)
        })
        .collect();
    let (point, values) = if fs.paired_batch() {
        // π1-rec3, π1-rec4: the batch two variables a round (SPEC-POINTS.md), its claim the combined claims' values.
        let target: F192 = combined
            .iter()
            .rev()
            .fold(F192::ZERO, |acc, (_, claim)| acc * lambda + F192::from(claim.value));
        super::batch::prove_pairs(&mut writer, &stacks, weights, lambda, target)?
    } else {
        super::batch::prove(&mut writer, &stacks, weights, lambda)?
    };
    clock.lap(&mut report, "batching sumcheck");
    on_stream(&writer.stream);
    let mut openings = Vec::new();
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
        crate::contract::rust_verifier_with(trace_shape, iv, roots, public, &proof.stream, variant)
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
        let point: Vec<F192> = opening.point.iter().map(|&x| x.into()).collect();
        if *commitment != mine.commitment || F192::from(opening.value) != mine.value || point != mine.point {
            return Err(format!("{commitment:?}: the opening is not of the verifier's claim"));
        }
        // The commitment: the stream's for C1 and C2 (its root and out-of-domain answer); the setup's is the
        // contract's constant.
        let ood = E::from(mine.ood);
        let commitment_ok = match commitment {
            Commitment::C1 => reduced.roots[0] == root_halves(&mine.root) && reduced.oods[0] == ood,
            Commitment::C2 => reduced.roots[1] == root_halves(&mine.root) && reduced.oods[1] == ood,
            Commitment::Setup => mine.root == roots.f && ood == roots.f_ood,
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
