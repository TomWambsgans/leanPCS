// Part of this repository. The tuples and the framework blocks are leanVM 42422001's (crates/verifier/src/{layout,
// bus}.rs there, through `leanvm_statement`). MIT OR Apache-2.0; see AGENTS.md.
//! The bus as a product heap (SPEC.md §5), prover side: every leaf's push-over-pull ratio, and the heap of their
//! products.

use leanvm_statement::N_TABLES;
use leanvm_statement::layout::{SEP_BYTECODE, SEP_MEM, SEP_STATE, gpow};
use primitives::field::{F64, F192, g_pow, g_powers, mul_by_g};
use quotient::ntt::Kx8;

use super::fingerprint::Fingerprint;
use super::prints::{Print, product};
use super::poly::{batch_invert, from_v};
use super::trace::Trace;
use crate::domain::is_active;
use crate::heap::{HeapLayout, Leaves};

/// The bus challenges and every table's flush fingerprints, compiled.
pub struct Bus {
    /// `eq(α, s)` for the 16 tuple slots.
    pub weights: Vec<F192>,
    pub beta: F192,
    /// Per table, per flush: the pulled and the pushed tuple's fingerprint.
    pub pull: Vec<Vec<Fingerprint>>,
    pub push: Vec<Vec<Fingerprint>>,
}

impl Bus {
    /// The Keccak VM's bus (`layout::tables`).
    pub fn new(alphas: &[F192], beta: F192) -> Self {
        let weights = primitives::multilinear::eq_table(alphas);
        let layout = leanvm_statement::layout::tables();
        let pull = layout
            .iter()
            .map(|t| t.flushes.pull.iter().map(|tuple| Fingerprint::new(tuple, &weights, beta)).collect())
            .collect();
        let push = layout
            .iter()
            .map(|t| t.flushes.push.iter().map(|tuple| Fingerprint::new(tuple, &weights, beta)).collect())
            .collect();
        Self {
            weights,
            beta,
            pull,
            push,
        }
    }

    /// The memory cell's pulled fingerprint (`count` its final count) or pushed one (`count = 1`).
    pub fn memory(&self, address: F64, count: F64, limbs: [F64; 3]) -> F192 {
        let w = &self.weights;
        let mut acc = self.beta + w[0] * from_v(SEP_MEM) + w[1].mul_base(address) + w[2].mul_base(count);
        for (k, &limb) in limbs.iter().enumerate() {
            acc += w[3 + k].mul_base(limb);
        }
        acc
    }

    /// The instruction's fingerprint: its 16 slots (slot 2 the count).
    pub fn bytecode(&self, slots: impl Fn(usize) -> F64) -> F192 {
        (0..16).fold(self.beta, |acc, s| acc + self.weights[s].mul_base(slots(s)))
    }

    /// `β + fp(SEP_STATE, pc, 1)`.
    pub fn state(&self, pc: F192) -> F192 {
        let w = &self.weights;
        self.beta + w[0] * from_v(SEP_STATE) + w[1] * pc + w[2]
    }
}

/// Table `t`'s leaves: `Π_j D'_j / Π_j D_j` on its active rows, 1 on its padding rows. Fails (returns the row) if
/// a pulled fingerprint vanishes.
pub fn table_leaves(trace: &Trace, t: usize, bus: &Bus) -> Result<Vec<F192>, usize> {
    assert!(trace.placed, "the rows at the verifier's positions");
    let columns = &trace.tables[t];
    let r = trace.heights[t];
    let n = 1usize << r;
    let rows = trace.rows[t];
    let active = |i: usize| is_active(i as u64, rows, r);
    let (pull, push) = (&bus.pull[t], &bus.push[t]);
    // The pull and push products, eight rows at a time (one at a time below eight rows).
    let mut den = vec![F192::ONE; n];
    let mut num = vec![F192::ONE; n];
    if n >= 8 {
        let prints = |list: &[Fingerprint]| -> Vec<Print<usize>> { list.iter().map(|f| Print::new(f, |c| c)).collect() };
        let (pull, push) = (prints(pull), prints(push));
        parallel::chunks_mut2(&mut den, &mut num, 1 << 10, |b, den, num| {
            for (k, (d, m)) in den.chunks_exact_mut(8).zip(num.chunks_exact_mut(8)).enumerate() {
                let at = (b << 10) + 8 * k;
                let col = |c: usize| Kx8::load(&columns[c][at..]);
                d.copy_from_slice(&product(&pull, col).to_array());
                m.copy_from_slice(&product(&push, col).to_array());
            }
        });
    } else {
        for i in 0..n {
            den[i] = pull.iter().fold(F192::ONE, |acc, f| acc * f.at(|c| columns[c][i]));
            num[i] = push.iter().fold(F192::ONE, |acc, f| acc * f.at(|c| columns[c][i]));
        }
    }
    parallel::for_each_mut(&mut den, |i, d| {
        if !active(i) {
            *d = F192::ONE;
        }
    });
    if let Some(i) = den.iter().position(|d| d.is_zero()) {
        return Err(i);
    }
    batch_invert(&mut den);
    parallel::chunks_mut_zip(&mut den, &num, 1 << 12, |b, den, num| {
        for (k, (d, &m)) in den.iter_mut().zip(num).enumerate() {
            if active((b << 12) + k) {
                *d *= m;
            }
        }
    });
    Ok(den)
}

/// The memory's leaves: `D_init / D_fin` of every cell.
pub fn memory_leaves(trace: &Trace, bus: &Bus) -> Vec<F192> {
    let n = 1usize << trace.log_memory;
    let address = g_powers(n);
    let m = &trace.memory;
    let limbs = |i: usize| [m[0][i], m[1][i], m[2][i]];
    let mut den: Vec<F192> = parallel::map_collect(n, |i| bus.memory(address[i], m[3][i], limbs(i)));
    batch_invert(&mut den);
    parallel::for_each_mut(&mut den, |i, slot| *slot *= bus.memory(address[i], F64::ONE, limbs(i)));
    den
}

/// The bytecode's 16 tuple slots at instruction `i`, its count `count`.
pub fn bytecode_slot(trace: &Trace, pc: &[F64], i: usize, s: usize, count: F64) -> F64 {
    let n = 1usize << trace.log_bytecode;
    match s {
        0 => F64(SEP_BYTECODE.c0),
        1 => pc[i],
        2 => count,
        _ => trace.bytecode[s * n + i],
    }
}

/// The bytecode's leaves: `D_init / D_fin` of every instruction.
pub fn bytecode_leaves(trace: &Trace, bus: &Bus) -> Vec<F192> {
    let n = 1usize << trace.log_bytecode;
    let pc = g_powers(n);
    let fp = |i: usize, count: F64| bus.bytecode(|s| bytecode_slot(trace, &pc, i, s, count));
    let mut den: Vec<F192> = parallel::map_collect(n, |i| fp(i, trace.bytecode_final[i]));
    batch_invert(&mut den);
    parallel::for_each_mut(&mut den, |i, slot| *slot *= fp(i, F64::ONE));
    den
}

/// The heap: position `i` holds node `i`, the leaves at `[2^(H-1), 2^H)` in `layout`'s blocks, unused blocks 1,
/// every inner node the product of its children, position 0 zero.
pub fn heap(layout: &HeapLayout, leaves: &[(Leaves, Vec<F192>)]) -> Vec<F192> {
    let size = 1usize << layout.h;
    // The leaves' blocks (each aligned to its length), written in parallel: a 2^22-node heap's fill and copies took
    // one thread milliseconds.
    let mut sources: Vec<(usize, &[F192])> = Vec::new();
    for block in &layout.blocks {
        if block.leaves == Leaves::Unused {
            continue;
        }
        let (_, values) = leaves.iter().find(|(l, _)| *l == block.leaves).expect("the block's leaves");
        assert_eq!(values.len(), 1 << block.r);
        sources.push((block.position as usize, values));
    }
    let mut heap: Vec<F192> = parallel::map_collect(size, |_| F192::ONE);
    // Chunks no longer than the shortest block: each in one block or none.
    let chunk = sources.iter().map(|(_, v)| v.len()).min().unwrap_or(size).clamp(1, 1 << 12);
    parallel::chunks_mut(&mut heap, chunk, |j, part| {
        let first = j * chunk;
        if let Some((at, v)) = sources.iter().find(|(at, v)| (*at..*at + v.len()).contains(&first)) {
            part.copy_from_slice(&v[first - at..first - at + part.len()]);
        }
    });
    tree_levels(&mut heap);
    heap
}

/// The root the state boundary requires: `fp(final) / fp(initial)`.
pub fn expected_root(bus: &Bus, log_bytecode: usize) -> F192 {
    let last = from_v(gpow((1u64 << log_bytecode) - 1));
    bus.state(last) * bus.state(F192::ONE).inv()
}

/// All leaves, by block kind ([`table_leaves`], [`memory_leaves`], [`bytecode_leaves`]: the same values, from
/// [`leaf_chunks`]).
pub fn all_leaves(trace: &Trace, bus: &Bus) -> Result<Vec<(Leaves, Vec<F192>)>, String> {
    let mut kinds = vec![Leaves::Memory, Leaves::Bytecode];
    kinds.extend((0..N_TABLES).map(Leaves::Table));
    let rows = LEAF_ROWS.min(1 << block_rows(trace, &kinds).into_iter().min().expect("a block"));
    let (chunks, firsts) = leaf_chunks(trace, bus, &kinds, rows)?;
    Ok(kinds
        .iter()
        .enumerate()
        .map(|(k, &kind)| (kind, chunks[firsts[k]..firsts[k + 1]].concat()))
        .collect())
}

/// The rows' variables of each block kind's leaves.
fn block_rows(trace: &Trace, kinds: &[Leaves]) -> Vec<usize> {
    kinds
        .iter()
        .map(|kind| match *kind {
            Leaves::Memory => trace.log_memory,
            Leaves::Bytecode => trace.log_bytecode,
            Leaves::Table(t) => trace.heights[t],
            Leaves::Unused => unreachable!("an unused block has no leaves"),
        })
        .collect()
}

/// The most rows a task of [`leaf_chunks`] takes.
const LEAF_ROWS: usize = 1 << 10;

/// The leaves of the blocks `kinds`, in chunks of `rows` rows (a power of two, at most a block's), block `k`'s chunks
/// `firsts[k]..firsts[k + 1]`, all in one dispatch: a chunk's fingerprints (a table's eight rows at a time, its
/// padding rows' skipped), their inverses by Montgomery's trick, the ratios. The values of [`table_leaves`],
/// [`memory_leaves`] and [`bytecode_leaves`]. Fails if a table's pulled fingerprint vanishes (its first such row).
fn leaf_chunks(trace: &Trace, bus: &Bus, kinds: &[Leaves], rows: usize) -> Result<(Vec<Vec<F192>>, Vec<usize>), String> {
    assert!(trace.placed, "the rows at the verifier's positions");
    let heights = block_rows(trace, kinds);
    let mut firsts = vec![0];
    for &r in &heights {
        assert!(rows <= 1 << r);
        firsts.push(firsts[firsts.len() - 1] + (1usize << r) / rows);
    }
    let prints = |list: &[Fingerprint]| -> Vec<Print<usize>> { list.iter().map(|f| Print::new(f, |c| c)).collect() };
    let tables: Vec<(Vec<Print<usize>>, Vec<Print<usize>>)> =
        (0..N_TABLES).map(|t| (prints(&bus.pull[t]), prints(&bus.push[t]))).collect();
    let n_bytecode = 1usize << trace.log_bytecode;
    let chunks: Vec<Result<Vec<F192>, usize>> = parallel::map_collect(firsts[kinds.len()], |task| {
        let k = firsts.partition_point(|&f| f <= task) - 1;
        let lo = (task - firsts[k]) * rows;
        let mut den = vec![F192::ONE; rows];
        let mut num = vec![F192::ONE; rows];
        // Whether row `lo + i` has a leaf of its own (a table's padding rows' leaves are 1).
        let mut active = vec![true; rows];
        match kinds[k] {
            Leaves::Memory => {
                let m = &trace.memory;
                let mut address = g_pow(lo);
                for (i, (d, n)) in den.iter_mut().zip(num.iter_mut()).enumerate() {
                    let limbs = [m[0][lo + i], m[1][lo + i], m[2][lo + i]];
                    *d = bus.memory(address, m[3][lo + i], limbs);
                    *n = bus.memory(address, F64::ONE, limbs);
                    address = mul_by_g(address);
                }
            }
            Leaves::Bytecode => {
                let mut pc = g_pow(lo);
                for (i, (d, n)) in den.iter_mut().zip(num.iter_mut()).enumerate() {
                    let slot = |s: usize, count: F64| match s {
                        0 => F64(SEP_BYTECODE.c0),
                        1 => pc,
                        2 => count,
                        _ => trace.bytecode[s * n_bytecode + lo + i],
                    };
                    *d = bus.bytecode(|s| slot(s, trace.bytecode_final[lo + i]));
                    *n = bus.bytecode(|s| slot(s, F64::ONE));
                    pc = mul_by_g(pc);
                }
            }
            Leaves::Table(t) => {
                let columns = &trace.tables[t];
                let (r, count) = (trace.heights[t], trace.rows[t]);
                active.iter_mut().enumerate().for_each(|(i, a)| *a = is_active((lo + i) as u64, count, r));
                let (pull, push) = &tables[t];
                if rows >= 8 {
                    for (j, ((d, n), a)) in den.chunks_exact_mut(8).zip(num.chunks_exact_mut(8)).zip(active.chunks_exact(8)).enumerate() {
                        if !a.iter().any(|&a| a) {
                            continue;
                        }
                        let at = lo + 8 * j;
                        let col = |c: usize| Kx8::load(&columns[c][at..]);
                        d.copy_from_slice(&product(pull, col).to_array());
                        n.copy_from_slice(&product(push, col).to_array());
                    }
                } else {
                    for i in 0..rows {
                        den[i] = bus.pull[t].iter().fold(F192::ONE, |acc, f| acc * f.at(|c| columns[c][lo + i]));
                        num[i] = bus.push[t].iter().fold(F192::ONE, |acc, f| acc * f.at(|c| columns[c][lo + i]));
                    }
                }
                for ((d, n), &a) in den.iter_mut().zip(num.iter_mut()).zip(&active) {
                    if !a {
                        (*d, *n) = (F192::ONE, F192::ONE);
                    }
                }
                if let Some(i) = den.iter().position(|d| d.is_zero()) {
                    return Err(lo + i);
                }
            }
            Leaves::Unused => unreachable!("an unused block has no leaves"),
        }
        // `num / den`, by one inversion.
        let mut prefix = Vec::with_capacity(rows);
        let mut acc = F192::ONE;
        for &d in &den {
            prefix.push(acc);
            acc *= d;
        }
        let mut inv = acc.inv();
        for i in (0..rows).rev() {
            let d = den[i];
            den[i] = if active[i] { inv * prefix[i] * num[i] } else { F192::ONE };
            inv *= d;
        }
        Ok(den)
    });
    let mut out = Vec::with_capacity(chunks.len());
    for (task, chunk) in chunks.into_iter().enumerate() {
        match chunk {
            Ok(c) => out.push(c),
            Err(row) => {
                let k = firsts.partition_point(|&f| f <= task) - 1;
                let Leaves::Table(t) = kinds[k] else { unreachable!("only a table's leaves fail") };
                return Err(format!("table {t}: a pull fingerprint vanishes at row {row}"));
            }
        }
    }
    Ok((out, firsts))
}

/// The heap ([`heap`]) of the bus's leaves ([`all_leaves`]), the leaves computed in one dispatch and written straight
/// to their blocks' positions: the same heap. Block `b`'s leaves are its positions `layout.blocks[b].position..`.
pub fn heap_of(trace: &Trace, bus: &Bus, layout: &HeapLayout) -> Result<Vec<F192>, String> {
    let blocks: Vec<&crate::heap::Block> = layout.blocks.iter().filter(|b| b.leaves != Leaves::Unused).collect();
    let kinds: Vec<Leaves> = blocks.iter().map(|b| b.leaves).collect();
    let heights = block_rows(trace, &kinds);
    assert!(blocks.iter().zip(&heights).all(|(b, &r)| b.r == r));
    let size = 1usize << layout.h;
    let rows = LEAF_ROWS.min(1 << heights.iter().copied().min().expect("a block")).min(size / 2);
    let (chunks, firsts) = leaf_chunks(trace, bus, &kinds, rows)?;
    // Each `rows`-aligned run of positions: its chunk of leaves, or none (an inner node's, or an unused block's).
    let mut chunk_at: Vec<Option<usize>> = vec![None; size / rows];
    for (k, block) in blocks.iter().enumerate() {
        let at = block.position as usize / rows;
        for (j, slot) in chunk_at[at..at + (firsts[k + 1] - firsts[k])].iter_mut().enumerate() {
            *slot = Some(firsts[k] + j);
        }
    }
    let mut heap: Vec<F192> =
        parallel::map_collect(size, |i| chunk_at[i / rows].map_or(F192::ONE, |c| chunks[c][i % rows]));
    drop(chunks);
    tree_levels(&mut heap);
    Ok(heap)
}

/// A heap's inner nodes from its leaves: every node the product of its children, position 0 zero.
fn tree_levels(heap: &mut [F192]) {
    let mut half = heap.len() / 2;
    while half > 1 {
        let (upper, lower) = heap.split_at_mut(half);
        let parents = &mut upper[half / 2..];
        parallel::chunks_mut(parents, 1 << 12, |j, chunk| {
            let first = j << 12;
            for (k, p) in chunk.iter_mut().enumerate() {
                let child = 2 * (first + k);
                *p = lower[child] * lower[child + 1];
            }
        });
        half /= 2;
    }
    heap[0] = F192::ZERO;
}
