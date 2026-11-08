// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The first commitment's polynomials and the setup's (SPEC.md §3), from a trace: every column's novel
//! coefficients (for the quotients' cosets) and its `B` coefficients (what the stack holds).

use leanvm_statement::N_TABLES;
use leanvm_statement::layout::SEP_BYTECODE;
use primitives::field::{F64, g_powers};
use quotient::ntt::{coefficients_from, coefficients_from_cols, subset_sums_from, subset_sums_many};

use super::trace::Trace;

/// A K-column of `2^r` rows as a polynomial of degree `< 2^r`: its novel and its `B` coefficients (`C1`'s columns
/// keep their `B` coefficients in the stack only, [`Column::novel_only`]).
#[derive(Clone)]
pub struct Column {
    pub novel: Vec<F64>,
    pub b: Vec<F64>,
}

impl Column {
    pub fn from_values(values: &[F64]) -> Self {
        let mut novel = vec![F64::ZERO; values.len()];
        coefficients_from(values, &mut novel, F64::ZERO);
        let mut b = vec![F64::ZERO; values.len()];
        subset_sums_from(&novel, &mut b);
        Self { novel, b }
    }

    /// Its novel coefficients alone, `b` empty: the stack takes the `B` ones from them (`Stack::put_b`).
    pub fn novel_only(values: &[F64]) -> Self {
        let mut novel = vec![F64::ZERO; values.len()];
        coefficients_from(values, &mut novel, F64::ZERO);
        Self { novel, b: Vec::new() }
    }

    pub fn vars(&self) -> usize {
        self.novel.len().trailing_zeros() as usize
    }

    /// [`Column::novel_only`] of several columns of one length, their transforms in the same dispatches.
    pub fn novel_only_many(values: &[&[F64]]) -> Vec<Self> {
        let len = values.first().map_or(0, |v| v.len());
        let mut novel: Vec<Vec<F64>> = values.iter().map(|_| vec![F64::ZERO; len]).collect();
        coefficients_from_cols(values, &mut novel.iter_mut().map(|n| &mut n[..]).collect::<Vec<_>>(), F64::ZERO);
        novel.into_iter().map(|novel| Self { novel, b: Vec::new() }).collect()
    }

    /// [`Column::from_values`] of several columns of one length, in the same dispatches.
    pub fn from_values_many(values: &[&[F64]]) -> Vec<Self> {
        let mut columns = Self::novel_only_many(values);
        let mut b: Vec<Vec<F64>> = columns.iter().map(|c| vec![F64::ZERO; c.novel.len()]).collect();
        let mut jobs: Vec<(&[F64], &mut [F64])> = columns.iter().map(|c| &c.novel[..]).zip(b.iter_mut().map(|b| &mut b[..])).collect();
        subset_sums_many(&mut jobs);
        for (c, b) in columns.iter_mut().zip(b) {
            c.b = b;
        }
        columns
    }
}

/// `C1`'s polynomials (novel coefficients only: their `B` ones are the stack's): the tables' columns (`SHA3`'s lanes being the copies), the counter inverses, the memory's
/// four columns and the bytecode's final counts. `q_flock` is the trace's, as values.
pub struct C1Polys {
    pub tables: Vec<Vec<Column>>,
    pub inverses: Vec<Column>,
    /// The inverse columns' values, `1 / Π_j c_j` on every row.
    pub inverse_values: Vec<Vec<F64>>,
    pub memory: [Column; 4],
    pub bytecode_final: Column,
}

/// The setup's polynomials: the bytecode's 16 tuple slots (slot 0 `SEP_BYTECODE`, 1 the pc `g^i`, 2 zero, then
/// leanVM's stacked bytecode's slots 3..16) and the memory's addresses `g^i`.
pub struct SetupPolys {
    pub slots: Vec<Column>,
    pub address: Column,
}

pub fn c1_polys(trace: &Trace) -> C1Polys {
    let layout = leanvm_statement::layout::tables();
    let mut tables_out = Vec::with_capacity(N_TABLES);
    let mut inverses = Vec::with_capacity(N_TABLES);
    let mut inverse_values = Vec::with_capacity(N_TABLES);
    for (t, table) in layout.iter().enumerate() {
        let columns = &trace.tables[t];
        tables_out.push(Column::novel_only_many(&columns.iter().map(|c| &c[..]).collect::<Vec<_>>()));
        let n = 1usize << trace.heights[t];
        let counters: Vec<usize> = table.count_columns().collect();
        // Every row's counters are nonzero (the placed trace's padding rows hold 1: SPEC.md §13, F1).
        let mut z: Vec<F64> = parallel::map_collect(n, |i| counters.iter().fold(F64::ONE, |acc, &c| acc * columns[c][i]));
        // One inversion a chunk.
        parallel::chunks_mut(&mut z, 1 << 12, |_, chunk| {
            let mut prefix = Vec::with_capacity(chunk.len());
            let mut acc = F64::ONE;
            for &x in chunk.iter() {
                prefix.push(acc);
                if !x.is_zero() {
                    acc *= x;
                }
            }
            let mut inv = acc.inv();
            for i in (0..chunk.len()).rev() {
                let x = chunk[i];
                if x.is_zero() {
                    continue;
                }
                chunk[i] = inv * prefix[i];
                inv *= x;
            }
        });
        inverses.push(Column::novel_only(&z));
        inverse_values.push(z);
    }
    C1Polys {
        tables: tables_out,
        inverses,
        inverse_values,
        memory: Column::novel_only_many(&trace.memory.iter().map(|m| &m[..]).collect::<Vec<_>>())
            .try_into()
            .unwrap_or_else(|_| unreachable!("four columns")),
        bytecode_final: Column::novel_only(&trace.bytecode_final),
    }
}

pub fn setup_polys(trace: &Trace) -> SetupPolys {
    let n = 1usize << trace.log_bytecode;
    let (sep, pc, zero) = (vec![F64(SEP_BYTECODE.c0); n], g_powers(n), vec![F64::ZERO; n]);
    let values: Vec<&[F64]> = (0..16)
        .map(|s| match s {
            0 => &sep[..],
            1 => &pc[..],
            2 => &zero[..],
            _ => &trace.bytecode[s * n..(s + 1) * n],
        })
        .collect();
    let slots = Column::from_values_many(&values);
    SetupPolys {
        slots,
        address: Column::from_values(&g_powers(1 << trace.log_memory)),
    }
}
