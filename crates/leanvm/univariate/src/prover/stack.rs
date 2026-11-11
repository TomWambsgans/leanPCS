// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The three stacks, filled: every column's words at the block `crate::stacks::StackLayout` gives it (the
//! verifier's `layouts`, from its column lists), the rest zero. Nothing the verifier checks
//! depends on the words outside the blocks: every weight is zero there, and every claim is on the whole stack's
//! multilinear, whatever the stack holds there.

use primitives::field::F64;
use quotient::ntt::Fill;

use crate::claims::Column;
use crate::stacks::StackLayout;

/// What a stack commits: whole lanes of `2^(vars - 6)` words, the stack's words past them zero.
pub struct Stack {
    pub layout: StackLayout,
    pub words: Vec<F64>,
}

impl Stack {
    /// A zero stack of `layout`, as many whole lanes as its blocks need.
    pub fn new(layout: StackLayout) -> Self {
        let len = Self::len(&layout);
        // Zeroed by the workers: one thread's `vec![F64::ZERO; len]` (a memset of C1's 620 MB at the reference
        // shape, C2's 340 MB) took 12 and 6 ms.
        Self {
            layout,
            words: quotient::ntt::zeros(len),
        }
    }

    /// The stack of `layout` with each `(column, limb, fill)`'s block filled (a column's `B` coefficients from its
    /// novel ones, or its words), the rest zero: as [`Stack::new`] then the puts, but each word written once
    /// (`quotient::ntt::filled_column`), not zeroed first (C1's and C2's zeroing took the workers 2.9 and 1.4 ms).
    pub fn filled(layout: StackLayout, fills: &[(Column, usize, Fill<'_>)]) -> Self {
        let jobs: Vec<(usize, usize, Fill)> = fills
            .iter()
            .map(|&(column, limb, fill)| {
                let (_, vars, offset) = layout.limbs(column)[limb];
                (offset as usize, 1usize << vars, fill)
            })
            .collect();
        let words = quotient::ntt::filled_column(Self::len(&layout), &jobs);
        Self { layout, words }
    }

    /// Words of a stack of `layout`: as many whole lanes of `2^(vars - 6)` as its blocks need.
    fn len(layout: &StackLayout) -> usize {
        let lane = 1usize << (layout.vars - super::opening::LANE_FOLD);
        (layout.words() as usize).div_ceil(lane).max(1) * lane
    }

    /// Words placed (the blocks), as WHIR's verifier is told.
    pub fn placed(&self) -> u64 {
        self.layout.words()
    }

    /// Fill the words past every block (inside the committed lanes) with pseudo-random words: nothing the verifier
    /// checks may depend on them (`PROVER.md`, "the stacks' unused words").
    pub fn fill_unused(&mut self, seed: u64) {
        let placed = self.placed() as usize;
        let mut state = seed | 1;
        for word in &mut self.words[placed..] {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            *word = F64(state);
        }
    }

    /// A K-column's words as placed: its `B` coefficients.
    pub fn k(&self, column: Column) -> &[F64] {
        let limbs = self.layout.limbs(column);
        assert_eq!(limbs.len(), 1, "{column:?} is a K-column");
        let (_, vars, offset) = limbs[0];
        &self.words[offset as usize..offset as usize + (1 << vars)]
    }

    /// An E-column's three limbs as placed.
    pub fn limbs(&self, column: Column) -> [&[F64]; 3] {
        let limbs = self.layout.limbs(column);
        assert_eq!(limbs.len(), 3, "{column:?} is an E-column");
        let mut out: [&[F64]; 3] = [&[]; 3];
        for (limb, vars, offset) in limbs {
            out[limb] = &self.words[offset as usize..offset as usize + (1 << vars)];
        }
        out
    }
}
