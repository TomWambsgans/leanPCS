// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The vectors of `formal/KeccakFlock/KeccakFlockTest/Rows.lean`: the Keccak-f block's rows (`keccak_flock::row_values`,
//! the verifier's walk of `crates/vendor/leanvm-42422001/flock/src/keccak.rs`'s block) on column weights `w[p] = (r_p, 0, 0)`, `r_p` the
//! `p`-th output of a xorshift64 generator. The walk only adds, so limb 0 of every row value is the XOR of the `r_p`
//! over the row's positions: 64 independent GF(2) column vectors at once. Printed per seed: an FNV-style digest
//! (`h ← h · 0x100000001b3 ⊕ v`, from `0xcbf29ce484222325`) of limb 0 of `A w` and of `B w` over the `2^17` rows, and
//! limb 0 of both at sample rows (one of each kind). The Lean test recomputes them from `KeccakFlock.r1cs.rows`.
//!
//! The vectors of `formal/KeccakFlock/KeccakFlockTest/Terminal.lean`: the structured terminal (`structured_terminal`)
//! and the walked one (`walked_terminal_with::<_, KeccakWalked>`) at skips `0..=6`, their inputs drawn from xorshift64
//! from `0x5eed ⊕ k` in `keccak_terminal.rs`'s order (`z_skip` when `k > 0`, `row_low` of `6 − k`, `chi_in` and
//! `chi_in'` of 11, `s` of 64, `α`), each element of `E` three successive draws `c0, c1, c2`. Printed: `k`, then both
//! terminals' limbs.
//!
//! `cargo test --release -p leanvm_statement --test lean_keccak_block -- --nocapture`

use leanvm_statement::field::E;
use leanvm_statement::flock_min::walked_terminal_with;
use leanvm_statement::keccak_flock::{KeccakWalked, LOG_SIZE, row_values, structured_terminal};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn e(&mut self) -> E {
        let c0 = self.next();
        let c1 = self.next();
        let c2 = self.next();
        E::new(c0, c1, c2)
    }
    fn es(&mut self, n: usize) -> Vec<E> {
        (0..n).map(|_| self.e()).collect()
    }
}

fn digest(v: &[E]) -> u64 {
    v.iter().fold(0xcbf2_9ce4_8422_2325u64, |h, e| {
        assert!(e.c1 == 0 && e.c2 == 0, "the walk only adds");
        h.wrapping_mul(0x0000_0100_0000_01b3) ^ e.c0
    })
}

/// Sample rows: the constant wire, an empty Y bit, an output X bit (round 23's lin-id), a free input, a copy, the x
/// quad's constant bit, an empty port word, a `t_0` bit, an `A_0` bit (lane 0, ι), a `t_23` bit, an empty run lane,
/// the suffix.
const SAMPLES: [usize; 12] = [
    64,
    64 + 5,
    64 * 4 * 7 + 13,
    64 * (4 * 3 + 2) + 40,
    64 * (4 * 24 + 3) + 63,
    64 * (4 * 25) + 1,
    64 * (4 * 30 + 2) + 9,
    64 * 128 + 17,
    64 * (128 + 32) + 3,
    64 * (64 * 25 + 24) + 50,
    64 * (64 * 7 + 28) + 2,
    100_000,
];

#[test]
fn vectors() {
    for seed in [1u64, 2, 3] {
        let mut rng = Rng(0x9e37_79b9_7f4a_7c15 ^ seed);
        let w: Vec<E> = (0..1usize << LOG_SIZE).map(|_| E::new(rng.next(), 0, 0)).collect();
        let (left, right) = row_values(&w);
        println!("seed {seed} {:016x} {:016x}", digest(&left), digest(&right));
        for k in SAMPLES {
            println!("row {seed} {k} {:016x} {:016x}", left[k].c0, right[k].c0);
        }
    }
}

#[test]
fn terminal_vectors() {
    for k in 0..=6usize {
        let mut rng = Rng(0x5eed ^ k as u64);
        let z_skip = (k > 0).then(|| rng.e());
        let row_low = rng.es(6 - k);
        let chi_in = rng.es(LOG_SIZE - 6);
        let chi_in_prime = rng.es(LOG_SIZE - 6);
        let s = rng.es(64);
        let alpha = rng.e();
        let st = structured_terminal(z_skip, &row_low, &chi_in, &chi_in_prime, &s, alpha);
        let wt = walked_terminal_with::<E, KeccakWalked>(z_skip, &row_low, &chi_in, &chi_in_prime, &s, alpha);
        assert_eq!(st, wt);
        println!(
            "terminal {k} {:016x} {:016x} {:016x} {:016x} {:016x} {:016x}",
            st.c0, st.c1, st.c2, wt.c0, wt.c1, wt.c2
        );
    }
}
