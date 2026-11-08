// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The vectors of `formal/RecCircuit/RecCircuitTest/PadCounts.lean`: `layout::pad_counts` on pseudo-random region
//! counts (each region: its row count, its expression roles, its forward roles, whether it has a port), and on the
//! carry case of the look-ahead (724,992 rows pad to 786,432 at both 2 and 3 digits). One line per case:
//! `case <n> | <count> <exprs> <forwards> <port> ... | <padded> ...`.
//!
//! `cargo test --release -p leanvm_rec --test lean_pad_counts -- --nocapture`

use leanvm_rec::circuit::layout::pad_counts;
use leanvm_rec::circuit::spec::{Formula, Poly, Region};

fn region(exprs: usize, forwards: usize, port: bool) -> Region {
    let mut roles = vec![Formula::Expr(Poly::default()); exprs];
    roles.extend(std::iter::repeat_n(Formula::Forward, forwards));
    if port {
        roles.push(Formula::Port(vec![0]));
    }
    Region {
        name: String::new(),
        roles,
    }
}

/// xorshift64*, a fixed stream.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn line(case: usize, spec: &[(usize, usize, usize, bool)]) -> String {
    let count: Vec<usize> = spec.iter().map(|s| s.0).collect();
    let regions: Vec<Region> = spec.iter().map(|&(_, e, f, p)| region(e, f, p)).collect();
    let padded = pad_counts(&count, &regions, 0);
    let ins: Vec<String> = spec
        .iter()
        .map(|&(c, e, f, p)| format!("{c} {e} {f} {}", p as u8))
        .collect();
    let outs: Vec<String> = padded.iter().map(|p| p.to_string()).collect();
    format!("case {case} | {} | {}", ins.join(" "), outs.join(" "))
}

#[test]
fn vectors() {
    let mut lines = Vec::new();
    // The carry: one region of 724,992 rows beside a small one, which the one-digit greedy padded a digit at a time.
    lines.push(line(0, &[(724_992, 10, 2, false), (300_001, 3, 0, false)]));
    lines.push(line(1, &[(724_992, 1, 0, false), (1, 1, 0, true)]));
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    for case in 2..202 {
        let regions = 1 + rng.below(8) as usize;
        let spec: Vec<(usize, usize, usize, bool)> = (0..regions)
            .map(|_| {
                let bits = 1 + rng.below(22);
                let c = (rng.next() >> (64 - bits)) as usize;
                let exprs = rng.below(40) as usize;
                let forwards = rng.below(4) as usize;
                let port = rng.below(5) == 0;
                (c, exprs, forwards, port)
            })
            .collect();
        lines.push(line(case, &spec));
    }
    for l in &lines {
        println!("{l}");
    }
}
