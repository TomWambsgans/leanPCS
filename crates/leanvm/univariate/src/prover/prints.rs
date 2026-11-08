// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! Bus fingerprints on eight points at once (`quotient::ntt`'s lanes): a [`Fingerprint`]'s coefficients in every
//! lane, its columns read by key, the terms' products unreduced and one reduction a fingerprint.

use primitives::field::{F64, F192, F192Unreduced};
use quotient::ntt::{ESplat, Ex8, Kx8, MixedSum};

use super::fingerprint::Fingerprint;

/// `constant + Σ c x_i + Σ c x_i x_j` on eight points, column `i` read by key `C`.
pub struct Print<C> {
    constant: Ex8,
    linear: Vec<(C, ESplat)>,
    quadratic: Vec<(C, C, ESplat)>,
}

impl<C: Copy> Print<C> {
    /// `f`, its column `c` read by `key(c)`.
    pub fn new(f: &Fingerprint, key: impl Fn(usize) -> C) -> Self {
        Self {
            constant: Ex8::splat(f.constant),
            linear: f.linear.iter().map(|&(c, k)| (key(c), ESplat::new(k))).collect(),
            quadratic: f
                .quadratic
                .iter()
                .map(|&(c, d, k)| (key(c), key(d), ESplat::new(k)))
                .collect(),
        }
    }

    /// The linear form `constant + Σ c x`.
    pub fn linear(constant: F192, terms: impl IntoIterator<Item = (C, F192)>) -> Self {
        Self {
            constant: Ex8::splat(constant),
            linear: terms.into_iter().map(|(s, c)| (s, ESplat::new(c))).collect(),
            quadratic: Vec::new(),
        }
    }

    /// Its values, the columns' read by `col`.
    #[inline(always)]
    pub fn at(&self, col: impl Fn(C) -> Kx8) -> Ex8 {
        self.terms(MixedSum::default(), col).reduce() + self.constant
    }

    /// `sum` plus its terms, the constant apart, unreduced.
    #[inline(always)]
    fn terms(&self, mut sum: MixedSum, col: impl Fn(C) -> Kx8) -> MixedSum {
        for &(s, ref c) in &self.linear {
            sum.add(c, col(s));
        }
        for &(s, t, ref c) in &self.quadratic {
            sum.add(c, col(s) * col(t));
        }
        sum
    }
}

/// A push fingerprint on eight points: its pull's (same index) terms plus `delta`'s, when that is fewer terms; else
/// alone.
enum Push8<C> {
    Delta { constant: Ex8, delta: Print<C> },
    Alone(Print<C>),
}

/// [`PullPush`] on eight points at once (`Ex8` lanes): each push fingerprint that differs from its pull in a
/// few terms (a memory flush's push is its pull with the count times `g`) from the pull's unreduced sum.
pub struct PullPush8<C> {
    pull: Vec<Print<C>>,
    push: Vec<Push8<C>>,
}

impl<C: Copy> PullPush8<C> {
    /// `pull` and `push`, their column `c` read by `key(c)`.
    pub fn new(pull: &[Fingerprint], push: &[Fingerprint], key: impl Fn(usize) -> C + Copy) -> Self {
        let push = push
            .iter()
            .enumerate()
            .map(|(i, f)| match pull.get(i).map(|p| difference(p, f)) {
                Some(d) if d.linear.len() + d.quadratic.len() < f.linear.len() + f.quadratic.len() => Push8::Delta {
                    constant: Ex8::splat(f.constant),
                    delta: Print::new(&d, key),
                },
                _ => Push8::Alone(Print::new(f, key)),
            })
            .collect();
        Self {
            pull: pull.iter().map(|f| Print::new(f, key)).collect(),
            push,
        }
    }

    /// `(Π pull, Π push)` on eight points, the columns' read by `col`.
    #[inline(always)]
    pub fn at(&self, col: impl Fn(C) -> Kx8 + Copy) -> (Ex8, Ex8) {
        let one = Ex8::splat(F192::ONE);
        let (mut p, mut q) = (one, one);
        for i in 0..self.pull.len().max(self.push.len()) {
            let mut pulled = MixedSum::default();
            if let Some(f) = self.pull.get(i) {
                pulled = f.terms(MixedSum::default(), col);
                let x = pulled.reduce() + f.constant;
                p = if i == 0 { x } else { p * x };
            }
            let y = match self.push.get(i) {
                Some(Push8::Delta { constant, delta }) => delta.terms(pulled, col).reduce() + *constant,
                Some(Push8::Alone(f)) => f.at(col),
                None => continue,
            };
            q = if i == 0 { y } else { q * y };
        }
        (p, q)
    }
}

/// The product of `prints`, the columns' read by `col`.
#[inline(always)]
pub fn product<C: Copy>(prints: &[Print<C>], col: impl Fn(C) -> Kx8 + Copy) -> Ex8 {
    match prints.split_first() {
        Some((first, rest)) => rest.iter().fold(first.at(col), |acc, f| acc * f.at(col)),
        None => Ex8::splat(F192::ONE),
    }
}

/// `Σ c x_i + Σ c x_i x_j` at one point, the constant apart, unreduced: column `i` read by key `C`.
struct Terms<C> {
    linear: Vec<(C, F192)>,
    quadratic: Vec<(C, C, F192)>,
}

impl<C: Copy> Terms<C> {
    #[inline(always)]
    fn at(&self, col: &impl Fn(C) -> F64) -> F192Unreduced {
        let mut acc = F192Unreduced::ZERO;
        for &(s, c) in &self.linear {
            acc ^= c.mul_base_unreduced(col(s));
        }
        for &(s, t, c) in &self.quadratic {
            acc ^= c.mul_base_unreduced(col(s) * col(t));
        }
        acc
    }
}

/// A push fingerprint: its pull's (same index) terms plus `delta`, when that is fewer terms; else alone.
enum Push<C> {
    Delta { constant: F192, delta: Terms<C> },
    Alone { constant: F192, terms: Terms<C> },
}

/// A table's pull and push products at one point, one point at a time in `E` (where the unreduced sums of mixed
/// products are cheaper than [`product`]'s lanes, aarch64): each push fingerprint that differs from its pull in a
/// few terms (a memory flush's push is its pull with the count times `g`) from the pull's unreduced sum.
pub struct PullPush<C> {
    pull: Vec<(F192, Terms<C>)>,
    push: Vec<Push<C>>,
}

impl<C: Copy> PullPush<C> {
    /// `pull` and `push`, their column `c` read by `key(c)`.
    pub fn new(pull: &[Fingerprint], push: &[Fingerprint], key: impl Fn(usize) -> C) -> Self {
        let terms = |f: &Fingerprint| Terms {
            linear: f.linear.iter().map(|&(c, k)| (key(c), k)).collect(),
            quadratic: f.quadratic.iter().map(|&(c, d, k)| (key(c), key(d), k)).collect(),
        };
        let push = push
            .iter()
            .enumerate()
            .map(|(i, f)| match pull.get(i).map(|p| difference(p, f)) {
                Some(d) if d.linear.len() + d.quadratic.len() < f.linear.len() + f.quadratic.len() => Push::Delta {
                    constant: d.constant,
                    delta: terms(&d),
                },
                _ => Push::Alone {
                    constant: f.constant,
                    terms: terms(f),
                },
            })
            .collect();
        Self {
            pull: pull.iter().map(|f| (f.constant, terms(f))).collect(),
            push,
        }
    }

    /// `(Π pull, Π push)` at one point, the columns' values read by `col`. Each product in four interleaved chains,
    /// so that the products' latencies overlap.
    #[inline(always)]
    pub fn at(&self, col: impl Fn(C) -> F64) -> (F192, F192) {
        let (mut p, mut q) = ([F192::ONE; 4], [F192::ONE; 4]);
        let times = |acc: &mut [F192; 4], i: usize, f: F192| {
            if i < 4 {
                acc[i] = f;
            } else {
                acc[i & 3] = acc[i & 3] * f;
            }
        };
        for i in 0..self.pull.len().max(self.push.len()) {
            let mut pulled = F192Unreduced::ZERO;
            if let Some((constant, terms)) = self.pull.get(i) {
                pulled = terms.at(&col);
                times(&mut p, i, pulled.reduce() + *constant);
            }
            match self.push.get(i) {
                Some(Push::Delta { constant, delta }) => {
                    times(&mut q, i, (pulled ^ delta.at(&col)).reduce() + self.pull[i].0 + *constant);
                }
                Some(Push::Alone { constant, terms }) => times(&mut q, i, terms.at(&col).reduce() + *constant),
                None => {}
            }
        }
        let all = |a: [F192; 4]| (a[0] * a[1]) * (a[2] * a[3]);
        (all(p), all(q))
    }
}

/// `push - pull`, term by term.
fn difference(pull: &Fingerprint, push: &Fingerprint) -> Fingerprint {
    let mut out = Fingerprint {
        constant: push.constant + pull.constant,
        linear: Vec::new(),
        quadratic: Vec::new(),
    };
    let mut linear: Vec<(usize, F192)> = push.linear.clone();
    for &(c, k) in &pull.linear {
        match linear.iter_mut().find(|(d, _)| *d == c) {
            Some((_, e)) => *e += k,
            None => linear.push((c, k)),
        }
    }
    let mut quadratic: Vec<(usize, usize, F192)> = push.quadratic.clone();
    for &(c, d, k) in &pull.quadratic {
        match quadratic.iter_mut().find(|(a, b, _)| (*a, *b) == (c, d)) {
            Some((_, _, e)) => *e += k,
            None => quadratic.push((c, d, k)),
        }
    }
    out.linear = linear.into_iter().filter(|(_, k)| !k.is_zero()).collect();
    out.quadratic = quadratic.into_iter().filter(|(_, _, k)| !k.is_zero()).collect();
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// [`PullPush`] is [`product`] of the pulls and of the pushes, pushes alike and unlike their pulls.
    #[test]
    fn pull_push_is_the_products() {
        let mut x = 0x2545_f491_4f6c_dd1du64;
        let mut next = move || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        let mut e = || F192::new(next(), next(), next());
        let pull: Vec<Fingerprint> = (0..6)
            .map(|i| Fingerprint {
                constant: e(),
                linear: vec![(i, e()), (6 + i, e()), (12, e())],
                quadratic: vec![(1, 2 + i % 3, e())],
            })
            .collect();
        let mut push = pull.clone();
        push[0].linear[1].1 = e();
        push[1].constant = e();
        push[2].linear.push((13, e()));
        push[3] = Fingerprint {
            constant: e(),
            linear: vec![(3, e())],
            quadratic: Vec::new(),
        };
        push.push(pull[5].clone());
        let both = PullPush::new(&pull, &push, |c| c);
        let lanes = |list: &[Fingerprint]| -> Vec<Print<usize>> { list.iter().map(|f| Print::new(f, |c| c)).collect() };
        let columns: Vec<[F64; 8]> = (0..14).map(|_| std::array::from_fn(|_| F64(next()))).collect();
        let col = |c: usize| Kx8::new(columns[c]);
        let (p, q) = (product(&lanes(&pull), col).to_array(), product(&lanes(&push), col).to_array());
        for k in 0..8 {
            assert_eq!(both.at(|c| columns[c][k]), (p[k], q[k]));
        }
        let (p8, q8) = PullPush8::new(&pull, &push, |c| c).at(col);
        assert_eq!((p8.to_array(), q8.to_array()), (p, q));
    }
}
