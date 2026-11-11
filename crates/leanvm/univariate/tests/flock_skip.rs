// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The zerocheck with a univariate skip of 3 to 6 (`flock::zerocheck::skip`), without a trace:
//!
//! - at a skip of 6, the skip module's round 1 and whole zerocheck write what leanVM's own do, byte for byte;
//! - at skips of 3, 4 and 5, on honest witnesses, the zerocheck's stream is accepted (its rounds re-checked with the
//!   verifier's sumcheck), and its three claims are the witness's evaluations at the point;
//! - the zerocheck also with π1-rec3's eq point (`EqPoint::Squares`, `FsShape::Rec3`: the sampled coordinates
//!   successive squares of one).
//!
//! Flock end to end on the Keccak-f block: `tests/flock_keccak.rs`.
//!
//! `cargo test --release -p leanvm_univariate --test flock_skip -- --nocapture`

use leanvm_statement::field::E;
use leanvm_statement::transcript::{Checks, FsShape, KeccakChannel, KeccakWriter, keccak_seed, sumcheck};
use leanvm_univariate::prover::flock::Chain;
use flock::zerocheck::skip::{EqPoint, prove_skip, round1};
use flock::zerocheck::univariate_skip_optimized::{
    c_s, medium_challenges, round1_shift_reduce_extract_c_packed_padded, small_challenges,
};
use flock::zerocheck::{PaddingSpec, prove_packed_padded};
use flock::field::F8;
use primitives::field::F192;
use flock::lagrange::lagrange_weights_naive;
use primitives::multilinear::eq_table;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn ext(&mut self) -> F192 {
        F192::new(self.next(), self.next(), self.next())
    }
}

fn to_e(x: F192) -> E {
    E::new(x.c0, x.c1, x.c2)
}

fn from_e(x: E) -> F192 {
    F192::new(x.c0, x.c1, x.c2)
}

/// An honest zerocheck witness: `c = a AND b`, bit `i` at byte `i / 8`, bit `i % 8`; a block's tail zero, as the
/// padding spec says.
fn witness(m: usize, padding: &PaddingSpec, rng: &mut Rng) -> [Vec<u8>; 3] {
    let bytes = (1usize << m) / 8;
    let mut a: Vec<u8> = (0..bytes).map(|_| rng.next() as u8).collect();
    let mut b: Vec<u8> = (0..bytes).map(|_| rng.next() as u8).collect();
    for bit in 0..1usize << m {
        if bit % (1 << padding.k_log) >= padding.useful_bits_per_block {
            a[bit / 8] &= !(1 << (bit % 8));
            b[bit / 8] &= !(1 << (bit % 8));
        }
    }
    let c: Vec<u8> = a.iter().zip(&b).map(|(&x, &y)| x & y).collect();
    [a, b, c]
}

/// `f̂(z, chi)`: the skip's Lagrange weights at `z` on the low `k` bits, eq at `chi` on the rest.
fn quirky(bits: &[u8], k: usize, z: F192, chi: &[F192]) -> F192 {
    let weights = lagrange_weights_naive(k, z);
    let eq = eq_table(chi);
    let mut acc = F192::ZERO;
    for (x, &e) in eq.iter().enumerate() {
        let mut inner = F192::ZERO;
        for (s, &w) in weights.iter().enumerate() {
            let i = (x << k) | s;
            if bits[i / 8] >> (i % 8) & 1 == 1 {
                inner += w;
            }
        }
        acc += e * inner;
    }
    acc
}

/// At a skip of 6, round 1 is leanVM's optimized kernel's message (times its `C_s`).
#[test]
fn round1_at_six_is_leanvms() {
    let mut rng = Rng(0x5eed_0001);
    for m in [14usize, 15, 17] {
        let padding = PaddingSpec {
            k_log: 14,
            useful_bits_per_block: 16_000,
        };
        let [a, b, c] = witness(m, &padding, &mut rng);
        let r_rest: Vec<F192> = small_challenges()
            .into_iter()
            .chain(medium_challenges())
            .chain((0..m - 6 - 7).map(|_| rng.ext()))
            .collect();
        let ntt_s = flock::ntt::AdditiveNttGf8::new(6, F8::ZERO);
        let ntt_l = flock::ntt::AdditiveNttGf8::new(6, F8(64));
        let table = flock::ntt::InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);
        let (ab, cc) = round1_shift_reduce_extract_c_packed_padded(&a, &b, &c, m, 6, &r_rest, &table, &padding);
        let theirs: Vec<F192> = ab.iter().zip(&cc).map(|(&x, &y)| c_s() * (x + y)).collect();
        assert_eq!(round1(&a, &b, &c, m, 6, &r_rest), theirs, "m = {m}");
    }
}

/// `BitFold` at every row width, 1 to 128 bytes (GFNI where the build has it), full and short blocks, against the
/// definition: the sum of the weights of the set bits.
#[test]
fn bit_fold_at_every_row_width() {
    use flock::zerocheck::bit_fold::{BLOCK, BitFold};
    fn check<const CHUNKS: usize>(rng: &mut Rng) {
        let weights: Vec<F192> = (0..8 * CHUNKS).map(|_| rng.ext()).collect();
        let fold = BitFold::new(&weights);
        for len in [BLOCK, 5] {
            let rows: Vec<[u8; CHUNKS]> = (0..len).map(|_| std::array::from_fn(|_| rng.next() as u8)).collect();
            let mut out = [F192::ZERO; BLOCK];
            fold.fold_block(&rows, &mut out);
            for (p, row) in rows.iter().enumerate() {
                let direct = (0..8 * CHUNKS)
                    .filter(|&s| row[s / 8] >> (s % 8) & 1 == 1)
                    .fold(F192::ZERO, |acc, s| acc + weights[s]);
                assert_eq!(out[p], direct, "rows of {CHUNKS} bytes, {len} rows, row {p}");
            }
        }
    }
    let mut rng = Rng(0x5eed_0006);
    check::<1>(&mut rng);
    check::<2>(&mut rng);
    check::<4>(&mut rng);
    check::<8>(&mut rng);
    check::<16>(&mut rng);
    check::<32>(&mut rng);
    check::<64>(&mut rng);
    check::<128>(&mut rng);
}

/// The byte rows' pair pass (products from a table) is the generic pass on one-byte rows, padding included.
#[test]
fn byte_pair_pass_is_the_generic_pass() {
    use flock::zerocheck::bit_fold::BitFold;
    use flock::zerocheck::multilinear::{PackedWitness, bit_round_pair, bit_round_pair_bytes};
    let mut rng = Rng(0x5eed_0007);
    for m in [11usize, 14, 17] {
        let padding = PaddingSpec {
            k_log: 14,
            useful_bits_per_block: 16_000,
        };
        let [a, b, c] = witness(m, &padding, &mut rng);
        // Any C bits (the message is linear in them), zero in the blocks' padding as the spec says.
        let [noise, ..] = witness(m, &padding, &mut rng);
        let c: Vec<u8> = c.iter().zip(&noise).map(|(&x, &y)| x ^ y).collect();
        let weights: [F192; 8] = std::array::from_fn(|_| rng.ext());
        let r_eq: Vec<F192> = (0..m - 4).map(|_| rng.ext()).collect();
        let bits = PackedWitness { a: &a, b: &b, c: &c };
        let generic = bit_round_pair(bits, &BitFold::new(&weights), &r_eq, &padding);
        assert_eq!(bit_round_pair_bytes(bits, &weights, &r_eq, &padding), generic, "m = {m}");
    }
}

/// The byte rows' pass with eq-scaled products' tables (the aarch64 pass) is the byte pass, at every scale, padding
/// included, down to fewer quad coordinates than the scale.
#[test]
fn scaled_byte_pair_pass_is_the_byte_pass() {
    use flock::zerocheck::multilinear::{PackedWitness, bit_round_pair_bytes, bit_round_pair_bytes_scaled};
    let mut rng = Rng(0x5eed_0008);
    let padding = PaddingSpec {
        k_log: 14,
        useful_bits_per_block: 16_000,
    };
    for m in [6usize, 7, 11, 15, 18] {
        let [a, b, c] = witness(m, &padding, &mut rng);
        let [noise, ..] = witness(m, &padding, &mut rng);
        let c: Vec<u8> = c.iter().zip(&noise).map(|(&x, &y)| x ^ y).collect();
        let bits = PackedWitness { a: &a, b: &b, c: &c };
        let w8: [F192; 8] = std::array::from_fn(|_| rng.ext());
        let r_eq: Vec<F192> = (0..m - 4).map(|_| rng.ext()).collect();
        let want = bit_round_pair_bytes(bits, &w8, &r_eq, &padding);
        assert_eq!(bit_round_pair_bytes_scaled::<1>(bits, &w8, &r_eq, &padding), want, "m = {m}");
        assert_eq!(bit_round_pair_bytes_scaled::<2>(bits, &w8, &r_eq, &padding), want, "m = {m}");
        assert_eq!(bit_round_pair_bytes_scaled::<3>(bits, &w8, &r_eq, &padding), want, "m = {m}");
    }
}

/// At a skip of 3, the byte kernel's round 1 (GFNI) is the generic one's.
#[test]
fn round1_bytes_is_the_generic_round1() {
    let mut rng = Rng(0x5eed_0005);
    for m in [11usize, 14, 17] {
        let padding = PaddingSpec {
            k_log: 14,
            useful_bits_per_block: 16_000,
        };
        let [a, b, c] = witness(m, &padding, &mut rng);
        // Not an honest witness's C: the message is linear in it, so any bits test the kernel.
        let c: Vec<u8> = c.iter().map(|&x| x ^ rng.next() as u8).collect();
        let r_rest: Vec<F192> = small_challenges()
            .into_iter()
            .chain(medium_challenges())
            .chain((0..m - 3 - 7).map(|_| rng.ext()))
            .collect();
        assert_eq!(
            flock::zerocheck::skip::round1_bytes(&a, &b, &c, m, &r_rest),
            flock::zerocheck::skip::round1_generic(&a, &b, &c, m, 3, &r_rest),
            "m = {m}"
        );
    }
}

/// At skips of 3 to 6, round 1 with the medium positions folded (GFNI) is the generic one's.
#[test]
fn round1_folded_is_the_generic_round1() {
    let mut rng = Rng(0x5eed_0008);
    for k in 3..=6 {
        for m in [k + 8, 16] {
            let padding = PaddingSpec {
                k_log: 14,
                useful_bits_per_block: 16_000,
            };
            let [a, b, c] = witness(m, &padding, &mut rng);
            let [noise, ..] = witness(m, &padding, &mut rng);
            let c: Vec<u8> = c.iter().zip(&noise).map(|(&x, &y)| x ^ y).collect();
            let r_rest: Vec<F192> = small_challenges()
                .into_iter()
                .chain(medium_challenges())
                .chain((0..m - k - 7).map(|_| rng.ext()))
                .collect();
            let generic = flock::zerocheck::skip::round1_generic(&a, &b, &c, m, k, &r_rest);
            assert_eq!(flock::zerocheck::skip::round1_folded(&a, &b, &c, m, k, &r_rest), generic, "k = {k}, m = {m}");
            if (4..=5).contains(&k) {
                assert_eq!(
                    flock::zerocheck::skip::round1_words(&a, &b, &c, m, k, &r_rest),
                    generic,
                    "words: k = {k}, m = {m}"
                );
            }
        }
    }
}

/// At a skip of 6 the skip module's zerocheck writes leanVM's stream, byte for byte, and leaves its claim.
#[test]
fn zerocheck_at_six_is_leanvms() {
    let mut rng = Rng(0x5eed_0002);
    for m in [14usize, 16, 18] {
        let padding = PaddingSpec {
            k_log: 14,
            useful_bits_per_block: 16_000,
        };
        let [a, b, c] = witness(m, &padding, &mut rng);
        let seed = keccak_seed(b"flock skip test!", &[m as u8; 32], &[6; 32]);
        let (mut w1, mut w2) = (KeccakWriter::new(seed), KeccakWriter::new(seed));
        let theirs = {
            let mut chain = Chain {
                writer: &mut w1,
                samples: Vec::new(),
                drawn: None,
            };
            prove_packed_padded(&a, &b, &c, m, &padding, &mut chain)
        };
        let mine = {
            let mut chain = Chain {
                writer: &mut w2,
                samples: Vec::new(),
                drawn: None,
            };
            prove_skip(&a, &b, &c, m, 6, EqPoint::Sampled, &padding, &mut chain)
        };
        assert_eq!(w1.stream, w2.stream, "m = {m}: the streams");
        assert_eq!(theirs, mine, "m = {m}: the claims");
        println!("m = {m}: skip 6, {} stream bytes, identical to leanVM's", w1.stream.len());
    }
}

/// At skips of 3 to 6, on honest witnesses, with leanVM's eq point and π1-rec's (its sampled coordinates squares of
/// one): the verifier's checks of the zerocheck hold, and the claims are the witness's evaluations at the point.
#[test]
fn zerocheck_skips_verify_and_are_faithful() {
    let mut rng = Rng(0x5eed_0003);
    let shapes = [(EqPoint::Sampled, FsShape::Main), (EqPoint::Squares, FsShape::Rec3)];
    for (k, (eq, fs)) in (3..=6).flat_map(|k| shapes.map(|shape| (k, shape))) {
        for m in [k + 8, 14, 17] {
            let padding = PaddingSpec {
                k_log: 14,
                useful_bits_per_block: 16_000,
            };
            let [a, b, c] = witness(m, &padding, &mut rng);
            let seed = keccak_seed(b"flock skip test!", &[m as u8; 32], &[k as u8; 32]);
            let mut writer = KeccakWriter::new(seed);
            let claim = {
                let mut chain = Chain {
                    writer: &mut writer,
                    samples: Vec::new(),
                    drawn: None,
                };
                prove_skip(&a, &b, &c, m, k, eq, &padding, &mut chain)
            };
            // The verifier's side (flock_min's zerocheck): the fixed coordinates, the samples, the coset's values,
            // `z`, the rounds with their eq coordinates, `v_a`, `v_b`.
            let mut channel = KeccakChannel::new(seed, &writer.stream, Checks::Enforce);
            use leanvm_statement::transcript::Channel;
            let mut r: Vec<Option<E>> = small_challenges()
                .into_iter()
                .chain(medium_challenges())
                .map(|x| Some(to_e(x)))
                .collect();
            r.extend(fs.draw(&mut channel, m - k - 7).into_iter().map(Some));
            let coset = channel.next_scalars(1 << k).unwrap();
            let z = channel.sample();
            let values: Vec<E> = [vec![E::default(); 1 << k], coset].concat();
            let start = leanvm_statement::flock::lagrange_weights(2 << k, z)
                .iter()
                .zip(&values)
                .fold(E::default(), |acc, (&w, &v)| acc + w * v);
            let (chi, running) = sumcheck(&mut channel, start, 3, &r).expect("the rounds");
            let (v_a, v_b) = (channel.next_scalar().unwrap(), channel.next_scalar().unwrap());
            channel.finish().expect("the whole stream");
            assert_eq!(from_e(z), claim.z);
            let chi: Vec<F192> = chi.into_iter().map(from_e).collect();
            assert_eq!(chi, claim.mlv_challenges);
            assert_eq!((from_e(v_a), from_e(v_b)), (claim.a_eval, claim.b_eval));
            let v_c = running + v_a * v_b;
            assert_eq!(from_e(v_c), claim.c_eval);
            assert_eq!(claim.a_eval, quirky(&a, k, claim.z, &chi), "k = {k}, m = {m}: â");
            assert_eq!(claim.b_eval, quirky(&b, k, claim.z, &chi), "k = {k}, m = {m}: b̂");
            assert_eq!(claim.c_eval, quirky(&c, k, claim.z, &chi), "k = {k}, m = {m}: ĉ");
            println!("k = {k}, m = {m}, {eq:?}: {} stream bytes, accepted, claims true", writer.stream.len());
        }
    }
}
