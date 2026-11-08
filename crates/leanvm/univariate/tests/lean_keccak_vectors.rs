// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Test vectors for the Lean transcription of the Keccak VM's verifier (`formal/UniKeccak`): `reduce` with
//! `Blake2s::Keccak` (`KECCAK.md`) on random, accepting and mutated streams and on the real Keccak proofs of
//! `tests/vectors/keccak*.txt`, each with the Rust verifier's verdict and its intermediate values (every challenge,
//! every value it requires to be zero, the claims it hands `PCS_OPEN`); and the Keccak-f block's structured lincheck
//! terminal (`keccak_flock::structured_terminal`) on random inputs at every skip, with the walked terminal's value.
//!
//! `KECCAK_VECTORS_OUT=$PWD/keccak_vectors.txt cargo test --release -p leanvm_univariate --test lean_keccak_vectors -- --ignored --nocapture`
//!
//! The format is `tests/lean_vectors.rs`'s (`formal/UniStatement/UniStatementTest/Runner.lean` reads it), with the
//! Keccak contract's setup: `SETUPROOTS <f> <a0> <b0>` the roots it binds (`SetupRoots::REFERENCE`, or for a real proof
//! its own `F`, as `tests/evm_vectors.rs` builds its contract), `CONTRACTIV` `contract::contract_iv_for(shape,
//! Blake2s::Keccak(..), program_iv, roots)`, `LAYOUTWORDS` `contract::layout_words_for(shape, Blake2s::Keccak(..))`. The configuration
//! (`<flock>` in the `VECTOR` line) is `keccak` (`KECCAK_MAIN`) or `keccak_rec3` (`KECCAK_REC3`). A real proof's
//! vector carries the contract's `PCS_OPEN` inputs (`PCSOPEN <hex>`, the vector file's `pcs_open` lines). Terminal
//! vectors are one line each:
//!
//! ```text
//! TERMINAL <k> <z_skip | -> <row_low> <chi_in> <chi_in'> <s> <alpha> <structured> <walked>
//! ```
//!
//! (each list a count then its elements; an element `c0:c1:c2`, lowercase hex limbs.) This file holds its own copy of
//! `tests/lean_format`'s logging channel and accepting streams (that module's IV is the BLAKE2s contract's), with
//! `sample_narrow` logged (π1-rec3's batch).

use std::fmt::Write as _;

use leanvm_statement::VerifierError;
use leanvm_statement::field::{E, ONE, ZERO};
use leanvm_statement::flock_min::walked_terminal_with;
use leanvm_statement::keccak_flock::{KeccakWalked, structured_terminal};
use leanvm_statement::shapes::PROGRAM_IV;
use leanvm_statement::transcript::{Channel, Checks, KeccakChannel, keccak_seed, narrow, scalar_bytes};
use leanvm_univariate::claims::Combined;
use leanvm_univariate::contract::{
    NAME, SetupRoots, contract_iv_for, layout_words_for, record_verifier, sample_stream,
};
use leanvm_univariate::{Blake2s, Claims, KECCAK_MAIN, KECCAK_REC3, Opening, Reduced, Shape, reduce};

/// Run `f` on a thread with a deep stack, as `tests/gas.rs` does.
fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

/// The contract's chain, logging what the verifier draws and checks (narrow challenges as drawn).
struct Logging<'a> {
    inner: KeccakChannel<'a>,
    cursor: usize,
    challenges: Vec<E>,
    zeros: Vec<E>,
    nonzeros: Vec<E>,
    scalar_at: Vec<usize>,
    zero_after: Vec<usize>,
}

impl Channel<E> for Logging<'_> {
    fn next_scalar(&mut self) -> Result<E, VerifierError> {
        let value = self.inner.next_scalar()?;
        self.scalar_at.push(self.cursor);
        self.cursor += 24;
        Ok(value)
    }

    fn next_root(&mut self) -> Result<[E; 2], VerifierError> {
        let halves = self.inner.next_root()?;
        self.cursor += 32;
        Ok(halves)
    }

    fn sample(&mut self) -> E {
        let challenge = self.inner.sample();
        self.challenges.push(challenge);
        challenge
    }

    fn sample_narrow(&mut self) -> E {
        let challenge = narrow(self.inner.sample());
        self.challenges.push(challenge);
        challenge
    }

    fn require_zero(&mut self, value: E, _error: VerifierError) -> Result<(), VerifierError> {
        self.zeros.push(value);
        self.zero_after.push(self.scalar_at.len());
        Ok(())
    }

    fn require_nonzero(&mut self, value: E, _error: VerifierError) -> Result<(), VerifierError> {
        self.nonzeros.push(value);
        Ok(())
    }

    fn next_integer(&mut self, bytes: usize) -> Result<E, VerifierError> {
        let value = self.inner.next_integer(bytes)?;
        self.cursor += bytes;
        Ok(value)
    }
}

/// What one run of the verifier gives.
struct Run {
    result: Result<Reduced<E>, VerifierError>,
    challenges: Vec<E>,
    zeros: Vec<E>,
    nonzeros: Vec<E>,
    scalar_at: Vec<usize>,
    zero_after: Vec<usize>,
}

impl Run {
    fn accepts(&self) -> bool {
        self.result.is_ok() && self.zeros.iter().all(|&z| z == ZERO) && self.nonzeros.iter().all(|&z| z != ZERO)
    }
}

/// One configuration: a named shape, the Keccak variant, the claims' mode, the program's IV.
#[derive(Clone)]
struct Config {
    name: String,
    shape: Shape,
    flock: (&'static str, Blake2s),
    claims: (&'static str, Claims),
    program_iv: [u8; 32],
    /// The setup roots the contract binds: `SetupRoots::REFERENCE`, or a real proof's own `F` (`tests/evm_vectors.rs`).
    roots: SetupRoots,
}

impl Config {
    /// The Keccak contract's IV (`contract_iv_for`) at the configuration's setup roots.
    fn contract_iv(&self) -> [u8; 32] {
        contract_iv_for(&self.shape, self.flock.1, &self.program_iv, &self.roots)
    }
}

fn run(config: &Config, iv: &[u8; 32], public: &[u8; 32], stream: &[u8]) -> Run {
    let seed = keccak_seed(&NAME, iv, public);
    let mut channel = Logging {
        inner: KeccakChannel::new(seed, stream, Checks::Enforce),
        cursor: 0,
        challenges: vec![],
        zeros: vec![],
        nonzeros: vec![],
        scalar_at: vec![],
        zero_after: vec![],
    };
    let words: [E; 4] =
        std::array::from_fn(|k| E::new(u64::from_be_bytes(public[8 * k..8 * k + 8].try_into().unwrap()), 0, 0));
    let result = reduce(&config.shape, words, &mut channel, config.flock.1, config.claims.1).and_then(|reduced| {
        channel.inner.finish()?;
        Ok(reduced)
    });
    Run {
        result,
        challenges: channel.challenges,
        zeros: channel.zeros,
        nonzeros: channel.nonzeros,
        scalar_at: channel.scalar_at,
        zero_after: channel.zero_after,
    }
}

fn count_bytes(counts: &[u64; 6]) -> [u8; 24] {
    let mut out = [0u8; 24];
    for (k, &c) in counts.iter().enumerate() {
        out[4 * k..4 * k + 4].copy_from_slice(&(c as u32).to_be_bytes());
    }
    out
}

/// A random stream announcing `counts`, made to pass every zero check, one check at a time, by solving for the scalar
/// read last before it (every check of this verifier is affine in it: the counts' range checks aside, which `counts`
/// meet; Flock's structured terminal in the last slice; the batch's terminal in the last stack value).
fn accepting(config: &Config, iv: &[u8; 32], public: &[u8; 32], len: usize, seed: u64, counts: &[u64; 6]) -> Vec<u8> {
    let mut stream = sample_stream(len, seed);
    stream[..24].copy_from_slice(&count_bytes(counts));
    let mut k = 0;
    loop {
        let current = run(config, iv, public, &stream);
        assert!(current.result.is_ok(), "a stream of the shape's length");
        if k >= current.zeros.len() {
            break;
        }
        if current.zeros[k] != ZERO {
            let read = current.zero_after[k];
            assert!(read > 0, "a scalar precedes the check");
            let offset = current.scalar_at[read - 1];
            let value_at = |x: E| {
                let mut patched = stream.clone();
                patched[offset..offset + 24].copy_from_slice(&scalar_bytes(x));
                run(config, iv, public, &patched).zeros[k]
            };
            let (v0, v1) = (value_at(ZERO), value_at(ONE));
            let slope = v0 + v1;
            assert!(slope != ZERO, "check {k} depends on its last scalar");
            let x = v0 * slope.inv();
            stream[offset..offset + 24].copy_from_slice(&scalar_bytes(x));
            assert_eq!(
                run(config, iv, public, &stream).zeros[k],
                ZERO,
                "check {k} holds once solved"
            );
        }
        k += 1;
    }
    assert!(
        run(config, iv, public, &stream).accepts(),
        "the solved stream is accepted"
    );
    stream
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn unhex(t: &str) -> Vec<u8> {
    (0..t.len() / 2)
        .map(|i| u8::from_str_radix(&t[2 * i..2 * i + 2], 16).expect("hex"))
        .collect()
}

fn element(x: E) -> String {
    format!("{:x}:{:x}:{:x}", x.c0, x.c1, x.c2)
}

fn elements(xs: &[E]) -> String {
    let mut out = xs.len().to_string();
    for &x in xs {
        out.push(' ');
        out.push_str(&element(x));
    }
    out
}

fn combined(claim: &Combined<E>) -> String {
    let mut out = format!("P {}", claim.points.len());
    for point in &claim.points {
        write!(out, " {}", elements(point)).unwrap();
    }
    write!(out, " T {}", claim.terms.len()).unwrap();
    for &(column, p, twist, coefficient) in &claim.terms {
        write!(out, " {:x} {p} {twist} {}", column.id(), element(coefficient)).unwrap();
    }
    write!(out, " V {} R {}", element(claim.value), claim.relations).unwrap();
    out
}

/// The vectors written so far, and the verdicts by kind (accepted, rejected).
#[derive(Default)]
struct Writer {
    out: String,
    id: usize,
    tally: std::collections::BTreeMap<&'static str, (usize, usize)>,
}

impl Writer {
    fn emit(&mut self, config: &Config, kind: &'static str, iv: &[u8; 32], public: &[u8; 32], stream: &[u8]) -> bool {
        self.emit_with(config, kind, iv, public, stream, "")
    }

    fn emit_with(
        &mut self,
        config: &Config,
        kind: &'static str,
        iv: &[u8; 32],
        public: &[u8; 32],
        stream: &[u8],
        extra: &str,
    ) -> bool {
        let r = run(config, iv, public, stream);
        let out = &mut self.out;
        writeln!(
            out,
            "VECTOR {} {} {} {} {kind}",
            self.id, config.name, config.flock.0, config.claims.0
        )
        .unwrap();
        let shape = config.shape;
        let rows: Vec<String> = shape.table_rows.iter().map(|r| r.to_string()).collect();
        writeln!(
            out,
            "SHAPE {} {} {}",
            shape.log_memory,
            shape.log_bytecode,
            rows.join(" ")
        )
        .unwrap();
        writeln!(out, "PROGRAMIV {}", hex(&config.program_iv)).unwrap();
        let roots = config.roots;
        writeln!(
            out,
            "SETUPROOTS {} {} {}",
            hex(&roots.f),
            hex(&roots.a0),
            hex(&roots.b0)
        )
        .unwrap();
        writeln!(out, "CONTRACTIV {}", hex(&config.contract_iv())).unwrap();
        let words: Vec<String> = layout_words_for(&shape, config.flock.1)
            .iter()
            .map(|w| hex(w))
            .collect();
        writeln!(out, "LAYOUTWORDS {} {}", words.len(), words.join(" ")).unwrap();
        let counts: Vec<String> = (0..6)
            .filter(|k| 4 * k + 4 <= stream.len())
            .map(|k| u32::from_be_bytes(stream[4 * k..4 * k + 4].try_into().unwrap()).to_string())
            .collect();
        writeln!(out, "COUNTS {} {}", counts.len(), counts.join(" ")).unwrap();
        writeln!(out, "IV {}", hex(iv)).unwrap();
        writeln!(out, "PUBLIC {}", hex(public)).unwrap();
        writeln!(out, "STREAM {} {}", stream.len(), hex(stream)).unwrap();
        match &r.result {
            Ok(_) => writeln!(out, "RESULT OK").unwrap(),
            Err(e) => writeln!(out, "RESULT ERR {e:?}").unwrap(),
        }
        writeln!(out, "CHALLENGES {}", elements(&r.challenges)).unwrap();
        writeln!(out, "ZEROS {}", elements(&r.zeros)).unwrap();
        writeln!(out, "NONZEROS {}", elements(&r.nonzeros)).unwrap();
        writeln!(out, "ACCEPT {}", r.accepts() as u8).unwrap();
        if let Ok(reduced) = &r.result {
            writeln!(out, "RELATIONS {}", reduced.relations).unwrap();
            let mut vars = format!("STACKVARS {}", reduced.stack_vars.len());
            for (commitment, v) in &reduced.stack_vars {
                write!(vars, " {commitment:?} {v}").unwrap();
            }
            writeln!(out, "{vars}").unwrap();
            writeln!(out, "OPENINGS {}", reduced.openings.len()).unwrap();
            for (commitment, opening) in &reduced.openings {
                match opening {
                    Opening::Point {
                        point,
                        value,
                        bit_slice,
                    } => {
                        let slice = match bit_slice {
                            None => "BITSLICE 0".to_string(),
                            Some(claim) => format!("BITSLICE 1 {}", combined(claim)),
                        };
                        writeln!(
                            out,
                            "OPENING {commitment:?} POINT {} VALUE {} {slice}",
                            elements(point),
                            element(*value)
                        )
                        .unwrap();
                    }
                    Opening::Weighted(claim) => {
                        writeln!(out, "OPENING {commitment:?} WEIGHTED {}", combined(claim)).unwrap()
                    }
                }
            }
            match &reduced.matrices {
                None => writeln!(out, "MATRICES 0").unwrap(),
                Some(m) => writeln!(
                    out,
                    "MATRICES 1 {} A {} B {}",
                    elements(&m.point),
                    element(m.a),
                    element(m.b)
                )
                .unwrap(),
            }
        }
        out.push_str(extra);
        writeln!(out, "END").unwrap();
        self.id += 1;
        let accepted = r.accepts();
        let entry = self.tally.entry(kind).or_default();
        if accepted {
            entry.0 += 1;
        } else {
            entry.1 += 1;
        }
        accepted
    }
}

/// Deterministic pseudo-random words.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn bytes32(&mut self) -> [u8; 32] {
        let mut out = [0u8; 32];
        for chunk in out.chunks_mut(8) {
            chunk.copy_from_slice(&self.next().to_le_bytes());
        }
        out
    }

    fn nonzero_byte(&mut self) -> u8 {
        loop {
            let b = (self.next() >> 24) as u8;
            if b != 0 {
                return b;
            }
        }
    }

    fn element(&mut self) -> E {
        E::new(self.next(), self.next(), self.next())
    }

    fn elements(&mut self, n: usize) -> Vec<E> {
        (0..n).map(|_| self.element()).collect()
    }
}

/// leanVM 9d50c92a3's Keccak VM runs (`tests/keccak_vm.rs`'s `KECCAK_RUNS`): name, memory cells, rows.
const RUNS: [(&str, u64, [u64; 6]); 4] = [
    ("keccak32", 184_479, [6956, 9877, 6578, 9652, 3995, 4440]),
    ("keccak128", 721_598, [24260, 36229, 24626, 35812, 15509, 17712]),
    ("keccak400", 2_243_324, [73288, 110893, 75762, 109932, 48157, 55316]),
    (
        "keccak1000",
        5_600_312,
        [181438, 275593, 188562, 273432, 120085, 138266],
    ),
];

fn shape_of(cells: u64, rows: [u64; 6]) -> Shape {
    Shape {
        log_memory: 64 - (cells - 1).leading_zeros() as usize,
        log_bytecode: 18,
        table_rows: rows,
    }
}

fn config(run: usize, flock: (&'static str, Blake2s), claims: (&'static str, Claims)) -> Config {
    let (name, cells, rows) = RUNS[run];
    Config {
        name: name.to_string(),
        shape: shape_of(cells, rows),
        flock,
        claims,
        program_iv: PROGRAM_IV,
        roots: SetupRoots::REFERENCE,
    }
}

/// The structured terminal on random inputs at every skip `k ≤ 6`, with the walked terminal's value (its reference).
fn terminal_vectors(out: &mut String, rng: &mut Rng) -> usize {
    let mut n = 0;
    for k in 0..=6usize {
        for _ in 0..2 {
            let z_skip = (k > 0).then(|| rng.element());
            let row_low = rng.elements(6 - k);
            let chi_in = rng.elements(11);
            let chi_in_prime = rng.elements(11);
            let s = rng.elements(64);
            let alpha = rng.element();
            let structured = structured_terminal(z_skip, &row_low, &chi_in, &chi_in_prime, &s, alpha);
            let walked = walked_terminal_with::<E, KeccakWalked>(z_skip, &row_low, &chi_in, &chi_in_prime, &s, alpha);
            assert_eq!(structured, walked, "the structured terminal is the walked one");
            writeln!(
                out,
                "TERMINAL {k} {} {} {} {} {} {} {} {}",
                z_skip.map_or("-".to_string(), element),
                elements(&row_low),
                elements(&chi_in),
                elements(&chi_in_prime),
                elements(&s),
                element(alpha),
                element(structured),
                element(walked)
            )
            .unwrap();
            n += 1;
        }
    }
    n
}

/// `KECCAK_VECTORS_OUT=<file> cargo test --release -p leanvm_univariate --test lean_keccak_vectors -- --ignored
/// --nocapture` (`KECCAK_REAL_DIR`, default `tests/vectors`: the real proofs `keccak.txt`, `keccak_rec3.txt`, if there).
#[test]
#[ignore]
fn lean_keccak_vectors() {
    deep(|| {
        let started = std::time::Instant::now();
        let path = std::env::var("KECCAK_VECTORS_OUT").unwrap_or_else(|_| "target/keccak_vectors.txt".to_string());
        let main = ("keccak", Blake2s::Keccak(KECCAK_MAIN));
        let rec3 = ("keccak_rec3", Blake2s::Keccak(KECCAK_REC3));
        let point = ("point", Claims::Point);
        let weighted = ("weighted", Claims::Weighted);
        let mut w = Writer::default();
        writeln!(
            w.out,
            "# leanvm_univariate Keccak VM differential test vectors (tests/lean_keccak_vectors.rs)"
        )
        .unwrap();
        let mut rng = Rng(0x5EED_1EA4_0000_00CC);
        let terminals = terminal_vectors(&mut w.out, &mut rng);

        // The full sets: the main line at the smallest run (both modes) and at 400 signatures, π1-rec3's shape at
        // 400 signatures (the recursion's) and the smallest.
        let full = [
            (0, main, point),
            (0, main, weighted),
            (2, main, point),
            (2, rec3, point),
            (0, rec3, point),
        ];
        for (c, &(run_index, flock, claims)) in full.iter().enumerate() {
            let config = config(run_index, flock, claims);
            let len = record_verifier(&config.shape, flock.1, claims.1).stream_len;
            let iv = config.contract_iv();
            for s in 0..2u64 {
                let public = rng.bytes32();
                let mut stream = sample_stream(len, 0x100 + 16 * c as u64 + s);
                if s == 1 {
                    stream[..24].copy_from_slice(&count_bytes(&config.shape.table_rows));
                }
                w.emit(&config, "random", &iv, &public, &stream);
            }
            let mut accepted = Vec::new();
            for s in 0..2u64 {
                let public = rng.bytes32();
                // One accepting vector under another program IV.
                let mut config = config.clone();
                if s == 1 {
                    config.program_iv = [7u8; 32];
                }
                let iv = config.contract_iv();
                let stream = accepting(
                    &config,
                    &iv,
                    &public,
                    len,
                    0x200 + 16 * c as u64 + s,
                    &config.shape.table_rows,
                );
                w.emit(&config, "accept", &iv, &public, &stream);
                accepted.push((public, stream));
            }
            // Other row counts that fit: none, one, the fewest a height sizes for, a full table, 2^r - 1, random.
            let heights = config.shape.heights();
            for s in 0..2u64 {
                let public = rng.bytes32();
                let pick = 2 * c as u64 + s;
                let counts: [u64; 6] = std::array::from_fn(|t| {
                    let r = heights[t];
                    let full = 1u64 << r;
                    match (pick + t as u64) % 6 {
                        0 => 0,
                        1 => 1,
                        2 => Shape::least_rows(r),
                        3 => full,
                        4 => full - 1,
                        _ => rng.next() % (full + 1),
                    }
                });
                let stream = accepting(&config, &iv, &public, len, 0x280 + 16 * c as u64 + s, &counts);
                w.emit(&config, "counts", &iv, &public, &stream);
            }
            let (public, base) = accepted[0].clone();
            // A count out of its range: above 2^r, or 2^r with a low bit set.
            {
                let t = (c + 5) % 6;
                let r = heights[t];
                let mut stream = base.clone();
                let bad = if c % 2 == 0 {
                    (1u64 << (r + 1)) + 3
                } else {
                    (1u64 << r) | 1
                };
                stream[4 * t..4 * t + 4].copy_from_slice(&(bad as u32).to_be_bytes());
                w.emit(&config, "badcount", &iv, &public, &stream);
            }
            let last_scalar = base.len() - 24;
            for position in [
                (rng.next() as usize) % base.len(),
                24 + (rng.next() as usize) % 32,
                last_scalar + (rng.next() as usize) % 24,
            ] {
                let mut stream = base.clone();
                stream[position] ^= rng.nonzero_byte();
                w.emit(&config, "mutate", &iv, &public, &stream);
            }
            w.emit(&config, "truncate", &iv, &public, &base[..base.len() - 1]);
            let mut extended = base.clone();
            extended.extend([0u8; 24]);
            w.emit(&config, "extend", &iv, &public, &extended);
        }
        // The other runs, the main line (1,000 signatures: a shape whose C1 does not fit WHIR, still a verifier).
        for (k, run_index) in [1usize, 3].into_iter().enumerate() {
            let config = config(run_index, main, point);
            let len = record_verifier(&config.shape, main.1, point.1).stream_len;
            let iv = config.contract_iv();
            let salt = 0x300 + 16 * k as u64;
            let public = rng.bytes32();
            w.emit(&config, "random", &iv, &public, &sample_stream(len, salt));
            let public = rng.bytes32();
            let stream = accepting(&config, &iv, &public, len, salt + 1, &config.shape.table_rows);
            w.emit(&config, "accept", &iv, &public, &stream);
            let mut mutated = stream.clone();
            let position = (rng.next() as usize) % mutated.len();
            mutated[position] ^= rng.nonzero_byte();
            w.emit(&config, "mutate", &iv, &public, &mutated);
        }

        // The real Keccak proofs, if there, with the contract's PCS_OPEN inputs, and three mutations each.
        let dir = std::env::var("KECCAK_REAL_DIR").unwrap_or_else(|_| "tests/vectors".to_string());
        for file in ["keccak.txt", "keccak_rec3.txt"] {
            let Ok(text) = std::fs::read_to_string(format!("{dir}/{file}")) else {
                println!("no {dir}/{file}: no real vector");
                continue;
            };
            let mut config_name = String::new();
            let mut shape_line: Vec<u64> = Vec::new();
            let mut public = [0u8; 32];
            let mut calldata = Vec::new();
            let mut calls: Vec<Vec<u8>> = Vec::new();
            let mut accepts = false;
            let mut whir_roots: Vec<Vec<u8>> = Vec::new();
            for line in text.lines().filter(|l| !l.starts_with('#') && !l.is_empty()) {
                let (key, value) = line.split_once(' ').expect("key value");
                match key {
                    "config" => config_name = value.to_string(),
                    "shape" => shape_line = value.split(' ').map(|x| x.parse().expect("a number")).collect(),
                    "public" => public.copy_from_slice(&unhex(value)),
                    "calldata" => calldata = unhex(value),
                    "pcs_open" => calls.push(unhex(value)),
                    "accepts" => accepts = value == "true",
                    "whir_root" => whir_roots.push(unhex(value)),
                    _ => {}
                }
            }
            let flock = match config_name.as_str() {
                "keccak" => main,
                "keccak_rec3" => rec3,
                other => panic!("no configuration {other}"),
            };
            let config = Config {
                name: format!("real-{config_name}"),
                shape: Shape {
                    log_memory: shape_line[0] as usize,
                    log_bytecode: shape_line[1] as usize,
                    table_rows: std::array::from_fn(|k| shape_line[2 + k]),
                },
                flock,
                claims: point,
                program_iv: PROGRAM_IV,
                // The contract binds the proof's own setup root `F` (the third call's), as `tests/evm_vectors.rs`.
                roots: SetupRoots {
                    f: whir_roots[2].clone().try_into().expect("32 bytes"),
                    ..SetupRoots::REFERENCE
                },
            };
            let iv = config.contract_iv();
            assert_eq!(&calldata[4..36], &public, "the calldata's public input");
            let stream = calldata[36..].to_vec();
            let extra: String = calls.iter().map(|c| format!("PCSOPEN {}\n", hex(c))).collect();
            assert!(accepts, "{config_name}: the vector's verdict");
            assert!(
                w.emit_with(&config, "real", &iv, &public, &stream, &extra),
                "{config_name}: the real proof is accepted"
            );
            for position in [
                (rng.next() as usize) % stream.len(),
                (rng.next() as usize) % 24,
                stream.len() - 24 + (rng.next() as usize) % 24,
            ] {
                let mut mutated = stream.clone();
                mutated[position] ^= rng.nonzero_byte();
                w.emit(&config, "real-mutate", &iv, &public, &mutated);
            }
        }

        std::fs::write(&path, &w.out).expect("the vectors file");
        println!(
            "{} vectors and {terminals} terminal vectors, {} lines, written to {path}",
            w.id,
            w.out.lines().count()
        );
        for (kind, (yes, no)) in &w.tally {
            println!("{kind}: {yes} accepted, {no} rejected");
        }
        println!("in {:.1} s", started.elapsed().as_secs_f64());
    });
}
