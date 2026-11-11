// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! `π2`'s circuit compiled from `π1`'s recorded verifier (SPEC-REC.md §2, §10), its witness from the real Keccak VM
//! proofs (`crates/leanvm/univariate/tests/vectors/`: π1-rec4's, π1-rec3's and the main line's).
//!
//! - every position's pull equals its push, and the public side holds (`spec::Circuit::check`);
//! - the circuit's calls, on its public inputs, are exactly the vector's claims;
//! - every digest and every element is `eval::evaluate`'s;
//! - a flipped stream byte, a changed public input, a changed witness word are each caught;
//! - the layout's counts: `N`, the fill, the regions, the blocks and the selector pairs;
//! - (`keccak_rec4_128_any_stream`, ignored) on streams that are no proof, the digests and elements still the
//!   evaluator's.
//!
//! `cargo test --release -p leanvm_rec --test circuit -- --nocapture --test-threads 1`

#[path = "../../univariate/tests/vectors/mod.rs"]
mod vectors;

use leanvm_statement::evm::record::Node;
use leanvm_statement::field::K;
use leanvm_statement::shapes::PROGRAM_IV;
use leanvm_statement::transcript::keccak_seed;
use leanvm_rec::circuit::compile::{Compiled, Inputs, Layout, pi2};
use leanvm_rec::circuit::spec::Failure;
use leanvm_rec::eval::{Value, evaluate};
use leanvm_univariate::contract::{NAME, Recorded, record_verifier_with};

const STREAM_AT: usize = 4 + 32;

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

fn vector(name: &str) -> vectors::Vector {
    let path = format!(
        "{}/../univariate/tests/vectors/{name}.txt",
        env!("CARGO_MANIFEST_DIR")
    );
    vectors::read(&std::fs::read_to_string(&path).expect("a committed vector"))
}

fn compiled(recorded: &Recorded, layout: Layout, iv: [u8; 32], public: [u8; 32], stream: &[u8]) -> Compiled {
    let c = pi2(
        recorded,
        layout,
        &Inputs {
            program_iv: PROGRAM_IV,
            public,
            stream,
        },
    );
    assert_eq!(c.pi1_iv, iv, "the circuit's seed hashes the recorded verifier's contract IV");
    c
}

/// Keccak-f's positions a permutation, by layout (SPEC-REC.md §2.4.1; D16v's `kd` rows as measured by
/// `circuit::tests::d16_rows_a_permutation`).
fn keccak_positions(layout: Layout) -> usize {
    match layout {
        Layout::D16v => 16 * (1536 + 6144 + 160 + 344),
    }
}

fn report(name: &str, layout: &str, c: &Compiled) {
    let s = &c.finished.stats;
    println!(
        "{name} {layout}: N = 2^{} ({} positions used, {:.1}%), {} rows, {} blocks, {} selector pairs, {} regions",
        s.log_n,
        s.positions_used,
        100.0 * s.fill(),
        s.rows_used,
        s.blocks,
        s.pairs,
        s.rows.len()
    );
    println!(
        "  Keccak-256 calls {}, Keccak-f {}, packings {}, free bits (alone, with a copy) {:?}, E units (ended, forwarded) mul {:?} add {:?} square {:?}",
        c.keccak_calls, c.permutations, c.packings, c.free_bits, c.arith[0], c.arith[1], c.arith[2]
    );
    println!(
        "  values {}, free {}, junk {}, free ends {}, dead slots {}, kappa {}, ports {}, forwards placed {} / unplaced {}",
        s.values,
        s.free_values,
        s.junk,
        s.free_ends,
        s.dead_slots,
        s.kappa,
        s.ports,
        s.forwards_placed,
        s.forwards_unplaced
    );
    println!(
        "  rows in blocks (padding included) {}, the verifier's formulas: {} terms, {} products; quotient 15N = 2^{:.2} words",
        s.rows_in_blocks,
        s.formula_terms,
        s.formula_products,
        (15.0f64).log2() + s.log_n as f64
    );
    let w = 1usize << s.log_width;
    for (region, rows) in &s.rows {
        println!("  {region:<22} {rows:>9} rows {:>10} positions", rows * w);
    }
}

/// A PCS claim's words, as the contract writes them: its root, then its out-of-domain answer, point and value, each
/// an element's word.
fn claim_words(claim: &[u8]) -> Vec<u8> {
    let c = pcs_claim::PcsClaim::decode(claim).expect("a well-formed claim");
    let element = |x: primitives::field::F192| {
        let mut w = [0u8; 32];
        w[8..].copy_from_slice(&pcs_claim::element_bytes(x));
        w
    };
    let mut out = c.root.to_vec();
    for x in [c.ood].into_iter().chain(c.point.iter().copied()).chain([c.value]) {
        out.extend(element(x));
    }
    out
}

/// `(log N, the fill's bounds)` expected.
fn run(name: &str, layout: Layout, log_n: u8, fill: (f64, f64)) {
    let v = vector(name);
    let variant = vectors::variant_of(&v.config);
    // The contract binds the proof's setup commitment `F` (the third claim's).
    let roots = vectors::setup_roots(&v);
    let recorded = record_verifier_with(&v.shape, variant, &roots);
    let stream = v.calldata[STREAM_AT..].to_vec();
    let iv = recorded.iv(&PROGRAM_IV);
    let c = compiled(&recorded, layout, iv, v.public, &stream);
    let s = &c.finished.stats;
    report(name, &format!("{layout:?}"), &c);
    // The counts: N, the fill, Keccak-f's positions, a block or two a region.
    assert_eq!(s.log_n, log_n, "{name} {layout:?}: N");
    assert!(
        fill.0 <= s.fill() && s.fill() <= fill.1,
        "{name} {layout:?}: the fill {}",
        s.fill()
    );
    let keccak: usize = s
        .rows
        .iter()
        .filter(|(r, _)| r.starts_with("keccak"))
        .map(|(_, &n)| n)
        .sum();
    // Every permutation's rows, but the last rounds' planes no lane read needs (D16v: 64 `k1` rows a plane).
    assert_eq!(
        keccak << s.log_width,
        c.permutations * keccak_positions(layout) - c.planes_unmade * 64 * 16,
        "{name}: Keccak-f's positions"
    );
    // At most two blocks a region on average; three where the rows fill `2^L` but for a few (π1-rec3 at 400
    // signatures with `C1`'s claim hashed in the circuit: 99.9%, little room to pad a region to fewer blocks).
    assert!(
        s.blocks <= 3 * s.rows.len(),
        "{name}: at most three blocks a region on average"
    );
    let circuit = &c.finished.circuit;
    let w = &c.finished.witness;

    // Every pull equals its push, and the public side holds.
    assert_eq!(
        circuit.check(w, &c.public),
        Ok(()),
        "{name} {layout:?}: the circuit holds"
    );
    // The calls on the public inputs are the vector's claims, word by word (root, out-of-domain answer, point,
    // value: the claims the contract packs and hashes).
    // The claims hashed in the circuit are the vector's by their Keccak-256s; the others by their words.
    let hashed: Vec<usize> = circuit.hashed.iter().map(|&i| i as usize).collect();
    let words: Vec<Vec<u8>> = (v.claims.iter().enumerate())
        .filter(|(i, _)| !hashed.contains(i))
        .map(|(_, claim)| claim_words(claim))
        .collect();
    assert_eq!(circuit.call_inputs(&c.public), words, "{name}: the calls are the vector's");
    let hashes: Vec<[u8; 32]> =
        hashed.iter().map(|&i| leanvm_statement::transcript::keccak256(&v.claims[i])).collect();
    assert_eq!(c.public.claim_hashes, hashes, "{name}: the claim hashes are the vector's claims'");
    let back = circuit.public_from_calls(v.public, &words).map(|p| leanvm_rec::circuit::spec::PublicInputs {
        claim_hashes: hashes.clone(),
        ..p
    });
    assert_eq!(back.as_ref(), Some(&c.public), "{name}: the public inputs are read back from the calls");
    // The digests and the elements are the evaluator's.
    let seed = keccak_seed(&NAME, &iv, &v.public);
    let values = evaluate(&c.expanded, seed, &v.public, &stream);
    for (&id, digest) in &c.digests {
        let mut bytes = [0u8; 32];
        for (i, &d) in digest.iter().enumerate() {
            bytes[i / 8] |= (c.finished.words[d as usize].0 as u8) << (i % 8);
        }
        assert_eq!(Value::State(bytes), values[id as usize], "{name}: digest of node {id}");
    }
    for (&id, limbs) in &c.limbs {
        let x = values[id as usize].e();
        let words = limbs.map(|l| c.finished.words[l as usize]);
        assert_eq!(
            words,
            [K(x.c0), K(x.c1), K(x.c2)],
            "{name}: the limbs of node {id} ({:?})",
            c.expanded.nodes[id as usize]
        );
    }
    println!("  checked: {} digests, {} elements", c.digests.len(), c.limbs.len());

    // A changed public input is caught.
    let mut other = c.public.clone();
    other.statement[5] ^= 1;
    assert!(
        matches!(circuit.check(w, &other), Err(Failure::Public { .. })),
        "{name}: the statement"
    );
    // An element and a root, where the contract encodes a claim (none with π1's three claims hashed), and a claim's
    // hash.
    if c.public.elements.len() > 3 {
        let mut other = c.public.clone();
        other.elements[3].c1 ^= 1 << 7;
        assert!(
            matches!(circuit.check(w, &other), Err(Failure::Public { .. })),
            "{name}: an element"
        );
    }
    if !c.public.roots.is_empty() {
        let mut other = c.public.clone();
        other.roots[0][9] ^= 1;
        assert!(
            matches!(circuit.check(w, &other), Err(Failure::Public { .. })),
            "{name}: a root"
        );
    }
    for k in 0..c.public.claim_hashes.len() {
        let mut other = c.public.clone();
        other.claim_hashes[k][9] ^= 1;
        assert!(
            matches!(circuit.check(w, &other), Err(Failure::Public { .. })),
            "{name}: claim hash {k}"
        );
    }
    // A changed witness word at wired positions is caught.
    let mut seed = 0x2545_f491_4f6c_dd1du64;
    let wired: Vec<usize> = (0..circuit.n()).filter(|&i| circuit.sigma[i] as usize != i).collect();
    for _ in 0..30 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        let i = wired[seed as usize % wired.len()];
        let mut bad = w.clone();
        bad[i] = bad[i] + K(1 << (seed % 64));
        assert!(
            circuit.check(&bad, &c.public).is_err(),
            "{name}: a change at {i} is caught"
        );
    }
    // A flipped stream byte (hashed, and in the middle) gives another witness the public side rejects.
    let mut mutated = stream.clone();
    mutated[stream.len() / 2] ^= 1;
    let m = compiled(&recorded, layout, iv, v.public, &mutated);
    assert_eq!(
        m.finished.circuit.sigma, circuit.sigma,
        "the circuit does not depend on the proof"
    );
    assert_eq!(
        m.finished.circuit.kappa, circuit.kappa,
        "the circuit does not depend on the proof"
    );
    assert!(
        matches!(
            circuit.check(&m.finished.witness, &c.public),
            Err(Failure::Public { .. })
        ),
        "{name}: a flipped stream byte is caught"
    );
    let zero_checks = recorded.graph.zero.len();
    let nodes = c.expanded.nodes.iter().filter(|n| matches!(n, Node::Mul(..))).count();
    println!("  mutations caught; {zero_checks} zero checks, {nodes} products in the expanded graph");
}

/// π1-rec4 at the reference shape (128 signatures), D16v: `2^24` positions at 97.8% with π1's three claims hashed.
#[test]
fn keccak_rec4_128_d16v() {
    deep(|| run("keccak128_rec4", Layout::D16v, 24, (0.95, 0.99)));
}

/// π1-rec4 at 400 signatures, D16v: `2^24` positions at 99.5% with π1's three claims hashed.
#[test]
fn keccak_rec4_400_d16v() {
    deep(|| run("keccak_rec4", Layout::D16v, 24, (0.95, 1.0)));
}

/// π1-rec3 (the Lean's) at the reference shape: its three claims do not fit `2^24`, so `C1`'s alone is hashed
/// (96.5%).
#[test]
fn keccak_rec3_128_d16v() {
    deep(|| run("keccak128_rec3", Layout::D16v, 24, (0.90, 0.99)));
}

/// The circuit evaluates π1-rec4's graph on streams that are no proof (the reference's with a byte flipped, and a
/// random one): every digest and every element's limbs are the evaluator's, so the witness is the graph's on any stream,
/// not only on an accepted one; how many zero checks hold is printed.
#[test]
#[ignore = "compiles the reference circuit twice (2^24 positions)"]
fn keccak_rec4_128_any_stream() {
    deep(|| {
        let v = vector("keccak128_rec4");
        let variant = vectors::variant_of(&v.config);
        let recorded = record_verifier_with(&v.shape, variant, &vectors::setup_roots(&v));
        let stream = v.calldata[STREAM_AT..].to_vec();
        let iv = recorded.iv(&PROGRAM_IV);
        let mut flipped = stream.clone();
        flipped[stream.len() / 2] ^= 1;
        let random = leanvm_univariate::contract::sample_stream(stream.len(), 0xabcdef);
        for (label, st) in [("flipped", flipped), ("random", random)] {
            let m = compiled(&recorded, Layout::D16v, iv, v.public, &st);
            let values = evaluate(&m.expanded, keccak_seed(&NAME, &iv, &v.public), &v.public, &st);
            for (&id, digest) in &m.digests {
                let mut bytes = [0u8; 32];
                for (i, &d) in digest.iter().enumerate() {
                    bytes[i / 8] |= (m.finished.words[d as usize].0 as u8) << (i % 8);
                }
                assert_eq!(Value::State(bytes), values[id as usize], "{label}: digest of node {id}");
            }
            for (&id, limbs) in &m.limbs {
                let x = values[id as usize].e();
                let words = limbs.map(|l| m.finished.words[l as usize]);
                assert_eq!(words, [K(x.c0), K(x.c1), K(x.c2)], "{label}: limbs of node {id}");
            }
            let holding = (recorded.graph.zero.iter())
                .filter(|&&(id, _)| values[m.map[id as usize] as usize].e() == leanvm_statement::field::E::default())
                .count();
            println!(
                "{label} stream: {} digests, {} elements agree; zero checks holding {holding}/{}",
                m.digests.len(),
                m.limbs.len(),
                recorded.graph.zero.len()
            );
        }
    });
}

/// The main line (every challenge hashed, the batch one variable a round) at 32 signatures, D16v: it does not fit
/// `2^24` (`2^25` at 53.6%), which is why the recursion proves π1-rec4 (π1-rec3 before it).
#[test]
fn keccak_32_d16v() {
    deep(|| run("keccak", Layout::D16v, 25, (0.50, 0.60)));
}
