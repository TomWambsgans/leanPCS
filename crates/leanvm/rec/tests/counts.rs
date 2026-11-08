// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The inner verifier's graph on real proofs, and its counts (SPEC-REC.md §1).
//!
//! - `the_graph_is_the_verifier_on_real_proofs`: the recorded graph, evaluated on each committed real proof
//!   (`crates/leanvm/univariate/tests/vectors/`), writes exactly the `PCS_OPEN` inputs the contract wrote, and its
//!   checks hold: the evaluator is the witness generator's core.
//! - `count_report` (ignored): the graph's counts at the reference shape, for the Keccak VM's two variants.
//!
//! `cargo test --release -p leanvm_rec --test counts -- --include-ignored --nocapture`

#[path = "../../univariate/tests/vectors/mod.rs"]
mod vectors;

use leanvm_statement::evm::record::Node;
use leanvm_statement::shapes::PROGRAM_IV;
use leanvm_statement::transcript::keccak_seed;
use leanvm_rec::count::{Counts, count, shared};
use leanvm_rec::eval::{call_inputs, checks, evaluate};
use leanvm_rec::{REFERENCE, permutations};
use leanvm_univariate::contract::{NAME, Recorded, record_verifier};
use leanvm_univariate::{Claims, KECCAK_MAIN, KECCAK_REC3, Variant};

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

const STREAM_AT: usize = 4 + 32;

fn vector(name: &str) -> vectors::Vector {
    let path = format!(
        "{}/../univariate/tests/vectors/{name}.txt",
        env!("CARGO_MANIFEST_DIR")
    );
    vectors::read(&std::fs::read_to_string(&path).expect("a committed vector"))
}

#[test]
fn the_graph_is_the_verifier_on_real_proofs() {
    deep(|| {
        for name in ["keccak", "keccak128_rec3", "keccak_rec3"] {
            let v = vector(name);
            let variant = vectors::variant_of(&v.config);
            let roots = leanvm_univariate::contract::SetupRoots {
                f: v.whir_roots[2],
                ..leanvm_univariate::contract::SetupRoots::REFERENCE
            };
            let recorded = leanvm_univariate::contract::record_verifier_with(&v.shape, variant, Claims::Point, &roots);
            let stream = &v.calldata[STREAM_AT..];
            assert_eq!(stream.len(), recorded.stream_len);
            let seed = keccak_seed(
                &NAME,
                &recorded.iv(&PROGRAM_IV),
                &v.public,
            );
            let values = evaluate(&recorded.graph, seed, &v.public, stream);
            let inputs = call_inputs(&recorded, &values, stream);
            assert_eq!(
                inputs, v.calls,
                "{name}: the evaluated graph writes the recorded PCS_OPEN inputs"
            );
            let (zero, nonzero) = checks(&recorded.graph, &values);
            assert!(
                zero.iter().all(|x| *x == Default::default()),
                "{name}: every zero check holds"
            );
            assert!(
                nonzero.iter().all(|x| *x != Default::default()),
                "{name}: every nonzero check holds"
            );
            // A flipped byte of the stream changes some call's input or breaks a check.
            let mut mutated = stream.to_vec();
            mutated[stream.len() / 2] ^= 1;
            let values = evaluate(&recorded.graph, seed, &v.public, &mutated);
            let (zero, _) = checks(&recorded.graph, &values);
            let broken =
                call_inputs(&recorded, &values, &mutated) != v.calls || zero.iter().any(|x| *x != Default::default());
            assert!(broken, "{name}: a mutated stream is caught");
            println!(
                "{name}: {} nodes evaluated, {} calls equal to the vector's, {} zero and {} nonzero checks hold",
                values.len(),
                inputs.len(),
                recorded.graph.zero.len(),
                recorded.graph.nonzero.len()
            );
        }
    });
}

struct Config {
    name: String,
    variant: Variant,
}

fn configs() -> Vec<Config> {
    vec![
        Config {
            name: "Keccak VM main line (KECCAK_MAIN)".into(),
            variant: KECCAK_MAIN,
        },
        Config {
            name: "Keccak VM π1-rec3 (KECCAK_REC3)".into(),
            variant: KECCAK_REC3,
        },
    ]
}

fn print_counts(name: &str, recorded: &Recorded, c: &Counts) {
    let graph = &recorded.graph;
    println!("\n### {name}");
    println!(
        "nodes {} (live {}), constants {}, statement words {}",
        c.nodes, c.live, c.consts, c.statement
    );
    println!(
        "stream {} B (hashed {} B); live reads: {} scalars, {} root halves, {} integers; {} live reads never hashed",
        c.stream_bytes, c.hashed_stream_bytes, c.scalars, c.halves, c.integers, c.unhashed_live_reads
    );
    let by: Vec<String> = c
        .hashes_by_permutations()
        .iter()
        .map(|(p, n)| format!("{n} of {p} perm"))
        .collect();
    let bytes: usize = c.hash_lengths.iter().sum();
    println!(
        "Keccak-256 calls {} ({} B hashed, longest {} B): {} Keccak-f permutations [{}]; challenges {}",
        c.hash_lengths.len(),
        bytes,
        c.hash_lengths.iter().max().unwrap_or(&0),
        c.permutations,
        by.join(", "),
        c.challenges
    );
    let o = &c.ops;
    println!(
        "graph ops: products {} (x*y {}, squares {}), linear {} (adds {}, +const {}, *const {})",
        o.products(),
        o.muls,
        o.squares,
        o.linear(),
        o.adds,
        o.add_const,
        o.mul_const
    );
    let k = &c.kernel_ops;
    println!(
        "ring kernels {}: products {} (x*y {}, squares {}), linear {} (adds {}, +const {}, *const {})",
        c.kernels,
        k.products(),
        k.muls,
        k.squares,
        k.linear(),
        k.adds,
        k.add_const,
        k.mul_const
    );
    let t = &c.total_ops;
    println!(
        "TOTAL E ops (kernels expanded): products {} (x*y {}, squares {}), linear {} (adds {}, +const {}, *const {})",
        t.products(),
        t.muls,
        t.squares,
        t.linear(),
        t.adds,
        t.add_const,
        t.mul_const
    );
    println!(
        "bit fields {}, zero checks {}, nonzero checks {}",
        c.bits, c.zero_checks, c.nonzero_checks
    );
    println!(
        "claims {}: distinct points {}, coordinates {} in all, {} distinct non-constant",
        c.claims.len(),
        c.distinct_points(),
        c.coordinates(),
        c.distinct_coordinates(graph)
    );
    for claim in &c.claims {
        let consts = claim
            .point
            .iter()
            .filter(|&&id| matches!(graph.nodes[id as usize], Node::Const(_)))
            .count();
        let (prefix, anywhere) = shared(&c.claims[0].point, &claim.point);
        println!(
            "  {}: {} coordinates ({} constant), shares a prefix of {} with {}'s point ({} of its coordinates anywhere in it)",
            claim.name,
            claim.point.len(),
            consts,
            prefix,
            c.claims[0].name,
            anywhere
        );
    }
    if c.claims.len() > 3 {
        let (prefix, anywhere) = shared(&c.claims[3].point, &c.claims[0].point);
        println!(
            "  {}'s point in {}'s: prefix {}, anywhere {}",
            c.claims[0].name, c.claims[3].name, prefix, anywhere
        );
    }
    // The packings pi2 needs: every live read and every challenge between bytes and E.
    let pack_bits = 192 * c.scalars + 128 * c.halves + 32 * c.integers + 192 * c.challenges;
    println!(
        "packings: {} reads + {} challenges = {} E cells from {} bits; {} stream bits + {} state bits absorbed",
        c.scalars + c.halves + c.integers,
        c.challenges,
        c.scalars + c.halves + c.integers + c.challenges,
        pack_bits,
        8 * c.hashed_stream_bytes,
        256 * (c.hash_lengths.len() - 1)
    );
}

#[test]
#[ignore]
fn count_report() {
    deep(|| {
        println!("## pi1's verifier graph at the reference shape (128 signatures), Claims::Point");
        println!("Keccak-256 of the seed: {} perm (80 B)", permutations(80));
        for config in configs() {
            let recorded = record_verifier(&REFERENCE, config.variant, Claims::Point);
            let counts = count(&recorded);
            print_counts(&config.name, &recorded, &counts);
        }
    });
}

/// The transcript's shape: the challenges' hashes in order, run-length encoded by the stream bytes each absorbs
/// (besides the 32-byte state), and the stream's bytes by the phase that reads them.
#[test]
#[ignore]
fn transcript_shape() {
    deep(|| {
        for config in configs().into_iter().take(2) {
            let recorded = record_verifier(&REFERENCE, config.variant, Claims::Point);
            let graph = &recorded.graph;
            println!("\n### {}: the challenges in order", config.name);
            let mut runs: Vec<(u32, usize)> = Vec::new();
            for node in &graph.nodes {
                if let Node::Hash(_, from, to) = *node {
                    match runs.last_mut() {
                        Some((bytes, n)) if *bytes == to - from => *n += 1,
                        _ => runs.push((to - from, 1)),
                    }
                }
            }
            let line: Vec<String> = runs.iter().map(|(b, n)| format!("{n}x{b}B")).collect();
            println!("  {}", line.join(" "));
            for (phase, bytes) in &recorded.reads {
                println!("  read {bytes:>5} B  [{phase}]");
            }
        }
    });
}
