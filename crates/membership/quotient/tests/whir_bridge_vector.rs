// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The test vectors for `formal/WhirBridge`, in the form leanerVM mumbai's Lean verifier reads (the scalar stream,
//! then one full Merkle path per query: the pruned batches expanded, as `Transcript::finish` returns them), of the
//! EIP's PCS claims (`pcs_claim`, version 1: the IV `keccak256(PCS_claim)`, a zero public digest, the root as the
//! stream's first two scalars, one opening of `f(z) = ood` and `f(point) = value`):
//!
//! * `public`: an opening of a pseudo-random table of `2^15` words;
//! * `witness`, `wiring`, `copy`, `gate`, `sum`: the five openings of a membership proof on a circuit of `2^17`
//!   rows, by the real prover.
//!
//! Each vector carries its claim's bytes (`pcsclaim`), from which the Lean recomputes the IV and the out-of-domain
//! point. Regenerate and check, from the repository root:
//!
//!   cargo test -p quotient --release --test whir_bridge_vector -- --ignored
//!   (cd formal/WhirBridge && lake env lean --run Test/Check.lean ../../target/whir_bridge_vector.txt)
//!
//! The first writes `target/whir_bridge_vector.txt` (or `$WHIR_BRIDGE_VECTOR`).

use pcs_claim::PcsClaim;
use primitives::field::{F64, F192};
use primitives::test_rng::Rng;
use quotient::circuit::{Builder, Src, public_words};
use quotient::opening::Commitment;
use quotient::protocol::{Index, open, prove_with_seed};
use quotient::statement::{Statement, pair};
use verifier::{Digest, E, Transcript};

fn words(bytes: &[u8; 32]) -> [u64; 4] {
    std::array::from_fn(|i| u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().expect("8 bytes")))
}

fn line(tag: &str, values: impl IntoIterator<Item = u64>) -> String {
    let mut s = tag.to_string();
    for v in values {
        s.push(' ');
        s.push_str(&v.to_string());
    }
    s.push('\n');
    s
}

fn limbs(x: &F192) -> [u64; 3] {
    [x.c0, x.c1, x.c2]
}

/// A vector: the claim's bytes, the root, the claim, the stream and one full path per query (the replay of
/// `pcs_claim::verify`'s transcript, nothing checked).
fn vector(name: &str, claim: &PcsClaim, proof: &fiat_shamir::transcript::Proof) -> String {
    let wire = &pcs_claim::wire_proof(proof);
    let mut transcript = Transcript::new(wire, Digest(pcs_claim::iv(claim)), Digest(pcs_claim::PUBLIC_DIGEST), false);
    let halves = transcript.next_scalars(2).expect("the root's two scalars");
    assert_eq!(Digest::from_halves(halves[0], halves[1]), Ok(Digest(claim.root)));
    let _lambda = transcript.sample();
    let zero = E::new(0, 0, 0);
    let n = claim.n as usize;
    verifier::whir::verify_whir(&mut transcript, n, 1u64 << n, pcs_claim::LOG_INV_RATE, zero, Digest(claim.root), &|_| zero)
        .expect("the replay walks the proof");
    let paths = transcript.finish().expect("the replay reads the whole proof");
    let mut out = format!("vector {name}\n");
    out += &line("pcsclaim", claim.encode().iter().map(|&b| b as u64));
    out += &line("root", words(&claim.root));
    out += &line("claim", claim.point.iter().chain([&claim.value]).flat_map(limbs));
    out += &line("stream", proof.stream.iter().flat_map(limbs));
    for path in &paths {
        out += &line(
            "open",
            [path.leaf.len() as u64]
                .into_iter()
                .chain(path.leaf.iter().map(|k| k.0))
                .chain(path.siblings.iter().flat_map(words)),
        );
    }
    out + "end\n"
}

#[test]
#[ignore = "writes the vectors `formal/WhirBridge` checks; run with --ignored"]
fn whir_bridge_vector() {
    let mut rng = Rng::new(0xB41D);
    let mut out = String::new();

    let table: Vec<F64> = (0..1u64 << 15)
        .map(|k| F64((k + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(17)))
        .collect();
    let committed = pcs_claim::commit(table);
    let claim = committed.claim_at(rng.ext_vec(15));
    let proof = pcs_claim::open(&committed, &claim);
    assert!(pcs_claim::verify(&claim.encode(), &pcs_claim::wire_proof(&proof)));
    out += &vector("public", &claim, &proof);

    let mut b = Builder::new();
    let x: Vec<Src> = (0..256).map(|_| b.input()).collect();
    let digest = b.keccak256_64(&[&x[..], &x[..]].concat());
    let circuit = b.finish(17, &public_words(&x, &digest));
    let index = Index::new(&circuit);
    let index_committed = index.commit();
    let commitment = Commitment::of(&index_committed);
    let y: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
    let statement = Statement { y, root: pair(&y, &y) };
    let inputs: Vec<bool> = (0..256).map(|i| (y[i / 8] >> (i % 8)) & 1 == 1).collect();
    let proved = prove_with_seed(&circuit, &index, &commitment, &statement, &circuit.cells(&inputs), &[7; 32]);
    let openings = open(&proved.tables, &proved.claims, &index_committed);
    let c = &proved.commitments;
    let on = [c.witness, commitment, c.table];
    let names = ["witness", "wiring", "copy", "gate", "sum"];
    for (((k, claim), proof), name) in proved.claims.all().into_iter().zip(&openings.0).zip(names) {
        let claim = on[k].pcs_claim(claim);
        assert!(pcs_claim::verify(&claim.encode(), &pcs_claim::wire_proof(proof)), "{name}");
        out += &vector(name, &claim, proof);
    }
    let path = std::env::var("WHIR_BRIDGE_VECTOR")
        .unwrap_or_else(|_| concat!(env!("CARGO_MANIFEST_DIR"), "/../../../target/whir_bridge_vector.txt").to_string());
    std::fs::write(&path, out).expect("write the vectors");
    println!("wrote {path}");
}
