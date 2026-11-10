// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The vectors `formal/WhirBridge/Test/CheckPcs.lean` reads: PCS claims (version 1) on polynomials of `n = 15, 16,
//! 18` variables (word `i` the low 64 bits of `keccak256("leanPCS-lean" || n || i)`, the point's coordinate `j` the
//! element the low 24 bytes of `keccak256("leanPCS-lean-point" || n || j)` encode), each with the claim's bytes, its
//! fields, the out-of-domain point, and its opening's stream and one full Merkle path per query (the replay of
//! `verify_claim`'s transcript, nothing checked).
//!
//! `cargo run --release -p pcs_claim --example lean_vector > target/pcs_claim_vector.txt`

use pcs_claim::{LOG_INV_RATE, PUBLIC_DIGEST, PcsClaim, commit, element_of, iv, ood_point, open, verify, wire_proof};
use primitives::field::{F64, F192};
use primitives::hash::hash as keccak256;

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

fn vector(name: &str, claim: &PcsClaim, proof: &fiat_shamir::transcript::Proof) -> String {
    use verifier::{Digest, E, Transcript};
    let wire = &wire_proof(proof);
    let n = claim.n as usize;
    let mut transcript = Transcript::new(wire, Digest(iv(claim)), Digest(PUBLIC_DIGEST), false);
    let halves = transcript.next_scalars(2).expect("the root's two scalars");
    assert_eq!(Digest::from_halves(halves[0], halves[1]), Ok(Digest(claim.root)));
    let _lambda = transcript.sample();
    let zero = E::new(0, 0, 0);
    verifier::whir::verify_whir(&mut transcript, n, 1u64 << n, LOG_INV_RATE, zero, Digest(claim.root), &|_| zero)
        .expect("the replay walks the proof");
    let paths = transcript.finish().expect("the replay reads the whole proof");
    let mut out = format!("vector {name}\n");
    out += &line("n", [n as u64]);
    out += &line("claimbytes", claim.encode().iter().map(|&b| b as u64));
    out += &line("payload", claim.hash().iter().map(|&b| b as u64));
    out += &line("root", words(&claim.root));
    out += &line("ood", limbs(&claim.ood));
    out += &line("point", claim.point.iter().flat_map(limbs));
    out += &line("value", limbs(&claim.value));
    out += &line("oodpoint", ood_point(n, &claim.root).iter().flat_map(limbs));
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

fn main() {
    let mut out = String::new();
    for n in [15usize, 16, 18] {
        let words: Vec<F64> = (0..1u64 << n)
            .map(|i| {
                let digest = keccak256(&[b"leanPCS-lean".as_slice(), &[n as u8], &i.to_be_bytes()].concat());
                F64(u64::from_be_bytes(digest[24..].try_into().expect("8 bytes")))
            })
            .collect();
        let committed = commit(words);
        let point: Vec<F192> = (0..n as u8)
            .map(|j| {
                let digest = keccak256(&[b"leanPCS-lean-point".as_slice(), &[n as u8], &[j]].concat());
                element_of(digest[8..].try_into().expect("24 bytes"))
            })
            .collect();
        let claim = committed.claim_at(point);
        let proof = open(&committed, &claim);
        assert!(verify(&claim.encode(), &wire_proof(&proof)), "the honest opening verifies");
        out += &vector(&format!("n{n}"), &claim, &proof);
    }
    print!("{out}");
}
