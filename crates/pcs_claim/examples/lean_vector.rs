// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The vectors `formal/WhirBridge/Test/CheckPcs.lean` reads: PCS claims (version 1) on polynomials of `n = 15, 16,
//! 18` variables (word `i` the low 64 bits of `keccak256("leanPCS-lean" || n || i)`, the point's coordinate `j` the
//! element the low 24 bytes of `keccak256("leanPCS-lean-point" || n || j)` encode), each with the claim's bytes, its
//! fields, the out-of-domain point, and its opening's stream and one full Merkle path per query (the paths
//! `verify_claim_paths` checks).
//!
//! `cargo run --release -p pcs_claim --example lean_vector > target/pcs_claim_vector.txt`

use pcs_claim::lean::{limbs, line, opening, words};
use pcs_claim::{Codeword, PcsClaim, commit, element_of, ood_point, open};
use primitives::field::{F64, F192};
use primitives::hash::hash as keccak256;

fn vector(name: &str, claim: &PcsClaim, proof: &fiat_shamir::transcript::Proof) -> String {
    let n = claim.n as usize;
    let mut out = format!("vector {name}\n");
    out += &line("n", [n as u64]);
    out += &line("claimbytes", claim.encode().iter().map(|&b| b as u64));
    out += &line("payload", claim.hash().iter().map(|&b| b as u64));
    out += &line("root", words(&claim.root));
    out += &line("ood", limbs(&claim.ood));
    out += &line("point", claim.point.iter().flat_map(limbs));
    out += &line("value", limbs(&claim.value));
    out += &line("oodpoint", ood_point(n, &claim.root).iter().flat_map(limbs));
    out + &opening(claim, proof) + "end\n"
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
        let committed = commit(words, false);
        let point: Vec<F192> = (0..n as u8)
            .map(|j| {
                let digest = keccak256(&[b"leanPCS-lean-point".as_slice(), &[n as u8], &[j]].concat());
                element_of(digest[8..].try_into().expect("24 bytes"))
            })
            .collect();
        let claim = committed.claim_at(point);
        let proof = open(committed.words(), &committed, &claim, Codeword::Free);
        out += &vector(&format!("n{n}"), &claim, &proof);
    }
    print!("{out}");
}
