// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! Test cases for the EIP draft's "PCS claims" section: a polynomial on `n = 15` variables whose word `i` is the low
//! 64 bits of `keccak256("leanPCS-test" || i)` (`i` 8 bytes, big-endian), its commitment (root, out-of-domain point
//! and answer), and a claim at a point whose coordinate `j` is the element the low 24 bytes of
//! `keccak256("leanPCS-point" || j)` encode: the encoded claim, its `keccak256` (the dependency's payload), and
//! whether its opening verifies.
//!
//! `cargo run --release -p pcs_claim --example eip_vectors`

use pcs_claim::{Codeword, PcsClaim, commit, element_bytes, element_of, ood_point, verify, wire_proof};
use primitives::field::F64;
use primitives::hash::hash as keccak256;

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn main() {
    let n = 15usize;
    let words: Vec<F64> = (0..1u64 << n)
        .map(|i| {
            let digest = keccak256(&[b"leanPCS-test".as_slice(), &i.to_be_bytes()].concat());
            F64(u64::from_be_bytes(digest[24..].try_into().unwrap()))
        })
        .collect();
    let committed = commit(words, false);
    let point: Vec<_> = (0..n as u8)
        .map(|j| {
            let digest = keccak256(&[b"leanPCS-point".as_slice(), &[j]].concat());
            element_of(digest[8..].try_into().unwrap())
        })
        .collect();
    let claim: PcsClaim = committed.claim_at(point);
    let bytes = claim.encode();
    println!("n           {n}");
    println!("f_0         {:#018x}", committed.words()[0].0);
    println!("f_1         {:#018x}", committed.words()[1].0);
    println!("root        0x{}", hex(&committed.root));
    println!(
        "ood z_0     0x{}",
        hex(&element_bytes(ood_point(n, &committed.root)[0]))
    );
    println!("ood answer  0x{}", hex(&element_bytes(committed.ood)));
    println!("point_0     0x{}", hex(&element_bytes(claim.point[0])));
    println!("value       0x{}", hex(&element_bytes(claim.value)));
    println!("PCS_claim   ({} bytes) 0x{}", bytes.len(), hex(&bytes));
    println!("keccak256   0x{}", hex(&claim.hash()));
    let proof = wire_proof(&pcs_claim::open(committed.words(), &committed, &claim, Codeword::Free));
    println!("verifies    {}", verify(&bytes, &proof));
    let mut wrong = claim.clone();
    wrong.value += primitives::field::F192::ONE;
    println!("value + 1   verifies {}", verify(&wrong.encode(), &proof));
}
