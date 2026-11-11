// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The test vectors for `formal/WhirBridge`, in the form leanerVM mumbai's Lean verifier reads (the scalar stream,
//! then one full Merkle path per query: the pruned batches expanded, as `Transcript::finish` returns them), of the
//! EIP's PCS claims (`pcs_claim`, version 1: the IV `keccak256(PCS_claim)`, a zero public digest, the root as the
//! stream's first two scalars, one opening of `f(z) = ood` and `f(point) = value`):
//!
//! * `public`: an opening of a pseudo-random table of `2^15` words;
//! * `witness`, `wiring`, `copy`: the three openings of a membership proof on a circuit of `2^17` rows, by
//!   the real prover.
//!
//! Each vector carries its claim's bytes (`pcsclaim`), from which the Lean recomputes the IV and the out-of-domain
//! point, and the paths `pcs_claim::verify_claim_paths` checks (`pcs_claim::lean::bridge_vector`). Regenerate and check, from the repository root:
//!
//!   cargo test -p quotient --release --test whir_bridge_vector -- --ignored
//!   (cd formal/WhirBridge && lake env lean --run Test/Check.lean ../../target/whir_bridge_vector.txt)
//!
//! The first writes `target/whir_bridge_vector.txt` (or `$WHIR_BRIDGE_VECTOR`).

use pcs_claim::lean::bridge_vector as vector;
use pcs_claim::{Codeword, commit, open as open_claim};
use primitives::field::F64;
use primitives::test_rng::Rng;
use quotient::circuit::{Builder, Src, public_words};
use quotient::opening::Commitment;
use quotient::protocol::{Index, open, prove_with_seed};
use quotient::statement::{Statement, pair};

#[test]
#[ignore = "writes the vectors `formal/WhirBridge` checks; run with --ignored"]
fn whir_bridge_vector() {
    let mut rng = Rng::new(0xB41D);
    let mut out = String::new();

    let table: Vec<F64> = (0..1u64 << 15)
        .map(|k| F64((k + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(17)))
        .collect();
    let committed = commit(table, false);
    let claim = committed.claim_at(rng.ext_vec(15));
    let proof = open_claim(committed.words(), &committed, &claim, Codeword::Free);
    out += &vector("public", &claim, &proof);

    let mut b = Builder::new();
    let x: Vec<Src> = (0..256).map(|_| b.input()).collect();
    let digest = b.keccak256_64(&[&x[..], &x[..]].concat());
    let circuit = b.finish(17, &public_words(&x, &digest));
    let index = Index::new(&circuit);
    let index_committed = index.commit();
    let commitment = Commitment::of(index_committed);
    let y: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
    let statement = Statement { y, root: pair(&y, &y) };
    let inputs: Vec<bool> = (0..256).map(|i| (y[i / 8] >> (i % 8)) & 1 == 1).collect();
    let proved = prove_with_seed(&circuit, &index, &commitment, &statement, &circuit.cells(&inputs), &[7; 32]);
    let openings = open(&proved.tables, &proved.claims, index_committed);
    let claims = proved.claims.pcs_claims(&commitment, &proved.commitments);
    for ((claim, proof), name) in claims.iter().zip(&openings.0).zip(["witness", "wiring", "copy"]) {
        out += &vector(name, claim, proof);
    }
    let path = std::env::var("WHIR_BRIDGE_VECTOR")
        .unwrap_or_else(|_| concat!(env!("CARGO_MANIFEST_DIR"), "/../../../target/whir_bridge_vector.txt").to_string());
    std::fs::write(&path, out).expect("write the vectors");
    println!("wrote {path}");
}
