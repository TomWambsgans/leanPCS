// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! `evm_link`'s check of a declared PCS claim ([`evm_link::Item::DeclaredClaim`]) on revm, with the mock frame of
//! PCS claims of `leanvm_statement::evm::machine`: the bytes the contract packs and hashes are
//! [`pcs_claim::PcsClaim::encode`]'s, the claim declared passes, any other revert; and its gas.

use evm_link::op::{self, push_usize};
use evm_link::{ClaimWords, Ending, Item, Options, Program, assemble, declared_claims};
use leanvm_statement::evm::machine::{self, PcsFrame};
use pcs_claim::{PcsClaim, element_bytes};
use primitives::field::F192;
use primitives::test_rng::Rng;

const TAG: &str = "test";

fn word(x: F192) -> [u8; 32] {
    op::word([x.c0, x.c1, x.c2])
}

fn claim(rng: &mut Rng, n: usize, seed: u8) -> PcsClaim {
    PcsClaim {
        n: n as u8,
        root: std::array::from_fn(|i| (i as u8).wrapping_mul(37) ^ seed),
        ood: rng.ext(),
        point: rng.ext_vec(n),
        value: rng.ext(),
    }
}

/// A contract whose outputs are these claims' words (copied from its code: root, ood, point, value, claim after
/// claim), and that checks each declared as payload `0, 1, ...` of the frame the last calldata byte names.
fn contract(claims: &[PcsClaim]) -> Vec<u8> {
    contract_checking(claims, claims.len())
}

/// [`contract`], checking only the first `checked` claims (the others' words are copied all the same).
fn contract_checking(claims: &[PcsClaim], checked: usize) -> Vec<u8> {
    let mut data = Vec::new();
    let mut words = Vec::new();
    for (index, c) in claims.iter().enumerate() {
        let first = data.len() / 32;
        data.extend(c.root);
        for &x in [&c.ood].into_iter().chain(&c.point).chain([&c.value]) {
            data.extend(word(x));
        }
        let n = c.point.len();
        words.push(ClaimWords {
            root: first,
            ood: first + 1,
            point: (first + 2..first + 2 + n).collect(),
            value: first + 2 + n,
            index,
        });
    }
    let outputs = data.len() / 32;
    let calldata_len = 1;
    let mut items = vec![(
        Item::CopyConst {
            first: 0,
            words: outputs,
            data: 0,
        },
        TAG,
    )];
    items.extend(
        declared_claims(calldata_len, &words[..checked])
            .into_iter()
            .map(|item| (item, TAG)),
    );
    let program = Program {
        items,
        data,
        scratch: 0,
        outputs,
        ending: Ending::Attest,
        calldata_len,
    };
    assemble(&program, &Options::default()).code
}

fn run(code: &[u8], frame: &PcsFrame) -> machine::Outcome {
    machine::call(code, &[], &[machine::PCS_FRAME], frame)
}

fn attests(outcome: &machine::Outcome) -> bool {
    let mut one = [0u8; 32];
    one[31] = 1;
    outcome.output.as_deref() == Some(&one[..])
}

#[test]
fn a_declared_claim_is_packed_as_encoded_and_passes() {
    let mut rng = Rng::new(11);
    for n in [1usize, 15, 22, 28, 32] {
        let c = claim(&mut rng, n, n as u8);
        let code = contract(std::slice::from_ref(&c));
        let mut frame = PcsFrame::default();
        frame.declare(c.encode());
        let outcome = run(&code, &frame);
        assert!(attests(&outcome), "n = {n}");
        // What the contract hashed before reading the payload: the claim's encoding, byte for byte.
        assert_eq!(outcome.claims, vec![c.encode()], "n = {n}");
        assert_eq!(pcs_claim::claim_len(n), c.encode().len());
    }
}

#[test]
fn another_claim_or_frame_reverts() {
    let mut rng = Rng::new(12);
    let c = claim(&mut rng, 20, 1);
    let code = contract(std::slice::from_ref(&c));
    // Another value, another root byte, another n's encoding of the same words: not declared.
    let mut other = c.clone();
    other.value += F192::ONE;
    let mut frame = PcsFrame::default();
    frame.declare(other.encode());
    assert!(!attests(&run(&code, &frame)));
    let mut other = c.clone();
    other.root[31] ^= 1;
    let mut frame = PcsFrame::default();
    frame.declare(other.encode());
    assert!(!attests(&run(&code, &frame)));
    // No claim declared, the frame of another mode or scheme.
    assert!(!attests(&run(&code, &PcsFrame::default())));
    for (mode, scheme) in [(0u8, op::PCS_SCHEME), (op::DEP_VERIFY_FRAME_MODE, 0x10)] {
        let mut frame = PcsFrame::default();
        frame.declare(c.encode());
        frame.mode = mode;
        frame.scheme = scheme;
        assert!(!attests(&run(&code, &frame)), "mode {mode}, scheme {scheme:#x}");
    }
}

#[test]
fn claims_are_checked_as_payloads_in_order() {
    let mut rng = Rng::new(13);
    let claims: Vec<PcsClaim> = (0..3).map(|k| claim(&mut rng, 16 + k, k as u8)).collect();
    let code = contract(&claims);
    let mut frame = PcsFrame::default();
    claims.iter().for_each(|c| frame.declare(c.encode()));
    let outcome = run(&code, &frame);
    assert!(attests(&outcome));
    assert_eq!(outcome.claims, claims.iter().map(PcsClaim::encode).collect::<Vec<_>>());
    // Swapped payloads: the first check fails.
    let mut frame = PcsFrame::default();
    [1, 0, 2].iter().for_each(|&k| frame.declare(claims[k].encode()));
    assert!(!attests(&run(&code, &frame)));
}

/// The 24 bytes of an element are the low 24 of its word: the packing drops exactly the top 8 zero bytes.
#[test]
fn elements_land_their_low_24_bytes() {
    let x = F192::new(u64::MAX, 0x0123_4567_89ab_cdef, 1);
    assert_eq!(&word(x)[8..], &element_bytes(x));
}

/// `op::reverse_halves` maps a root word (`machine::root_word`) to the root's bytes, and back.
#[test]
fn reverse_halves_is_the_root_word_involution() {
    let root: [u8; 32] = std::array::from_fn(|i| (i as u8) * 7 + 1);
    let root_word = machine::root_word(&root);
    // PUSH32 the root word, reverse its halves, return it.
    let code = [
        &[op::PUSH32][..],
        &root_word,
        &op::reverse_halves(),
        &[op::PUSH0, op::MSTORE],
        &push_usize(32),
        &[op::PUSH0, op::RETURN],
    ]
    .concat();
    let outcome = machine::call(&code, &[], &[], &PcsFrame::default());
    assert_eq!(outcome.output.as_deref(), Some(&root[..]));
}

/// The gas of checking one declared claim, by `n`: the frame check is paid once; each claim its packing, its
/// `KECCAK256` and its payload's read.
#[test]
#[ignore]
fn gas_per_claim() {
    let mut rng = Rng::new(14);
    println!("{:>4} {:>8} {:>12}", "n", "bytes", "gas a claim");
    for n in [15usize, 20, 22, 24, 28] {
        let one = claim(&mut rng, n, 1);
        let two = claim(&mut rng, n, 2);
        let claims = [one, two];
        let gas = |checked: usize| {
            let mut frame = PcsFrame::default();
            claims[..checked].iter().for_each(|c| frame.declare(c.encode()));
            let outcome = run(&contract_checking(&claims, checked), &frame);
            assert!(attests(&outcome));
            outcome.execution
        };
        // The second claim's check alone: the same outputs, one claim checked or two.
        println!("{n:>4} {:>8} {:>12}", pcs_claim::claim_len(n), gas(2) - gas(1));
    }
}
