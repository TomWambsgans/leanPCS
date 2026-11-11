// Part of this repository: adversarial tests (commit 5ff0904), adapted to the selector,
// the index commitment in storage, the checks of the declared PCS claims and the word 1 returned; the test of
// calldata dropping a root's third limb is turned around. MIT OR Apache-2.0; see AGENTS.md.
//! Adversarial tests of the verifier contract and of its checks of the claims its transaction declares, none of
//! which needs a proof: the contract's claims are compared with the Rust verifier's on random and tampered calldata,
//! degenerate proofs are built from the transcript, the bytecode is walked for its stack, jumps and gas, and the
//! frame of PCS claims is made of other kinds.

use std::collections::BTreeMap;

use primitives::field::F192;
use primitives::test_rng::Rng;
use quotient::opening::Commitment;
use quotient::protocol::{VerifyError, verify};
use quotient::statement::Statement;
use quotient::transcript::{Proof, ProverChain, TranscriptError, root_halves, halves_root};
use revm::primitives::Address;

use crate::machine::{Chain, DEP_VERIFY_FRAME_MODE, FIELD_MUL, FIELD_MUL_GAS, Frame, Outcome, PcsFrame, root_word};
use crate::quotient::{
    CALLDATA_LEN, Contract, INPUTS, PCS_FRAME, VERIFIED, VERIFY, calldata, claims_contract, contract, decode, pcs_claims,
};

/// The sizes of circuit the contract takes.
const LOG_ROWS: std::ops::RangeInclusive<usize> = quotient::protocol::MIN_LOG_ROWS..=quotient::protocol::MAX_LOG_ROWS;
/// The selector, then the statement, the two roots and the proof's other scalars; then the index of the frame of
/// PCS claims.
const ARGS_LEN: usize = CALLDATA_LEN - 1;

/// Calldata as the statement and proof it stands for: the inverse of [`calldata`].
fn parse(data: &[u8]) -> (Statement, Proof) {
    assert_eq!(data.len(), CALLDATA_LEN);
    let data = &data[4..ARGS_LEN];
    let word = |at: usize| u64::from_be_bytes(data[at..at + 8].try_into().unwrap());
    let scalar = |i: usize| {
        let at = 128 + 24 * i;
        F192::new(word(at + 16), word(at + 8), word(at))
    };
    let mut stream = vec![];
    for k in 0..2 {
        let root: [u8; 32] = data[64 + 32 * k..96 + 32 * k].try_into().unwrap();
        stream.extend(root_halves(&root));
        stream.push(scalar(k));
    }
    stream.extend((2..INPUTS).map(scalar));
    let statement = Statement {
        y: data[..32].try_into().unwrap(),
        root: data[32..64].try_into().unwrap(),
    };
    (statement, Proof { stream })
}

fn random_index(rng: &mut Rng) -> Commitment {
    Commitment {
        root: random_bytes(rng),
        ood: rng.ext(),
    }
}

fn random_bytes<const N: usize>(rng: &mut Rng) -> [u8; N] {
    std::array::from_fn(|_| rng.next_u8())
}

/// The selector of `verify`, random arguments, and the frame [`PCS_FRAME`].
fn random_calldata(rng: &mut Rng) -> Vec<u8> {
    VERIFY
        .iter()
        .copied()
        .chain((4..ARGS_LEN).map(|_| rng.next_u8()))
        .chain([PCS_FRAME])
        .collect()
}

/// Calldata the Rust verifier rejects as degenerate: the copy identity's denominator `d · d' + w_m` is zero, which
/// the prover controls through `next`, sent after `t`.
fn degenerate(index: &Commitment, log_rows: usize, rng: &mut Rng) -> Vec<u8> {
    let statement = Statement {
        y: random_bytes(rng),
        root: random_bytes(rng),
    };
    let mut chain = ProverChain::new(&quotient::protocol::label(index, &statement));
    chain.send_root(&random_bytes(rng));
    chain.send(rng.ext());
    let (alpha, beta) = (chain.sample(), chain.sample());
    let _mu = chain.sample();
    chain.send_root(&random_bytes(rng));
    chain.send(rng.ext());
    let t = chain.sample();
    let a: [F192; 4] = std::array::from_fn(|_| rng.ext());
    a.iter().for_each(|&x| chain.send(x));
    let m = log_rows + 2;
    let mut w = vec![t];
    for k in 0..m {
        w.push(w[k] * w[k] + w[k]);
    }
    let x = a[0] + t * a[1] + w[1] * (a[2] + t * a[3]);
    let d = alpha + x + beta * t;
    let next = (w[m] * d.inv() + alpha + x) * beta.inv();
    chain.send(next);
    let _rho = chain.sample();
    calldata(&statement, &chain.into_proof()).expect("roots of 128 bits")
}

/// The frame declaring the claims the Rust verifier leaves on `data`, if it leaves any.
fn block_for(index: &Commitment, data: &[u8], log_rows: usize) -> PcsFrame {
    let (statement, proof) = parse(data);
    let mut block = PcsFrame::default();
    if let Ok((commitments, claims)) = verify(index, &statement, &proof, log_rows) {
        pcs_claims(index, &commitments, &claims).iter().for_each(|claim| block.declare(claim));
    }
    block
}

/// A contract deployed for the circuit committed as `index_root`, with no owner, on a chain of its own.
struct Deployed {
    chain: Chain,
    address: Address,
}

fn deploy(contract: &Contract, index: &Commitment) -> Deployed {
    let mut chain = Chain::default();
    let address = crate::quotient::deploy(&mut chain, contract, index, Address::ZERO)
        .0
        .expect("a deployment");
    Deployed { chain, address }
}

/// A call of the contract, in a transaction whose frame of PCS claims is `block`.
fn call(deployed: &Deployed, data: &[u8], block: &PcsFrame) -> Outcome {
    deployed.chain.call(deployed.address, data, block)
}

/// The verifiers on one calldata, each check one assertion: the claims contract returns what `verify` leaves; the
/// contract succeeds, returning the word 1, against a frame declaring those claims exactly when `verify` accepts,
/// and fails against `other`, a frame of other claims.
fn agree(index: &Commitment, log_rows: usize, codes: &(Deployed, Deployed), data: &[u8], other: &PcsFrame) -> bool {
    let (statement, proof) = parse(data);
    let expected = verify(index, &statement, &proof, log_rows);
    assert_ne!(
        expected.as_ref().err(),
        Some(&VerifyError::Transcript(TranscriptError::NotARoot))
    );
    let returned = call(&codes.0, data, &PcsFrame::default()).output;
    assert_eq!(
        returned.as_deref().and_then(|output| decode(output, log_rows)),
        expected.clone().ok(),
        "claims contract, {data:02x?}"
    );
    let own = call(&codes.1, data, &block_for(index, data, log_rows)).output;
    assert_eq!(
        own,
        expected.is_ok().then(|| VERIFIED.to_vec()),
        "contract, {data:02x?}"
    );
    assert_eq!(
        call(&codes.1, data, other).output,
        None,
        "foreign openings, {data:02x?}"
    );
    expected.is_ok()
}

/// The claims contract and the contract, deployed for `index_root`.
fn codes(index: &Commitment, log_rows: usize) -> (Deployed, Deployed) {
    (
        deploy(&claims_contract(log_rows), index),
        deploy(&contract(log_rows), index),
    )
}

/// Random calldata, at every size of circuit the block knows, with random and extreme index roots.
#[test]
fn random_calldata_agrees() {
    let mut rng = Rng::new(0xADD);
    for log_rows in LOG_ROWS {
        let extreme = |byte: u8, rng: &mut Rng| Commitment {
            root: [byte; 32],
            ood: if byte == 0 { F192::ZERO } else { rng.ext() },
        };
        for index in [extreme(0, &mut rng), extreme(0xff, &mut rng), random_index(&mut rng)] {
            let codes = codes(&index, log_rows);
            let mut extremes: Vec<Vec<u8>> = [0u8, 0xff, 0x80, 0x01]
                .iter()
                .map(|&b| [&VERIFY[..], &[b; ARGS_LEN - 4], &[PCS_FRAME]].concat())
                .collect();
            // Roots of all ones, scalars of all zeros, and the reverse.
            let mut mixed = vec![0xff; 192];
            mixed.resize(ARGS_LEN - 4, 0);
            extremes.push([&VERIFY[..], &mixed.iter().map(|b| !b).collect::<Vec<_>>(), &[PCS_FRAME]].concat());
            extremes.push([&VERIFY[..], &mixed, &[PCS_FRAME]].concat());
            let other = block_for(&index, &random_calldata(&mut rng), log_rows);
            let samples = extremes.into_iter().chain((0..200).map(|_| random_calldata(&mut rng)));
            for data in samples {
                assert!(agree(&index, log_rows, &codes, &data, &other));
            }
        }
    }
}

/// Every single-bit change of a calldata, at the smallest and the largest circuit: the verifiers agree on every
/// change of the arguments, the original's claims never pass the changed calldata, and every change of the selector
/// reverts, as does every change of the frame's index (the transaction has no such frame).
#[test]
fn bit_flips_agree() {
    let mut rng = Rng::new(0xF11);
    for log_rows in [*LOG_ROWS.start(), *LOG_ROWS.end()] {
        let index = random_index(&mut rng);
        let codes = codes(&index, log_rows);
        let base = random_calldata(&mut rng);
        let honest = block_for(&index, &base, log_rows);
        assert_eq!(call(&codes.1, &base, &honest).output, Some(VERIFIED.to_vec()));
        for bit in 0..8 * CALLDATA_LEN {
            let mut data = base.clone();
            data[bit / 8] ^= 1 << (bit % 8);
            if bit < 32 {
                assert_eq!(call(&codes.0, &data, &PcsFrame::default()).output, None, "bit {bit}");
                assert_eq!(call(&codes.1, &data, &honest).output, None, "bit {bit}");
                assert_eq!(call(&codes.1, &data, &PcsFrame::declaring_all()).output, None, "bit {bit}");
            } else if bit >= 8 * ARGS_LEN {
                assert_eq!(call(&codes.1, &data, &honest).output, None, "bit {bit}");
                assert_eq!(call(&codes.1, &data, &PcsFrame::declaring_all()).output, None, "bit {bit}");
            } else {
                assert!(agree(&index, log_rows, &codes, &data, &honest), "bit {bit}");
            }
        }
    }
}

/// The one rejection a prover can reach without grinding a hash: both contracts revert where the Rust verifier
/// finds a zero denominator, the calling one even when its frame declares everything; one bit off, all accept.
/// No other test reaches the contract's nonzero check: with it compiled out (`ISZERO` and its jump replaced by a
/// `POP`), every other test of the crate passes.
#[test]
fn degenerate_proofs_revert() {
    let mut rng = Rng::new(0xDE6);
    for log_rows in [*LOG_ROWS.start(), 20, *LOG_ROWS.end()] {
        let index = random_index(&mut rng);
        let codes = codes(&index, log_rows);
        let other = PcsFrame::default();
        for _ in 0..8 {
            let data = degenerate(&index, log_rows, &mut rng);
            let (statement, proof) = parse(&data);
            assert_eq!(
                verify(&index, &statement, &proof, log_rows).err(),
                Some(VerifyError::Degenerate)
            );
            assert!(!agree(&index, log_rows, &codes, &data, &other));
            assert_eq!(call(&codes.1, &data, &PcsFrame::declaring_all()).output, None);
            let mut near = data.clone();
            // `next`'s last byte: the scalar the prover chose to make the denominator vanish.
            near[4 + 128 + 24 * 6 + 23] ^= 1;
            assert!(agree(&index, log_rows, &codes, &near, &other));
            assert_eq!(
                call(&codes.1, &near, &PcsFrame::declaring_all()).output,
                Some(VERIFIED.to_vec())
            );
        }
    }
}

/// Calldata of any other length reverts, whatever it holds and whatever its frame declares.
#[test]
fn other_lengths_revert() {
    let mut rng = Rng::new(0x1E2);
    let index = random_index(&mut rng);
    let codes = codes(&index, 22);
    let full = random_calldata(&mut rng);
    for len in (0..=CALLDATA_LEN + 64).filter(|&len| len != CALLDATA_LEN) {
        let mut data = full.clone();
        data.resize(len, 0);
        assert_eq!(call(&codes.0, &data, &PcsFrame::default()).output, None, "{len}");
        assert_eq!(call(&codes.1, &data, &PcsFrame::declaring_all()).output, None, "{len}");
    }
    // Zero bytes past the end are not the same calldata: the size is checked, not the bytes read.
    let mut long = full.clone();
    long.extend([0; 8]);
    assert_eq!(call(&codes.1, &long, &PcsFrame::declaring_all()).output, None);
}

/// A commitment's word in calldata is the word a claim encodes for its root, and roots and words correspond one
/// to one.
#[test]
fn root_words_are_the_calldata_words() {
    let mut rng = Rng::new(0x5007);
    for _ in 0..1000 {
        let data = random_calldata(&mut rng);
        let (_, proof) = parse(&data);
        assert_eq!(calldata(&parse(&data).0, &proof), Ok(data.clone()));
        for (i, at) in [(0, 68), (3, 100)] {
            let root = halves_root(&[proof.stream[i], proof.stream[i + 1]]).unwrap();
            assert_eq!(root_word(&root)[..], data[at..at + 32]);
            assert_eq!(root_halves(&root), [proof.stream[i], proof.stream[i + 1]]);
        }
    }
}

/// A proof the Rust verifier rejects for a commitment scalar wider than 128 bits (`NotARoot`) has no calldata:
/// `calldata` refuses it rather than drop the third limb, which would make it calldata the contract accepts. A
/// proof scalar's third limb is kept.
#[test]
fn calldata_of_a_proof_that_is_not_a_root() {
    let mut rng = Rng::new(0x2007);
    let index = random_index(&mut rng);
    let data = random_calldata(&mut rng);
    let (statement, proof) = parse(&data);
    for at in [0, 1, 3, 4] {
        let mut wide = proof.clone();
        wide.stream[at].c2 = 1;
        assert_eq!(
            verify(&index, &statement, &wide, 22).err(),
            Some(VerifyError::Transcript(TranscriptError::NotARoot))
        );
        assert_eq!(calldata(&statement, &wide), Err(TranscriptError::NotARoot), "{at}");
    }
    let mut wide = proof.clone();
    wide.stream[2].c2 ^= 1;
    assert_ne!(calldata(&statement, &wide).expect("a proof scalar's 192 bits"), data);
}

/// The contract takes its claims as declared only in the frame calldata names, if it is a dependency verification
/// frame of PCS claims holding their hashes as payloads `0 .. 3`, in order: the frame after another one, named so,
/// passes; a frame of another mode, of the leanSPHINCS scheme (whose message hashes its sender chooses), or of no
/// scheme, a frame the transaction does not have, the claims in another order, one left out or one more first, all
/// revert.
#[test]
fn only_a_frame_of_pcs_claims_passes() {
    let mut rng = Rng::new(0x0DA7A);
    let index = random_index(&mut rng);
    let deployed = deploy(&contract(22), &index);
    let data = random_calldata(&mut rng);
    let honest = block_for(&index, &data, 22);
    let claims = honest.claims().to_vec();
    assert_eq!(claims.len(), 4);
    let passes = |data: &[u8], block: &PcsFrame| {
        let outcome = call(&deployed, data, block);
        assert!(outcome.output.as_ref().is_none_or(|output| *output == VERIFIED));
        outcome.output.is_some()
    };
    assert!(passes(&data, &honest));
    // After another frame, as calldata names it.
    let mut second = honest.clone();
    second.before.push(Frame {
        mode: 0,
        data: honest.data(),
    });
    let mut named = data.clone();
    *named.last_mut().unwrap() = 1;
    assert!(passes(&named, &second));
    assert!(!passes(&data, &second), "the frame before it is not of PCS claims");
    assert!(!passes(&named, &honest), "the transaction has no second frame");
    // Other kinds of frames.
    for (mode, scheme) in [(0, 0x12), (DEP_VERIFY_FRAME_MODE, 0x10), (DEP_VERIFY_FRAME_MODE, 0x00)] {
        let mut other = honest.clone();
        (other.mode, other.scheme) = (mode, scheme);
        assert!(!passes(&data, &other), "mode {mode}, scheme {scheme:#04x}");
        other.declare_all = true;
        assert!(!passes(&data, &other), "mode {mode}, scheme {scheme:#04x}, declaring all");
    }
    // Other payloads.
    let frame = |claims: &[Vec<u8>]| {
        let mut block = PcsFrame::default();
        claims.iter().for_each(|claim| block.declare_input(claim.clone()));
        block
    };
    let reversed: Vec<Vec<u8>> = claims.iter().rev().cloned().collect();
    assert!(!passes(&data, &frame(&reversed)));
    assert!(!passes(&data, &frame(&claims[..3])));
    assert!(!passes(&data, &frame(&[vec![vec![0; 32]], claims.clone()].concat())));
    assert!(passes(&data, &frame(&[claims.clone(), vec![vec![1]]].concat())), "a fifth claim, unread");
}

/// The claims the contract checks are, byte for byte, the Rust verifier's, in order: no more, no other bytes. The
/// wiring table's is against the commitment in storage.
#[test]
fn claims_are_the_rust_openings() {
    let mut rng = Rng::new(0x1A9);
    for log_rows in LOG_ROWS {
        let index = random_index(&mut rng);
        let deployed = deploy(&contract(log_rows), &index);
        for _ in 0..20 {
            let data = random_calldata(&mut rng);
            let (statement, proof) = parse(&data);
            let (commitments, claims) = verify(&index, &statement, &proof, log_rows).expect("a reduction");
            let expected: Vec<Vec<u8>> =
                pcs_claims(&index, &commitments, &claims).iter().map(|claim| claim.encode()).collect();
            let outcome = call(&deployed, &data, &PcsFrame::declaring_all());
            assert_eq!(outcome.output, Some(VERIFIED.to_vec()));
            assert_eq!(outcome.claims, expected);
        }
    }
}

/// What a walk of the straight-line path finds.
#[derive(Debug, Default)]
struct Walk {
    /// Execution gas by opcode, its dynamic part (words copied or hashed, memory) included.
    gas: BTreeMap<&'static str, u64>,
    max_stack: usize,
    memory_words: u64,
    /// `(offset, size)` of each claim checked: what the last `KECCAK256` before a payload's `FRAMEDATALOAD` hashed.
    calls: Vec<(u64, u64)>,
    hashed: Option<(u64, u64)>,
    /// Where each `JUMPI` would go.
    jumps: Vec<u64>,
    end: usize,
}

fn memory_cost(words: u64) -> u64 {
    3 * words + words * words / 512
}

/// Walk `code` from its start to its `STOP` or `RETURN`, no jump taken, pricing each instruction as Cancun (and
/// Prague, Osaka) does, with the first `SLOAD` of a slot cold, and EIP-8141's `FRAMEPARAM` and `FRAMEDATALOAD`. Offsets and sizes must
/// be pushed constants.
fn walk(code: &[u8]) -> Walk {
    let mut walk = Walk::default();
    let mut stack: Vec<Option<u64>> = vec![];
    let mut loaded = vec![];
    let mut pc = 0;
    let pop = |stack: &mut Vec<Option<u64>>| stack.pop().expect("no underflow");
    let expand = |walk: &mut Walk, offset: Option<u64>, size: Option<u64>| -> u64 {
        let size = size.expect("a constant size");
        if size == 0 {
            return 0;
        }
        let words = (offset.expect("a constant offset") + size).div_ceil(32);
        if words <= walk.memory_words {
            return 0;
        }
        let cost = memory_cost(words) - memory_cost(walk.memory_words);
        walk.memory_words = words;
        cost
    };
    loop {
        let op = code[pc];
        let (name, cost): (&'static str, u64) = match op {
            0x5f => {
                stack.push(Some(0));
                ("PUSH", 2)
            }
            0x60..=0x7f => {
                let n = (op - 0x5f) as usize;
                let bytes = &code[pc + 1..pc + 1 + n];
                let value = (n <= 8).then(|| bytes.iter().fold(0u64, |acc, &b| acc << 8 | b as u64));
                stack.push(value);
                pc += n;
                ("PUSH", 3)
            }
            0x80 => {
                let top = *stack.last().unwrap();
                stack.push(top);
                ("DUP", 3)
            }
            0x81 => {
                let second = stack[stack.len() - 2];
                stack.push(second);
                ("DUP", 3)
            }
            0x90 | 0x91 => {
                let len = stack.len();
                stack.swap(len - 1, len - 2 - (op - 0x90) as usize);
                ("SWAP", 3)
            }
            FIELD_MUL => {
                pop(&mut stack);
                pop(&mut stack);
                stack.push(None);
                ("FIELD_MUL", FIELD_MUL_GAS)
            }
            0x16..=0x18 | 0x1b | 0x1c => {
                pop(&mut stack);
                pop(&mut stack);
                stack.push(None);
                ("logic", 3)
            }
            0x15 | 0x35 => {
                pop(&mut stack);
                stack.push(None);
                (if op == 0x15 { "ISZERO" } else { "CALLDATALOAD" }, 3)
            }
            0x34 | 0x36 | 0x3d | 0x5a => {
                stack.push(None);
                ("env", 2)
            }
            0x50 => {
                pop(&mut stack);
                ("POP", 2)
            }
            0x51 => {
                let offset = pop(&mut stack);
                let cost = 3 + expand(&mut walk, offset, Some(32));
                stack.push(None);
                ("MLOAD", cost)
            }
            0x52 => {
                let offset = pop(&mut stack);
                pop(&mut stack);
                ("MSTORE", 3 + expand(&mut walk, offset, Some(32)))
            }
            0x54 => {
                let slot = pop(&mut stack).expect("a constant slot");
                let cold = !loaded.contains(&slot);
                loaded.push(slot);
                stack.push(None);
                ("SLOAD", if cold { 2_100 } else { 100 })
            }
            0x20 => {
                let (offset, size) = (pop(&mut stack), pop(&mut stack));
                let cost = 30 + 6 * size.unwrap().div_ceil(32) + expand(&mut walk, offset, size);
                walk.hashed = Some((offset.unwrap(), size.unwrap()));
                stack.push(None);
                ("KECCAK256", cost)
            }
            0x37 | 0x39 => {
                let (dest, _, size) = (pop(&mut stack), pop(&mut stack), pop(&mut stack));
                let cost = 3 + 3 * size.unwrap().div_ceil(32) + expand(&mut walk, dest, size);
                (if op == 0x37 { "CALLDATACOPY" } else { "CODECOPY" }, cost)
            }
            0x57 => {
                let dest = pop(&mut stack).expect("a pushed destination");
                pop(&mut stack);
                walk.jumps.push(dest);
                ("JUMPI", 10)
            }
            0xb3 => {
                pop(&mut stack);
                pop(&mut stack);
                stack.push(None);
                ("FRAMEPARAM", 2)
            }
            0xb1 => {
                let offset = pop(&mut stack).expect("a constant offset");
                pop(&mut stack);
                if offset >= 1 {
                    walk.calls.push(walk.hashed.expect("a claim hashed"));
                }
                stack.push(None);
                ("FRAMEDATALOAD", 3)
            }
            0x00 => {
                walk.end = pc;
                return walk;
            }
            0xf3 => {
                let (offset, size) = (pop(&mut stack), pop(&mut stack));
                let cost = expand(&mut walk, offset, size);
                *walk.gas.entry("RETURN").or_default() += cost;
                walk.end = pc;
                return walk;
            }
            _ => panic!("opcode {op:#04x} at {pc}"),
        };
        *walk.gas.entry(name).or_default() += cost;
        walk.max_stack = walk.max_stack.max(stack.len());
        pc += 1;
    }
}

/// Where instructions start, as a jump's analysis finds them.
fn boundaries(code: &[u8]) -> Vec<bool> {
    let mut starts = vec![false; code.len()];
    let mut pc = 0;
    while pc < code.len() {
        starts[pc] = true;
        pc += 1 + if (0x60..=0x7f).contains(&code[pc]) {
            (code[pc] - 0x5f) as usize
        } else {
            0
        };
    }
    starts
}

/// The code's straight line: a stack far from its limit, its first jump to `setIndexRoot` right after it and
/// every other one to the one revert, after that, deployable size, and the gas revm charges equal to an
/// independent pricing of each instruction. Prints both contracts' gas by opcode:
/// `cargo test --release -p evm -- --nocapture gas_by_opcode`.
#[test]
fn gas_by_opcode() {
    let mut rng = Rng::new(0x6A5);
    for log_rows in LOG_ROWS {
        let index = random_index(&mut rng);
        let returning = claims_contract(log_rows);
        let calling = contract(log_rows);
        let data = random_calldata(&mut rng);
        let block = block_for(&index, &data, log_rows);
        let mut totals = vec![];
        for (name, compiled, block) in [
            ("returning", &returning, PcsFrame::default()),
            ("checking", &calling, block),
        ] {
            let code = &compiled.code;
            let walk = walk(code);
            assert!(walk.max_stack <= 1024);
            assert_eq!(walk.memory_words as usize, compiled.memory_words);
            let starts = boundaries(code);
            let (&entry, fails) = walk.jumps.split_first().unwrap();
            let entry = entry as usize;
            assert_eq!(entry, walk.end + 1);
            assert!(starts[entry] && code[entry] == 0x5b);
            let revert = fails[0] as usize;
            assert!(fails.iter().all(|&at| at as usize == revert));
            assert!(revert > entry && starts[revert]);
            assert_eq!(&code[revert..revert + 4], &[0x5b, 0x5f, 0x5f, 0xfd]);
            // `setIndexCommitment`'s one jump is to the revert too.
            let to_revert = [0x61, (revert >> 8) as u8, revert as u8, 0x57];
            assert!(code[entry..revert].windows(4).any(|window| window == to_revert));
            let outcome = call(&deploy(compiled, &index), &data, &block);
            assert!(outcome.output.is_some());
            let total: u64 = walk.gas.values().sum();
            assert_eq!(total, outcome.execution, "{name}, 2^{log_rows} rows");
            totals.push(total);
            if log_rows == 22 {
                println!(
                    "{name}: {} bytes of code (EIP-170: 24576), stack at most {}, memory {} words, gas {total}",
                    code.len(),
                    walk.max_stack,
                    walk.memory_words
                );
                println!("  {:?}", walk.gas);
                println!("  claims (offset, size): {:?}", walk.calls);
            }
            assert!(code.len() <= 24_576, "{name}: {} bytes", code.len());
        }
        // The claims hashed are the EIP's encoding, `82 + 24 n` bytes: the witness table's and the wiring table's in
        // `m` variables, the quotient table's two in `m + 4`.
        let sizes: Vec<u64> = walk(&calling.code).calls.iter().map(|&(_, size)| size).collect();
        let vars = quotient::protocol::table_vars(log_rows);
        let expected: Vec<u64> = [0, 1, 2, 2].iter().map(|&k| 82 + 24 * vars[k] as u64).collect();
        assert_eq!(sizes, expected);
        if log_rows == 22 {
            println!("difference: {}", totals[1] - totals[0]);
        }
    }
}
