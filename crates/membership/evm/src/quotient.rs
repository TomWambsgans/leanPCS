// Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
// file crates/membership/evm/src/quotient.rs; new here: the checks of the declared claims, the selector, the index commitment in
// storage, its deployment and `setIndexCommitment`. MIT OR Apache-2.0; see AGENTS.md.
//! The membership verifier (`quotient::protocol::reduce`) as a contract, its ABI, and its deployment.
//!
//! The contract ([`contract`]) checks that its transaction declares the six PCS claims a proof leaves
//! ([`pcs_claims`]: the EIP's encoding, `crates/pcs_claim`) in its frame of PCS claims ([`crate::machine`]), and
//! returns the word 1; without the checks ([`claims_contract`]), it returns the commitments and the claims. Its code
//! depends on the circuit's size alone: the circuit's commitment (its index table's root and out-of-domain answer)
//! is in storage, where its owner can change it.
//!
//! # ABI
//!
//! **`verify(bytes32 y, bytes32 root, bytes proof)`**, selector [`VERIFY`] (`0xde12c640`), its arguments
//! **packed**, not ABI-encoded, then the index of the transaction's frame of PCS claims: calldata is exactly
//! [`CALLDATA_LEN`] (461) bytes,
//!
//! | bytes      | what                                                                                          |
//! |------------|-----------------------------------------------------------------------------------------------|
//! | `0..4`     | `0xde12c640`                                                                                  |
//! | `4..36`    | `y`                                                                                           |
//! | `36..68`   | `root`                                                                                        |
//! | `68..196`  | the roots of the witness table's commitment and of the quotient table's parts `H`, `Q`, `G` |
//! | `196..460` | the proof's eleven other scalars, 24 bytes each, big-endian: the four out-of-domain answers, the four `a_j`, `next`, `Q`'s and `G`'s values |
//! | `460`      | the index of the transaction's frame of PCS claims                                            |
//!
//! `proof` is bytes `68..460`, as [`calldata`] writes them. The contract reverts on calldata of another length or
//! selector, on value, and on a proof the verifier rejects or whose claims the transaction does not declare (the
//! frame byte 460 names must be a dependency verification frame of PCS claims, and its payloads `0 .. 5` the hashes
//! of the six claims, in order); otherwise it returns [`VERIFIED`], the word 1, as `abi.encode(true)`. It writes
//! nothing, so a `STATICCALL` will do:
//!
//! ```solidity
//! (bool ok, bytes memory ret) = verifier.staticcall(abi.encodePacked(bytes4(0xde12c640), y, root, proof, frame));
//! require(ok && ret.length == 32 && abi.decode(ret, (bool)));
//! ```
//!
//! **`setIndexCommitment(bytes32 indexRoot, bytes32 indexOod)`**, selector [`SET_INDEX`], ABI-encoded (68 bytes):
//! from the owner, with no value, it stores the circuit's commitment in slots 0 and 1 and returns nothing; otherwise
//! it reverts. The owner is fixed at deployment; an owner of 0 fixes the commitment for good.
//!
//! **Deployment**: `constructor(bytes32 indexRoot, bytes32 indexOod, address owner)`. The init code ([`init_code`])
//! is the creation code, then the three arguments ABI-encoded (96 bytes); it stores the circuit's commitment (the
//! root as its 32 bytes, the out-of-domain answer as a word) in slots 0 and 1, writes `owner` into the code, and
//! reverts on value or on arguments of another length.

use std::collections::HashMap;

use evm_link::ClaimWords;
use pcs_claim::PcsClaim;
use primitives::field::F192;
use quotient::opening::{Claim, Commitment};
use quotient::protocol::{Claims, Commitments, NAME, Reduced, label, reduce, sum_point};
use quotient::statement::Statement;
use quotient::transcript::{Proof, TranscriptError, halves_root};
use revm::primitives::Address;

use crate::codegen::{COMMITMENT, Ending, Entry, SCALAR_BYTES, SCALARS, Word, compile};
pub use crate::codegen::{Contract, SET_INDEX, VERIFY, creation_code};
use crate::contract::Recorder;
use crate::machine::element_word;
use crate::record::{Graph, Sym, record};

/// What the contract returns on a proof it accepts: the word 1, `abi.encode(true)`.
pub const VERIFIED: [u8; 32] = {
    let mut word = [0; 32];
    word[31] = 1;
    word
};

/// The proof's scalars that are not roots' halves.
pub const INPUTS: usize = 11;

/// The verifying calldata's length: the selector, the statement, four roots, the other scalars, the frame's index.
pub const CALLDATA_LEN: usize = VERIFY.len() + SCALARS + SCALAR_BYTES * INPUTS + 1;

/// Where the stream holds the roots' halves: each commitment's two scalars, then its out-of-domain answer.
const ROOT_SCALARS: [usize; 8] = [0, 1, 3, 4, 6, 7, 9, 10];

/// The contract verifying proofs against the circuit of `2^log_rows` rows whose commitment the deployment stores
/// ([`init_code`]): it reverts unless its transaction declares the six claims a proof leaves ([`pcs_claims`]), and
/// returns [`VERIFIED`].
pub fn contract(log_rows: usize) -> Contract {
    build(log_rows, &entry(), true)
}

/// The same verifier, returning the commitments and the claims ([`decode`]) instead of checking them.
pub fn claims_contract(log_rows: usize) -> Contract {
    build(log_rows, &entry(), false)
}

/// The init code deploying `contract` (either of the two above) for the circuit committed as `index`, owned by
/// `owner`: its creation code, then the constructor's three arguments.
pub fn init_code(contract: &Contract, index: &Commitment, owner: Address) -> Vec<u8> {
    assert!(contract.owner_at.is_some(), "a contract reading its commitment from storage");
    [&creation_code(contract)[..], &index.root, &element_word(index.ood), owner.into_word().as_slice()].concat()
}

/// Deploy `contract` on `chain` for the circuit committed as `index`, owned by `owner`, by a transaction: its
/// address, unless the creation failed, and the transaction's init code and execution gas.
pub fn deploy(
    chain: &mut crate::machine::Chain,
    contract: &Contract,
    index: &Commitment,
    owner: Address,
) -> (Option<Address>, (Vec<u8>, u64)) {
    let init = init_code(contract, index, owner);
    let (address, outcome) = chain.deploy(&init);
    (address, (init, outcome.execution))
}

/// How the contract is entered ([`Entry`]).
fn entry() -> Entry {
    let some = Commitment {
        root: [0xa5; 32],
        ood: F192::new(1, 2, 3),
    };
    let zero = Statement {
        y: [0; 32],
        root: [0; 32],
    };
    let label = label(&some, &zero);
    assert!(
        label.len() == 136 && label[16..48] == some.root && label[48..72] == element_word(some.ood)[8..],
        "the label is a name, the commitment and the statement"
    );
    Entry {
        name: label[..16].try_into().expect("a 16-byte name"),
    }
}

fn build(log_rows: usize, entry: &Entry, declared: bool) -> Contract {
    let Recorded {
        graph,
        outputs,
        ending,
        inputs,
    } = recorded(log_rows, entry, declared);
    compile(&graph, &outputs, &ending, entry, inputs)
}

/// What a contract is compiled from: the graph the recorder leaves, the words the contract writes (the claims'
/// fields, or what it returns), how it ends, and how many scalars of the proof it reads.
pub(crate) struct Recorded {
    pub(crate) graph: Graph,
    pub(crate) outputs: Vec<Word>,
    pub(crate) ending: Ending,
    pub(crate) inputs: usize,
}

/// What [`contract`] is compiled from (`formal/Implementation` is about this graph). Used by the test that emits
/// it as Lean (`lean.rs`).
#[cfg(test)]
pub(crate) fn deployed(log_rows: usize) -> Recorded {
    recorded(log_rows, &entry(), true)
}

/// The output words, each written once however many claims read it.
#[derive(Default)]
struct Region {
    words: Vec<Word>,
    index: HashMap<String, usize>,
}

impl Region {
    fn at(&mut self, word: Word) -> usize {
        let key = format!("{word:?}");
        *self.index.entry(key).or_insert_with(|| {
            self.words.push(word);
            self.words.len() - 1
        })
    }
}

fn recorded(log_rows: usize, entry: &Entry, declared: bool) -> Recorded {
    assert_eq!(&entry.name, NAME, "the entry's name is the protocol's");
    let ((reduced, read), graph) = record(|| {
        let mut recorder = Recorder::new();
        let reduced = reduce(&mut recorder, log_rows).unwrap_or_else(|_| unreachable!("a recorder rejects nothing"));
        (reduced, recorder.read)
    });
    let Reduced {
        roots,
        oods,
        witness,
        wiring,
        h,
        q,
        g,
        sum,
    } = reduced;
    assert_eq!(read as usize, INPUTS);
    let node = |sym: &Sym| Word::Node(sym.0);
    let (outputs, ending) = if declared {
        let mut region = Region::default();
        let root = |k: usize| Word::Calldata(COMMITMENT + 32 * k);
        let claim = |region: &mut Region, root: Word, ood: Word, point: Vec<Word>, value: Word, index: usize| {
            ClaimWords {
                root: region.at(root),
                ood: region.at(ood),
                point: point.into_iter().map(|w| region.at(w)).collect(),
                value: region.at(value),
                index,
            }
        };
        let nodes = |point: &[Sym]| point.iter().map(node).collect::<Vec<_>>();
        let sum_words = sum_point(log_rows).into_iter().map(|x| Word::Const(element_word(x))).collect();
        let claims = vec![
            claim(&mut region, root(0), node(&oods[0]), nodes(&witness.0), node(&witness.1), 0),
            claim(&mut region, Word::StoredRoot, Word::StoredOod, nodes(&wiring.0), node(&wiring.1), 1),
            claim(&mut region, root(1), node(&oods[1]), nodes(&h.0), node(&h.1), 2),
            claim(&mut region, root(2), node(&oods[2]), nodes(&q.0), node(&q.1), 3),
            claim(&mut region, root(3), node(&oods[3]), nodes(&g.0), node(&g.1), 4),
            claim(&mut region, root(1), node(&oods[1]), sum_words, node(&sum), 5),
        ];
        (region.words, Ending::Declared(claims))
    } else {
        let mut outputs: Vec<Word> = Vec::new();
        for (root, ood) in roots.iter().zip(&oods) {
            outputs.extend(root.iter().map(node));
            outputs.push(node(ood));
        }
        for (point, value) in [&witness, &wiring, &h, &q, &g] {
            outputs.extend(point.iter().chain([value]).map(node));
        }
        outputs.push(node(&sum));
        (outputs, Ending::Return)
    };
    Recorded {
        graph,
        outputs,
        ending,
        inputs: read as usize,
    }
}

/// The PCS claims [`contract`] checks declared, in order: those a proof leaves ([`quotient::protocol::verify`]) on
/// their commitments, as [`quotient::protocol::verify_openings`] opens them.
pub fn pcs_claims(index: &Commitment, commitments: &Commitments, claims: &Claims) -> Vec<PcsClaim> {
    let on = [commitments.witness, *index, commitments.h, commitments.q, commitments.g];
    claims.all().iter().map(|(k, claim)| on[*k].pcs_claim(claim)).collect()
}

/// The calldata of `setIndexCommitment(index)`.
pub fn set_index_calldata(index: &Commitment) -> Vec<u8> {
    [&SET_INDEX[..], &index.root, &element_word(index.ood)].concat()
}

/// The index of the transaction's frame of PCS claims that calldata names ([`calldata`]): the first frame.
pub const PCS_FRAME: u8 = 0;

/// A statement and its proof as calldata verifying them: the selector, the statement, the four roots (each the word
/// of its bytes), the other scalars, then a byte, the index of the transaction's frame of PCS claims
/// ([`PCS_FRAME`]). A root's scalars are 128-bit, and calldata has room for no more: a proof with a larger one, which
/// the Rust verifier rejects, has no calldata (`NotARoot`). A proof of another length has calldata of another
/// length, which the contract rejects as the Rust verifier does.
pub fn calldata(statement: &Statement, proof: &Proof) -> Result<Vec<u8>, TranscriptError> {
    let stream = &proof.stream;
    let mut data = [&VERIFY[..], &statement.y, &statement.root].concat();
    for pair in ROOT_SCALARS.chunks(2) {
        let halves = [
            *stream.get(pair[0]).ok_or(TranscriptError::Exhausted)?,
            *stream.get(pair[1]).ok_or(TranscriptError::Exhausted)?,
        ];
        data.extend(halves_root(&halves)?);
    }
    for (i, scalar) in stream.iter().enumerate() {
        if !ROOT_SCALARS.contains(&i) {
            [scalar.c2, scalar.c1, scalar.c0].iter().for_each(|limb| data.extend(limb.to_be_bytes()));
        }
    }
    data.push(PCS_FRAME);
    Ok(data)
}

/// What [`claims_contract`] returned: the four commitments and the six claims.
pub fn decode(output: &[u8], log_rows: usize) -> Option<(Commitments, Claims)> {
    let words: Vec<F192> = output
        .as_chunks::<32>()
        .0
        .iter()
        .map(|word| {
            let limb = |i: usize| u64::from_be_bytes(word[24 - 8 * i..32 - 8 * i].try_into().unwrap());
            (limb(3) == 0).then(|| F192::new(limb(0), limb(1), limb(2)))
        })
        .collect::<Option<_>>()?;
    let [w, wiring, h, q, g] = quotient::protocol::table_vars(log_rows);
    let mut rest = &words[..];
    let mut take = |n: usize| {
        let (head, tail) = rest.split_at_checked(n)?;
        rest = tail;
        Some(head.to_vec())
    };
    let mut commitment = || {
        let c = take(3)?;
        Some(Commitment {
            root: halves_root(&[c[0], c[1]]).ok()?,
            ood: c[2],
        })
    };
    let (witness_c, h_c, q_c, g_c) = (commitment()?, commitment()?, commitment()?, commitment()?);
    let mut claim = |vars: usize| {
        let mut point = take(vars + 1)?;
        let value = point.pop()?;
        Some(Claim { point, value })
    };
    let (witness, wiring, h_claim, q_claim, g_claim) = (claim(w)?, claim(wiring)?, claim(h)?, claim(q)?, claim(g)?);
    let sum = Claim {
        point: sum_point(log_rows),
        value: *take(1)?.first()?,
    };
    rest.is_empty().then_some(())?;
    Some((
        Commitments {
            witness: witness_c,
            h: h_c,
            q: q_c,
            g: g_c,
        },
        Claims {
            witness,
            wiring,
            h: h_claim,
            q: q_claim,
            g: g_claim,
            sum,
        },
    ))
}

#[cfg(test)]
mod tests {
    use std::sync::LazyLock;

    use super::*;
    use crate::codegen::{INDEX_OOD_SLOT, INDEX_ROOT_SLOT};
    use revm::primitives::U256;
    use crate::machine::{CALLER, Chain, DEPLOYER, PcsFrame, frame_gas, transaction_gas};
    use primitives::test_rng::Rng;
    use quotient::circuit::{LOG_ROWS, membership, membership_inputs};
    use quotient::protocol::{Index, prove_with_seed, verify};
    use quotient::statement::{DEPTH, Secret};
    use revm::primitives::TxKind;

    /// Who may change the circuit's commitment.
    const OWNER: Address = Address::with_last_byte(0x0e);

    /// A full-size membership proof.
    fn proof(rng: &mut Rng) -> (Commitment, Statement, Proof) {
        let mut bytes = || std::array::from_fn(|_| rng.next_u64() as u8);
        let secret = Secret {
            x: bytes(),
            siblings: std::array::from_fn::<_, DEPTH, _>(|_| bytes()),
            directions: 0x5A3C_96F0,
        };
        let statement = secret.statement();
        let circuit = membership();
        let cells = circuit.cells(&membership_inputs(&secret));
        let index = Index::new(&circuit);
        let commitment = Commitment::of(&index.commit());
        // The proof's seed from the test generator, so that the tests repeat: `prove` draws a fresh one.
        let seed = std::array::from_fn(|_| rng.next_u64() as u8);
        let proved = prove_with_seed(&circuit, &index, &commitment, &statement, &cells, &seed);
        (commitment, statement, proved.proof)
    }

    /// The tests' proof, made once for all of them.
    static HONEST: LazyLock<(Commitment, Statement, Proof)> = LazyLock::new(|| proof(&mut Rng::new(0xE8)));

    /// A chain holding `contract`, deployed for the circuit committed as `index` and owned by [`OWNER`].
    fn deployed(contract: &Contract, index: &Commitment) -> (Chain, Address) {
        let mut chain = Chain::default();
        let (address, _) = deploy(&mut chain, contract, index, OWNER);
        (chain, address.expect("a deployment"))
    }

    fn block_of(claims: &[PcsClaim]) -> PcsFrame {
        let mut block = PcsFrame::default();
        claims.iter().for_each(|claim| block.declare(claim));
        block
    }

    /// A block proving the claims the Rust verifier leaves, if it leaves any.
    fn block_for(index: &Commitment, statement: &Statement, proof: &Proof) -> PcsFrame {
        match verify(index, statement, proof, LOG_ROWS) {
            Ok((commitments, claims)) => block_of(&pcs_claims(index, &commitments, &claims)),
            Err(_) => PcsFrame::default(),
        }
    }

    /// Change scalar `at` of a proof (a root's within its 128 bits), or change it back.
    fn tamper(proof: &mut Proof, at: usize) {
        proof.stream[at] += if ROOT_SCALARS.contains(&at) { F192::new(1, 2, 0) } else { F192::new(1, 2, 3) };
    }

    /// The contract without its checks and the Rust verifier leave the same commitments and claims, on an honest
    /// proof and on tampered ones, and the contract reverts on calldata of another length.
    #[test]
    fn contract_is_the_verifier() {
        let (index, statement, mut proof) = HONEST.clone();
        let (chain, address) = deployed(&claims_contract(LOG_ROWS), &index);
        let returned = |statement: &Statement, proof: &Proof| {
            let output = chain
                .call(address, &calldata(statement, proof).unwrap(), &PcsFrame::default())
                .output;
            output.as_deref().and_then(|output| decode(output, LOG_ROWS))
        };
        let expected = verify(&index, &statement, &proof, LOG_ROWS).expect("a reduction");
        assert_eq!(returned(&statement, &proof), Some(expected));
        for at in 0..proof.stream.len() {
            tamper(&mut proof, at);
            assert_eq!(returned(&statement, &proof), verify(&index, &statement, &proof, LOG_ROWS).ok(), "{at}");
            tamper(&mut proof, at);
        }
        let mut other = statement;
        other.y[5] ^= 4;
        assert_eq!(returned(&other, &proof), verify(&index, &other, &proof, LOG_ROWS).ok());

        let mut long = calldata(&statement, &proof).unwrap();
        assert_eq!(long.len(), CALLDATA_LEN);
        long.push(0);
        let none = PcsFrame::default();
        assert!(chain.call(address, &long, &none).output.is_none());
        assert!(chain.call(address, &long[..long.len() - 2], &none).output.is_none());
    }

    /// The contract succeeds, returning the word 1, exactly when the frame declares the six claims the Rust verifier
    /// leaves, in order: on the honest proof, and on tampered ones, which leave other claims.
    #[test]
    fn contract_checks_the_declared_claims() {
        let (index, statement, proof) = HONEST.clone();
        let (chain, address) = deployed(&contract(LOG_ROWS), &index);
        let succeeds = |statement: &Statement, proof: &Proof, block: &PcsFrame| {
            let output = chain.call(address, &calldata(statement, proof).unwrap(), block).output;
            assert!(output.as_ref().is_none_or(|output| *output == VERIFIED));
            output.is_some()
        };
        let honest = block_for(&index, &statement, &proof);
        assert!(succeeds(&statement, &proof, &honest));

        let (commitments, claims) = verify(&index, &statement, &proof, LOG_ROWS).expect("a reduction");
        let all = pcs_claims(&index, &commitments, &claims);
        assert!(!succeeds(&statement, &proof, &PcsFrame::default()));
        for missing in 0..all.len() {
            let mut some = all.clone();
            some.remove(missing);
            assert!(!succeeds(&statement, &proof, &block_of(&some)), "{missing}");
        }
        // Two claims swapped; a claim on another commitment; a claim with another value.
        let mut swapped = all.clone();
        swapped.swap(2, 5);
        assert!(!succeeds(&statement, &proof, &block_of(&swapped)));
        let mut elsewhere = all.clone();
        elsewhere[3].root = commitments.g.root;
        assert!(!succeeds(&statement, &proof, &block_of(&elsewhere)));
        let mut valued = all.clone();
        valued[4].value += F192::ONE;
        assert!(!succeeds(&statement, &proof, &block_of(&valued)));

        let mut tampered = proof.clone();
        for at in 0..proof.stream.len() {
            tamper(&mut tampered, at);
            assert!(!succeeds(&statement, &tampered, &honest), "{at}");
            let own = block_for(&index, &statement, &tampered);
            let verifies = verify(&index, &statement, &tampered, LOG_ROWS).is_ok();
            assert_eq!(succeeds(&statement, &tampered, &own), verifies, "{at}");
            tamper(&mut tampered, at);
        }
        let mut other = statement;
        other.root[17] ^= 0x20;
        assert!(!succeeds(&other, &proof, &honest));
        assert!(succeeds(&other, &proof, &block_for(&index, &other, &proof)));
    }

    /// A call of the verifier is the selector [`VERIFY`] then the arguments packed, with no value.
    #[test]
    fn contract_checks_its_selector() {
        let (index, statement, proof) = HONEST.clone();
        let (mut chain, address) = deployed(&contract(LOG_ROWS), &index);
        let honest = block_for(&index, &statement, &proof);
        let data = calldata(&statement, &proof).unwrap();
        assert_eq!(data[..4], [0xde, 0x12, 0xc6, 0x40]);
        assert_eq!((data.len(), data[CALLDATA_LEN - 1]), (CALLDATA_LEN, PCS_FRAME));
        let succeeds = |data: &[u8]| {
            let output = chain.call(address, data, &honest).output;
            assert!(output.as_ref().is_none_or(|output| *output == VERIFIED));
            output.is_some()
        };
        assert!(succeeds(&data));
        for byte in 0..4 {
            for bit in [0x01, 0x80] {
                let mut other = data.clone();
                other[byte] ^= bit;
                assert!(!succeeds(&other), "{byte} {bit}");
            }
        }
        let mut other = data.clone();
        other[..4].copy_from_slice(&SET_INDEX);
        assert!(!succeeds(&other));
        assert!(!succeeds(&data[4..]));
        assert!(!succeeds(&[]));
        assert!(chain.transact(CALLER, address, &data, U256::from(1), &honest).output.is_none());
        assert_eq!(chain.transact(CALLER, address, &data, U256::ZERO, &honest).output, Some(VERIFIED.to_vec()));
        assert_eq!(chain.storage(address, U256::from(INDEX_ROOT_SLOT)).to_be_bytes::<32>(), index.root);
    }

    /// The circuit's commitment is the one in storage, for the transcript and for the wiring table's claim alike: the
    /// one the deployment stores, then the one `setIndexCommitment` stores, from the owner only.
    #[test]
    fn contract_reads_the_index_commitment_from_storage() {
        let (index, statement, proof) = HONEST.clone();
        let contract = contract(LOG_ROWS);
        let (mut chain, address) = deployed(&contract, &index);
        let stored = |chain: &Chain| {
            let word = |slot: u8| chain.storage(address, U256::from(slot)).to_be_bytes::<32>();
            (word(INDEX_ROOT_SLOT), word(INDEX_OOD_SLOT))
        };
        assert_eq!(stored(&chain), (index.root, element_word(index.ood)));
        let mut code = contract.code.clone();
        let at = contract.owner_at.expect("an owner");
        code[at..at + 32].copy_from_slice(OWNER.into_word().as_slice());
        assert_eq!(chain.code(address), code);

        let data = calldata(&statement, &proof).unwrap();
        let other_index = Commitment {
            ood: index.ood + F192::ONE,
            ..index
        };
        let expected = verify(&other_index, &statement, &proof, LOG_ROWS).expect("a reduction");
        let (returning, at) = deployed(&claims_contract(LOG_ROWS), &other_index);
        let output = returning.call(at, &data, &PcsFrame::default()).output;
        assert_eq!(output.and_then(|output| decode(&output, LOG_ROWS)), Some(expected));
        let (honest, other) = (block_for(&index, &statement, &proof), block_for(&other_index, &statement, &proof));
        let succeeds = |chain: &Chain, block: &PcsFrame| chain.call(address, &data, block).output.is_some();
        assert!(succeeds(&chain, &honest));
        assert!(!succeeds(&chain, &other));

        let none = PcsFrame::default();
        let set = set_index_calldata(&other_index);
        let mut wrong = set.clone();
        wrong[3] ^= 1;
        for (from, data, value) in [
            (CALLER, &set[..], 0u64),
            (DEPLOYER, &set[..], 0),
            (OWNER, &set[..], 1),
            (OWNER, &set[..67], 0),
            (OWNER, &[&set[..], &[0]].concat()[..], 0),
            (OWNER, &wrong[..], 0),
            (OWNER, &data[..], 0),
        ] {
            let outcome = chain.transact(from, address, data, U256::from(value), &none);
            assert!(outcome.output.is_none(), "{from} {}", data.len());
            assert_eq!(stored(&chain), (index.root, element_word(index.ood)));
        }
        assert_eq!(chain.transact(OWNER, address, &set, U256::ZERO, &none).output, Some(vec![]));
        assert_eq!(stored(&chain), (other_index.root, element_word(other_index.ood)));
        assert!(!succeeds(&chain, &honest));
        assert!(succeeds(&chain, &other));
        let back = set_index_calldata(&index);
        assert_eq!(chain.transact(OWNER, address, &back, U256::ZERO, &none).output, Some(vec![]));
        assert!(succeeds(&chain, &honest));
    }

    /// The init code deploys the contract with exactly its three arguments and no value, and reverts otherwise.
    #[test]
    fn deployment_takes_its_arguments() {
        let contract = contract(LOG_ROWS);
        let index = Commitment {
            root: [0xa7; 32],
            ood: F192::new(5, 6, 7),
        };
        let init = init_code(&contract, &index, OWNER);
        let mut chain = Chain::default();
        let long = [&init[..], &[0]].concat();
        for init in [&init[..init.len() - 1], &long[..], &init[..init.len() - 32], &init[..init.len() - 96]] {
            assert_eq!(chain.deploy(init).0, None, "{}", init.len());
        }
        let paid = chain.run(DEPLOYER, TxKind::Create, &init, U256::from(1), &PcsFrame::default());
        assert_eq!(paid.1, None);
        let (address, outcome) = chain.deploy(&init);
        let address = address.expect("a deployment");
        assert_eq!(outcome.output.as_deref(), Some(&chain.code(address)[..]));
        assert_eq!(chain.storage(address, U256::from(INDEX_ROOT_SLOT)).to_be_bytes::<32>(), index.root);
        assert_eq!(chain.storage(address, U256::from(INDEX_OOD_SLOT)).to_be_bytes::<32>(), element_word(index.ood));
        assert!(contract.code.len() <= 24_576, "EIP-170");
    }

    /// The membership contracts' bytecode, pinned: the Keccak-256 of the deployed contract's code and of the claims
    /// contract's, since the claims are the EIP's PCS claims (one point each, the commitments' out-of-domain answers).
    #[test]
    fn membership_bytecode_is_pinned() {
        let hex = |code: &[u8]| -> String { primitives::hash::hash(code).iter().map(|b| format!("{b:02x}")).collect() };
        let codes = [hex(&contract(LOG_ROWS).code), hex(&claims_contract(LOG_ROWS).code)];
        assert_eq!(
            codes,
            [
                "0ad734634290e48a9e628a746f17901cfb1def18db698c40267c767c5a242eb3",
                "02a5e5abe62ca81259019b62998c99efdae6d357eb432f76939c8794ce332815",
            ]
        );
    }

    /// `n` with a comma every three digits.
    fn grouped(n: u64) -> String {
        let digits = n.to_string();
        let mut out = String::new();
        for (i, digit) in digits.chars().enumerate() {
            if i > 0 && (digits.len() - i).is_multiple_of(3) {
                out.push(',');
            }
            out.push(digit);
        }
        out
    }

    /// What a call costs: `cargo test --release -p evm -- --ignored --nocapture --exact quotient::tests::gas_report`.
    #[test]
    #[ignore]
    fn gas_report() {
        let (index, statement, proof) = proof(&mut Rng::new(0x6A6));
        let data = calldata(&statement, &proof).unwrap();
        let block = block_for(&index, &statement, &proof);
        let contract = contract(LOG_ROWS);
        let mut chain = Chain::default();
        let (address, (init, deployment)) = deploy(&mut chain, &contract, &index, OWNER);
        let address = address.expect("a deployment");
        let outcome = chain.call(address, &data, &block);
        assert_eq!(outcome.output, Some(VERIFIED.to_vec()));
        let zeros = data.iter().filter(|&&byte| byte == 0).count();
        println!(
            "calldata   : {} bytes, {zeros} of them zero: selector 4, statement 64, roots 128, scalars {}, frame 1",
            data.len(),
            SCALAR_BYTES * INPUTS
        );
        println!("FIELD_MUL  : {}", contract.field_muls);
        println!("KECCAK256  : {} (transcript), and one a claim", contract.hashes);
        println!("claims     : {} declared (witness, wiring, H, Q, G, sum on H)", block.claims().len());
        println!("SLOAD      : 2, cold (4,200 gas): the index commitment's root and out-of-domain answer");
        println!("code       : {} bytes (EIP-170 limit 24,576)", grouped(contract.code.len() as u64));
        println!("memory     : {} words", contract.memory_words);
        let (standard, floor, gas) = frame_gas(&data, &block, outcome.execution);
        println!();
        println!("Under EIP-8141 (EIP-7976's floor) with the EIP draft's pcs_gas in both, without FRAME_TX_INTRINSIC_COST");
        println!("and the per-frame costs; the frame of PCS claims is {} bytes:", block.data().len());
        println!("execution {}", grouped(outcome.execution));
        println!("standard  {}  (16/4 a byte of calldata and frame, execution, pcs_gas)", grouped(standard));
        println!("floor     {}  (64 a byte of calldata and frame, pcs_gas)", grouped(floor));
        println!("gas       {}", grouped(gas));
        println!();
        println!(
            "Deployment: init code {} bytes; {} gas ({} without the 21,000)",
            init.len(),
            grouped(transaction_gas(&init, deployment)),
            grouped(transaction_gas(&init, deployment) - 21_000)
        );
        let set = set_index_calldata(&index);
        let outcome = chain.transact(OWNER, address, &set, U256::ZERO, &PcsFrame::default());
        assert_eq!(outcome.output, Some(vec![]));
        println!(
            "setIndexCommitment by the owner: execution {}, transaction {}",
            grouped(outcome.execution),
            grouped(transaction_gas(&set, outcome.execution))
        );
    }
}
