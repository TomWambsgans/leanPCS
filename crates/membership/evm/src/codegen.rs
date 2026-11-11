// Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
// file crates/membership/evm/src/codegen.rs; new here: the checks of the declared claims, the entry by calldata's length
// (no selector), the index commitment in storage, `setIndexCommitment` and the creation code; the compilation and the
// assembly are now `crates/evm_link`'s (`front`, `assemble`), this file the code of each node, the entry and the
// outputs. MIT OR Apache-2.0; see AGENTS.md.
//! A recorded graph as EVM bytecode: straight-line code, a value used once left on the stack and a shared one
//! kept in a memory slot, which is reused after its last read.

use evm_link::front::{self, Check, Dag, Piece, Source};
use evm_link::op::{
    AND, CALLDATACOPY, CALLDATALOAD, CALLDATASIZE, CALLER, CALLVALUE, DUP1, DUP2, FIELD_MUL, JUMPDEST, JUMPI,
    KECCAK256, MSTORE, OR, PUSH0, PUSH32, SHL, SHR, SLOAD, SSTORE, STOP, SWAP1, XOR, push, push_fixed, push_usize, word,
};
use evm_link::{ClaimWords, Options};
use quotient::protocol::NAME;

use crate::record::{Graph, Node};

/// Memory below the slots is scratch for hashing: the seed's 136 bytes (at 16), or a state and the scalars it absorbs.
const SEED_SCRATCH: usize = 0xa0;

/// The selector of `setIndexCommitment(bytes32,bytes32)`. A call of the verifier has none: it is calldata of the
/// verifier's length.
pub const SET_INDEX: [u8; 4] = [0xda, 0xb9, 0x9d, 0xbd];
/// The storage slots holding the circuit's commitment: its root, and its out-of-domain answer (as a word, the top
/// 64 bits zero).
pub const INDEX_ROOT_SLOT: u8 = 0;
pub const INDEX_OOD_SLOT: u8 = 1;

/// Where the arguments (calldata) hold the statement's two words, then the two commitments' roots; the proof's other
/// scalars follow them.
pub const COMMITMENT: usize = 64;
pub const SCALARS: usize = COMMITMENT + 2 * 32;
pub const SCALAR_BYTES: usize = 24;

/// A word the contract writes to its output region.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Word {
    /// A recorded value.
    Node(u32),
    /// The word of the arguments at this offset.
    Calldata(usize),
    /// The circuit's commitment's root and out-of-domain answer, in storage: the seed writes them, having read them.
    StoredRoot,
    StoredOod,
}

/// What the contract does with its output region, once written.
pub enum Ending {
    /// Return it.
    Return,
    /// Revert unless the transaction declares these PCS claims, their fields words of the region, as payloads `0,
    /// 1, ...` of the frame of PCS claims the caller names in the last byte of calldata
    /// ([`evm_link::declared_claims`]); return the word 1.
    Declared(Vec<ClaimWords>),
}

/// No tags: this contract's gas is not broken down by phase.
const UNTAGGED: &str = "";

/// The graph, with the output words the seed writes: the code of each node.
struct Nodes<'a> {
    graph: &'a Graph,
    stored_root: Option<usize>,
    stored_ood: Option<usize>,
}

impl Dag for Nodes<'_> {
    fn len(&self) -> usize {
        self.graph.nodes.len()
    }

    fn operands(&self, id: u32) -> Vec<u32> {
        match self.graph.nodes[id as usize] {
            Node::Add(a, b) | Node::Mul(a, b) => vec![a, b],
            Node::Hash(state, scalars, n) => [&[state][..], &scalars[..n as usize]].concat(),
            Node::Frobenius(a) | Node::Low(a) => vec![a],
            _ => vec![],
        }
    }

    fn commutative(&self, id: u32) -> bool {
        matches!(self.graph.nodes[id as usize], Node::Add(..) | Node::Mul(..))
    }

    fn is_const(&self, id: u32) -> bool {
        matches!(self.graph.nodes[id as usize], Node::Const(_))
    }

    fn code(&self, id: u32) -> Vec<Piece> {
        let bytes = |bytes: &[&[u8]]| Piece::Code(bytes.concat());
        let read = |offset: usize| Piece::Calldata { offset, len: 32 };
        match self.graph.nodes[id as usize] {
            Node::Const(limbs) => front::code(push(&word(limbs))),
            // A statement word: the eight bytes at `8 k`, the word's top.
            Node::Statement(k) => vec![read(8 * k as usize), bytes(&[&[CALLDATALOAD], &push_usize(192), &[SHR]])],
            Node::Root(k) => {
                let half = if k % 2 == 0 {
                    bytes(&[&push_usize(128), &[SHR]])
                } else {
                    bytes(&[&push(&[0xff; 16]), &[AND]])
                };
                vec![read(COMMITMENT + 32 * (k as usize / 2)), bytes(&[&[CALLDATALOAD]]), half]
            }
            Node::Input(i) => vec![
                read(SCALARS + SCALAR_BYTES * i as usize),
                bytes(&[&[CALLDATALOAD], &push_usize(64), &[SHR]]),
            ],
            Node::Add(..) => front::code(vec![XOR]),
            Node::Mul(..) => front::code(vec![FIELD_MUL]),
            // `(c0, c1, c2)` to `(c0, c2, c1 + c2)`.
            Node::Frobenius(_) => {
                let low = push(&[0xff; 8]);
                front::code(
                    [
                        &[DUP1][..],
                        &push_usize(128),
                        &[SHR, DUP2],
                        &push_usize(64),
                        &[SHR],
                        &low,
                        &[AND, DUP2, XOR],
                        &push_usize(128),
                        &[SHL, SWAP1],
                        &push_usize(64),
                        &[SHL, OR, SWAP1],
                        &low,
                        &[AND, OR],
                    ]
                    .concat(),
                )
            }
            // The label: the name, the circuit's commitment (its root and out-of-domain answer, read from storage:
            // two cold `SLOAD`s), then the statement copied from calldata, 136 bytes from 16. The wiring table's
            // claim takes the commitment too, written to its output words now. The name is the low half of the word
            // at 0; the answer's word at 56, its top 8 zero bytes under the root's word at 32, written after it.
            Node::Seed => {
                let mut code = vec![bytes(&[&push(NAME), &[PUSH0, MSTORE], &push_usize(INDEX_OOD_SLOT.into()), &[SLOAD]])];
                if let Some(k) = self.stored_ood {
                    code.extend([bytes(&[&[DUP1]]), Piece::Output(k)]);
                }
                code.push(bytes(&[&push_usize(56), &[MSTORE], &push_usize(INDEX_ROOT_SLOT.into()), &[SLOAD]]));
                if let Some(k) = self.stored_root {
                    code.extend([bytes(&[&[DUP1]]), Piece::Output(k)]);
                }
                code.extend([
                    bytes(&[&push_usize(32), &[MSTORE], &push_usize(64)]),
                    Piece::Calldata { offset: 0, len: 64 },
                    bytes(&[&push_usize(88), &[CALLDATACOPY], &push_usize(136), &push_usize(16), &[KECCAK256]]),
                ]);
                code
            }
            // Every operand reaches the stack before any is written to the scratch words.
            Node::Hash(_, _, n) => {
                let n = n as usize;
                let mut code: Vec<u8> = (1..=n).rev().flat_map(|k| [&push_usize(32 * k)[..], &[MSTORE]].concat()).collect();
                code.extend([&[PUSH0, MSTORE][..], &push_usize(32 * (n + 1)), &[PUSH0, KECCAK256]].concat());
                front::code(code)
            }
            Node::Low(_) => front::code([&push(&[0xff; 24])[..], &[AND]].concat()),
        }
    }

    fn tag(&self, _id: u32) -> Option<&'static str> {
        None
    }

    fn work(&self, _id: u32) -> u32 {
        3
    }
}

/// A contract, and what one call of it executes: its code is straight-line, so every instruction runs once.
#[derive(Clone)]
pub struct Contract {
    /// The code, with no owner ([`creation_code`] writes one at `owner_at`).
    pub code: Vec<u8>,
    /// Where the code holds its owner, the word a `PUSH32` pushes.
    pub owner_at: usize,
    pub field_muls: usize,
    pub hashes: usize,
    /// Memory it touches, in words.
    pub memory_words: usize,
}

/// `setIndexCommitment(bytes32 root, bytes32 ood)`: revert unless calldata is its selector, `root` and `ood`, with
/// no value, from the owner; else store them. The owner is the word of a `PUSH32`, which the creation code writes.
fn set_index(fail: usize) -> (Vec<u8>, Option<usize>) {
    let mut code = [
        &[JUMPDEST, PUSH0, CALLDATALOAD][..],
        &push_usize(224),
        &[SHR],
        &push(&SET_INDEX),
        &[XOR, CALLDATASIZE],
        &push_usize(4 + 64),
        &[XOR, OR, CALLVALUE, OR, CALLER, PUSH32],
    ]
    .concat();
    let owner = code.len();
    code.extend([0; 32]);
    code.extend([&[XOR, OR][..], &push_fixed(fail, 2), &[JUMPI], &push_usize(4), &[CALLDATALOAD]].concat());
    code.extend([&push_usize(INDEX_ROOT_SLOT.into())[..], &[SSTORE]].concat());
    code.extend([&push_usize(36)[..], &[CALLDATALOAD], &push_usize(INDEX_OOD_SLOT.into()), &[SSTORE, STOP]].concat());
    (code, Some(owner))
}

/// The contract. A call of the verifier is calldata of the arguments, no selector: the statement, the commitments and
/// `inputs` scalars of the proof, of `SCALAR_BYTES` each, then a byte. On such a call, with no value, it
/// reverts unless every node of `graph.nonzero` is nonzero (checked after the entry's checks), else writes `outputs`
/// to a region of fresh memory, one word each, and ends as `ending` says. Any other call is one of
/// `setIndexCommitment(bytes32 root, bytes32 ood)`, or reverts: from the owner, with no value, it stores them in
/// slots [`INDEX_ROOT_SLOT`] and [`INDEX_OOD_SLOT`] and returns nothing.
pub fn compile(graph: &Graph, outputs: &[Word], ending: &Ending, inputs: usize) -> Contract {
    // Then a byte, the index of the transaction's frame of PCS claims (a returning contract reads past it).
    let calldata_len = SCALARS + SCALAR_BYTES * inputs + 1;
    let words = outputs
        .iter()
        .map(|word| match *word {
            Word::Node(id) => front::Word::Node(id),
            Word::Calldata(offset) => {
                front::Word::Code(vec![Piece::Calldata { offset, len: 32 }, Piece::Code(vec![CALLDATALOAD])], UNTAGGED)
            }
            Word::StoredRoot | Word::StoredOod => front::Word::Written,
        })
        .collect();
    let absorbed = graph.nodes.iter().map(|node| match node {
        Node::Hash(_, _, n) => *n as usize,
        _ => 0,
    });
    let source = Source {
        dag: &Nodes {
            graph,
            stored_root: outputs.iter().position(|word| *word == Word::StoredRoot),
            stored_ood: outputs.iter().position(|word| *word == Word::StoredOod),
        },
        // Not a call of the verifier: calldata of another length, or value.
        entry: [&[CALLDATASIZE][..], &push_usize(calldata_len), &[XOR, CALLVALUE, OR]].concat(),
        entry_other: true,
        entry_tag: UNTAGGED,
        checks: graph.nonzero.iter().map(|&id| (id, Check::Nonzero)).collect(),
        outputs: words,
        claims: match ending {
            Ending::Return => Vec::new(),
            Ending::Declared(claims) => claims.clone(),
        },
        outputs_tag: UNTAGGED,
        scratch: SEED_SCRATCH.max(32 * (1 + absorbed.max().unwrap_or(0))),
        calldata_len,
    };
    let compiled = front::compile(&source);
    let options = Options {
        other: Some(&set_index),
        ..Options::default()
    };
    let assembled = evm_link::assemble(&compiled.program, &options);
    let used = |of: &dyn Fn(Node) -> bool| {
        (graph.nodes.iter().zip(&compiled.uses)).filter(|&(&node, &uses)| uses > 0 && of(node)).count()
    };
    Contract {
        code: assembled.code,
        owner_at: assembled.other_patch.expect("setIndexCommitment's owner"),
        field_muls: used(&|node| matches!(node, Node::Mul(..))),
        hashes: used(&|node| matches!(node, Node::Hash(..) | Node::Seed)),
        memory_words: assembled.memory_words,
    }
}

/// The creation code of `contract`, which its constructor's arguments follow in the init code: those of
/// `constructor(bytes32 indexRoot, bytes32 indexOod, address owner)`, ABI-encoded (96 bytes). It reverts on value, or
/// on arguments of another length; else it stores `indexRoot` and `indexOod` in slots [`INDEX_ROOT_SLOT`] and
/// [`INDEX_OOD_SLOT`], writes the `owner` word into the code, and returns the code.
pub fn creation_code(contract: &Contract) -> Vec<u8> {
    evm_link::creation_code(&contract.code, &[INDEX_ROOT_SLOT, INDEX_OOD_SLOT], Some(contract.owner_at))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// [`SET_INDEX`] is the selector of `setIndexCommitment(bytes32,bytes32)`.
    #[test]
    fn set_index_selector() {
        let digest = primitives::hash::hash(b"setIndexCommitment(bytes32,bytes32)");
        assert_eq!(SET_INDEX, digest[..4], "{:02x?}", &digest[..4]);
    }
}
