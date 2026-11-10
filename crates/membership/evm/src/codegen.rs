// Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
// file crates/membership/evm/src/codegen.rs; new here: the checks of the declared claims, the selector, the index commitment in
// storage (`Entry`), `setIndexCommitment` and the creation code; the assembly is now `crates/evm_link`'s. MIT OR Apache-2.0; see
// AGENTS.md.
//! A recorded graph as EVM bytecode: straight-line code, a value used once left on the stack and a shared one
//! kept in a memory slot, which is reused after its last read.

use evm_link::op::{
    AND, CALLDATACOPY, CALLDATALOAD, CALLDATASIZE, CALLER, CALLVALUE, CODECOPY, CODESIZE, DUP1, DUP2, FIELD_MUL,
    ISZERO, JUMPDEST, JUMPI, KECCAK256, MLOAD, MSTORE, OR, PUSH0, PUSH32, RETURN, REVERT, SHL, SHR, SLOAD, SSTORE,
    STOP, SWAP1, XOR, push, push_usize,
};
use evm_link::{ClaimWords, Item, Options, Program};

use crate::record::{Graph, Node};

/// Memory below the slots is scratch for hashing: the seed's 136 bytes (at 16), or a state and the scalars it absorbs.
const SEED_SCRATCH: usize = 0xa0;

/// The selector of `verify(bytes32,bytes32,bytes)`, the first 4 bytes of the `keccak256` of that signature: calldata
/// starting with it is a proof to verify.
pub const VERIFY: [u8; 4] = [0xde, 0x12, 0xc6, 0x40];
/// The selector of `setIndexCommitment(bytes32,bytes32)`.
pub const SET_INDEX: [u8; 4] = [0xda, 0xb9, 0x9d, 0xbd];
/// The storage slots holding the circuit's commitment: its root, and its out-of-domain answer (as a word, the top
/// 64 bits zero).
pub const INDEX_ROOT_SLOT: u8 = 0;
pub const INDEX_OOD_SLOT: u8 = 1;

/// Where the arguments (calldata after the selector, if any) hold the statement's two words, then the four
/// commitments' roots; the proof's other scalars follow them.
pub const COMMITMENT: usize = 64;
pub const SCALARS: usize = COMMITMENT + 4 * 32;
pub const SCALAR_BYTES: usize = 24;

/// How calls enter the contract: calldata starts with [`VERIFY`], and a call of the verifier carries no value. The
/// circuit's commitment is in storage slots [`INDEX_ROOT_SLOT`] and [`INDEX_OOD_SLOT`], which the creation code
/// writes and the owner may change ([`SET_INDEX`]).
#[derive(Clone, Copy, Debug)]
pub struct Entry {
    /// The transcript's label is the protocol's 16-byte name, the circuit's commitment, then the statement.
    pub name: [u8; 16],
}

/// `PUSH2` of an address in the code: one length whatever the address, so code can be laid out in two passes.
fn push2(at: usize) -> [u8; 3] {
    assert!(at < 1 << 16, "an address of two bytes");
    [0x61, (at >> 8) as u8, at as u8]
}

/// A field element as a word: limb 0 lowest.
fn word(limbs: [u64; 3]) -> [u8; 32] {
    evm_link::op::word(limbs)
}

/// A word the contract writes to its output region.
#[derive(Clone, Copy, Debug)]
pub enum Word {
    /// A recorded value.
    Node(u32),
    Const([u8; 32]),
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

struct Compiler<'a> {
    graph: &'a Graph,
    entry: &'a Entry,
    /// Where calldata holds the arguments: after the selector, if any.
    base: usize,
    /// The output words of [`Word::StoredRoot`] and [`Word::StoredOod`], if the seed writes them.
    stored_root: Option<usize>,
    stored_ood: Option<usize>,
    /// Kept in memory: used more than once, and not a constant.
    shared: Vec<bool>,
    done: Vec<bool>,
    /// Stack words evaluating a node takes.
    depth: Vec<u32>,
    items: Vec<(Item, &'static str)>,
}

impl Compiler<'_> {
    fn code(&mut self, bytes: &[u8]) {
        self.items.push((Item::Code(bytes.to_vec()), UNTAGGED));
    }

    fn item(&mut self, item: Item) {
        self.items.push((item, UNTAGGED));
    }

    /// Push the offset of calldata bytes `offset..offset + len`, which the code then reads.
    fn calldata(&mut self, offset: usize, len: usize) {
        self.item(Item::Calldata { offset, len });
    }

    fn operands(node: Node) -> Vec<u32> {
        match node {
            Node::Add(a, b) | Node::Mul(a, b) if a == b => vec![a],
            Node::Add(a, b) | Node::Mul(a, b) => vec![a, b],
            Node::Hash(state, scalars, n) => [&[state][..], &scalars[..n as usize]].concat(),
            Node::Frobenius(a) | Node::Low(a) => vec![a],
            _ => vec![],
        }
    }

    /// Leave the node's value on the stack.
    fn eval(&mut self, id: u32) {
        let at = id as usize;
        if self.shared[at] && self.done[at] {
            self.item(Item::Load(id));
            return;
        }
        match self.graph.nodes[at] {
            Node::Const(limbs) => self.code(&push(&word(limbs))),
            Node::Statement(k) | Node::Root(k) => {
                let offset = match self.graph.nodes[at] {
                    Node::Root(_) => self.base + COMMITMENT + 32 * (k as usize / 2),
                    _ => self.base + 32 * (k as usize / 2),
                };
                self.calldata(offset, 32);
                self.code(&[CALLDATALOAD]);
                if k % 2 == 0 {
                    self.code(&[&push_usize(128)[..], &[SHR]].concat());
                } else {
                    self.code(&[&push(&[0xff; 16])[..], &[AND]].concat());
                }
            }
            Node::Input(i) => {
                self.calldata(self.base + SCALARS + SCALAR_BYTES * i as usize, 32);
                self.code(&[&[CALLDATALOAD][..], &push_usize(64), &[SHR]].concat());
            }
            Node::Add(a, b) | Node::Mul(a, b) => {
                let op = if matches!(self.graph.nodes[at], Node::Add(..)) {
                    XOR
                } else {
                    FIELD_MUL
                };
                if a == b {
                    self.eval(a);
                    self.code(&[DUP1]);
                } else {
                    // The deeper operand first, so the other is evaluated over one word, not under many.
                    let (first, second) = if self.depth[a as usize] >= self.depth[b as usize] {
                        (a, b)
                    } else {
                        (b, a)
                    };
                    self.eval(first);
                    self.eval(second);
                }
                self.code(&[op]);
            }
            Node::Frobenius(a) => {
                // `(c0, c1, c2)` to `(c0, c2, c1 + c2)`.
                self.eval(a);
                let low = push(&[0xff; 8]);
                self.code(&[&[DUP1][..], &push_usize(128), &[SHR]].concat());
                self.code(&[&[DUP2][..], &push_usize(64), &[SHR], &low, &[AND, DUP2, XOR]].concat());
                self.code(&[&push_usize(128)[..], &[SHL, SWAP1], &push_usize(64), &[SHL, OR]].concat());
                self.code(&[&[SWAP1][..], &low, &[AND, OR]].concat());
            }
            // The label: the name, the circuit's commitment (its root and out-of-domain answer, read from storage:
            // two cold `SLOAD`s), then the statement copied from calldata, 136 bytes from 16. The wiring table's
            // claim takes the commitment too, written to its output words now.
            Node::Seed => {
                // The name as the low half of the word at 0; the answer's word at 56, its top 8 zero bytes under the
                // root's word at 32, written after it.
                self.code(&[&push(&self.entry.name)[..], &[PUSH0, MSTORE]].concat());
                self.code(&[&push_usize(INDEX_OOD_SLOT.into())[..], &[SLOAD]].concat());
                if let Some(k) = self.stored_ood {
                    self.code(&[DUP1]);
                    self.item(Item::Output(k));
                }
                self.code(&[&push_usize(56)[..], &[MSTORE]].concat());
                self.code(&[&push_usize(INDEX_ROOT_SLOT.into())[..], &[SLOAD]].concat());
                if let Some(k) = self.stored_root {
                    self.code(&[DUP1]);
                    self.item(Item::Output(k));
                }
                self.code(&[&push_usize(32)[..], &[MSTORE]].concat());
                self.code(&push_usize(64));
                self.calldata(self.base, 64);
                self.code(&[&push_usize(88)[..], &[CALLDATACOPY]].concat());
                self.code(&[&push_usize(136)[..], &push_usize(16), &[KECCAK256]].concat());
            }
            Node::Hash(state, scalars, n) => {
                // Every operand reaches the stack before any is written to the scratch words.
                self.eval(state);
                for &scalar in &scalars[..n as usize] {
                    self.eval(scalar);
                }
                for k in (1..=n as usize).rev() {
                    self.code(&[&push_usize(32 * k)[..], &[MSTORE]].concat());
                }
                self.code(&[PUSH0, MSTORE]);
                self.code(&[&push_usize(32 * (n as usize + 1))[..], &[PUSH0, KECCAK256]].concat());
            }
            Node::Low(a) => {
                self.eval(a);
                self.code(&[&push(&[0xff; 24])[..], &[AND]].concat());
            }
        }
        if self.shared[at] {
            self.done[at] = true;
            self.item(Item::Store(id));
        }
    }
}

/// A contract, and what one call of it executes: its code is straight-line, so every instruction runs once.
#[derive(Clone)]
pub struct Contract {
    /// The code, with no owner ([`creation_code`] writes one at `owner_at`).
    pub code: Vec<u8>,
    /// Where the code holds its owner, the word a `PUSH32` pushes, if it reads the circuit's commitment from
    /// storage.
    pub owner_at: Option<usize>,
    pub field_muls: usize,
    pub hashes: usize,
    /// Memory it touches, in words.
    pub memory_words: usize,
}

/// The program, and the setIndexRoot tail's maker.
struct Compiled {
    program: Program,
    field_muls: usize,
    hashes: usize,
}

fn program(graph: &Graph, outputs: &[Word], ending: &Ending, entry: &Entry, inputs: usize) -> Compiled {
    let base = VERIFY.len();
    // Then a byte, the index of the transaction's frame of PCS claims (a returning contract reads past it).
    let calldata_len = base + SCALARS + SCALAR_BYTES * inputs + 1;
    let stored_root = outputs.iter().position(|word| matches!(word, Word::StoredRoot));
    let stored_ood = outputs.iter().position(|word| matches!(word, Word::StoredOod));
    let n = graph.nodes.len();
    let mut uses = vec![0u32; n];
    let output_nodes = || {
        outputs.iter().filter_map(|word| match word {
            Word::Node(id) => Some(*id),
            _ => None,
        })
    };
    for root in graph.nonzero.iter().copied().chain(output_nodes()) {
        uses[root as usize] += 1;
    }
    for at in (0..n).rev() {
        if uses[at] > 0 {
            for operand in Compiler::operands(graph.nodes[at]) {
                uses[operand as usize] += 1;
            }
        }
    }
    let shared: Vec<bool> = (0..n)
        .map(|at| uses[at] > 1 && !matches!(graph.nodes[at], Node::Const(_)))
        .collect();
    let mut depth = vec![1u32; n];
    for at in 0..n {
        let of = |id: u32| if shared[id as usize] { 1 } else { depth[id as usize] };
        depth[at] = match Compiler::operands(graph.nodes[at])[..] {
            [] => 1,
            // A lone operand, and what the instruction works in above it.
            [a] => of(a).max(3),
            [a, b] if matches!(graph.nodes[at], Node::Add(..) | Node::Mul(..)) => {
                if of(a) == of(b) {
                    of(a) + 1
                } else {
                    of(a).max(of(b))
                }
            }
            ref operands => {
                operands
                    .iter()
                    .zip(0..)
                    .map(|(&id, below)| of(id) + below)
                    .max()
                    .unwrap()
                    + 2
            }
        };
    }

    let mut compiler = Compiler {
        graph,
        entry,
        base,
        stored_root,
        stored_ood,
        shared,
        done: vec![false; n],
        depth,
        items: Vec::new(),
    };
    // Not a call of the verifier: calldata of another length, or of another selector, or value.
    compiler.code(&[&[CALLDATASIZE][..], &push_usize(calldata_len), &[XOR]].concat());
    let selector = [
        &[PUSH0, CALLDATALOAD][..],
        &push_usize(224),
        &[SHR],
        &push(&VERIFY),
        &[XOR],
    ];
    compiler.code(&[&selector.concat()[..], &[OR, CALLVALUE, OR]].concat());
    compiler.item(Item::OtherIf);
    for &id in &graph.nonzero {
        compiler.eval(id);
        compiler.code(&[ISZERO]);
        compiler.item(Item::FailIf);
    }
    // The region is fresh memory: a zero word is left as it is, and a run of constants is copied from the code
    // (`CODECOPY` and its three operands, 12 gas and 3 a word) when that is cheaper than a `PUSH` of each nonzero
    // word and of its address, and an `MSTORE` (9 gas).
    let mut data = Vec::new();
    let mut k = 0;
    while k < outputs.len() {
        let run = outputs[k..]
            .iter()
            .take_while(|word| matches!(word, Word::Const(_)))
            .count();
        let constants = || {
            outputs[k..k + run].iter().filter_map(|word| match word {
                Word::Const(bytes) => Some(bytes),
                _ => None,
            })
        };
        let nonzero = constants().filter(|bytes| **bytes != [0; 32]).count();
        if 12 + 3 * run < 9 * nonzero {
            compiler.item(Item::CopyConst {
                first: k,
                words: run,
                data: data.len(),
            });
            constants().for_each(|bytes| data.extend_from_slice(bytes));
            k += run;
            continue;
        }
        match outputs[k] {
            Word::Node(id) => compiler.eval(id),
            Word::Const(bytes) if bytes == [0; 32] => {
                k += 1;
                continue;
            }
            Word::Const(bytes) => compiler.code(&push(&bytes)),
            Word::Calldata(offset) => {
                compiler.calldata(base + offset, 32);
                compiler.code(&[CALLDATALOAD]);
            }
            Word::StoredRoot | Word::StoredOod => {
                k += 1;
                continue;
            }
        }
        compiler.item(Item::Output(k));
        k += 1;
    }
    if let Ending::Declared(claims) = ending {
        evm_link::declared_claims(calldata_len, claims).into_iter().for_each(|item| compiler.item(item));
    }
    for k in [compiler.stored_root, compiler.stored_ood].into_iter().flatten() {
        let written = compiler
            .items
            .iter()
            .any(|(item, _)| matches!(item, Item::Output(at) if *at == k));
        assert!(written, "the seed writes the stored commitment");
    }
    let count = |of: &dyn Fn(Node) -> bool| (0..n).filter(|&at| uses[at] > 0 && of(graph.nodes[at])).count();
    let absorbed = graph.nodes.iter().map(|node| match node {
        Node::Hash(_, _, n) => *n as usize,
        _ => 0,
    });
    Compiled {
        program: Program {
            items: compiler.items,
            data,
            scratch: SEED_SCRATCH.max(32 * (1 + absorbed.max().unwrap_or(0))),
            outputs: outputs.len(),
            ending: match ending {
                Ending::Return => evm_link::Ending::Return,
                Ending::Declared(_) => evm_link::Ending::Attest,
            },
            calldata_len,
        },
        field_muls: count(&|node| matches!(node, Node::Mul(..))),
        hashes: count(&|node| matches!(node, Node::Hash(..) | Node::Seed)),
    }
}

/// `setIndexCommitment(bytes32 root, bytes32 ood)`: revert unless calldata is its selector, `root` and `ood`, with
/// no value, from the owner; else store them. The owner is the word of a `PUSH32`, which the creation code writes.
fn set_index(fail: usize) -> (Vec<u8>, Option<usize>) {
    let mut code = [
        &[JUMPDEST, PUSH0, CALLDATALOAD][..],
        &push_usize(224),
        &[SHR],
        &push(&SET_INDEX),
    ]
    .concat();
    code.extend(
        [
            &[XOR, CALLDATASIZE][..],
            &push_usize(4 + 64),
            &[XOR, OR, CALLVALUE, OR, CALLER, PUSH32],
        ]
        .concat(),
    );
    let owner = code.len();
    code.extend([0; 32]);
    code.extend([&[XOR, OR][..], &push2(fail), &[JUMPI], &push_usize(4), &[CALLDATALOAD]].concat());
    code.extend([&push_usize(INDEX_ROOT_SLOT.into())[..], &[SSTORE]].concat());
    code.extend([&push_usize(36)[..], &[CALLDATALOAD], &push_usize(INDEX_OOD_SLOT.into()), &[SSTORE, STOP]].concat());
    (code, Some(owner))
}

fn options() -> Options<'static> {
    let other: evm_link::Other<'static> = &set_index;
    Options {
        jump_width: 2,
        other: Some(other),
        ..Options::default()
    }
}

/// The contract. A call of the verifier is calldata of the selector ([`VERIFY`]) and the arguments: the statement,
/// the commitments and `inputs` scalars of the proof, of `SCALAR_BYTES` each. On such a call, with no value, it
/// reverts unless every node of `graph.nonzero` is nonzero (checked after the entry's checks), else writes `outputs`
/// to a region of fresh memory, one word each, and ends as `ending` says. Any other call is one of
/// `setIndexCommitment(bytes32 root, bytes32 ood)`, or reverts: from the owner, with no value, it stores them in
/// slots [`INDEX_ROOT_SLOT`] and [`INDEX_OOD_SLOT`] and returns nothing.
pub fn compile(graph: &Graph, outputs: &[Word], ending: &Ending, entry: &Entry, inputs: usize) -> Contract {
    let compiled = program(graph, outputs, ending, entry, inputs);
    let assembled = evm_link::assemble(&compiled.program, &options());
    Contract {
        code: assembled.code,
        owner_at: assembled.other_patch,
        field_muls: compiled.field_muls,
        hashes: compiled.hashes,
        memory_words: assembled.memory_words,
    }
}

/// The creation code of `contract`, which its constructor's arguments follow in the init code: those of
/// `constructor(bytes32 indexRoot, bytes32 indexOod, address owner)`, ABI-encoded (96 bytes) (none for a contract
/// without an owner, a test's). It reverts on value, or on arguments of another length; else it stores `indexRoot`
/// and `indexOod` in slots [`INDEX_ROOT_SLOT`] and [`INDEX_OOD_SLOT`], writes the `owner` word into the code, and
/// returns the code.
pub fn creation_code(contract: &Contract) -> Vec<u8> {
    let runtime = contract.code.len();
    let arguments = if contract.owner_at.is_some() { 96 } else { 0 };
    // The revert is the last 4 bytes of the `prefix` bytes before the code.
    let build = |prefix: usize| {
        let length = [
            &[CODESIZE][..],
            &push2(prefix + runtime + arguments),
            &[XOR, CALLVALUE, OR],
        ]
        .concat();
        let mut code = [&length[..], &push2(prefix - 4), &[JUMPI]].concat();
        // The code and the arguments, to memory at 0.
        code.extend([&push2(runtime + arguments)[..], &push2(prefix), &[PUSH0, CODECOPY]].concat());
        if let Some(owner_at) = contract.owner_at {
            code.extend(
                [
                    &push2(runtime)[..],
                    &[MLOAD],
                    &push_usize(INDEX_ROOT_SLOT.into()),
                    &[SSTORE],
                ]
                .concat(),
            );
            code.extend([&push2(runtime + 32)[..], &[MLOAD], &push_usize(INDEX_OOD_SLOT.into()), &[SSTORE]].concat());
            code.extend([&push2(runtime + 64)[..], &[MLOAD], &push2(owner_at), &[MSTORE]].concat());
        }
        code.extend([&push2(runtime)[..], &[PUSH0, RETURN, JUMPDEST, PUSH0, PUSH0, REVERT]].concat());
        code
    };
    let prefix = build(4).len();
    [build(prefix), contract.code.clone()].concat()
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

    /// The opcodes, the frame's mode and the scheme of PCS claims are the machine's.
    #[test]
    fn opcodes_are_the_machines() {
        use crate::machine as m;
        use evm_link::op;
        assert_eq!(FIELD_MUL, m::FIELD_MUL);
        assert_eq!((op::FRAMEDATALOAD, op::FRAMEPARAM), (m::FRAMEDATALOAD, m::FRAMEPARAM));
        assert_eq!((op::DEP_VERIFY_FRAME_MODE, op::PCS_SCHEME), (m::DEP_VERIFY_FRAME_MODE, m::PCS_SCHEME));
    }
}
