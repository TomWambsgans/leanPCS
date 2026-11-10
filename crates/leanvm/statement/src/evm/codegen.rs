// Adapted from this repository's crates/membership/evm/src/codegen.rs (itself adapted from leanVM
// (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6): the same compilation of
// a recorded graph to straight-line code, a value used once left on the stack and a shared one kept in a memory slot
// reused after its last read; here for leanVM's verifier: the transcript absorbs runs of calldata, a check is of zero
// or of nonzero, commitments come from calldata or storage, every byte of code carries the phase it computes, and a
// measuring build that never reverts. The compilation and the assembly are now `crates/evm_link`'s (`front`, and
// `assemble`), this file the code of each node, the entry and the outputs. MIT OR Apache-2.0; see AGENTS.md.
//! A recorded graph as EVM bytecode, one contract ([`compile`]).

use evm_link::front::{self, Check, Dag, Piece, Source};
pub use evm_link::op::word;
use evm_link::op::{
    AND, CALLDATACOPY, CALLDATALOAD, CALLDATASIZE, CALLVALUE, FIELD_MUL, KECCAK256, MSTORE, OR, PUSH0, SHR, SLOAD, XOR,
    push, push_usize,
};
use evm_link::{Options, Program, Tags};

use crate::evm::record::{Graph, Node};

/// The selector of `verify(bytes32,bytes)`: calldata starting with it is a proof to verify.
pub const VERIFY: [u8; 4] = [0x8e, 0x76, 0x0a, 0xfe];
/// Calldata: the selector, the public input's four 64-bit words (big-endian each, word 0 first), the stream, then a
/// byte, the index of the transaction's frame of PCS claims (a returning contract reads past it).
pub const PUBLIC_INPUT: usize = VERIFY.len();
pub const STREAM: usize = PUBLIC_INPUT + 32;

/// The phases of what is not the verifier's arithmetic.
pub const ENTRY: &str = "entry: selector, length, no value";
pub const CALLS: &str = "claims: written, hashed, checked declared in the frame";
pub const ROOTS: &str = "claims: fixed commitments read (cold SLOAD)";
pub const MEASURE: &str = "measurement only (JUMPDEST after each check, subtracted)";

/// EIP-170's limit on a contract's code.
pub const MAX_CODE: usize = 24_576;

/// How the contract is entered and seeded.
#[derive(Clone, Copy, Debug)]
pub struct Entry {
    /// The transcript's seed hashes this name, the program's IV and the public input.
    pub name: [u8; 16],
    pub iv: [u8; 32],
    /// Bytes of the stream.
    pub stream_len: usize,
    /// A check that fails jumps to the instruction after it instead of the revert, so that any calldata runs the whole
    /// code: the gas of a valid proof plus one (a `JUMPDEST`) per check.
    pub measure: bool,
}

/// A word the contract writes to its output region.
#[derive(Clone, Copy, Debug)]
pub enum Word {
    /// A recorded value.
    Node(u32),
    Const([u8; 32]),
    /// The word of the stream at this byte offset: a root's two 16-byte halves.
    Stream(usize),
    /// The word in this storage slot: a fixed commitment.
    Stored(u8),
}

/// What the contract does with its output region, once written.
pub enum Ending {
    /// Return it.
    Return,
    /// Revert unless the transaction declares the claims these runs of words of it encode, in order and back to back,
    /// as payloads `0, 1, ...` of the frame of PCS claims calldata names ([`evm_link::declared`]); return the word 1.
    Declared(Vec<usize>),
    /// As [`Ending::Declared`], each claim written at the region's start just before it is checked, and only where
    /// the claim before left another word (`evm_link::front::Source::reuse`): claims sharing a point write it once.
    DeclaredReusing(Vec<usize>),
}

/// The graph, with how the contract is seeded: the code of each node.
struct Nodes<'a> {
    graph: &'a Graph,
    entry: &'a Entry,
}

impl Dag for Nodes<'_> {
    fn len(&self) -> usize {
        self.graph.nodes.len()
    }

    fn operands(&self, id: u32) -> Vec<u32> {
        match self.graph.nodes[id as usize] {
            Node::Add(a, b) | Node::Mul(a, b) => vec![a, b],
            Node::Hash(state, _, _) | Node::Low(state) | Node::Narrow(state) | Node::Bits(state, _, _) => vec![state],
            Node::RingWeight(kernel, _) => self.graph.kernels[kernel as usize].clone(),
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
        let read = |offset: usize, len: usize| Piece::Calldata { offset, len };
        match self.graph.nodes[id as usize] {
            Node::Const(limbs) => front::code(push(&word(limbs))),
            Node::Statement(k) => vec![
                read(PUBLIC_INPUT + 8 * k as usize, 32),
                bytes(&[&[CALLDATALOAD], &push_usize(192), &[SHR]]),
            ],
            Node::Input { offset, len } => vec![
                read(STREAM + offset as usize, 32),
                bytes(&[&[CALLDATALOAD], &push_usize(256 - 8 * len as usize), &[SHR]]),
            ],
            Node::Add(..) => front::code(vec![XOR]),
            Node::Mul(..) => front::code(vec![FIELD_MUL]),
            // The name and the IV, as two overlapping words at 0 and 16, then the public input at 48.
            Node::Seed => {
                let head = [&self.entry.name[..], &self.entry.iv[..16]].concat();
                vec![
                    bytes(&[
                        &push(&head),
                        &[PUSH0, MSTORE],
                        &push(&self.entry.iv),
                        &push_usize(16),
                        &[MSTORE],
                        &push_usize(32),
                    ]),
                    read(PUBLIC_INPUT, 32),
                    bytes(&[&push_usize(48), &[CALLDATACOPY], &push_usize(80), &[PUSH0, KECCAK256]]),
                ]
            }
            // The state (evaluated first: its evaluation may hash too) at 0, then the stream's bytes.
            Node::Hash(_, from, to) => {
                let len = (to - from) as usize;
                let mut code = vec![bytes(&[&[PUSH0, MSTORE]])];
                if len > 0 {
                    code.extend([
                        bytes(&[&push_usize(len)]),
                        read(STREAM + from as usize, len),
                        bytes(&[&push_usize(32), &[CALLDATACOPY]]),
                    ]);
                }
                code.push(bytes(&[&push_usize(32 + len), &[PUSH0, KECCAK256]]));
                code
            }
            Node::Low(_) => front::code([&push(&[0xff; 24])[..], &[AND]].concat()),
            Node::Narrow(_) => front::code([&push(&[0xff; 20])[..], &[AND]].concat()),
            Node::RingWeight(_, n) => front::code(crate::evm::kernel::ring_weight_code(n as usize)),
            Node::Bits(_, shift, width) => {
                let mut code = Vec::new();
                if shift > 0 {
                    code.extend(push_usize(shift as usize));
                    code.push(SHR);
                }
                if width < 64 {
                    code.extend(push_usize((1usize << width) - 1));
                    code.push(AND);
                }
                front::code(code)
            }
        }
    }

    fn tag(&self, id: u32) -> Option<&'static str> {
        (!self.is_const(id)).then(|| self.graph.phases[id as usize])
    }
}

/// A contract, and what one call of it executes: its code is straight-line, so every instruction runs once.
pub struct Contract {
    pub code: Vec<u8>,
    /// The phase of each byte of code.
    pub phase_of: Vec<&'static str>,
    pub calldata_len: usize,
    pub field_muls: usize,
    pub xors: usize,
    pub hashes: usize,
    /// Bytes the transcript hashes, the states included.
    pub hashed_bytes: usize,
    pub checks: usize,
    /// Memory it touches, in words.
    pub memory_words: usize,
}

/// The program, and what it computes.
fn program(graph: &Graph, outputs: &[Word], ending: &Ending, entry: &Entry) -> (Program, Stats) {
    let calldata_len = STREAM + entry.stream_len + 1;
    // Not a call of the verifier: calldata of another length, or of another selector, or value.
    let selector = [
        &[CALLDATASIZE][..],
        &push_usize(calldata_len),
        &[XOR, PUSH0, CALLDATALOAD],
        &push_usize(224),
        &[SHR],
        &push(&VERIFY),
        &[XOR, OR, CALLVALUE, OR],
    ];
    let words = outputs
        .iter()
        .map(|word| match *word {
            Word::Node(id) => front::Word::Node(id),
            Word::Const(bytes) => front::Word::Const(bytes),
            Word::Stream(offset) => front::Word::Code(
                vec![
                    Piece::Calldata {
                        offset: STREAM + offset,
                        len: 32,
                    },
                    Piece::Code(vec![CALLDATALOAD]),
                ],
                CALLS,
            ),
            Word::Stored(slot) => {
                front::Word::Code(front::code([&push_usize(slot.into())[..], &[SLOAD]].concat()), ROOTS)
            }
        })
        .collect();
    // Below the slots: the hashing scratch, a state and the longest run of the stream absorbed (and the seed's 80).
    let absorbed = graph.nodes.iter().map(|node| match node {
        Node::Hash(_, from, to) => (to - from) as usize,
        _ => 0,
    });
    let scratch = (32 + absorbed.max().unwrap_or(0)).max(80).next_multiple_of(32);
    // A ring-weight kernel's words, from 0 (the hashing's scratch is free between nodes).
    let kernels = graph.nodes.iter().map(|node| match node {
        Node::RingWeight(_, n) => 32 * crate::evm::kernel::scratch_words(*n as usize),
        _ => 0,
    });
    let scratch = scratch.max(kernels.max().unwrap_or(0));
    let checks = graph.zero.iter().map(|&(id, _)| (id, Check::Zero));
    let source = Source {
        dag: &Nodes { graph, entry },
        entry: selector.concat(),
        entry_tag: ENTRY,
        checks: checks
            .chain(graph.nonzero.iter().map(|&(id, _)| (id, Check::Nonzero)))
            .collect(),
        outputs: words,
        calls: match ending {
            Ending::Return => None,
            Ending::Declared(runs) | Ending::DeclaredReusing(runs) => Some(runs.clone()),
        },
        reuse: matches!(ending, Ending::DeclaredReusing(_)),
        calls_tag: CALLS,
        scratch,
        calldata_len,
    };
    let compiled = front::compile(&source);
    let n = graph.nodes.len();
    let used = |at: usize| compiled.uses[at] > 0;
    let count = |of: &dyn Fn(Node) -> bool| (0..n).filter(|&at| used(at) && of(graph.nodes[at])).count();
    let stats = Stats {
        calldata_len,
        field_muls: count(&|node| matches!(node, Node::Mul(..))),
        xors: count(&|node| matches!(node, Node::Add(..))),
        hashes: count(&|node| matches!(node, Node::Hash(..) | Node::Seed)),
        hashed_bytes: (0..n)
            .filter(|&at| used(at))
            .map(|at| match graph.nodes[at] {
                Node::Hash(_, from, to) => 32 + (to - from) as usize,
                Node::Seed => 80,
                _ => 0,
            })
            .sum(),
        // The entry's, the graph's, and the frame's of PCS claims (`evm_link::pcs_frame_check`), if the program has one.
        checks: graph.zero.len() + graph.nonzero.len() + 1 + usize::from(!matches!(ending, Ending::Return)),
    };
    (compiled.program, stats)
}

struct Stats {
    calldata_len: usize,
    field_muls: usize,
    xors: usize,
    hashes: usize,
    hashed_bytes: usize,
    checks: usize,
}

fn options(measure: bool, jump_width: usize) -> Options<'static> {
    Options {
        jump_width,
        measure,
        other: None,
        tags: Tags {
            measure: MEASURE,
            ending: CALLS,
            tail: ENTRY,
        },
    }
}

/// The contract. A call of it is calldata of the selector, the public input and `entry.stream_len` bytes of stream,
/// with no value. It reverts unless every node of `graph.zero` is zero and every one of `graph.nonzero` nonzero, else
/// writes `outputs` to a region of fresh memory, one word each, and ends as `ending` says.
pub fn compile(graph: &Graph, outputs: &[Word], ending: &Ending, entry: &Entry) -> Contract {
    let (program, stats) = program(graph, outputs, ending, entry);
    let assembled = evm_link::assemble(&program, &options(entry.measure, 3));
    Contract {
        code: assembled.code,
        phase_of: assembled.tags,
        calldata_len: stats.calldata_len,
        field_muls: stats.field_muls,
        xors: stats.xors,
        hashes: stats.hashes,
        hashed_bytes: stats.hashed_bytes,
        checks: stats.checks,
        memory_words: assembled.memory_words,
    }
}
