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
    AND, CALLDATACOPY, CALLDATALOAD, CALLDATASIZE, CALLVALUE, FIELD_MUL, FRAMEDATALOAD, KECCAK256, MSTORE, OR, PUSH0, SHR,
    SLOAD, XOR,
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
#[derive(Clone, Debug)]
pub struct Entry {
    /// The transcript's seed hashes this name, the program's IV and the public input.
    pub name: [u8; 16],
    pub iv: [u8; 32],
    /// Bytes of the stream.
    pub stream_len: usize,
    /// A check that fails jumps to the instruction after it instead of the revert, so that any calldata runs the whole
    /// code: the gas of a valid proof plus one (a `JUMPDEST`) per check.
    pub measure: bool,
    /// Calldata starts with the selector [`VERIFY`] (π1's contracts); without it (π2's, whose only entry is the
    /// verifier: `docs/leanvm/rec/PERF_GAS.md`) the public input is at byte 0, and the length and the value alone are
    /// checked.
    pub selector: bool,
    /// The frame words the seed hashes after the public input, and the statement's words `4 + 4j ..` read: payload
    /// `frame[j]` of the transaction's frame of PCS claims (π2's hashed claims' Keccak-256s; `PERF_GAS.md`).
    pub frame: Vec<u8>,
}

impl Entry {
    /// Where calldata holds the public input.
    pub fn public_input_at(&self) -> usize {
        if self.selector { PUBLIC_INPUT } else { 0 }
    }

    /// Where calldata holds the stream.
    pub fn stream_at(&self) -> usize {
        self.public_input_at() + 32
    }

    /// The code pushing the frame's payload `p` (the frame's index the calldata's last byte).
    fn frame_word(&self, p: u8) -> Vec<Piece> {
        let last = self.stream_at() + self.stream_len;
        vec![
            Piece::Calldata { offset: last, len: 1 },
            Piece::Code([&[CALLDATALOAD][..], &push_usize(248), &[SHR], &push_usize(1 + 32 * p as usize), &[FRAMEDATALOAD]].concat()),
        ]
    }
}

/// A word the contract writes to its output region.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Word {
    /// A recorded value.
    Node(u32),
    Const([u8; 32]),
    /// The word of the stream at this byte offset: a root's two 16-byte halves.
    Stream(usize),
    /// The word in this storage slot: a fixed commitment.
    Stored(u8),
}

/// A PCS claim (the EIP draft's, `crates/pcs_claim`) as the contract has its fields: the commitment's root (its 32
/// bytes as the claim has them), its out-of-domain answer, the point's coordinates and the value (elements, words with
/// their top 64 bits zero).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim {
    pub root: Word,
    pub ood: Word,
    pub point: Vec<Word>,
    pub value: Word,
}

impl Claim {
    /// Its fields in the claim's order: the root, the out-of-domain answer, the point, the value.
    pub fn words(&self) -> Vec<Word> {
        [self.root, self.ood].into_iter().chain(self.point.iter().copied()).chain([self.value]).collect()
    }
}

/// What the contract does once its checks pass.
pub enum Ending {
    /// Write the outputs and return them.
    Return,
    /// Revert unless the transaction declares these claims, in order, as payloads `0, 1, ...` of the frame of PCS
    /// claims calldata names (`evm_link::declared_claims`); return the word 1. Their fields are written once each
    /// (claims sharing a point's coordinates write them once).
    Claims(Vec<Claim>),
    /// [`Ending::Claims`], each claim the payload of the index beside it.
    ClaimsAt(Vec<(usize, Claim)>),
}

/// The distinct words of `claims`, in first appearance, and each claim's fields as indices of them (payloads `0, 1, …`).
pub fn claim_outputs(claims: &[Claim]) -> (Vec<Word>, Vec<evm_link::ClaimWords>) {
    let indexed: Vec<(usize, Claim)> = claims.iter().cloned().enumerate().collect();
    claim_outputs_at(&indexed)
}

/// [`claim_outputs`], each claim the payload of the index beside it.
pub fn claim_outputs_at(claims: &[(usize, Claim)]) -> (Vec<Word>, Vec<evm_link::ClaimWords>) {
    let mut words: Vec<Word> = Vec::new();
    let mut at = |w: Word| match words.iter().position(|&x| x == w) {
        Some(k) => k,
        None => {
            words.push(w);
            words.len() - 1
        }
    };
    let fields = claims
        .iter()
        .map(|&(index, ref c)| evm_link::ClaimWords {
            root: at(c.root),
            ood: at(c.ood),
            point: c.point.iter().map(|&w| at(w)).collect(),
            value: at(c.value),
            index,
        })
        .collect();
    (words, fields)
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
            Node::Hash(state, _, _)
            | Node::Low(state)
            | Node::Narrow(state)
            | Node::Wide(state, _)
            | Node::Bits(state, _, _) => vec![state],
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
            Node::Statement(k) if k < 4 => vec![
                read(self.entry.public_input_at() + 8 * k as usize, 32),
                bytes(&[&[CALLDATALOAD], &push_usize(192), &[SHR]]),
            ],
            // A frame word's 64-bit word: payload `frame[j]`, its bytes `8l..8l+8`.
            Node::Statement(k) => {
                let (j, l) = ((k as usize - 4) / 4, (k as usize - 4) % 4);
                let mut code = self.entry.frame_word(self.entry.frame[j]);
                code.push(bytes(&[&push_usize(64 * (3 - l)), &[SHR]]));
                code.push(bytes(&[&push(&[0xff; 8]), &[AND]]));
                code
            }
            Node::Input { offset, len } => vec![
                read(self.entry.stream_at() + offset as usize, 32),
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
                    read(self.entry.public_input_at(), 32),
                    bytes(&[&push_usize(48), &[CALLDATACOPY]]),
                ]
                .into_iter()
                .chain(self.entry.frame.iter().enumerate().flat_map(|(j, &p)| {
                    let mut code = self.entry.frame_word(p);
                    code.push(bytes(&[&push_usize(80 + 32 * j), &[MSTORE]]));
                    code
                }))
                .chain([bytes(&[&push_usize(80 + 32 * self.entry.frame.len()), &[PUSH0, KECCAK256]])])
                .collect()
            }
            // The state (evaluated first: its evaluation may hash too) at 0, then the stream's bytes.
            Node::Hash(_, from, to) => {
                let len = (to - from) as usize;
                let mut code = vec![bytes(&[&[PUSH0, MSTORE]])];
                if len > 0 {
                    code.extend([
                        bytes(&[&push_usize(len)]),
                        read(self.entry.stream_at() + from as usize, len),
                        bytes(&[&push_usize(32), &[CALLDATACOPY]]),
                    ]);
                }
                code.push(bytes(&[&push_usize(32 + len), &[PUSH0, KECCAK256]]));
                code
            }
            Node::Low(_) => front::code([&push(&[0xff; 24])[..], &[AND]].concat()),
            Node::Narrow(_) => front::code([&push(&[0xff; 20])[..], &[AND]].concat()),
            // KECCAK256 gives the digest alone, not the sponge's rate: π1-rec4 has no contract (it runs in π2's circuit).
            Node::Wide(..) => panic!("a wide challenge has no EVM code (π1-rec4 has no contract of its own)"),
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
    let calldata_len = entry.stream_at() + entry.stream_len + 1;
    // Not a call of the verifier: calldata of another length, or of another selector, or value.
    let selector = if entry.selector {
        [
            &[CALLDATASIZE][..],
            &push_usize(calldata_len),
            &[XOR, PUSH0, CALLDATALOAD],
            &push_usize(224),
            &[SHR],
            &push(&VERIFY),
            &[XOR, OR, CALLVALUE, OR],
        ]
        .concat()
    } else {
        [&[CALLDATASIZE][..], &push_usize(calldata_len), &[XOR, CALLVALUE, OR]].concat()
    };
    let (outputs, claims) = match ending {
        Ending::Return => (outputs.to_vec(), Vec::new()),
        Ending::Claims(claims) => {
            assert!(outputs.is_empty(), "a contract checking claims writes their fields alone");
            claim_outputs(claims)
        }
        Ending::ClaimsAt(claims) => {
            assert!(outputs.is_empty(), "a contract checking claims writes their fields alone");
            claim_outputs_at(claims)
        }
    };
    let words = outputs
        .iter()
        .map(|word| match *word {
            Word::Node(id) => front::Word::Node(id),
            Word::Const(bytes) => front::Word::Const(bytes),
            Word::Stream(offset) => front::Word::Code(
                vec![
                    Piece::Calldata {
                        offset: entry.stream_at() + offset,
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
    let scratch = (32 + absorbed.max().unwrap_or(0)).max(80 + 32 * entry.frame.len()).next_multiple_of(32);
    // A ring-weight kernel's words, from 0 (the hashing's scratch is free between nodes).
    let kernels = graph.nodes.iter().map(|node| match node {
        Node::RingWeight(_, n) => 32 * crate::evm::kernel::scratch_words(*n as usize),
        _ => 0,
    });
    let scratch = scratch.max(kernels.max().unwrap_or(0));
    let checks = graph.zero.iter().map(|&(id, _)| (id, Check::Zero));
    let source = Source {
        dag: &Nodes { graph, entry },
        entry: selector,
        entry_tag: ENTRY,
        checks: checks
            .chain(graph.nonzero.iter().map(|&(id, _)| (id, Check::Nonzero)))
            .collect(),
        outputs: words,
        calls: None,
        claims,
        reuse: false,
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
                // The name and IV's head, the public input and the frame words the seed reads (`Node::Seed`).
                Node::Seed => 80 + 32 * entry.frame.len(),
                _ => 0,
            })
            .sum(),
        // The entry's, the graph's, and the frame's of PCS claims (`evm_link::pcs_frame_check`), if the program has one
        // (each claim's check is a check of its own, `Program::checks`).
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

/// The contract. A call of it is calldata of the selector (if `entry.selector`), the public input and `entry.stream_len` bytes of stream,
/// with no value. It reverts unless every node of `graph.zero` is zero and every one of `graph.nonzero` nonzero, else
/// writes `outputs` to a region of fresh memory, one word each, and returns them ([`Ending::Return`]), or checks the
/// claims declared ([`Ending::Claims`], `outputs` empty).
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
