// Part of this repository; moved here from crates/leanvm_statement/src/evm/codegen.rs, itself adapted from this
// repository's crates/membership/evm/src/codegen.rs (adapted from leanVM (https://github.com/leanEthereum/leanVM), branch
// PCS-openings-aggregation, commit 651453c6): the compilation of a recorded graph to straight-line code, a value used
// once left on the stack and a shared one kept in a memory slot, the deeper operand evaluated first; here for any graph
// whose nodes' code works on their operands on the stack. MIT OR Apache-2.0; see
// AGENTS.md.
//! A recorded graph as a straight-line [`Program`].
//!
//! A node's value is computed where it is first needed, from its operands' values on the stack: a value read once is
//! left there for its reader, one read more than once is also kept in a memory slot ([`Item::Store`]) and read from it
//! after ([`Item::Load`]). The program checks the values it must (zero, or nonzero), then writes its outputs, then ends:
//! it returns them, or checks that the transaction declares the PCS claims whose fields they are and returns the word
//! 1.

use crate::{Ending, Item, Program, Tag};

/// A piece of a node's code: instructions, a push of a calldata offset, or a write of an output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Piece {
    Code(Vec<u8>),
    /// Push the offset of bytes `offset..offset + len` of the call's calldata, which the code reads (`len`: 32 for a
    /// `CALLDATALOAD`, the length of a `CALLDATACOPY`).
    Calldata {
        offset: usize,
        len: usize,
    },
    /// Pop the word on top into output word `k` ([`Word::Written`]): a word the node's code reads on its way (a
    /// commitment loaded from storage for the seed, and a claim's field).
    Output(usize),
}

/// Code of instructions only.
pub fn code(bytes: Vec<u8>) -> Vec<Piece> {
    vec![Piece::Code(bytes)]
}

/// A recorded graph: nodes, each after its operands.
pub trait Dag {
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// The node's operands, which its code finds on the stack, the last on top. A node of two equal operands is
    /// computed from one (its value duplicated).
    fn operands(&self, id: u32) -> Vec<u32>;
    /// Whether its two operands may be evaluated in either order: then the deeper is evaluated first.
    fn commutative(&self, id: u32) -> bool;
    fn is_const(&self, id: u32) -> bool;
    /// Its code, run with its operands on the stack, leaving its value instead.
    fn code(&self, id: u32) -> Vec<Piece>;
    /// What it computes, for the breakdown of the gas; a constant's is its reader's (`None`).
    fn tag(&self, id: u32) -> Option<Tag>;
    /// Stack words its code takes above a lone operand, for the order of evaluation.
    fn work(&self, _id: u32) -> u32 {
        4
    }
}

/// What the program requires of a value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Check {
    Zero,
    Nonzero,
}

/// A word the program writes to its outputs region.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Word {
    /// A recorded value.
    Node(u32),
    Const([u8; 32]),
    /// Code that pushes the word (from calldata, or storage), and what it computes.
    Code(Vec<Piece>, Tag),
    /// A word a node's code writes itself ([`Piece::Output`]): nothing is written for it here.
    Written,
}

/// What a program is compiled from.
pub struct Source<'a, D> {
    pub dag: &'a D,
    /// Code leaving one word, nonzero unless the call is one of the verifier: it reverts then, or with `entry_other`
    /// jumps to the other entry ([`crate::Options::other`]).
    pub entry: Vec<u8>,
    pub entry_other: bool,
    pub entry_tag: Tag,
    pub checks: Vec<(u32, Check)>,
    pub outputs: Vec<Word>,
    /// Checks that the transaction declares these PCS claims (the EIP draft's encoding, [`crate::declared_claims`]),
    /// their fields any of the outputs, as payloads `claims[j].index` of the frame of PCS claims the caller names in
    /// the last byte of calldata, then the word 1 returned; or (none) the outputs returned.
    pub claims: Vec<crate::ClaimWords>,
    /// The tag of the outputs written and of the claims' checks.
    pub outputs_tag: Tag,
    /// Bytes of memory the nodes' code uses as scratch, from 0.
    pub scratch: usize,
    pub calldata_len: usize,
}

/// A compiled program, and how often each node is read.
pub struct Compiled {
    pub program: Program,
    /// Reads of each node, a check or an output being one; zero for a node nothing needs.
    pub uses: Vec<u32>,
}

struct Compiler<'a, D> {
    dag: &'a D,
    shared: Vec<bool>,
    done: Vec<bool>,
    depth: Vec<u32>,
    items: Vec<(Item, Tag)>,
    tag: Tag,
}

/// The operands a node is computed from: one, for two equal ones.
fn operands_of<D: Dag>(dag: &D, id: u32) -> Vec<u32> {
    match dag.operands(id)[..] {
        [a, b] if a == b => vec![a],
        ref operands => operands.to_vec(),
    }
}

impl<D: Dag> Compiler<'_, D> {
    fn code(&mut self, bytes: Vec<u8>) {
        self.items.push((Item::Code(bytes), self.tag));
    }

    fn pieces(&mut self, pieces: Vec<Piece>) {
        for piece in pieces {
            match piece {
                Piece::Code(bytes) => self.code(bytes),
                Piece::Calldata { offset, len } => self.item(Item::Calldata { offset, len }),
                Piece::Output(k) => self.item(Item::Output(k)),
            }
        }
    }

    fn item(&mut self, item: Item) {
        self.items.push((item, self.tag));
    }

    /// Leave the node's value on the stack.
    fn eval(&mut self, id: u32) {
        let at = id as usize;
        // Reading a value kept in memory, or pushing a constant, is its reader's.
        if self.shared[at] && self.done[at] {
            self.item(Item::Load(id));
            return;
        }
        let tag = self.dag.tag(id).unwrap_or(self.tag);
        let outer = std::mem::replace(&mut self.tag, tag);
        let operands = self.dag.operands(id);
        match operands[..] {
            [a, b] if a == b => {
                self.eval(a);
                self.code(vec![crate::op::DUP1]);
            }
            // The deeper operand first, so the other is evaluated over one word, not under many.
            [a, b] if self.dag.commutative(id) && self.depth[a as usize] < self.depth[b as usize] => {
                self.eval(b);
                self.eval(a);
            }
            _ => operands.iter().for_each(|&operand| self.eval(operand)),
        }
        self.pieces(self.dag.code(id));
        if self.shared[at] {
            self.done[at] = true;
            self.item(Item::Store(id));
        }
        self.tag = outer;
    }

    /// Leave an output word on the stack.
    fn word(&mut self, word: &Word, outputs_tag: Tag) {
        match word {
            &Word::Node(id) => self.eval(id),
            Word::Const(bytes) => self.code(crate::op::push(bytes)),
            Word::Code(pieces, tag) => {
                self.tag = tag;
                self.pieces(pieces.clone());
            }
            Word::Written => unreachable!("a word a node writes"),
        }
        self.tag = outputs_tag;
    }
}

/// The program `source` describes.
pub fn compile<D: Dag>(source: &Source<D>) -> Compiled {
    let dag = source.dag;
    let n = dag.len();
    let mut uses = vec![0u32; n];
    let output_nodes = source.outputs.iter().filter_map(|word| match *word {
        Word::Node(id) => Some(id),
        _ => None,
    });
    for root in source.checks.iter().map(|&(id, _)| id).chain(output_nodes) {
        uses[root as usize] += 1;
    }
    for at in (0..n).rev() {
        if uses[at] > 0 {
            for operand in operands_of(dag, at as u32) {
                uses[operand as usize] += 1;
            }
        }
    }
    let shared: Vec<bool> = (0..n).map(|at| uses[at] > 1 && !dag.is_const(at as u32)).collect();
    let mut depth = vec![1u32; n];
    for at in 0..n {
        let of = |id: u32| if shared[id as usize] { 1 } else { depth[id as usize] };
        let operands = operands_of(dag, at as u32);
        depth[at] = match operands[..] {
            [] => 1,
            // A lone operand, and what the instruction works in above it.
            [a] => of(a).max(dag.work(at as u32)),
            [a, b] if dag.commutative(at as u32) => {
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
        dag,
        shared,
        done: vec![false; n],
        depth,
        items: Vec::new(),
        tag: source.entry_tag,
    };
    compiler.code(source.entry.clone());
    compiler.item(if source.entry_other { Item::OtherIf } else { Item::FailIf });
    for &(id, check) in &source.checks {
        compiler.eval(id);
        compiler.tag = dag.tag(id).unwrap_or(source.entry_tag);
        if check == Check::Nonzero {
            compiler.code(vec![crate::op::ISZERO]);
        }
        compiler.item(Item::FailIf);
    }
    compiler.tag = source.outputs_tag;
    // The region is fresh memory: a zero word is left as it is, and a run of constants is copied from the code
    // (`CODECOPY` and its three operands, 12 gas and 3 a word) when that is cheaper than a `PUSH` of each nonzero
    // word and of its address, and an `MSTORE` (9 gas).
    let outputs = &source.outputs;
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
        if outputs[k] != Word::Written && outputs[k] != Word::Const([0; 32]) {
            compiler.word(&outputs[k], source.outputs_tag);
            compiler.item(Item::Output(k));
        }
        k += 1;
    }
    for (k, _) in outputs.iter().enumerate().filter(|(_, word)| **word == Word::Written) {
        let written = compiler.items.iter().any(|(item, _)| *item == Item::Output(k));
        assert!(written, "output {k} is written by a node's code");
    }
    if !source.claims.is_empty() {
        let fields = |c: &crate::ClaimWords| c.words().into_iter().max();
        assert!(
            source.claims.iter().filter_map(fields).all(|k| k < outputs.len()),
            "a claim's fields are outputs"
        );
        crate::declared_claims(source.calldata_len, &source.claims).into_iter().for_each(|item| compiler.item(item));
    }
    Compiled {
        program: Program {
            items: compiler.items,
            data,
            scratch: source.scratch,
            outputs: outputs.len(),
            ending: if source.claims.is_empty() { Ending::Return } else { Ending::Attest },
            calldata_len: source.calldata_len,
        },
        uses,
    }
}
