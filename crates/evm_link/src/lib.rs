// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! A verifier compiled to straight-line EVM code, as one contract.
//!
//! This repository's contracts are not written by hand: a verifier written on a scalar type is run on a scalar that
//! records every operation, and the recorded graph is compiled (`crates/membership/evm`, `crates/leanvm/statement`).
//! The code is straight-line, the cheapest code to run, so it grows with what the verifier computes: the membership
//! verifier is 6,314 bytes, π2's 13.2 KB. This crate takes the compiled program, a list of [`Item`]s (code, and the
//! values kept in memory slots), and assembles it into one contract ([`assemble`]).
//!
//! # Using it from a verifier's code generator
//!
//! A code generator turns its graph into items: for each node, its operands' evaluation, its code (calldata offsets
//! as [`Item::Calldata`]) and a [`Item::Store`] if it is read again; checks with [`Item::FailIf`]; the outputs with
//! [`Item::Output`] and [`Item::CopyConst`] and the checks of the claims declared with [`declared`] (or, in the EIP
//! draft's encoding of a PCS claim, packed from their fields' words, with [`declared_claims`]). [`front`] is such
//! a generator for any graph of nodes whose code works on their operands on the stack ([`front::Dag`]):
//! `crates/leanvm/statement` (`src/evm/codegen.rs`) gives it its nodes' code, entry and outputs. `crates/membership/evm`
//! keeps a generator of its own and calls [`assemble`] the same way. [`creation_code`] deploys a contract.

mod assemble;
pub mod front;
pub mod op;

use assemble::assemble_program;

/// What an item's code computes, for a breakdown of the gas (a protocol's phase).
pub type Tag = &'static str;

/// One step of a straight-line program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Item {
    /// Instructions.
    Code(Vec<u8>),
    /// Keep the value on top of the stack in the node's memory slot too (`DUP1`, its address, `MSTORE`).
    Store(u32),
    /// Push the node's value, kept by an earlier [`Item::Store`].
    Load(u32),
    /// Pop the value into output word `k`.
    Output(usize),
    /// Copy `words` constant words, from `data` on in [`Program::data`], to output words `first` on.
    CopyConst { first: usize, words: usize, data: usize },
    /// With a frame's index on top of the stack: hash `words` output words from `first` on (`KECCAK256`), and revert
    /// unless the hash is payload `index` of that frame, the word at `1 + 32 index` of its `data` (`FRAMEDATALOAD`):
    /// unless the transaction declares the claim these words encode. Pops the index.
    Declared { first: usize, words: usize, index: usize },
    /// With a frame's index on top of the stack: revert unless payload `index` of that frame is `keccak256` of the
    /// PCS claim (the EIP draft's encoding, `crates/pcs_claim`) whose fields are these output words: the root (one
    /// word, its 32 bytes as the claim has them), the out-of-domain answer, the point's `n` coordinates and the value
    /// (elements of `E`, words with their top 64 bits zero). The claim's `82 + 24 n` bytes are packed in the memory
    /// past the outputs, hashed, and compared with `FRAMEDATALOAD(1 + 32 index)`. Pops the index. The words may be
    /// any outputs, in any order (claims may share a point's words).
    DeclaredClaim(ClaimWords),
    /// Push `offset`, where bytes `offset..offset + len` of the call's calldata are, which the code reads.
    Calldata { offset: usize, len: usize },
    /// Pop, and revert if it is nonzero.
    FailIf,
    /// Pop, and jump to the other entry ([`Options::other`]; the revert if there is none) if it is nonzero.
    OtherIf,
}

/// Where a PCS claim's fields are among the outputs, and its payload's index in the frame ([`Item::DeclaredClaim`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimWords {
    pub root: usize,
    pub ood: usize,
    pub point: Vec<usize>,
    pub value: usize,
    pub index: usize,
}

impl ClaimWords {
    /// The claim's bytes: `82 + 24 n`.
    pub fn claim_len(&self) -> usize {
        82 + 24 * self.point.len()
    }

    /// Bytes of memory the packing takes past the outputs: the header's word, the root's, the elements'.
    pub fn buffer(&self) -> usize {
        64 + 24 * (self.point.len() + 2)
    }
}

/// The PCS version a claim's first byte names (the EIP draft's version `1`, `pcs_claim::VERSION`).
pub const PCS_VERSION: u8 = 1;

/// How the program ends, once its outputs are written.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ending {
    /// Return the outputs.
    Return,
    /// Return the word 1 (after its checks of the declared claims passed).
    Attest,
}

/// A straight-line program: what a code generator hands to [`assemble`].
#[derive(Clone, Debug)]
pub struct Program {
    /// Each item, and what its code computes.
    pub items: Vec<(Item, Tag)>,
    /// The constants [`Item::CopyConst`] copies.
    pub data: Vec<u8>,
    /// Bytes of memory, from 0, that the code uses as scratch (hashing); the slots start there.
    pub scratch: usize,
    /// Words of the outputs region.
    pub outputs: usize,
    pub ending: Ending,
    /// The length of calldata, which the program's entry checks.
    pub calldata_len: usize,
}

impl Program {
    /// The data a run of items needs in its code: all of it if it copies any.
    fn data_of(&self, items: &[(Item, Tag)]) -> Vec<u8> {
        let copies = items.iter().any(|(item, _)| matches!(item, Item::CopyConst { .. }));
        if copies { self.data.clone() } else { Vec::new() }
    }

    /// The program's checks, each one `JUMPDEST` in a measuring build.
    pub fn checks(&self) -> usize {
        let checks = |item: &Item| matches!(item, Item::FailIf | Item::Declared { .. } | Item::DeclaredClaim(_));
        self.items.iter().filter(|(item, _)| checks(item)).count()
    }
}

/// Items that push the index of the transaction's frame of PCS claims, which the caller gives as the last byte of the
/// calldata (of `calldata_len` bytes).
pub fn frame_index(calldata_len: usize) -> Vec<Item> {
    use crate::op::{CALLDATALOAD, SHR, push_usize};
    vec![
        Item::Calldata {
            offset: calldata_len - 1,
            len: 1,
        },
        Item::Code([&[CALLDATALOAD][..], &push_usize(248), &[SHR]].concat()),
    ]
}

/// Items that revert unless the frame the caller names ([`frame_index`]) is a dependency verification frame of PCS
/// claims: its mode `DEP_VERIFY_FRAME_MODE` and its first byte `PCS_SCHEME`. Its payloads then declare PCS claims; the
/// same bytes elsewhere (a message hash of a leanSPHINCS frame, which its sender chooses, say) declare nothing.
pub fn pcs_frame_check(calldata_len: usize) -> Vec<Item> {
    use crate::op::*;
    let mut items = frame_index(calldata_len);
    let check = [
        &push_usize(FRAMEPARAM_MODE.into())[..],
        &[DUP2, FRAMEPARAM],
        &push_usize(DEP_VERIFY_FRAME_MODE.into()),
        &[XOR, SWAP1, PUSH0, FRAMEDATALOAD],
        &push_usize(248),
        &[SHR],
        &push_usize(PCS_SCHEME.into()),
        &[XOR, OR],
    ];
    items.push(Item::Code(check.concat()));
    items.push(Item::FailIf);
    items
}

/// Items that revert unless the claim `words` output words from `first` on encode is payload `index` of the frame the
/// caller names. A payload past the frame's `data` reads as zero, which no hash is but with probability `2^-256`.
pub fn declare(calldata_len: usize, first: usize, words: usize, index: usize) -> Vec<Item> {
    let mut items = frame_index(calldata_len);
    items.push(Item::Declared { first, words, index });
    items
}

/// [`pcs_frame_check`], then [`declare`] of these runs of the outputs, back to back, as payloads `0, 1, ...`.
pub fn declared(calldata_len: usize, runs: &[usize]) -> Vec<Item> {
    let mut items = pcs_frame_check(calldata_len);
    let mut first = 0;
    for (index, &words) in runs.iter().enumerate() {
        items.extend(declare(calldata_len, first, words, index));
        first += words;
    }
    items
}

/// Items that revert unless the PCS claim of `words` is payload `words.index` of the frame the caller names.
pub fn declare_claim(calldata_len: usize, words: ClaimWords) -> Vec<Item> {
    let mut items = frame_index(calldata_len);
    items.push(Item::DeclaredClaim(words));
    items
}

/// [`pcs_frame_check`], then [`declare_claim`] of each claim.
pub fn declared_claims(calldata_len: usize, claims: &[ClaimWords]) -> Vec<Item> {
    let mut items = pcs_frame_check(calldata_len);
    for words in claims {
        items.extend(declare_claim(calldata_len, words.clone()));
    }
    items
}

/// The tags of the code the assembler adds.
#[derive(Clone, Copy, Debug)]
pub struct Tags {
    /// A measuring build's `JUMPDEST` after each check.
    pub measure: Tag,
    /// The ending, once the outputs are written.
    pub ending: Tag,
    /// The revert and the data after the code.
    pub tail: Tag,
}

impl Default for Tags {
    fn default() -> Self {
        Self {
            measure: "measurement only (JUMPDEST after each check, subtracted)",
            ending: "ending",
            tail: "revert, data",
        }
    }
}

/// Code the other entry runs: given the revert's address, its bytes, and where in them a word is to be written at
/// deployment (an owner), if anywhere.
pub type Other<'a> = &'a dyn Fn(usize) -> (Vec<u8>, Option<usize>);

/// How code is laid out.
#[derive(Clone, Copy)]
pub struct Options<'a> {
    /// Bytes of a pushed jump destination or code offset: 2 for code under 64 KB, 3 under 16 MB.
    pub jump_width: usize,
    /// A failed check jumps to the instruction after it instead of the revert (a `JUMPDEST`), so that any calldata
    /// runs the whole code: the gas of a valid proof plus one per check.
    pub measure: bool,
    /// The other entry, placed after the code and before the revert.
    pub other: Option<Other<'a>>,
    pub tags: Tags,
}

impl Default for Options<'_> {
    fn default() -> Self {
        Self {
            jump_width: 2,
            measure: false,
            other: None,
            tags: Tags::default(),
        }
    }
}

/// A contract's code.
#[derive(Clone, Debug)]
pub struct Assembled {
    pub code: Vec<u8>,
    /// The tag of each byte.
    pub tags: Vec<Tag>,
    /// Memory it touches, in words.
    pub memory_words: usize,
    /// Where [`Options::other`]'s word to write at deployment is.
    pub other_patch: Option<usize>,
    /// Memory slots it reuses.
    pub slots: usize,
}

/// The program as one contract.
pub fn assemble(program: &Program, options: &Options) -> Assembled {
    assemble_program(program, options)
}

/// The creation code of `runtime`, which the constructor's arguments follow in the init code: one word for each of
/// `slots`, which it stores there. It reverts on value or on arguments of another length, else returns `runtime`.
pub fn creation_code(runtime: &[u8], slots: &[u8]) -> Vec<u8> {
    use crate::op::*;
    let arguments = 32 * slots.len();
    // The revert is the last 4 bytes of the `prefix` bytes before the code.
    let build = |prefix: usize| {
        let length = [
            &[CODESIZE][..],
            &push_fixed(prefix + runtime.len() + arguments, 2),
            &[XOR, CALLVALUE, OR],
        ];
        let mut code = [&length.concat()[..], &push_fixed(prefix - 4, 2), &[JUMPI]].concat();
        // The code and the arguments, to memory at 0.
        let copy = [
            &push_fixed(runtime.len() + arguments, 2)[..],
            &push_fixed(prefix, 2),
            &[PUSH0, CODECOPY],
        ];
        code.extend(copy.concat());
        for (k, &slot) in slots.iter().enumerate() {
            let store = [
                &push_fixed(runtime.len() + 32 * k, 2)[..],
                &[MLOAD],
                &push_usize(slot.into()),
                &[SSTORE],
            ];
            code.extend(store.concat());
        }
        code.extend(
            [
                &push_fixed(runtime.len(), 2)[..],
                &[PUSH0, RETURN, JUMPDEST, PUSH0, PUSH0, REVERT],
            ]
            .concat(),
        );
        code
    };
    let prefix = build(4).len();
    [build(prefix), runtime.to_vec()].concat()
}
