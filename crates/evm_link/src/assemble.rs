// Part of this repository; the assembly of a straight-line program (values kept in memory slots reused after their
// last read, one revert, constants copied from the code, since then the checks of declared PCS claims) is moved here from
// crates/membership/evm/src/codegen.rs (adapted from leanVM (https://github.com/leanEthereum/leanVM), branch
// PCS-openings-aggregation, commit 651453c6) and crates/leanvm_statement/src/evm/codegen.rs, unchanged. MIT OR
// Apache-2.0; see AGENTS.md.
//! A program's code, as one contract.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};

use crate::op::*;
use crate::{Assembled, Ending, Item, Options, Program, Tag};

/// Where the program keeps what it computes, once its slots are allocated.
struct Layout {
    /// The slot of each node kept in memory, by id.
    slot: HashMap<u32, usize>,
    slots: usize,
    /// Where the outputs start, after the slots.
    region: usize,
}

fn allocate(program: &Program) -> Layout {
    // A slot is free again after its node's last read.
    let mut reads: HashMap<u32, u32> = HashMap::new();
    for (item, _) in &program.items {
        if let Item::Load(id) = item {
            *reads.entry(*id).or_default() += 1;
        }
    }
    let mut slot = HashMap::new();
    let (mut free, mut n_slots) = (BinaryHeap::new(), 0);
    for (item, _) in &program.items {
        match item {
            Item::Store(id) => {
                let s = free.pop().map_or_else(
                    || {
                        n_slots += 1;
                        n_slots - 1
                    },
                    |Reverse(s)| s,
                );
                slot.insert(*id, s);
            }
            Item::Load(id) => {
                assert!(slot.contains_key(id), "node {id} is read before it is kept");
                let left = reads.get_mut(id).expect("a read");
                *left -= 1;
                if *left == 0 {
                    free.push(Reverse(slot[id]));
                }
            }
            _ => {}
        }
    }
    Layout {
        slot,
        slots: n_slots,
        region: program.scratch + 32 * n_slots,
    }
}

/// The program's code, and the lengths it was laid out with.
pub(crate) fn assemble_program(program: &Program, options: &Options) -> Assembled {
    let layout = allocate(program);
    let w = options.jump_width;
    let address = |id: u32| -> usize { program.scratch + 32 * layout.slot[&id] };
    let returned = layout.region;
    // Where declared PCS claims are packed to be hashed: past the outputs.
    let pack = returned + 32 * program.outputs;
    let buffer = (program.items.iter())
        .filter_map(|(item, _)| match item {
            Item::DeclaredClaim(words) => Some(words.buffer()),
            _ => None,
        })
        .max()
        .unwrap_or(0);
    let tags = &options.tags;

    // `other`: the other entry; `fail`: the revert; `data_at`: the constants.
    let lay = |other: usize, fail: usize, data_at: usize| {
        let mut code: Vec<u8> = Vec::new();
        let mut tag_of: Vec<Tag> = Vec::new();
        let put = |code: &mut Vec<u8>, tag_of: &mut Vec<Tag>, bytes: &[u8], tag: Tag| {
            code.extend_from_slice(bytes);
            tag_of.resize(code.len(), tag);
        };
        // A check: jump to the revert if the top of the stack is nonzero, or, measuring, to the next instruction.
        let check_at = |code: &mut Vec<u8>, tag_of: &mut Vec<Tag>, tag: Tag| {
            if options.measure {
                let next = code.len() + w + 2;
                code.extend([&push_fixed(next, w)[..], &[JUMPI]].concat());
                tag_of.resize(code.len(), tag);
                code.push(JUMPDEST);
                tag_of.resize(code.len(), tags.measure);
            } else {
                code.extend([&push_fixed(fail, w)[..], &[JUMPI]].concat());
                tag_of.resize(code.len(), tag);
            }
        };
        for (item, tag) in &program.items {
            let tag = *tag;
            match *item {
                Item::Code(ref bytes) => put(&mut code, &mut tag_of, bytes, tag),
                Item::Store(id) => put(
                    &mut code,
                    &mut tag_of,
                    &[&[DUP1][..], &push_usize(address(id)), &[MSTORE]].concat(),
                    tag,
                ),
                Item::Load(id) => put(
                    &mut code,
                    &mut tag_of,
                    &[&push_usize(address(id))[..], &[MLOAD]].concat(),
                    tag,
                ),
                Item::Output(k) => put(
                    &mut code,
                    &mut tag_of,
                    &[&push_usize(returned + 32 * k)[..], &[MSTORE]].concat(),
                    tag,
                ),
                Item::Calldata { offset, .. } => put(&mut code, &mut tag_of, &push_usize(offset), tag),
                Item::CopyConst { first, words, data } => {
                    let bytes = [
                        &push_usize(32 * words)[..],
                        &push_fixed(data_at + data, w),
                        &push_usize(returned + 32 * first),
                        &[CODECOPY],
                    ];
                    put(&mut code, &mut tag_of, &bytes.concat(), tag);
                }
                // The frame's index on the stack: the claim's bytes packed past the outputs, at `pack + 30`: the
                // header `VERSION || n` (the low two bytes of the word at `pack`), the root (the word at `pack + 32`),
                // then each element's low 24 bytes, from `pack + 64` on. An element's word is stored 8 bytes before
                // its place, so its top 8 zero bytes land on the previous element's tail: the elements are stored
                // last first, then the root (over the first element's 8 zero bytes), then the header.
                Item::DeclaredClaim(ref words) => {
                    let n = words.point.len();
                    let mut bytes = Vec::new();
                    let elements: Vec<usize> = [words.ood]
                        .into_iter()
                        .chain(words.point.iter().copied())
                        .chain([words.value])
                        .collect();
                    for (k, &at) in elements.iter().enumerate().rev() {
                        bytes.extend(push_usize(returned + 32 * at));
                        bytes.push(MLOAD);
                        bytes.extend(push_usize(pack + 64 + 24 * k - 8));
                        bytes.push(MSTORE);
                    }
                    bytes.extend(push_usize(returned + 32 * words.root));
                    bytes.push(MLOAD);
                    bytes.extend(push_usize(pack + 32));
                    bytes.push(MSTORE);
                    bytes.extend(push_usize(((crate::wire::VERSION as usize) << 8) | n));
                    bytes.extend(push_usize(pack));
                    bytes.push(MSTORE);
                    bytes.extend(push_usize(words.claim_len()));
                    bytes.extend(push_usize(pack + 30));
                    bytes.extend([KECCAK256, SWAP1]);
                    bytes.extend(push_usize(1 + 32 * words.index));
                    bytes.extend([FRAMEDATALOAD, XOR]);
                    put(&mut code, &mut tag_of, &bytes, tag);
                    check_at(&mut code, &mut tag_of, tag);
                }
                Item::FailIf => check_at(&mut code, &mut tag_of, tag),
                Item::OtherIf => put(
                    &mut code,
                    &mut tag_of,
                    &[&push_fixed(other, w)[..], &[JUMPI]].concat(),
                    tag,
                ),
            }
        }
        let tail = match program.ending {
            Ending::Return => [&push_usize(32 * program.outputs)[..], &push_usize(returned), &[RETURN]].concat(),
            // The word 1, which an account without code does not return.
            Ending::Attest => [&push_usize(1)[..], &[PUSH0, MSTORE], &push_usize(32), &[PUSH0, RETURN]].concat(),
        };
        put(&mut code, &mut tag_of, &tail, tags.ending);
        (code, tag_of)
    };
    let body = lay(0, 0, 0).0.len();
    let tail_len = options.other.map_or(0, |other| other(0).0.len());
    let fail = body + tail_len;
    let other = if options.other.is_some() { body } else { fail };
    let (mut code, mut tag_of) = lay(other, fail, fail + REVERT_CODE.len());
    let mut other_patch = None;
    if let Some(make) = options.other {
        let (tail, patch) = make(fail);
        other_patch = patch.map(|at| code.len() + at);
        code.extend(tail);
    }
    code.extend(REVERT_CODE);
    code.extend_from_slice(&program.data_of(&program.items));
    tag_of.resize(code.len(), tags.tail);
    Assembled {
        code,
        tags: tag_of,
        memory_words: (pack + buffer).div_ceil(32),
        other_patch,
        slots: layout.slots,
    }
}
