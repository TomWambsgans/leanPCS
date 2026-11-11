// Part of this repository; the push helpers are moved here from crates/membership/evm/src/codegen.rs (adapted from leanVM
// (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6). MIT OR Apache-2.0; see
// AGENTS.md.
//! The opcodes the generated code uses, `PUSH` of numbers, and the stack effect of straight-line code.

pub const STOP: u8 = 0x00;
/// `FIELD_MUL`, the EIP draft's `MULFIELD` (unassigned on mainnet): the product in `GF(2^192)` of two words' low 192 bits.
pub const FIELD_MUL: u8 = 0x1f;
pub const ISZERO: u8 = 0x15;
pub const AND: u8 = 0x16;
pub const OR: u8 = 0x17;
pub const XOR: u8 = 0x18;
pub const SHL: u8 = 0x1b;
pub const SHR: u8 = 0x1c;
pub const KECCAK256: u8 = 0x20;
pub const CALLER: u8 = 0x33;
pub const CALLVALUE: u8 = 0x34;
pub const CALLDATALOAD: u8 = 0x35;
pub const CALLDATASIZE: u8 = 0x36;
pub const CALLDATACOPY: u8 = 0x37;
pub const CODESIZE: u8 = 0x38;
pub const CODECOPY: u8 = 0x39;
pub const POP: u8 = 0x50;
pub const MLOAD: u8 = 0x51;
pub const MSTORE: u8 = 0x52;
pub const SLOAD: u8 = 0x54;
pub const SSTORE: u8 = 0x55;
pub const JUMPI: u8 = 0x57;
pub const JUMPDEST: u8 = 0x5b;
pub const PUSH0: u8 = 0x5f;
pub const PUSH32: u8 = 0x7f;
pub const DUP1: u8 = 0x80;
pub const DUP2: u8 = 0x81;
pub const SWAP1: u8 = 0x90;
pub const RETURN: u8 = 0xf3;
pub const REVERT: u8 = 0xfd;

/// EIP-8141's `FRAMEDATALOAD`: the word of frame `frameIndex`'s `data` at `offset` (on top), as `CALLDATALOAD`.
pub const FRAMEDATALOAD: u8 = 0xb1;
/// EIP-8141's `FRAMEPARAM`: parameter `param` of frame `frameIndex` (on top).
pub const FRAMEPARAM: u8 = 0xb3;
/// `FRAMEPARAM`'s parameter of a frame's mode.
pub const FRAMEPARAM_MODE: u8 = 0x02;
/// EIP-8288's mode of a dependency verification frame.
pub const DEP_VERIFY_FRAME_MODE: u8 = 4;
/// The scheme of PCS claims, a dependency verification frame's first byte (the EIP draft's `PCS_SCHEME`).
pub const PCS_SCHEME: u8 = 0x12;

/// The revert every failed check jumps to.
pub const REVERT_CODE: [u8; 4] = [JUMPDEST, PUSH0, PUSH0, REVERT];

/// `PUSH` of a big-endian number, in as few bytes as it takes.
pub fn push(bytes: &[u8]) -> Vec<u8> {
    let trimmed = &bytes[bytes.iter().position(|&b| b != 0).unwrap_or(bytes.len())..];
    if trimmed.is_empty() {
        return vec![PUSH0];
    }
    let mut code = vec![PUSH0 + trimmed.len() as u8];
    code.extend_from_slice(trimmed);
    code
}

pub fn push_usize(value: usize) -> Vec<u8> {
    push(&value.to_be_bytes())
}

/// `PUSH` of an address in the code in `width` bytes whatever the address, so that code can be laid out in two
/// passes.
pub fn push_fixed(at: usize, width: usize) -> Vec<u8> {
    assert!(
        (1..=4).contains(&width) && at < 1 << (8 * width),
        "an address of {width} bytes"
    );
    let mut code = vec![PUSH0 + width as u8];
    code.extend_from_slice(&at.to_be_bytes()[8 - width..]);
    code
}

/// A field element as a word: limb 0 lowest.
pub fn word(limbs: [u64; 3]) -> [u8; 32] {
    let mut bytes = [0; 32];
    for (i, limb) in limbs.iter().enumerate() {
        bytes[24 - 8 * i..32 - 8 * i].copy_from_slice(&limb.to_be_bytes());
    }
    bytes
}

/// Code that reverses the bytes within each 16-byte half of the word on top of the stack (stack effect `(1, 1)`):
/// a root as the transcript absorbs it, the two little-endian numbers of its halves (`s_0 · 2^128 + s_1`, a "root
/// word"), to its 32 bytes as a PCS claim encodes them, and back (it is an involution). Four swaps of adjacent groups
/// (bytes, pairs, quads, octets), 132 gas.
pub fn reverse_halves() -> Vec<u8> {
    let mut code = Vec::new();
    for shift in [8usize, 16, 32, 64] {
        // The low `shift` bits of every group of `2 shift`.
        let mut mask = [0u8; 32];
        for (i, byte) in mask.iter_mut().enumerate() {
            let bit = 8 * (31 - i);
            *byte = if bit % (2 * shift) < shift { 0xff } else { 0 };
        }
        let push_mask = [&[PUSH32][..], &mask].concat();
        code.extend([DUP1]);
        code.extend(push_usize(shift));
        code.extend([SHR]);
        code.extend(&push_mask);
        code.extend([AND, SWAP1]);
        code.extend(&push_mask);
        code.extend([AND]);
        code.extend(push_usize(shift));
        code.extend([SHL, OR]);
    }
    code
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pushes_are_as_short_as_the_number() {
        assert_eq!(push_usize(0), [PUSH0]);
        assert_eq!(push_usize(0x80), [0x60, 0x80]);
        assert_eq!(push_usize(0x1234), [0x61, 0x12, 0x34]);
        assert_eq!(push_fixed(0x12, 2), [0x61, 0x00, 0x12]);
        assert_eq!(push_fixed(0x1234, 3), [0x62, 0x00, 0x12, 0x34]);
    }
}
