---
title: leanPCS
description: Aggregate polynomial commitment openings and add a MULFIELD instruction, for cheap verification of STARKs onchain
author: TBD
discussions-to: https://ethereum-magicians.org/t/TBD
status: Draft
type: Standards Track
category: Core
created: 2026-11-01
requires: 8141, 8288
---

<!-- WARNING: The field will likely change to 128 bits. -->

## Abstract

This EIP lets a transaction declare PCS claims ("PCS" for "Polynomial Commitment Scheme"), each stating that a committed multilinear polynomial takes a given value at a given point, as [EIP-8288](https://eips.ethereum.org/EIPS/eip-8288) dependencies. Contracts read the declared claims through frame introspection, and the block proves them. This EIP also introduces a new EVM instruction `MULFIELD` that multiplies two elements of the finite field $\mathrm{GF}(2^{192})$. Together, they let users cheaply verify STARKs (aka post-quantum hash-based SNARKs) onchain. All the heavy PCS opening proofs of a block are aggregated into a single STARK.

## Motivation

Today, verifying a pre-quantum SNARK onchain costs about 200,000 gas thanks to the elliptic-curve precompiles. Post-quantum STARKs are much larger, and much more expensive to verify. Recursive aggregation amortizes this cost: a single STARK per block proves all the others. [EIP-8288](https://eips.ethereum.org/EIPS/eip-8288) was initially designed to aggregate whole STARKs, which would require enshrining a new STARK-friendly ISA, such as RISC-V.

STARKs are complicated. The good news is: the majority (in term of proof size and verification time) of a STARK verification is much simpler: it's just PCS openings. With this EIP, Ethereum aggregates the PCS part (big proof size) part, and smart contracts run the rest of the STARK verification in the EVM (small proof size) (this part is called the "polynomial interactive oracle proof" (PIOP)). The PIOP mostly computes a few hashes (for Fiat-Shamir) and does arithmetic in some finite field. We pick binary fields for their simplicity and their state of the art performance. The EVM can already add field elements with `XOR` (`0x18`). For efficient field multiplication, we introduce a new `MULFIELD` EVM instruction.

The goal of this EIP is to get most of the benefits (cheap onchain STARK verification) from [EIP-8288](https://eips.ethereum.org/EIPS/eip-8288) without the complexity of enshrining a new ISA.

## Specification

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be interpreted as described in [RFC 2119](https://www.rfc-editor.org/rfc/rfc2119) and [RFC 8174](https://www.rfc-editor.org/rfc/rfc8174).

| Constant                     | Value  |
|------------------------------|--------|
| `PCS_SCHEME`                 | `0x12` |
| `MAX_PCS_VARIABLES`          | `32`   |
| `PCS_TX_GAS`                 | `5000` |
| `PCS_CLAIM_GAS`              | `1000` |
| `MAX_PCS_CLAIMS_PER_TX`      | `256`  |

The other constants, dependency verification frames, the recursive STARK and mempool wrappers come from EIP-8288.

### Fields

Let $K = \mathrm{GF}(2)[Y] / (Y^{64} + Y^4 + Y^3 + Y + 1)$ and $E = K[X] / (X^3 + X + 1)$. An element of $K$ is encoded as a 64-bit integer whose bit $j$ is the coefficient of $Y^j$. An element $a + bX + cX^2$ of $E$, with $a, b, c \in K$, is encoded as the word `a | (b << 64) | (c << 128)`.

### `MULFIELD`

The instruction `MULFIELD` (`0x1f`) pops `a` and `b`, ignores their top 64 bits, and pushes their product in $E$. It costs 10 gas.

### PCS claims

A PCS claim states that the multilinear polynomial over $K$ in `n` variables committed to as `commitment` takes the value `value` (in $E$) at `point` (in $E^n$), under PCS version `version`:

```
PCS_claim = version (1 byte) || n (1 byte) || commitment (56 bytes) || point (24 * n bytes) || value (24 bytes)
```

Under the hood, `commitment` is a 32-byte Merkle root and a 24-byte out-of-domain answer (in $E$). A PCS claim is well-formed if `version` is supported, `1 <= n <= MAX_PCS_VARIABLES`, and it is `82 + 24 * n` bytes long.

Each PCS version defines a verifier `pcs_verify(PCS_claim, opening_proof)`. We start at version `1`: WHIR at rate 1/2, in the list-decoding regime.

### Dependencies

This EIP replaces the dependency format of EIP-8288, its `(scheme, data_hash, verification_key_hash)` triples and its `LEANSTARK_SCHEME`. A dependency is `scheme (1 byte) || payload`, where the scheme fixes the payload's width:

| `scheme` | `payload` | The dependency holds if |
|---|---|---|
| `LEANSPHINCS_SCHEME` | `msg_hash (32 bytes) \|\| public_key (32 bytes)` | `public_key` signs `msg_hash` with leanSPHINCS |
| `PCS_SCHEME` | `keccak256(PCS_claim)` (32 bytes) | `PCS_claim` holds |

EIP-8288 then applies to dependencies in place of triples:

- **Frames.** A dependency verification frame declares dependencies of one scheme: its `data` is `scheme || payload_0 || ... || payload_{k-1}`, with `1 <= k <= MAX_DEPENDENCIES_PER_FRAME`, and its dependencies are the `scheme || payload_j`.
- **`dependencies(tx)`** is the sorted, deduplicated list of the dependencies of the transaction's frames, where a `msg_hash` of 32 zero bytes stands for `compute_sig_hash(tx)`.
- **`get_deps_hash(deps)`** is `keccak256(concat(deps))`: We use Keccak-256 in place of EIP-8288's `DEPS_HASH`.
- **The recursive STARK** proves a leanSPHINCS dependency from its signature, and a PCS dependency from `(PCS_claim, opening_proof)`: it checks that `PCS_claim` hashes to the payload and that `pcs_verify(PCS_claim, opening_proof)` holds.
- **Gas.** A transaction with `s` leanSPHINCS and `c` PCS dependencies in its frames, duplicates included, pays `LEANSPHINCS_VERIFICATION_GAS * s + PCS_CLAIM_GAS * c`, plus `PCS_TX_GAS` if `c > 0`, as intrinsic gas. Dependency verification frames have `limits.execution = 0`.
- **Mempool.** EIP-8288's limits on leanSPHINCS dependencies stay. `dependencies(tx)` holds at most `MAX_PCS_CLAIMS_PER_TX` PCS dependencies, which travel only in mode 1 wrappers.

### Reading PCS claims

A valid block proves every dependency of its transactions. So a contract can rely on `PCS_claim` if its transaction declares it, which the contract checks in three steps, given a frame index `i` and a payload index `j`:

1. `FRAMEPARAM(0x02, i)` is `DEP_VERIFY_FRAME_MODE`: frame `i` is a dependency verification frame.
2. The first byte of `FRAMEDATALOAD(0, i)` is `PCS_SCHEME`: its dependencies are PCS claims.
3. `FRAMEDATALOAD(1 + 32 * j, i)` is `keccak256(PCS_claim)`: its payload `j` declares `PCS_claim`.

## Rationale

### Benchmarks

Two applications of the reference implementation, with their PIOPs as straight-line EVM contracts and their PCS claims declared in a frame. The PIOP column is the gas of the contract call that verifies the PIOP, with its calldata priced by EIP-7623 and without the 21,000 base cost; the totals add the frame (`1 + 32` bytes a claim) and the PCS intrinsic gas, with calldata priced by EIP-7623 or by [EIP-7976](./eip-7976.md)'s floor of 64 gas a byte.

| Application | Prover (M4 Max) | Calldata | PIOP | PCS claims | Total (EIP-7623) | Total (EIP-7976) |
|---|---|---|---|---|---|---|
| Zero-knowledge membership in a Keccak-256 Merkle tree of depth 32 | 1.7 s | 253 bytes | 18,855 gas | 4 | about 30,000 gas | about 33,000 gas |
| leanVM verification, i.e. any computation thanks to recursion | 2.1 s | 1,005 bytes | 43,819 gas | 7 | about 60,000 gas | about 91,000 gas |

<!-- To reproduce both benchmarks: `sh bench.sh` in the reference implementation (https://github.com/TomWambsgans/leanPCS). -->

### Why a 192-bit field

For a PCS like WHIR, 192 bits is large enough to get provable 128-bit security in the list-decoding regime. TBD: what about a 128-bit field?

### Why `MULFIELD` is an instruction

A STARK verifier does many field multiplications, and a precompile call costs at least 100 gas. CPUs multiply binary polynomials natively, with `PCLMULQDQ` on x86 and `PMULL` on ARM, and a zkEVM can typically use the same finite field in order to make field mutliplication very cheap, hence the choice of only 10 gas. TODO: double check ??

### Why WHIR

WHIR is a state of the art multilinear PCS. WHIR can also be made zero-knowledge by changing only the prover (committing to random masks), so private applications can use the same scheme. A multilinear PCS can easily be transformed into a univariate one (but not vice versa).

### Why a new dependency format

EIP-8288's triples, a statement's hash and a verification key's hash, are made for whole STARKs. Neither scheme here has a verification key. A signature needs its message and public key (64 bytes); a PCS claim needs only its hash (32 bytes), since the contract computes the claim itself.

### Why PCS claims travel only in mode 1 wrappers

The sender aggregates the openings of its transaction client side, into one STARK that it broadcasts in a mode 1 wrapper. The mempool then verifies one STARK, whatever the number of PCS claims. `PCS_TX_GAS` pays for that STARK, once per transaction, and `PCS_CLAIM_GAS` pays for what each PCS claim adds onchain: a dependency of the block, which the block's STARK proves.

### Upgrades

The field cannot change, but the PCS can: a fork can add a version $v + 1$ that brings the latest performance improvements of PCSs. A PCS used for witness commitment can easily use it, without upgrading the old smart contract. Commitments stored in contracts, typically circuit verification keys, can also be migrated (thanks JD):

To migrate a stored commitment `com` to `com'`, a contract derives a random point $r$ from both commitments by Fiat-Shamir, and requires its transaction to declare two PCS claims: `com` under version $v$ and `com'` under version $v + 1$ take the same value $y$ at $r$. If `com` and `com'` commit to different polynomials, this check passes with probability at most $n / 2^{192}$ (Schwartz–Zippel).

## Backwards Compatibility

`MULFIELD` uses the opcode `0x1f`, which was previously undefined: executing it halted exceptionally. This EIP replaces the dependency format, the gas and the `LEANSTARK_SCHEME` of EIP-8288, which is not yet deployed. Nothing changes for existing transactions.

## Test Cases

### `MULFIELD`

| `a` | `b` | `MULFIELD(a, b)` |
|-----|-----|------------------|
| `0x8000000000000000` | `0x2` | `0x1b` |
| `0x10000000000000000` | `0x100000000000000000000000000000000` | `0x10000000000000001` |
| `0x100000000000000000000000000000000` | `0x100000000000000000000000000000000` | `0x100000000000000010000000000000000` |
| `0x0123456789abcdeffedcba98765432100f1e2d3c4b5a6978` | `0x8796a5b4c3d2e1f00123456789abcdef1032547698badcfe` | `0x7da2e3b52de3b3f4793532f0de83952e8394b1a39681a4de` |
| `0xffffffffffffffff000000000000000000000000000000000000000000000002` | `0x8000000000000000` | `0x1b` |

### PCS claims

TBD.

## Reference Implementation

The following Python code implements `MULFIELD`:

```python
def mul_k(a, b):  # multiplication in K
    r = 0
    for i in range(64):
        if (b >> i) & 1:
            r ^= a << i
    for i in range(126, 63, -1):  # reduce by Y^64 + Y^4 + Y^3 + Y + 1
        if (r >> i) & 1:
            r ^= ((1 << 64) | 0b11011) << (i - 64)
    return r

def mulfield(a, b):  # multiplication in E
    x = [(a >> (64 * i)) & (2**64 - 1) for i in range(3)]
    y = [(b >> (64 * i)) & (2**64 - 1) for i in range(3)]
    c = [0] * 5
    for i in range(3):
        for j in range(3):
            c[i + j] ^= mul_k(x[i], y[j])
    for d in (4, 3):  # X^d = X^(d-2) + X^(d-3)
        c[d - 2] ^= c[d]
        c[d - 3] ^= c[d]
    return c[0] | (c[1] << 64) | (c[2] << 128)
```

## Security Considerations

TBD

## Copyright

Copyright and related rights waived via [CC0](../LICENSE.md).
