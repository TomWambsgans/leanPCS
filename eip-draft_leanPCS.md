---
title: leanPCS
description: Cheap verification of STARKs thanks to aggregation of PCS openings and a new MULFIELD instruction
author: Greg Hirsch
discussions-to: https://ethereum-magicians.org/t/TBD
status: Draft
type: Standards Track
category: Core
created: 2026-11-01
requires: 8141, 8288
---

## Abstract

This EIP lets a transaction declare PCS claims ("PCS" for "Polynomial Commitment Scheme"), each stating that a committed multilinear polynomial takes a given value at a given point, as [EIP-8288](./eip-8288.md) dependencies of [EIP-8141](./eip-8141.md) frame transactions. Contracts read the declared claims through frame introspection, and the block proves them. This EIP also introduces a new EVM instruction `MULFIELD` that multiplies two elements of the finite field $\mathrm{GF}(2^{192})$. Together, they let users cheaply verify STARKs (post-quantum, hash-based SNARKs) onchain. All the heavy PCS opening proofs of a block are aggregated into a single STARK.

## Motivation

Today, verifying a pre-quantum SNARK onchain costs about 200,000 gas thanks to the elliptic-curve precompiles. Post-quantum STARKs are much larger, and much more expensive to verify. Recursive aggregation amortizes this cost: a single STARK per block proves all the others. [EIP-8288](./eip-8288.md) was initially designed to aggregate whole STARKs, which would require enshrining a STARK-friendly ISA such as RISC-V.

Most of a STARK verification, in proof size and in verification time, is simply PCS openings. With this EIP, Ethereum aggregates this heavy part, and smart contracts run the cheap remaining part of the STARK verification in the EVM. This rest is called the "polynomial interactive oracle proof" (PIOP). The PIOP mostly computes a few hashes (for Fiat-Shamir) and does arithmetic in some finite field. We pick binary fields for their simplicity and their state of the art performance. The EVM can already add field elements with `XOR` (`0x18`). For efficient field multiplication, we introduce a new `MULFIELD` EVM instruction.

The goal of this EIP is to get most of the benefits (cheap onchain STARK verification) from [EIP-8288](./eip-8288.md) without the complexity of enshrining a new ISA.


## WARNING (TODO delete this)

- The field GF(2^192) will soon be replaced by GF(2^128). TLDR: it will further improve performance, with the same security.
- I am not a frame expert
- Gas pricing is not finalized

## Specification

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be interpreted as described in [RFC 2119](https://www.rfc-editor.org/rfc/rfc2119) and [RFC 8174](https://www.rfc-editor.org/rfc/rfc8174).

| Constant                     | Value  |
|------------------------------|--------|
| `PCS_SCHEME`                 | `0x12` |
| `MAX_PCS_VARIABLES`          | `32`   |
| `PCS_TX_GAS`                 | `5000` |
| `PCS_CLAIM_GAS`              | `1000` |
| `MAX_PCS_CLAIMS_PER_TX`      | `256`  |

The other constants, dependency verification frames, the recursive STARK and mempool wrappers come from EIP-8288, and frame transactions, `FRAMEPARAM` and `FRAMEDATALOAD` from EIP-8141.

### Fields

Let $K = \mathrm{GF}(2)[Y] / (Y^{64} + Y^4 + Y^3 + Y + 1)$ and $E = K[X] / (X^3 + X + 1)$. An element of $K$ is encoded as a 64-bit integer whose bit $j$ is the coefficient of $Y^j$. An element $a + bX + cX^2$ of $E$, with $a, b, c \in K$, is encoded as the word `a | (b << 64) | (c << 128)`, and in bytes as that word's low 24 bytes, big-endian.

### `MULFIELD`

The instruction `MULFIELD` (`0x1f`) pops `a` (the top of the stack) and then `b`, ignores their top 64 bits, and pushes their product in $E$ (the product is commutative, so the order does not matter). It costs 10 gas.

### PCS claims

A PCS claim states that the multilinear polynomial $f$ over $K$ in `n` variables committed to as `commitment` takes the value `value` (in $E$) at `point` (in $E^n$), under PCS version `version`:

```
PCS_claim = version (1 byte) || n (1 byte) || commitment (56 bytes) || point_0 || ... || point_{n-1} (24 bytes each) || value (24 bytes)
```

- **The polynomial.** $f(x) = \sum_i f_i \prod_j \ell_j(i, x)$, where $f_i \in K$ is the $i$-th of the $2^n$ committed values, and $\ell_j(i, x)$ is $x_j$ if bit $j$ of $i$ is 1 and $1 - x_j$ otherwise (bit 0 is the least significant).
- **The commitment.** `commitment = root (32 bytes) || ood (24 bytes)`. `root` is the Merkle root of the PCS version's encoding of $f$. `ood` is the out-of-domain answer $f(z)$, where $z_j$ is the element encoded by the last 24 bytes of `keccak256("leanPCS-ood" || version || n || root || j)` (`version`, `n` and `j` are one byte each).
- **Well-formedness.** A PCS claim is well-formed if `version` is supported, `1 <= n <= MAX_PCS_VARIABLES`, and it is `82 + 24 * n` bytes long.

Each PCS version defines a verifier `pcs_verify(PCS_claim, opening_proof)`. It MUST return false if `PCS_claim` is not well-formed, and MUST check, in one opening, both $f(z)$ = `ood` and $f$(`point`) = `value`. The first check is what ties a commitment to one polynomial: in the list-decoding regime, a root alone fits a list of polynomials, and the answer at $z$, a point drawn from the root, singles one out.

We start at version `1`: ZK-WHIR at rate 1/2 in the list-decoding regime. Version `1` is not fully specified here yet. For now, its parameters, transcript and proof encoding are those of the reference implementation (`crates/pcs_claim` in this repository, at commit `bb2da7f0`), which supports `15 <= n <= 28`, returns false for any other `n`, and is not zero knowledge yet.

### Dependencies

This EIP replaces the dependency format of EIP-8288, its `(scheme, data_hash, verification_key_hash)` triples and its `LEANSTARK_SCHEME`. A dependency is `scheme (1 byte) || payload`, where the scheme fixes the payload's width:

| `scheme` | `payload` | The dependency holds if |
|---|---|---|
| `LEANSPHINCS_SCHEME` | `msg_hash (32 bytes) \|\| public_key (32 bytes)` | `public_key` signs `msg_hash` with leanSPHINCS |
| `PCS_SCHEME` | `keccak256(PCS_claim)` (32 bytes) | `PCS_claim` holds |

EIP-8288 applies, with these changes:

- **Frames.** A dependency verification frame is valid only if its `data` is `scheme || payload_0 || ... || payload_{k-1}`, with `scheme` one of the two above and `1 <= k <= MAX_DEPENDENCIES_PER_FRAME`. It declares the dependencies `scheme || payload_j`.
- **`dependencies(tx)`** is the list of the dependencies the transaction's frames declare, each `msg_hash` of 32 zero bytes replaced by `compute_sig_hash(tx)`, then deduplicated and sorted. Every list of dependencies (of a transaction, a block or a wrapper) is sorted byte by byte (lexicographic order).
- **`get_deps_hash(deps)`** is `keccak256(concat(deps))`, in place of `DEPS_HASH`.
- **The recursive STARK** proves a PCS dependency from a `PCS_claim` hashing to its payload and an `opening_proof` with `pcs_verify(PCS_claim, opening_proof)`. A false or ill-formed claim cannot be proven, so its transaction cannot be included.
- **Limits.** A transaction declaring more than `MAX_PCS_CLAIMS_PER_TX` PCS dependencies, duplicates included, is invalid. PCS dependencies travel only in mode 1 wrappers.
- **Gas.** leanSPHINCS dependencies are priced as in EIP-8288. A frame of PCS dependencies has `limits.execution = 0` and adds nothing to `recursive_stark_gas(tx)`. Instead, a transaction declaring `c > 0` PCS dependencies, duplicates included, adds `pcs_gas(tx) = PCS_TX_GAS + PCS_CLAIM_GAS * c` to both `frame_tx_intrinsic_gas` and `calldata_floor_gas` (EIP-8141).

### Reading PCS claims

A valid block proves every declared dependency, so a contract may rely on `PCS_claim` once it checks that payload `j` of frame `i` declares it:

1. `FRAMEPARAM(i, 0x02)` (the mode) is `DEP_VERIFY_FRAME_MODE`;
2. the first byte of `FRAMEDATALOAD(0, i)` is `PCS_SCHEME`;
3. `FRAMEDATALOAD(1 + 32 * j, i)` is `keccak256(PCS_claim)`.

Arguments are written from the top of the stack, as EIP-8141 defines them: `FRAMEPARAM(frameIndex, param)` and `FRAMEDATALOAD(offset, frameIndex)`.

In a transaction eligible for EIP-8141's public mempool, dependency verification frames come after the validation prefix, since no recognized validation prefix contains one. Validation code can still read them: `FRAMEPARAM` and `FRAMEDATALOAD` also read later frames.

## Rationale

### Benchmarks

Gas follows EIP-8141 with [EIP-7976](./eip-7976.md)'s calldata floor, without the per-transaction and per-frame overheads: *PIOP* is the PIOP's frame, *Total* adds the frame of PCS claims and `pcs_gas`. *Prover* adds 0.1 s per claim for aggregating, client side, every PCS opening, into a common STARK.

| Application | Prover (Apple M4 Max) | Calldata | PIOP | PCS claims | Total |
|---|---|---|---|---|---|
| Zero-knowledge membership in a Keccak-256 Merkle tree of depth 32 | 1.7 s | 273 bytes | 20,085 gas | 3 | 31,680 gas |
| leanVM verification (here 128 leanXMSS signatures), i.e. any computation thanks to recursion | 3.6 s | 577 bytes | 40,396 gas | 7 | 63,328 gas |

### Why a new dependency format

EIP-8288's triples, a statement's hash and a verification key's hash, are made for whole STARKs. Neither scheme here has a verification key. A signature needs its message and public key (64 bytes); a PCS claim needs only its hash (32 bytes), since the contract computes the claim itself.

### Why PCS claims travel only in mode 1 wrappers

The sender aggregates the openings of its transaction client side, into one STARK that it broadcasts in a mode 1 wrapper. The mempool then recursively aggregates only one STARK, whatever the number of PCS claims. `PCS_TX_GAS` pays for this per-transaction work: verifying and aggregating one more STARK. `PCS_CLAIM_GAS` pays for each claim's share: a dependency of the block.

### Upgrades

The field cannot change, but the PCS can: a future fork can add a version $v + 1$ that brings the latest performance improvements of PCSs. PCS opnings used to commit to witness can adapted without redeploying legacy smart contracts relying on leanPCS.Commitments stored in contracts, typically circuit verification keys, can be migrated, following this idea of JD:

To migrate a stored commitment `com` (version $v$) to `com'` (version $v + 1$, same `n`), a contract derives a point $r$ from both by Fiat-Shamir and requires its transaction to declare that both take the same value at $r$. Distinct polynomials pass with probability at most $n / 2^{192}$ (Schwartz–Zippel).

## Backwards Compatibility

`MULFIELD` uses the opcode `0x1f`, which was previously undefined: executing it halted exceptionally. This EIP replaces the dependency format, the gas of PCS dependencies and the `LEANSTARK_SCHEME` of EIP-8288, which is not yet deployed. Nothing changes for existing transactions.

## Reference Implementation

### `MULFIELD`

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

### PCS claims

TODO

## Security Considerations

**A proof is not tied to its transaction.** A declared claim only says that the claim is true. Anyone who sees a pending transaction can copy its proof, its frame of PCS claims and the STARK that proves them into another transaction, with other frames. So when a proof authorizes something (a payment, a call), what it authorizes has to be part of the application's own transcript, from the start. With the claims in a frame's `data`, the proof cannot commit to `compute_sig_hash(tx)`, as a signature does: that hash covers the frame's `data`, and the claims depend on the transcript. The contract has to hash the relevant parts of the transaction itself, for example the chain id, the sender, the nonce, the fees and the frames it authorizes.

TODO 

## Copyright

Copyright and related rights waived via [CC0](../LICENSE.md).
