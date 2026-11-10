---
title: leanPCS
description: Aggregate polynomial commitment openings and add a MULFIELD instruction, for cheap verification of STARKs onchain
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

Today, verifying a pre-quantum SNARK onchain costs about 200,000 gas thanks to the elliptic-curve precompiles. Post-quantum STARKs are much larger, and much more expensive to verify. Recursive aggregation amortizes this cost: a single STARK per block proves all the others. [EIP-8288](./eip-8288.md) was initially designed to aggregate whole STARKs, which would require enshrining a STARK-friendly ISA in which every application is written, such as RISC-V.

STARKs are complicated. The good news is that most of a STARK verification, in proof size and in verification time, is much simpler: it is just PCS openings. With this EIP, Ethereum aggregates the PCS openings (most of the proof size), and smart contracts run the rest of the STARK verification in the EVM (a small proof). This rest is called the "polynomial interactive oracle proof" (PIOP). The PIOP mostly computes a few hashes (for Fiat-Shamir) and does arithmetic in some finite field. We pick binary fields for their simplicity and their state of the art performance. The EVM can already add field elements with `XOR` (`0x18`). For efficient field multiplication, we introduce a new `MULFIELD` EVM instruction.

The goal of this EIP is to get most of the benefits (cheap onchain STARK verification) from [EIP-8288](./eip-8288.md) without the complexity of enshrining a new ISA.

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

Let $K = \mathrm{GF}(2)[Y] / (Y^{64} + Y^4 + Y^3 + Y + 1)$ and $E = K[X] / (X^3 + X + 1)$. An element of $K$ is encoded as a 64-bit integer whose bit $j$ is the coefficient of $Y^j$. An element $a + bX + cX^2$ of $E$, with $a, b, c \in K$, is encoded as the word `a | (b << 64) | (c << 128)`.

### `MULFIELD`

The instruction `MULFIELD` (`0x1f`) pops `a` (the top of the stack) and then `b`, ignores their top 64 bits, and pushes their product in $E$ (the product is commutative, so the order does not matter). It costs 10 gas.

### PCS claims

A PCS claim states that the multilinear polynomial $f$ over $K$ in `n` variables committed to as `commitment` takes the value `value` (in $E$) at `point` (in $E^n$), under PCS version `version`:

```
PCS_claim = version (1 byte) || n (1 byte) || commitment (56 bytes) || point (24 * n bytes) || value (24 bytes)
```

- **Elements.** An element of $E$ is 24 bytes: the big-endian encoding of its word `a | (b << 64) | (c << 128)`, i.e. the low 24 bytes of the word `MULFIELD` takes. `point` is `point_0 || ... || point_{n-1}`.
- **The polynomial.** $f$ is given by its $2^n$ values $f_i \in K$ on the Boolean hypercube: $f(x) = \sum_i f_i \prod_j \ell_j(i, x)$, where $\ell_j(i, x) = x_j$ if bit $j$ of $i$ is 1 and $1 - x_j$ otherwise, bit 0 being the least significant.
- **The commitment.** `commitment = root (32 bytes) || ood (24 bytes)`: `root` is the Merkle root of the PCS version's encoding of $f$, and `ood` is the out-of-domain answer $f(z)$ at the point $z = (z_0, \dots, z_{n-1})$, where $z_j$ is the element whose encoding is the low 24 bytes of `keccak256("leanPCS-ood" || version (1 byte) || n (1 byte) || root || j (1 byte))`.
- **Well-formedness.** A PCS claim is well-formed if `version` is supported, `1 <= n <= MAX_PCS_VARIABLES`, and it is `82 + 24 * n` bytes long.

Each PCS version defines a verifier `pcs_verify(PCS_claim, opening_proof)`, false if `PCS_claim` is not well-formed. It checks, in one opening, that $f(z) = $ `ood` and $f($`point`$) = $ `value`, and its Fiat-Shamir transcript starts from `keccak256(PCS_claim)` only.

We start at version `1`: leanVM's WHIR (commit `c445e3d5`) at rate 1/2 with its folding schedule, in the list-decoding regime, with Keccak-256 Merkle trees. Until it has a full specification, its parameters, transcript and proof encoding are those of the reference implementation. The reference implementation supports `n` up to 28.

In the list-decoding regime, a Merkle root alone binds only a short list of polynomials. The out-of-domain answer binds the commitment to one of them: $z$ is derived from `root` after it is fixed, and two distinct polynomials of the list agree at $z$ with probability at most $n / 2^{192}$. So claims on one commitment, declared separately, are about one polynomial.

### Dependencies

This EIP replaces the dependency format of EIP-8288, its `(scheme, data_hash, verification_key_hash)` triples and its `LEANSTARK_SCHEME`. A dependency is `scheme (1 byte) || payload`, where the scheme fixes the payload's width:

| `scheme` | `payload` | The dependency holds if |
|---|---|---|
| `LEANSPHINCS_SCHEME` | `msg_hash (32 bytes) \|\| public_key (32 bytes)` | `public_key` signs `msg_hash` with leanSPHINCS |
| `PCS_SCHEME` | `keccak256(PCS_claim)` (32 bytes) | `PCS_claim` holds |

EIP-8288 then applies to dependencies in place of triples:

- **Frames.** A dependency verification frame declares dependencies of one scheme: its `data` is `scheme || payload_0 || ... || payload_{k-1}`, and its dependencies are the `scheme || payload_j`. The frame is invalid unless `scheme` is `LEANSPHINCS_SCHEME` or `PCS_SCHEME`, `len(data) = 1 + w * k` with `w` the scheme's payload width (64 or 32) and `1 <= k <= MAX_DEPENDENCIES_PER_FRAME`. EIP-8288's other constraints on the frame stay: `target` is `None`, `value` and `flags` are `0`, `limits.state` is `0`, and it is not part of an atomic batch.
- **`dependencies(tx)`** is the sorted, deduplicated list of the dependencies of the transaction's frames, where a `msg_hash` of 32 zero bytes stands for `compute_sig_hash(tx)`.
- **`get_deps_hash(deps)`** is `keccak256(concat(deps))`: we use Keccak-256 in place of EIP-8288's `DEPS_HASH`.
- **The recursive STARK** proves a leanSPHINCS dependency from its signature, and a PCS dependency from `(PCS_claim, opening_proof)`: it checks that `PCS_claim` hashes to the payload and that `pcs_verify(PCS_claim, opening_proof)` holds. A PCS dependency whose claim is false or not well-formed cannot be proven, so its transaction cannot be included.
- **Validity.** A transaction whose frames declare more than `MAX_PCS_CLAIMS_PER_TX` PCS dependencies, duplicates included, is invalid.
- **Gas.** leanSPHINCS dependencies are priced as in EIP-8288: their frame's `limits.execution` is `LEANSPHINCS_VERIFICATION_GAS` per dependency, and each adds `LEANSTARK_VERIFICATION_GAS` to `recursive_stark_gas(tx)`. A frame of PCS dependencies has `limits.execution = 0`, and its dependencies are not counted in `recursive_stark_gas(tx)`. Instead, a transaction with `c` PCS dependencies in its frames, duplicates included, pays `pcs_gas(tx) = PCS_TX_GAS + PCS_CLAIM_GAS * c` if `c > 0` (and 0 otherwise), added to both `frame_tx_intrinsic_gas` and `calldata_floor_gas` of EIP-8141.
- **Mempool.** EIP-8288's limits on leanSPHINCS dependencies stay. PCS dependencies travel only in mode 1 wrappers.

### Reading PCS claims

A valid block proves every dependency of its transactions. So a contract can rely on `PCS_claim` if its transaction declares it, which the contract checks in three steps, given a frame index `i` and a payload index `j` (arguments listed from the top of the stack):

1. `FRAMEPARAM(i, 0x02)` (the mode) is `DEP_VERIFY_FRAME_MODE`: frame `i` is a dependency verification frame.
2. The first byte of `FRAMEDATALOAD(0, i)` is `PCS_SCHEME`: its dependencies are PCS claims.
3. `FRAMEDATALOAD(1 + 32 * j, i)` is `keccak256(PCS_claim)`: its payload `j` declares `PCS_claim`.

## Rationale

### Benchmarks

Two applications of the reference implementation, with their PIOPs as straight-line EVM contracts and their PCS claims declared in a frame. Gas is priced as for an EIP-8141 frame transaction, whose calldata floor is [EIP-7976](./eip-7976.md)'s, and excludes `FRAME_TX_INTRINSIC_COST` and the per-frame costs. PIOP is the gas of the frame that verifies the PIOP: its execution and its calldata. Total is `max(standard, floor)` for that frame and the frame of PCS claims, with `pcs_gas` in both. Prover is the measured prover time plus 0.1 s per PCS claim, a heuristic for the client-side aggregation of its opening. The membership proof is zero-knowledge assuming a zero-knowledge PCS opening (ZK-WHIR); the reference implementation's openings are plain WHIR, which has the same claims and gas.

| Application | Prover (M4 Max) | Calldata | PIOP | PCS claims | Total |
|---|---|---|---|---|---|
| Zero-knowledge membership in a Keccak-256 Merkle tree of depth 32 | 7.8 s | 461 bytes | 29,504 gas | 6 | 52,856 gas |
| leanVM verification (here 128 leanXMSS signatures), i.e. any computation thanks to recursion | 9.1 s | 1,101 bytes | 70,464 gas | 8 | 99,912 gas |

### Why a 192-bit field

For a PCS like WHIR, 192 bits leaves room for its provable bounds in the list-decoding regime: the reference parameters reach about 128 bits of security, which a 128-bit field could not.

### Why `MULFIELD` is an instruction

A STARK verifier does many field multiplications, and a precompile call costs at least 100 gas (a warm `STATICCALL`). CPUs multiply binary polynomials natively, with `PCLMULQDQ` on x86 and `PMULL` on ARM: a product in $E$ is nine 64-bit carry-less multiplications and a few reductions, so 10 gas is conservative.

### Why WHIR

WHIR is a state-of-the-art multilinear PCS. It can also be made zero-knowledge by changing only the prover (committing to random masks), so private applications can use the same scheme.

### Why a new dependency format

EIP-8288's triples, a statement's hash and a verification key's hash, are made for whole STARKs. Neither scheme here has a verification key. A signature needs its message and public key (64 bytes); a PCS claim needs only its hash (32 bytes), since the contract computes the claim itself.

### Why PCS claims travel only in mode 1 wrappers

The sender aggregates the openings of its transaction client side, into one STARK that it broadcasts in a mode 1 wrapper. The mempool then verifies one STARK, whatever the number of PCS claims, and the block's STARK aggregates it. `PCS_TX_GAS` pays for this per-transaction work: verifying and aggregating one more STARK. `PCS_CLAIM_GAS` pays for each claim's share: a dependency of the block, which the block's STARK proves. A mode 0 wrapper would instead make the mempool verify one opening per claim. `pcs_gas` is in the calldata floor too, otherwise a transaction whose floor binds would get its claims for free.

### Upgrades

The field cannot change, but the PCS can: a fork can add a version $v + 1$ that brings the latest performance improvements of PCSs. The version is part of each claim, so applications use it through verifier contracts that build claims of version $v + 1$. Commitments stored in contracts, typically circuit verification keys, can be migrated, following an idea of Justin Drake.

To migrate a stored commitment `com` to `com'` (same `n`), a contract derives a random point $r$ from both commitments by Fiat-Shamir, and requires its transaction to declare two PCS claims: `com` under version $v$ and `com'` under version $v + 1$ take the same value $y$ at $r$. Both commitments bind one polynomial each, thanks to their out-of-domain answers. If these polynomials differ, the check passes with probability at most $n / 2^{192}$ per attempt (Schwartz–Zippel).

## Backwards Compatibility

`MULFIELD` uses the opcode `0x1f`, which was previously undefined: executing it halted exceptionally. This EIP replaces the dependency format, the gas of PCS dependencies and the `LEANSTARK_SCHEME` of EIP-8288, which is not yet deployed. Nothing changes for existing transactions.

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

Let `n = 15`, `f_i` the big-endian integer of the last 8 bytes of `keccak256("leanPCS-test" || i)` (`i` as 8 big-endian bytes) for `0 <= i < 2^15`, and `point_j` the element given by the last 24 bytes of `keccak256("leanPCS-point" || j)` (`j` as 1 byte). Then:

| | |
|---|---|
| `root` | `0xbb8bf6812454571b29372e3814e0191723474a9b1d7d168996583a20ad8f571d` |
| `z_0` | `0x4d6ecf1f234f956695633f79174496ff57a2989512eab8ff` |
| `ood` | `0x0a49bdd16e116e295326a21aafaa2fdf33776694660edebf` |
| `value` | `0x873b3af84c179f9afeb4782f18feab9696f4f5e643b83441` |
| `PCS_claim` | 442 bytes, starting `0x010fbb8bf681…` |
| `keccak256(PCS_claim)` | `0x0222bb22c488ace98574fe97002cd35168ed13dc80650b5efbc812643221e108` |

`pcs_verify` accepts the reference implementation's opening of this claim, and rejects it for `value + 1`.

## Reference Implementation

The reference implementation ([github.com/TomWambsgans/leanPCS](https://github.com/TomWambsgans/leanPCS)) contains provers, EVM verifier contracts and PCS version 1 for the two applications of the benchmarks, and `bench.sh`, which reproduces the benchmarks.

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

The security of PCS claims relies on EIP-8288 and on the soundness of each PCS version.

**Binding.** In the list-decoding regime, a root binds a list of at most $L$ polynomials (at the reference parameters, $L$ goes from 87,315 at $n = 15$ down to 3,564 at $n = 28$). The out-of-domain answer selects one: an adversary trying $Q$ roots finds one where two polynomials of its list agree at $z$ with probability at most $Q \cdot \binom{L}{2} \cdot n / 2^{192}$, that is at most $Q \cdot 2^{-156}$. A PCS version without this binding would make separately declared claims on one commitment forgeable.

**Fiat-Shamir.** The transcript of an opening starts from the PCS claim only, not from the transcript of the application. The application's own Fiat-Shamir must therefore fix its commitments before it draws the points it claims at.

**Frames.** A contract MUST check that the frame it reads is a dependency verification frame whose first byte is `PCS_SCHEME`: the same 32 bytes in another frame, or a `msg_hash` in a leanSPHINCS frame, which its sender chooses, prove nothing. Past the frame's `data`, `FRAMEDATALOAD` reads zero, which no Keccak-256 output is but with probability $2^{-256}$, so a contract need not check `j < k`.

**Application soundness.** A declared PCS claim only proves that the claim is true. Each application must still verify the rest of its proof correctly.

**Denial of service.** Gas, `MAX_PCS_VARIABLES`, `MAX_PCS_CLAIMS_PER_TX` (a validity rule) and the restriction to mode 1 wrappers bound the work a transaction imposes on the mempool and on builders, as in EIP-8288. A false claim cannot be proven, so its transaction cannot be included; mempool nodes reject it when its wrapper's STARK does not verify.

**Removed versions.** Removing a PCS version makes unmigrated commitments unusable, for example commitments hardcoded in contract code.

## Copyright

Copyright and related rights waived via [CC0](../LICENSE.md).
