---
title: leanPCS
description: Add a PCS_OPEN precompile and a MULFIELD instruction, for cheap verification of STARKs onchain
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

This EIP introduces a new precompile, `PCS_OPEN` (for "Polynomial Commitment Scheme Opening"), that contracts can call to verify that a committed multilinear polynomial takes a given value at a given point. This EIP also introduces a new EVM instruction `MULFIELD` that multiplies two elements of the finite field $\mathrm{GF}(2^{192})$. Together, they let users cheaply verify post-quantum STARKs (scalable transparent arguments of knowledge) onchain. All the heavy PCS opening proofs of a block are aggregated, into a single STARK, following [EIP-8288](https://eips.ethereum.org/EIPS/eip-8288).

## Motivation

Today, verifying a pre-quantum SNARK onchain costs about 200,000 gas thanks to the elliptic-curve precompiles. Post-quantum STARKs, based on hash functions, are much larger, and much more expensive to verify. Recursive aggregation amortizes this cost: a single STARK per block proves all the others. [EIP-8288](https://eips.ethereum.org/EIPS/eip-8288) was initially designed to aggregate whole STARKs, which would require enshrining a new STARK-friendly ISA, such as RISC-V.

The majority of the work of a STARK verifier is checking PCS openings. With this EIP, Ethereum aggregates this heavy part, and smart contracts run the rest of the verifier in the EVM (this part is called the "polynomial interactive oracle proof" (PIOP)). The PIOP mostly does arithmetic in some finite field. We pick binary fields for their simplicity and their state of the art performance. The EVM can already add field elements with `XOR` (`0x18`). For efficient field multiplication, we introduce a new `MULFIELD` EVM instruction.

The goal of this EIP is to get most of the benefits (cheap onchain STARK verification) from [EIP-8288](https://eips.ethereum.org/EIPS/eip-8288) without the complexity of enshrining a new ISA.

## Specification

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be interpreted as described in [RFC 2119](https://www.rfc-editor.org/rfc/rfc2119) and [RFC 8174](https://www.rfc-editor.org/rfc/rfc8174).

| Constant                     | Value  |
|------------------------------|--------|
| `PCS_OPEN_ADDRESS`           | `TBD`  |
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

Each PCS version defines a verifier `pcs_verify(PCS_claim, opening_proof)`, whose Fiat-Shamir transcript starts from `PCS_claim`. We start at version `1`: WHIR at rate 1/2, in the list-decoding regime.

### Dependencies

This EIP replaces the dependency format of EIP-8288, its `(scheme, data_hash, verification_key_hash)` triples and its `LEANSTARK_SCHEME`. A dependency is `scheme (1 byte) || payload`, where the scheme fixes the payload:

| `scheme` | `payload` | The dependency holds if |
|---|---|---|
| `LEANSPHINCS_SCHEME` | `msg_hash (32 bytes) \|\| public_key (32 bytes)` | `public_key` signs `msg_hash` with leanSPHINCS |
| `PCS_SCHEME` | `keccak256(PCS_claim)` (32 bytes) | `PCS_claim` holds |

EIP-8288 then applies to dependencies in place of triples:

- **Frames.** The `data` of a dependency verification frame is the concatenation of 1 to `MAX_DEPENDENCIES_PER_FRAME` dependencies. A frame whose `data` does not split into dependencies is invalid. Contracts read them with `FRAMEDATACOPY`.
- **`dependencies(tx)`** is the sorted, deduplicated list of the dependencies of the transaction's frames, where a `msg_hash` of 32 zero bytes stands for `compute_sig_hash(tx)`.
- **`get_deps_hash(deps)`** is `keccak256(concat(deps))`: EIP-8288's `DEPS_HASH` is Keccak-256.
- **The recursive STARK** proves a leanSPHINCS dependency from its signature, and a PCS dependency from `(PCS_claim, opening_proof)`: it checks that `PCS_claim` hashes to the payload and that `pcs_verify(PCS_claim, opening_proof)` holds. A PCS dependency with an unsupported version cannot be proven, so its transaction cannot be included.
- **Gas.** A transaction with `s` leanSPHINCS and `c` PCS dependencies in its frames, duplicates included, pays `LEANSPHINCS_VERIFICATION_GAS * s + PCS_CLAIM_GAS * c`, plus `PCS_TX_GAS` if `c > 0`, as intrinsic gas. Dependency verification frames have `limits.execution = 0`.
- **Mempool.** EIP-8288's limits on leanSPHINCS dependencies stay. `dependencies(tx)` holds at most `MAX_PCS_CLAIMS_PER_TX` PCS dependencies, which travel only in mode 1 wrappers.

### `PCS_OPEN`

The precompile `PCS_OPEN`, at `PCS_OPEN_ADDRESS`, takes a `PCS_claim` as input, and fails if it is not well-formed. Otherwise it returns the 32-byte word `1` if `PCS_SCHEME || keccak256(PCS_claim)` is in `dependencies(tx)` for the current transaction `tx`, and `0` otherwise. It costs `30 + 6 * ceil(len(PCS_claim) / 32)` gas.

A valid block proves every dependency of its transactions, so a result of `1` means that the PCS claim holds.

## Rationale

### Why a 192-bit field

For a PCS like WHIR, 192 bits is large enough to get provable 128-bit security in the list-decoding regime. TBD: what about a 128-bit field?

### Why `MULFIELD` is an instruction

A STARK verifier does many field multiplications, and a precompile call costs at least 100 gas. CPUs multiply binary polynomials natively, with `PCLMULQDQ` on x86 and `PMULL` on ARM, so 10 gas is conservative.

### Why WHIR

Verifying WHIR is mostly checking Merkle paths, which is exactly the part that aggregation removes. WHIR can also be made zero-knowledge by changing only the prover, so private applications can use the same precompile.

### Why a new dependency format

EIP-8288's triples are shaped for whole STARKs: a statement's hash and a verification key's hash. Here no scheme has a verification key. A signature needs its message and its public key, which its account contract reads in the frame. A PCS claim needs only its hash, because the contract computes `point` and `value` itself while verifying its proof. So each scheme fixes its payload, 65 bytes a signature and 33 bytes a PCS claim, and `get_deps_hash` hashes the encoding that frames carry, the scheme byte keeping schemes apart.

### Why Keccak-256

Keccak-256 is the EVM's hash, so `PCS_OPEN` costs what `KECCAK256` costs on the same bytes, and Keccak-f, a permutation of 64-bit words, is cheap to prove with binary fields. Contracts, clients and the aggregation STARK compute the same hash.

### Why PCS claims travel only in mode 1 wrappers

The sender aggregates the openings of its transaction client side, into one STARK that it broadcasts in a mode 1 wrapper. The mempool then verifies one STARK, whatever the number of PCS claims. `PCS_TX_GAS` pays for that STARK, once per transaction, and `PCS_CLAIM_GAS` pays for each PCS claim's share of the aggregation. A mode 0 wrapper would instead make the mempool verify one opening per PCS claim, over every transaction in the wrapper. For the same reason, PCS claims need no per-wrapper limit: each one adds only its 33 bytes, which its transaction already carries.

### Upgrades

The field cannot change, but the PCS can. New proofs simply use the new version, but commitments stored in contracts, such as the commitment to a circuit, must be migrated. Following an idea of Justin Drake, a fork adds version $v + 1$, and removes version $v$ after a deprecation period.

To migrate a stored commitment `com` to `com'`, a contract derives a random point $r$ from both commitments by Fiat-Shamir, and requires `PCS_OPEN` to return `1` for two PCS claims: `com` under version $v$ and `com'` under version $v + 1$ take the same value $y$ at $r$. If `com` and `com'` commit to different polynomials, this check passes with probability at most $n / 2^{192}$ (Schwartz–Zippel).

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

### `PCS_OPEN`

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

The security of `PCS_OPEN` relies on EIP-8288 and on the soundness of each PCS version. In the list-decoding regime, the out-of-domain answer in a commitment is what binds it to a single polynomial.

The Fiat-Shamir transcript of a WHIR proof starts from the PCS claim only, not from the transcript of the application. This is believed to be sound, but it has not been formally analyzed yet.

`PCS_OPEN` only proves that a PCS claim is true. Each application must still verify the rest of its proof correctly, for example by deriving evaluation points by Fiat-Shamir after its commitments are fixed.

Removing a PCS version makes unmigrated commitments unusable, for example commitments hardcoded in contract code. Gas, `MAX_PCS_VARIABLES`, `MAX_PCS_CLAIMS_PER_TX` and the restriction to mode 1 wrappers bound denial-of-service risks, as in EIP-8288.

## Copyright

Copyright and related rights waived via [CC0](../LICENSE.md).
