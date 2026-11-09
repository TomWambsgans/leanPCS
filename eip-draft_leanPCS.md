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

## Abstract

This EIP introduces a precompile, `PCS_OPEN` (for "Polynomial Commitment Scheme Opening"), that contracts can call to verify that a committed multilinear polynomial takes a given value at a given point. This EIP also introduces `MULFIELD`, a new EVM instruction that multiplies two elements of the binary field $\mathrm{GF}(2^{192})$. Together, they let users cheaply verify post-quantum STARKs (scalable transparent arguments of knowledge) onchain. `PCS_OPEN` acts as a post-quantum equivalent of the elliptic-curve precompiles used to verify pre-quantum SNARKs (succinct non-interactive arguments of knowledge). All the heavy PCS opening proofs are aggregated, via a STARK, so they don't appear in the block, following [EIP-8288](https://eips.ethereum.org/EIPS/eip-8288).

## Motivation

Today, verifying a pre-quantum SNARK on chain costs about 200,000 gas thanks to the elliptic-curve precompiles. Post-quantum STARKs, based on hash functions, are much larger, and much more expensive to verify. Recursive aggregation amortizes this cost: a single STARK per block proves all the others. [EIP-8288](https://eips.ethereum.org/EIPS/eip-8288) was intiially designed to aggregates whole STARKs, which would require to enshrine a new STARK-friendly ISA, such as RiscV.

This EIP aggregates less. The majority of the work of a STARK verifier is checking PCS openings. With this EIP, Ethereum aggregates this heavy part, and smart contracts run the rest of the verifier, the polynomial interactive oracle proof (PIOP), in the Ethereum Virtual Machine (EVM). The PIOP mostly does arithmetic in some finite field. We pick binary fields for their simplicity and their state of the art performance. The EVM can already add field elements with `XOR` (`0x18`). For efficient field multiplication, we introduce a new `MULFIELD` EVM instruction.

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

`DEPS_HASH`, `dependencies(tx)`, `get_deps_hash`, dependency verification frames and mempool wrappers come from EIP-8288.

### Fields

Let $K = \mathrm{GF}(2)[Y] / (Y^{64} + Y^4 + Y^3 + Y + 1)$ and $E = K[X] / (X^3 + X + 1)$. An element of $K$ is encoded as a 64-bit integer whose bit $j$ is the coefficient of $Y^j$. An element $a + bX + cX^2$ of $E$, with $a, b, c \in K$, is encoded as the word `a | (b << 64) | (c << 128)`.

TODO: 128 bits field

### `MULFIELD`

The instruction `MULFIELD` (`0x1f`) pops `a` and `b`, ignores their top 64 bits, and pushes their product in $E$. It costs 10 gas.

### Claims

A claim has the following form: "the multilinear polynomial $f$, in `n` variables, with a commitment `commitment` (56 bytes), takes the value `value` (in $E$) at `point` (in $E^n$)". A claim is encoded as:

```
claim = n (1 byte) || commitment (56 bytes) || point (24 * n bytes) || value (24 bytes)
```

Under the hood, `commitment` is a 32-byte Merkle root and a 24-byte out-of-domain answer (in $E$). A claim is well-formed if `1 <= n <= MAX_PCS_VARIABLES` and if it is `81 + 24 * n` bytes long.

Each PCS version defines a verifier `pcs_verify(version, claim, opening_proof)`, whose Fiat-Shamir transcript starts from `claim`. Version `1` is the only version: WHIR at rate 1/4, in the list-decoding regime.

### Declaring claims

A transaction declares that `claim` holds under PCS version `version` by including the dependency

```
pcs_dependency(version, claim) = (PCS_SCHEME, DEPS_HASH(claim), version.to_bytes(32, "big"))
```

in an EIP-8288 dependency verification frame: `data_hash` is the claim's hash, and `verification_key_hash` holds the version. This EIP changes EIP-8288 as follows:

1. **Frame validity.** A triple's `scheme` may also be `PCS_SCHEME`, if `int.from_bytes(verification_key_hash, "big")` is a supported version. Each such triple adds `PCS_CLAIM_GAS` to the frame's required `limits.execution`, and the first frame of the transaction with such a triple also adds `PCS_TX_GAS`.
2. **Digest.** `get_deps_hash` also hashes each dependency's scheme:
   ```
   get_deps_hash(deps) = DEPS_HASH(concat([
       bytes([t.scheme]) + t.data_hash + t.verification_key_hash
       for t in deps
   ]))
   ```
3. **Recursive STARK.** The recursive STARK proves a `PCS_SCHEME` dependency from a witness `(claim, opening_proof)`: it checks that `claim` hashes to `data_hash`, and that `opening_proof` opens `claim` under the version in `verification_key_hash`, that is, that `pcs_verify(version, claim, opening_proof)` holds.
4. **Mempool.** A transaction has at most `MAX_PCS_CLAIMS_PER_TX` `PCS_SCHEME` dependencies, counted on `dependencies(tx)`. They travel only in mode 1 wrappers: a mode 0 wrapper with a `PCS_SCHEME` dependency is invalid.

### `PCS_OPEN`

The precompile `PCS_OPEN`, at `PCS_OPEN_ADDRESS`, takes the input `version (1 byte) || claim`. The call fails if `version` is not supported or if `claim` is not well-formed. Otherwise it returns the 32-byte word `1` if `pcs_dependency(version, claim)` is in `dependencies(tx)` for the current transaction `tx`, and `0` otherwise. It costs `30 + 6 * ceil(len(input) / 32)` gas.

A valid block proves every dependency of its transactions, so a result of `1` means that the claim holds.

## Rationale

### Why a 192-bit field

For a PCS like WHIR, 192 bits is large enough to get provable 128-bit security in the list-decoding regime. TBD: what about a 128-bit field?

### Why `MULFIELD` is an instruction

A STARK verifier does many field multiplications, and a precompile call costs at least 100 gas. CPUs multiply binary polynomials natively, with `PCLMULQDQ` on x86 and `PMULL` on ARM, so 10 gas is conservative.

### Why WHIR

Verifying WHIR is mostly checking Merkle paths, which is exactly the part that aggregation removes. WHIR can also be made zero-knowledge by changing only the prover, so private applications can use the same precompile.

### Why claims are hashed

The contract computes `point` and `value` itself while verifying its proof, so the transaction does not need to include them: it only declares a 96-byte triple per claim. `PCS_OPEN` computes `DEPS_HASH` for the contract, because this hash is chosen to be cheap in the aggregation STARK, not in the EVM. The scheme is included in `get_deps_hash` so that dependencies of different schemes cannot collide.

### Why claims travel only in mode 1 wrappers

The sender aggregates the openings of its transaction client side, into one STARK that it broadcasts in a mode 1 wrapper. The mempool then verifies one STARK, whatever the number of claims. `PCS_TX_GAS` pays for that STARK, once per transaction, and `PCS_CLAIM_GAS` pays for each claim's share of the aggregation. A mode 0 wrapper would instead make the mempool verify one opening per claim, over every transaction in the wrapper. For the same reason, claims need no per-wrapper limit: each one adds only its 96-byte triple, which its transaction already carries.

### Upgrades

The field cannot change, but the PCS can. New proofs simply use the new version, but commitments stored in contracts, such as the commitment to a circuit, must be migrated. Following an idea of Justin Drake, a fork adds version $v + 1$, and removes version $v$ after a deprecation period.

To migrate a stored commitment `com` to `com'`, a contract derives a random point $r$ from both commitments by Fiat-Shamir, and requires `PCS_OPEN` to return `1` for both `(v, com, r, y)` and `(v + 1, com', r, y)`, with the same $y$. If `com` and `com'` commit to different polynomials, this check passes with probability at most $n / 2^{192}$ (Schwartz–Zippel).

## Backwards Compatibility

`MULFIELD` uses the opcode `0x1f`, which was previously undefined: executing it halted exceptionally. This EIP also changes `get_deps_hash` of EIP-8288. Nothing else changes for existing transactions, and `LEANSTARK_SCHEME` remains reserved.

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

The Fiat-Shamir transcript of a WHIR proof starts from the claim only, not from the transcript of the application. This is believed to be sound, but it has not been formally analyzed yet.

`PCS_OPEN` only proves that a claim is true. Each application must still verify the rest of its proof correctly, for example by deriving evaluation points by Fiat-Shamir after its commitments are fixed.

Removing a PCS version makes unmigrated commitments unusable, for example commitments hardcoded in contract code. `MAX_PCS_VARIABLES`, `PCS_TX_GAS`, `PCS_CLAIM_GAS`, `MAX_PCS_CLAIMS_PER_TX` and the restriction to mode 1 wrappers bound denial-of-service risks, as in EIP-8288.

## Copyright

Copyright and related rights waived via [CC0](../LICENSE.md).
