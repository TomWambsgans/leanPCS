# The PCS claim (version 1)

What `crates/pcs_claim` implements: the EIP draft's PCS claim (`eip-draft_leanPCS.md`, "PCS claims"), its
commitment and its opening, the one PCS version both lines use. Both lines' contracts check their claims declared in
the transaction's frame of PCS claims in exactly this encoding (`evm_link::Item::DeclaredClaim`).

## The claim

A PCS claim states that the multilinear polynomial `f` over `K = GF(2^64)` in `n` variables committed to as
`commitment` takes the value `value` (in `E = GF(2^192) = K[X]/(X^3 + X + 1)`) at `point` (in `E^n`):

```
PCS_claim = version (1 byte) || n (1 byte) || commitment (56 bytes) || point (24 * n bytes) || value (24 bytes)
commitment = root (32 bytes) || ood (24 bytes)
```

- `version` is `1` (`pcs_claim::VERSION`).
- An element `c0 + c1 X + c2 X^2` of `E` (`c_k ∈ K`, each a 64-bit integer whose bit `j` is the coefficient of
  `Y^j`) is the 192-bit integer `c0 | c1 << 64 | c2 << 128`, big-endian, 24 bytes: the low 24 bytes of the EVM word
  `MULFIELD` takes (`element_bytes`).
- `point` is its `n` coordinates in order, `point_0` first.
- **Well-formed**: `version = 1`, `1 <= n <= MAX_PCS_VARIABLES = 32`, and exactly `82 + 24 n` bytes
  (`PcsClaim::decode`). Every 24 bytes are an element. Version 1 supports `15 <= n <= 28` (WHIR's stacks of `2^15` to
  `2^28` words): a well-formed claim outside that range is never proven (`verify` rejects it).
- The dependency's payload is `keccak256(PCS_claim)` (`PcsClaim::hash`).

## The polynomial's variables

`f(x) = Σ_i f_i · Π_j (x_j if bit j of i is 1, else 1 − x_j)`, `f_i ∈ K` the `i`-th of the `2^n` committed words,
bit 0 the least significant. In WHIR's terms the words are a stack of `64` lanes of `2^(n−6)` words, word `i` being
word `i mod 2^(n−6)` of lane `i >> (n−6)`: `x_0 .. x_{n−7}` are the coordinates inside a lane and `x_{n−6} .. x_{n−1}`
the lane's index, the order in which WHIR's prover reads a weight's lane tensors (`low[y] · scales[l]`) and its
verifier evaluates a point of the stack (`verifier::whir`'s `evaluate_basis`). Tested against the formula written out
(`the_variable_order_is_bit_j_for_x_j`, `an_opening_proves_the_naive_value`).

## The commitment

- `root`: the Merkle root of leanVM's WHIR commitment (commit `c445e3d5`, `pcs::whir::commit`) to the `2^n` words:
  every one of the `64` lanes Reed–Solomon encoded at rate `1/2` (an additive NTT over `K`), one Merkle leaf per
  codeword position holding that position across the `64` lanes, Keccak-256 throughout. All `64` lanes are committed
  (no truncated zero tail: the verifier knows only `n`).
- `ood`: `f(z)` at the **out-of-domain point** `z ∈ E^n` derived from the root alone: `z_j` is the element the low 24
  bytes of `keccak256("leanPCS-ood" || version || n || root || j)` encode (`version`, `n`, `j` one byte each;
  `ood_point`).

## The opening (`pcs_verify`)

One WHIR opening proves both `f(z) = ood` and `f(point) = value`:

1. The transcript is leanVM's Keccak-256 duplex (`fiat_shamir`, `verifier::Transcript`), started from the IV
   `keccak256(PCS_claim)` (the dependency's payload itself) and a zero public digest. No other bytes are hashed into
   the seed; the claim's first two bytes (`version || n`) are the prefix the verifier fixes.
2. The proof's first two scalars are the root (`ProverState::add_root`, each 16-byte half a little-endian number);
   the verifier checks they are the claim's root before reading anything else.
3. `λ` is the transcript's first challenge; the opening proves `Σ_x W(x) f(x) = ood + λ · value` for the weight
   `W = eq(z, ·) + λ · eq(point, ·)`, with leanVM's WHIR prover (`recursive_prover_with_lane_tensors`) and verifier
   (`verifier::whir::verify_whir`), unchanged.
4. **Parameters (version 1)**: leanVM's deployed ladder (`pcs::whir::DEPLOYED_SCHEDULE`,
   `verifier::whir::Ladder::Deployed`): rate `1/2` at level 0, the domain shrinking by 3 bits after the first fold of
   `2^6` lanes and by 1 after each later one (rates `1/2, 1/16, 1/128, ...`), its 128-bit Johnson-regime profile, no
   out-of-domain sample at level 0 (the commitment's `ood` is the one), those of the deeper levels as leanVM's.

## Why the out-of-domain answer binds

In the list-decoding regime a root does not bind one polynomial: the committed words are within the decoding radius
of a list of at most `L` codewords (`L <= 323` at these parameters, the Johnson bound leanVM's profile is computed
at), so two openings of one root, made separately, could be of two polynomials of the list. The answer at `z` singles
one out. `z` is a random-oracle output of the root, so it is drawn after the list is fixed; two distinct multilinear
polynomials in `n` variables agree at a uniform point of `E^n` with probability at most `n / 2^192`
(Schwartz–Zippel), so the probability that two members of a root's list share an answer at `z` is at most
`C(L, 2) · n / 2^192 <= 2^-171` (`L = 323`, `n = 28`). An adversary trying `Q` roots succeeds with probability at most
`Q · C(L, 2) · n / 2^192`: about 171 bits as `Q/ε`. Every claim opened against `(root, ood)` is therefore of the one
list member with that answer, and claims on one commitment may be opened, aggregated and proven separately.

## The EVM check (`evm_link`)

A contract holds a claim's fields as words: the root as one word (its 32 bytes as the claim has them) and each element
as a word with its top 64 bits zero. `Item::DeclaredClaim` packs the claim's `82 + 24 n` bytes in memory past the
outputs (each element's word stored 8 bytes before its place, last element first, so that its top 8 zero bytes fall on
the previous element's tail; then the root; then the header's two bytes), hashes them with `KECCAK256` and compares
the hash with `FRAMEDATALOAD(1 + 32 j, i)` after the frame check (`FRAMEPARAM(0x02, i) = DEP_VERIFY_FRAME_MODE`, first
byte `PCS_SCHEME`). Gas of one claim's check (`tests/evm_packing.rs`, `gas_per_claim`): 381 at `n = 15`, 465 at 20,
501 at 22, 531 at 24, 597 at 28. A contract whose transcript holds a root as its two scalars (`s_0 · 2^128 + s_1`, the
halves' little-endian numbers) turns it into the root's bytes with `op::reverse_halves` (132 gas).

## What the EIP text says

- The claim, its byte encoding, well-formedness and the payload as above; the out-of-domain point's derivation.
- Version `1`: leanVM's WHIR at rate `1/2` with its deployed ladder, the transcript seeded by `keccak256(PCS_claim)`,
  the root as the proof's first scalars, the opening of `f(z) = ood` and `f(point) = value` at one random combination.
- Security: the out-of-domain answer binds the commitment to one polynomial except with probability
  `Q · C(L, 2) · n / 2^192`.
