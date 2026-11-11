<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# QuotientSecurity: the reduction (F1) and the circuit (F0)

Ported from leanVM's `formal/quotient` (branch `PCS-openings-aggregation`, commit `651453c6`) to the membership
circuit of commit `f96a7938` (the gate `V = X + C + Y·C`; the deployed circuit has since swapped the roles,
`V = Y + C + X·C`: [`docs/LEAN_PORT.md`](../../docs/LEAN_PORT.md)). A library of `formal/EndToEnd`; sorry-free, on
`propext`, `Classical.choice` and `Quot.sound` only, no `native_decide`. The end theorems that use it are in
[`../README.md`](../README.md).

- **F1, the reduction** (five field elements → claims), with **ideal commitments**: round-by-round knowledge
  soundness, completeness, honest-verifier zero knowledge, Fiat–Shamir in the ROM: `Instance.soundness`,
  `zero_knowledge`, `completeness`, for every wiring. Its zero knowledge is for ideal hiding commitments; the end
  theorem takes the PCS's as a hypothesis (`PcsZeroKnowledge`).
- **F0, the circuit** (`CircuitLayout.lean`, `Pinning.lean`, `Statement.lean`, `Deployed.lean`,
  `DeployedConcrete.lean`; with `formal/Circuit` and `formal/Field`). `Instance.soundness_circuit`: for a wiring that
  lays a loop-free χ circuit `C` (`Laid`) with `coordinate_weight`'s weights, an accepted proof of `statementWords x Y
  y root` holds `C`'s computation on some input bits with public words 0–3 the halves of `(y, root)`, except with
  `(Q + 3)/2^128`; `soundness_circuit_bits` reads the public bits as `circuit::public_words` does. Not vacuous:
  `laid_wiringOf`, `relation_wiringOf`, `relation_statementWords`. `soundness_membership_deployed`: an accepted
  proof's cells are a computation of the deployed `2^22`-row circuit (off its `16` random rows, `ChiCircuit.isRandom`)
  whose input bits give `x` and a path with `y = H(x ‖ 0x11..)` and the path from `H(x ‖ 0x22..)` ending at `root`,
  Keccak-256 checked against mumbai's (`keccak256_bits`); `soundness_membership_deployed_concrete`: the same over
  `primitives`' `F192` (CompPoly's `BF64.Ext3`), no field hypothesis left. σ equals the Rust's by a hash of both dumps
  (SHA-256 `41c92f12…6655`, 2026-11-10). Completeness with any values in the random rows' cells:
  `Completeness.honest_relation_deployed_random`.

## The port to this protocol (F1)

Upstream's circuit is a full adder; this protocol differs in three ways, and the Lean files describe this one.

- **The gate** (`Protocol.lean`'s `gate`, `quotient::protocol`'s `gate` at `f96a7938`): `V + X + C + Y·C`, that is
  `V = X ⊕ (C ∧ ¬Y)` on bits (Keccak's χ), of degree 2, with no `θ` and no carries. `θ = β_1` stays in `Params`:
  it places a row's four cells at `x, x + 1, x + θ, x + θ + 1`.
- **The circuit argument** (`Circuit.lean`): `ChiCircuit` replaces `AdderCircuit`. An input row reads its own
  output in `X`, `Y` and `C` (`quotient::circuit::Builder::input`), so its gate is `v + v + v + v·v = v^2 + v`
  and `input_is_bit`: it holds `0` or `1`; every other row reads constants or rows of lower rank, and
  `gate_output`: on bits the gate gives `V = chiOf X Y C`, a bit. `ChiCircuit.determined`: two assignments, in
  any field of characteristic 2, that satisfy every gate and agree on the inputs agree everywhere, and every
  output is a bit (no `GF(4)`). `cells_determined`, `copy_iterate`, `word_pins`, `Wired` are as before, on bits.
- **The size**: `2^22` rows, cells named by `m = 24` bits (`22 + 2`, the opaque `le24`), `N = 2^24` cells;
  the tables have `m + 1 = 25` (witness), `m = 24` (wiring) and `m + 6 = 30` (quotient) variables, as
  `claims_iff_accepts_ofCantor` states them (the WHIR stacks are not modelled: a table of the layout is a table
  whose other chunks are zero). The PCS protocol of `f96a7938` commits the quotient table in three parts, `H`, `Q`,
  `G` (`PcsBridge.mle_assemble`: the table is their assembly).

**The bounds, re-derived** (`Degrees.lean`, `Concrete.lean`, `Bits.lean`). `Bounds.identity` is the largest
of the bounds on the terms of the two identities (upstream summed them): with the gate of degree 2 it is
`max (max (2 * denominator) cells + max cells rows + quotient) (2 * denominator + max (pub + cell) (2 * cell))`
(the terms `D D' h`, `v_cells q`, `v_rows (D D' q_gate + v_cells j)`, `pub w D D'`, `D D' gate`; it bounds the
product the verifier inverts too). At the instance's table sizes (witness polynomials `2^23`, quotients `2^26`,
wiring and cells `2^24`, rows `2^22`, public weight `2^24 + 9 * 2^10`): a cell's polynomial `4 * 2^23 + 3`, a
denominator `3 * 2^24 + 4`, and `Params.ofCantor_identity_eq`: the identities' degree is at most `11 * 2^24 + 8`
(the copy identity's `D D' h`; the sum was `2^28 + 2^22 + 9230`), so `Params.ofCantor_identity_le_margin`: at most
`2^28` (and `Params.ofCantor_identity`: at most `2^29`). The public weight's degree (`natDegree_membershipPub_le`) is
`Σ_{11 ≤ j < 24} 2^j + 11 * 2^10 = 2^24 + 9 * 2^10`. The three round errors over `q = 2^192` (`rbrError_le`): the
copy argument `(4 N + 8) / q = (2^26 + 8) / 2^192`, about `2^-166` (upstream `(2 N^2 + 4 N + 8) / q`, about
`2^-143`), the identities `(11 * 2^24 + 8) / 2^192 < 2^-164`, the last `3 / 2^192`; each `≤ 2^-128`, so
`knowledgeSoundness_bits`, `knowledgeSoundness_ofCantor`, `knowledgeSoundness_membership`, `Instance.soundness` give
`(Q + 3) / 2^128`.

*The first challenge, tight* (`card_consistent_le`, `card_copy_le`, `LogDerivative.lean`). Upstream excluded
`2 N^2` values of `β` (any two poles meeting) and `2 N q^2` triples with a vanishing denominator. Now, if the
copy from `x₁` to `σ x₁` fails: a consistent triple has, at every cell, both denominators zero or neither
(`consistent_denominators`: the copy identity at a cell is `D D' h = D + D' + pub w D D'`), and where none
vanishes the sum of logarithmic derivatives meets the target. The pole `w(σ x₁) + β σ x₁` of the first term of
`σ x₁` is cancelled only by the first term of another cell (`N - 1` values of `β`) or the second term of a
cell other than `x₁` (`N - 1` values; the second term of `x₁` has the same label and another value): outside
these `2 N - 2` values (`poleBetas`) the cleared polynomial in `α` is not zero and of degree at most `2 N`, and
every consistent `α` is a root of it. So at most `(2 N - 2) q + 2 N q` pairs `(α, β)` per `γ`, and with the other
cases (a gate fails: `2 N q^2`; a word fails: `(2 N + words) q^2`) at most `(4 N + words) q^2` triples.

*The margin for WHIR's lists* (`rbrError_mul_sq_le`, `rbrError_list_margin`, `rbrError_list_margin_ofCantor`,
`roundError_mul_sq_le`; used by the union bounds of `Compose` and of `ComposePcs/ListChain4.lean`, while the end
theorem's chain is pinned by the out-of-domain answers instead, `Pinned4.lean`). With WHIR without an out-of-domain
sample at level 0, each challenge is union-bounded over the level-0 Johnson lists involved: `L` for `(α, β, γ)` and
for `ρ`, `L^2` for `t`. For any `L ≤ 2^18` (leanerVM's generic list hypothesis; its certified parameters give
`L ≤ 7908`) and identities of degree at most `2^28`, every round error times `L^2` stays at most `2^-128`: on the
instance `2^36 (2^26 + 8) / 2^192`, about `2^-130`, `2^36 (11 * 2^24 + 8) / 2^192`, about `2^-128.5`, and
`3 * 2^36 / 2^192`. Both tightenings are needed: upstream's first round times `2^18` is `2^-125`, and the summed
degree `2^28 + 2^22 + 9230` times `2^36` exceeds `2^-128`.

Zero knowledge: `zkError = (2 N + 4 * 2^22) / q = 3 * 2^24 / 2^192` (`zkError_le`, the mask's vanishing polynomial
`w_22` in the row variable). The honest messages (`honest_legal`, for a first message of degree `2^22 + 2`): copy
quotient at most `3 * 2^24 + 9249`, gate quotient at most `7 * 2^22 + 22`, both within the quotient table's `2^26`.
Completeness's uncounted rejection (`1 + w_k(t) = 0` for some `k ≤ m + 1`) is about `2^26 / q`.

**The claims against the Rust `reduce`** (at `f96a7938`). Reviewed coordinate by coordinate: the witness, wiring and
quotient claims' points and values, the sum claim, the cells of the row of `t`, the gate, the public weight's
product, the target, the rows' polynomial and the rejection; the comparison is written out above
`claims_iff_accepts_ofCantor` (`Concrete.lean`). No mismatch; `reduce` is leanVM's but for the gate, which is the
model's `gate` on `cellAt`.

## The Keccak-256 chain (F4a, `formal/QuotientRpm`)

`QuotientRpm` lifts F1's knowledge soundness from a random oracle on `(statement, messages)` to the Keccak-256
transcript of `transcript.rs` (the chain of two roots, no out-of-domain answers, whose lemmas `ComposePcs`'s four-root
chain reuses), commitments still ideal: `knowledgeSoundness_chain` (ROM, `(Q + 8)(roundError + 3(Q + 8)/2^256)`),
`knowledgeSoundness_rpm` (one random permutation, `+ Q²/2^509`), and for every circuit `Instance.soundness_rpm`:
`(Q + 8)(2^-163 + 3(Q + 8)/2^256) + Q²/2^509`.
