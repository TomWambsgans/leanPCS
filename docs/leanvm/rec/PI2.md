<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# π2's PIOP: prover, verifier, contract, gas

π2 proves that π1's recorded verifier (the Keccak VM's π1-rec3, `SPEC-REC.md` §1) accepts and outputs its `PCS_OPEN`
claims. Its circuit is `SPEC-REC.md` §10's; this file is its PIOP. Code in `crates/leanvm/rec/src/pi2/`; the Lean
proofs are in `formal/RecCompose`. Numbers are **measured** unless marked modelled; the real runs below are on a Mac
(Apple M4 Max, 16 cores, `RUSTFLAGS="-C target-cpu=native"`, 2026-11-08, with other jobs running: load average 9–11,
three runs within 0.1 s).

```sh
export RUSTFLAGS="-C target-cpu=native"   # the field's native SIMD paths (AVX-512/GFNI on x86)
cargo test --release -p leanvm_rec --lib pi2                                                  # indicators, inverse, WHIR queries
cargo test --release -p leanvm_rec --test pi2 -- --nocapture                                   # synthetic circuits, contract parity
cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_gas            # the real circuits' gas
cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_end_to_end     # 2^24 prover, end to end (10 GB)
PI2_VECTOR=keccak_rec3 cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_end_to_end   # 400 signatures
cargo test --release -p leanvm_rec --test pi2 -- --ignored --nocapture gas_report               # the synthetic target shapes
```

## 0. Results

**The contract, on the real circuit** (D16v × π1-rec3, `real_end_to_end` on `keccak128_rec3.txt`; `c = 0`, no
21,000 base):

| | 128 signatures (reference) | 400 signatures |
|---|---:|---:|
| calldata (zero bytes) | 980 B (66) | 980 B (62) |
| execution | **28,325** | 29,105 |
| code | 13,491 B, one contract | 13,911 B |
| claims / calls | 7 / 6 | 7 / 6 |
| **EIP-7623** | **43,213** (floor 37,220) | 44,041 |
| with the 21,000 base | 64,213 | 65,041 |
| EIP-7976 | 62,720 | 62,720 |

At `c = 0` the standard price binds (`16 · 914 + 4 · 66 + 28,325`). The contract at the reference shape: 753
`FIELD_MUL`s, 860 `XOR`s, 6 Keccak-256 (1,184 B), 244 words of memory, 208 words written for `PCS_OPEN`; the straight
build is the deployable one. The execution depends on the circuit alone: `real_gas` and `tests/keccak_vm_rec.rs`
measure it on a sample stream (4 zero bytes; 44,737 at 400 signatures).

**The prover** on the real witness (128 signatures):

| | |
|---|---:|
| the witness: compile, adapt, check | 3.8 s |
| the setup's commitment (`σ`, `κ`; once per circuit, not per proof) | 1.5 s |
| **prove / open (3 WHIR openings)** | **4.4 s / 1.7 s** |
| peak memory (the circuit's compilation included) | 9.79 GB |

At 400 signatures (an earlier run, Mac): 2.9 s compile, 3.0 s prove, 0.9 s open, 9.8 GB. π1-rec3's own prover at
128 signatures: 2.72 s cold with its checks (6.75 GB); warm, median of 3, 3.65 s (6.86 GB).

**End to end** (`real_end_to_end`): π1-rec3's real proof → its circuit and witness → π2's proof → its three openings
verify (`quotient::opening::verify`, what `PCS_OPEN` checks) → the contract accepts, `PCS_OPEN` attesting exactly its 7
claims in 6 calls (π1's 3 are the vector's inputs, which π1's openings prove; π2's 4 in 3) → 18 flipped calldata bytes
(the public input, π1's roots and elements, `W`'s and `Q`'s roots, the values) are each rejected.

D32v (`PI2_LAYOUT=d32v`) is supported by the same prover and verifier, and tested on synthetic circuits (§6); it has
not been measured on the Keccak VM's π1.

## 1. What π2 proves

`crate::circuit::spec` is the interface (SPEC-REC.md §10.1); `pi2::adapt` turns it into the PIOP's
`pi2::circuit::Circuit`:

- `N = 2^m` positions on `V_m`, rows of `2^r` (D16v `r = 4`, D32v `r = 5`); position `i` at `ω_i`.
- Every position pushes `(P(ω_i), σ(ω_i))`: `P = w + Σ_p I_p (E_p + w) + κ`, `I_p` the indicator of pair `p`'s coset
  (a (block, role) pair whose formula is not a forward), `E_p` its formula of the row's cells.
- Every position but the **holes** pulls `(w(ω_i), ω_i)`. A hole is a port's own position: its push goes to an outside
  tag `ω_{N+J}`, and no formula reads its value.
- The public side: for each port `J`, the verifier adds `1/(α + F_J + β ω_{N+J})`.

So the copy argument is: `h = (1 + 1_S)/(α + w + βx) + 1/(α + P + βσ)` on `V_m`, `1_S` the holes' indicator (the
sum of the port pairs'), and `Σ_V h = Σ_J 1/(α + F_J + β τ_J)`. The identity is
`h d_pull d_push + (1 + 1_S) d_push + d_pull = q Z_V`, of degree below `5N` (`1_S d_push` is below `4N`), so `q` is
below `4N` as in SPEC-REC §2.3. Both sides are sets of (value, tag) pairs: the pulls' tags are the non-hole positions,
the pushes' are `σ`'s values (injective), the public tags are outside `V_m`.

## 2. The protocol

**Transcript** (`KeccakChannel`): the seed `keccak(NAME ‖ IV ‖ public input)`, `NAME = "leanvm-rec-pi2v1"`, then the
stream:

1. the public data: π1's roots `C1`, `C2` (32 bytes each, `PCS_OPEN`'s root words, §8), π1's claims' 17 distinct
   elements (14 narrow challenges and 3 values, 24 bytes each);
2. `W`'s root; `α, β, γ`;
3. `Q`'s root; `t`;
4. the `2^r` fold values `a_k` and `ξ = κ(t) + β σ(t)` (17 values for D16v, 33 for D32v); `ρ`.

The first challenge hashes the state and everything before it: the public data is bound there, not by a separate
`keccak(public data)`. The **IV** is `keccak("leanvm-rec-iv-v2" ‖ π1's contract IV ‖ the setup root ‖ the circuit's
digest ‖ the three layout words)` (`prover::iv`), a constant of the code.

**The tables.**

| table | content | variables | stack | basis |
|---|---|---:|---:|---|
| `W` | `w` | `m` | `max(m, 24)` | `B` (`B_k = Π_l (w_l or 1 + w_l)`) |
| `Q` | `h` (degree `< N`) and `q`'s four chunks, three limbs each: 15 chunks of `N` | `m + 5` (position, 2 digits, `h` or `q`, 2 limbs) | `m + 4`: 60 lanes of `2^(m-2)` | novel |
| setup | `κ` then `κ + σ` | `m + 1` | `max(m + 1, 24)` | `B` |

The stacks are at least `2^24` words, the smallest leanerVM's certified parameters cover; the query ladders of every
stack are pinned to `params/whir_params.py --large`'s (`stacks_take_the_certified_queries`). D32v's `W` (`2^23` words)
sits on a `2^24` stack, half its lanes absent. Small test circuits take `2^15` stacks.

**The verifier at `t`** (`verifier::reduce`, generic over `Scalar`):

1. the digits `w_0 … w_{m+2}`, `w_{l+1} = w_l² + w_l`;
2. the row's cells `v_c = w(t + ω_c) = Σ_k a_k eq(k, (w_l + ω_{c>>l})_{l<r})`, folding the top variable first, the odd
   cell of each pair from the even one (§9, lever 3a): `r · 2^(r-1)` products;
3. the normalised block polynomials `Ẑ_s(t)`, `Ẑ_s = Ẑ_{s-1} + c_s Ẑ_{s-1}²`, so that
   `I_p(t) = w_m / (Ẑ_s(t) + Ẑ_s(c_p))`: `w_m` factors out of every indicator;
4. each group's indicators (pairs of one role, one formula) summed as one fraction `N_g / D_g`; the public side as one
   fraction `N / D`, its `β ω_τ` along a walk of the tags' bits, the zero checks' coset in closed form (§9, lever 3c);
5. the pushes' sum `A / B = Σ_g (N_g/D_g)(E_g(v_{c⊕k_g}) + v_0)` accumulated as one fraction (a one-pair group
   adds `X/d`, three products; a larger one `N_g X / D_g`, four), the pull-less groups' `S_n / S_d` likewise; then
   `P(t) = v_0 + w_m A/B + κ(t)`, `d_push = α + P(t) + βσ(t) = D_n / B` with `D_n = (α + v_0 + ξ) B + w_m A`,
   `d_pull = α + v_0 + βt`, `1_S = w_m S_n / S_d`;
6. the identity `h d_pull d_push + q w_m = (1 + 1_S) d_push + d_pull` at `t`, one combination of `h(t)` and `q(t)`:
   `Y = d_pull D_n + w_m B = B (d_pull d_push + w_m)`, `X = (S_d + w_m S_n) D_n + d_pull B S_d`;
7. one inversion, of `S_d Y · w_{m+2} · D` (required nonzero: it covers `t ∈ V_{m+2}`, every group denominator and the
   public side's), by the norm (two Frobenius maps from the limbs' shifts, 76 products); `1/w_{m+2}` from it, and
   `1/w_l = (1 + w_l)/w_{l+1}` down to `l = 0`.

**The claims** (4 in 3 calls, after π1's 3):

- `W` at `(ρ, ρ², …, ρ^{2^{r-1}}, w_r, …, w_{m-1})`, value `Σ_k eq(ρ⃗, k) a_k`;
- `Q` at `(u_0, …, u_{m+1}, ρ', y_0, y_1)`, `u_l = w_l/(1 + w_l) = 1 + 1/w_l + 1/w_{l+1}`, `ρ' = w_m B / Y` (the
  identity's `c_q/(c_h + c_q)`), value `s (t / w_{m+2}) X / (S_d Y)`, that is `(1 + ρ') h(t) + ρ' q(t)` (`(y_0, y_1)`
  and `s` the limbs' coordinates and scale, as `crates/membership/quotient`; `Π (1 + w_l)^{-1}` telescopes to
  `t / w_{m+2}`); and at `(1^m, 0, 0, 0, y_0, y_1)`, `h`'s top coefficient `Σ_V h`, value `s T`;
- the setup at `(w_0, …, w_{m-1}, β)`, value `ξ` (its halves `κ`, `κ + σ`: `(1 + β) κ + β (κ + σ) = κ + βσ`).

**The contract** (`contract`): reads the stream, runs the verifier, then calls `PCS_OPEN` 6 times: π1's three (their
words `circuit::spec::Circuit::calls`: constants, the stream's roots, the elements read, the pairs' coordinates
derived from their challenges), then `W`'s (one claim), the setup's (one; its root a constant) and `Q`'s (two). Layout
words: π1's as the vector's; π2's `prover::layout_word` (§8).

## 3. The prover (`prover`)

1. `w`'s novel coefficients (`quotient::ntt`), its `B` coefficients (subset sums): `W`, committed.
2. `α, β, γ`; the pushes on `V_m`; `h` (one batched inversion a run of 4,096), checked to sum to the public target;
   `h`'s novel coefficients.
3. On `D = β_{m+2} + V_{m+2}` (`4N` points, disjoint from `V_m`): `w`, `h` by transforms (four transforms of `2^m`),
   `σ`, `κ` with the setup (fixed by the circuit). Eight points at a time: the row's cells (`x + ω_c` stays in `D`),
   every pair's indicator (a chunk of 4,096 points at a time: a pair whose block spans the chunk is periodic in it, one
   batched inversion), the formulas, `P`, `d_pull`, `d_push`, and `q = numerator / Z_V` (`Z_V` takes four values on
   `D`). `q`'s novel coefficients: `q` has degree below `4N`, so `4N` points determine it.
4. `Q`, committed (its stack built in place); `t`; the fold values and `ξ`; `ρ`; the verifier's claims, opened by
   `quotient::opening` (leanVM's WHIR unchanged, rate 1/2, the claims on one commitment in one opening).
   `PI2_PROFILE=1` prints the phases.

## 4. Decisions and deviations from SPEC-REC's design

1. **Holes are pull-less, not summed** (the design added the holes' sums `Σ 1/D(0, ω_h)` to the target). The
   identity's pull term carries `1 + 1_S`, `1_S` the sum of the port pairs' indicators, which the verifier has computed
   anyway; the holes' closed-form sums are not needed. A hole's value is then unconstrained: `adapt` checks that no
   formula of a port's region reads a hole (the circuit compiler never places a value there), and panics otherwise;
   `Circuit::validate` is asserted on the setup path (`Spec::of`, `Setup::new`, `contract::Instance::new`) too. Same
   degree, same soundness argument, with one case to account for: at a hole the identity reads
   `d_pull (h d_push + 1) = 0`, so if `α + w(x) + βx = 0` there, `h(x)` is free, and so is `Σ h`. `w` at a hole is
   committed in `W` before `α, β`: this is the vanishing-denominator event, at most `(ports) · L_W / 2^192`, inside
   SPEC-REC §5's `4N/2^192` term.
2. **The ports' fingerprints are not `Σ γ^l L_l`.** Three limbs (an element, a zero check) are `L_0 + Y L_1 + Y² L_2`:
   the element itself, so the verifier's term is `α + x + βτ` with no product. Four limbs (the statement, a root) are
   `(L_0 + Y L_1) + γ (L_2 + Y L_3)`: a root's two 16-byte halves as `next_root` reads them, one product. Both bind the
   limbs (injective on `K³`; for all but one `γ` on `K⁴`), as `spec::Circuit::check` compares them.
3. **`h(t)` is not sent** (§9, lever 2): `Q`'s claim is the identity's combination of `h(t)` and `q(t)`, and the
   verifier inverts once at the end. (The first build sent it, with `σ(t)` and `κ(t)` apart: `2^r + 3` values.)
4. **`W` and the setup in the `B` basis, `Q` in the novel basis.** The `B` basis makes a claim at the digits themselves
   (no inversion); `Q` needs the novel basis for `Σ_V h` to be one entry (the top coefficient), so its point takes the
   `u_l`.
5. **`ρ` is `W`'s fold only.** `W`'s claim is a polynomial of degree `2^r − 1` in `ρ`; the setup's and `Q`'s claims
   take no `ρ` (§9, lever 2).
6. **The extension coset is `4N`**, not `8N`: `q` has degree below `4N`.
7. **The public data is in the stream**, absorbed by the first challenge, the statement in the seed (the design: a
   separate `D = keccak(public data)`).
8. **No row counts among the public terms** (SPEC-REC §10.4 item 3).
9. **Stacks of at least `2^24` words** at the target shapes (§2).
10. **The verifier's arithmetic** (§2): normalised indicators, fractions by groups, the inverse by the norm. Measured on
    the synthetic D16v target: 56.3K → 46.2K execution, before §9's levers.

## 5. The synthetic circuits (`synth`)

Before the real circuit existed, `synth` built circuits with every row kind of SPEC-REC §2.4 / §2.6 (χ formulas, D
units, XORs, packings, free bits, `E` products and sums, constants, ports of every source) and a witness satisfying them
by construction (FIFO wiring), small (`2^11`, `2^12` positions) and at the design's target shapes (`2^24` and `2^23`,
about 200 and 280 pairs, `target_d16v`, `target_d32v`). They remain the PIOP's tests and `gas_report`'s shapes. The real
D16v circuit of the Keccak VM's π1 has 133 pairs at the reference shape.

## 6. Tests

- `lib`: an indicator is one on its coset and zero on `V_m`'s rest (every alignment and size); the inverse; the zero
  coset's closed form; the stacks' WHIR query ladders are the certified ones.
- `tests/pi2.rs`, D16v and D32v synthetic circuits and the interface's own example (padded, through `adapt`):
  - the honest proof's four claims hold on the tables and its three openings verify;
  - witness mutations (random constrained positions), a changed element, a changed public input: a false claim;
  - flipped stream bytes: claims the openings do not prove;
  - the contract equals the Rust verifier word for word, straight and deployable, on the honest stream and a random
    one; it accepts the honest proof with `PCS_OPEN` attesting exactly its calls, and rejects flipped bytes.
- `tests/pi2_real.rs`, the real circuits (`PI2_VECTOR=keccak128_rec3`, the default, or `keccak_rec3`): `real_gas`, the
  gas and parity (straight, deployable) of D16v; `real_end_to_end` as in §0.
- `tests/keccak_vm_rec.rs`: π1-rec3 at 128 and 400 signatures compiled into D16v on a sample stream, the contract's gas
  and parity.
- `tests/lean_pi2_prover.rs`: vectors for the Lean honest prover's differential test (`formal/RecCompose`).

## 7. Soundness (as SPEC-REC §5)

The rounds are SPEC-REC §5's, as the Lean states them (`formal/RecPiop`'s `err`):

- the copy argument `(α, β, γ)`: `(3N + 2)/2^192` over `W`'s list, the pulls over the non-holes, `γ` the four-limb
  ports' fingerprints, degree 1 (153.1 bits after the list);
- `t`: the identity, degree below `5N`, over `W`'s and `Q`'s lists (140.6 bits after the union);
- `ρ`: `W`'s fold (degree `2^r − 1`) over both lists (163.0).

These depend only on `N` and the stacks. With the three openings charged once (`269 · 2^-137` a query), π2 keeps
128.93 bits as `Q/ε` at `Q = 2^64`: `RecCompose.pi2Bound` (`pi2Bound_le_bits`).

## 8. The `PCS_OPEN` ABI, the IVs, the setup path

- **One `PCS_OPEN` ABI for the six calls.** Every call is `machine.rs`'s `root word, layout word, k, k × (point,
  value)`:
  - every root word is `PCS_OPEN`'s, `s_0 · 2^128 + s_1` (`machine::root_word`: each 16-byte half of the hash
    reversed). π1's prover sends a root as its two WHIR scalars, so π1's stream carries `C1`'s and `C2`'s root words as
    they are, and the circuit's root ports pack the stream's bytes as they are (`circuit::compile`). π2's `W` and `Q`
    roots are in calldata so; π1's setup root `F` and π2's setup root are constants so;
  - every layout word names its stack: π1's are `leanvm_univariate::contract::layout_word`'s (shape, code, variables,
    words placed); π2's `prover::layout_word`'s, in the same format (the tag `"pi2"`, `log_n`, the codes `0x5601`
    `W`, `0x5602` `Q`, `0x5603` setup, the variables, the words placed). π2's IV hashes these words;
  - a precompile is a registry keyed by the layout word (`contract::registry`): π1's layouts are opened by
    `leanvm_univariate`'s opening, π2's three by `quotient::opening`; `Q`'s two claims stay in one call (one opening).
  - The mock decodes (`leanvm_statement::evm::machine::{decode, PcsOpen::decoding}`): an input attests only if it
    decodes under the registry (a known layout word, which fixes the variables; `k ≥ 1`; the exact length; every
    element's top 64 bits zero) into a registered opening (the root as its opening has it, the layout word, the
    claims). The end-to-end tests register π1's openings from the vector's inputs (`contract::pi1_opening`) and π2's
    from the proof's roots and the reduction (`contract::openings`), so a call in another format fails them.
- **The holes on the setup path.** `Spec::of` and `Setup::new` assert `Circuit::validate`, which also requires `κ` zero
  off the expression slots.
- **Derived instances.** The circuit compiler takes the program's IV (`compile::Inputs::program_iv`) and derives
  π1's contract IV from the recorded verifier (`Recorded::iv`: its shape, setup roots and variant), kept as
  `Compiled::pi1_iv`. `contract::Instance::new` builds the instance from the validated circuit, its spec, the setup
  root, π1's IV and calls, and computes π2's IV.
- **π1's IV binds its variant.** `leanvm_univariate::contract::contract_iv` hashes `variant_bytes` (the tag
  `"keccak-vm"`, the skip and the Fiat–Shamir shape's code), so a π1-rec3 proof is not a main-line proof.

## 9. Optimisation levers

Each lever is in the code; its gain was measured when it was made, on the π1 of that time, so the figures below are
the gains then, and the current figures are §0's.

**Lever 1d: π1-rec3, the paired batch** (`SPEC-POINTS.md` §3; `FsShape::Rec3`; **π1's Fiat–Shamir shape**). The
batching sumcheck takes two variables a round on `V_2`'s coordinate functionals: a pair's polynomial
`G(X) = G̃(y_0(X), y_1(X))` of degree 8, its stream `c_0, c_1, c_2, c_4 … c_8` (`c_3 = claim + c_6`, as `V_2 = GF(4)`),
one challenge `z_j` a pair, the point's coordinates `pair_point(z_j) = (z_j + β_1(z_j² + z_j), z_j² + z_j)`; at 27
variables 13 pairs and one plain round, at 28 variables 14 pairs: 14 challenges, all narrow (lever 1c).
- **π1's prover** (`prover::batch::prove_pairs`): `G̃` from four rounds on the batch's state, the one on `u_0` (with the
  claim it gives all of `h(u_0)`) and the one on `u_1` with `u_0` bound to `0`, `1`, `β_1` on clones (`Weight` and
  `Folded` are `Clone`); `G̃`'s coefficients in `u_0` by interpolation (`β_1² + β_1 = 1`: no inversion); `G` by
  composition. Checked against the claim each pair (`c_3 + c_6`).
- **π2** (`circuit::compile::pair_coordinate`): a call word that is `y_0(z)` or `y_1(z)` of a challenge `z` becomes
  `CallWord::Pair { element, coordinate }`, `z` the port (`spec::pair_word`; `public_from_calls` recovers
  `z = y_0 + β_1 y_1` and checks both coordinates); π2's verifier computes `pair_point` of its public scalars
  (`Reduced::pair_points`, dead unless a call reads them).
- **The contract** reads 14 `z_j` and 3 values, and derives the coordinates (one squaring, one product by `β_1` and two
  additions a pair).
- **Soundness**: a pair of degree 8 with a narrow challenge errs with probability `8/2^160`, over `C1`'s and `C2`'s
  lists (`SPEC-POINTS.md` §5).

**Lever 1c: narrow batch challenges** (`FsShape::Rec2`'s, kept by `Rec3`; `Channel::sample_narrow`,
`transcript::NARROW_BITS`; **π1's Fiat–Shamir shape**). The batching sumcheck's challenges, which the contract carries
in calldata, are the hash's low 160 bits instead of 192 (limb 2 below `2^32`): each element's 24 calldata bytes start
with four zeros, which EIP-7623 prices at 4 (standard) and 10 (floor) instead of 16 and 40. π1's verifier draws them
with `sumcheck_pairs_drawn(.., narrow)`, its prover likewise, the recorder as `record::Node::Narrow` (an `AND` with 20
bytes of ones in the contract), π2's circuit packs limb 2 from 32 digest bits. A plain round of degree 2 errs with
probability `2/2^160`. Not taken: reading the challenges as 20 bytes (a new read width in π2's verifier and stream).

**Lever 1a′: no claims on Flock's matrices.** The Keccak VM's π1 has none: its lincheck terminal is the structured one
(`keccak_flock::structured_terminal`), computed by π1's verifier, so its claims are three (`C1`, `C2`, `F`), all at the
batch's point.

**Lever 3c: the zero checks as one closed-form term.** π1's zero checks are ports of value 0, each a fraction
`1/(α + βτ_J)` of the public side. The circuit compiler makes them the first ports, padded with constant-zero ports
(`spec::Source::Pad`) to a power of two `2^k`, so that their outside tags are the aligned coset `ω_N + V_k`.
`Spec::of` finds such a coset of zero-valued terms (`Spec::zero_coset`), and the verifier adds its sum in closed form:
with `Y = α + βω_N` and `F = β^(2^k) w_k(X/β) = Σ a_i X^(2^i) β^(2^k − 2^i)` (`w_k = s^k`, the Cantor subspace
polynomial; `X^16 + X` for `k = 4`), `Σ_(u ∈ V_k) 1/(Y + βu) = F'(Y)/F(Y) = β^(2^k − 1)/F(Y)`, about 15 products
instead of one fraction a check. Tested against the sum (`the_zero_coset_sum_is_its_closed_form`, `k ≤ 5`).

**Lever 3b: the calls' inputs written once** (`evm_link::front::Source::reuse`, `codegen::Ending::PcsOpenReusing`).
Each call's input is written at the region's start just before the call, and only where the call before left another
word (a zero of fresh memory is not written either). π1's calls at the batch's point (`C1`, `C2`, `F`) write `r` once;
π2's calls are ordered `W`, the setup, `Q`, so the setup's point reuses `W`'s digits `w_4 … w_{m-1}`. The node of a
word written once is then read once, so it is not kept in a memory slot either. The parity build keeps the words in
place (it returns them all).

**Lever 3a: the fold's siblings.** At every level of the row's fold, the cells `2k` and `2k + 1` fold their parent at
`z = w_l + ω_{2k}` and `z + 1` (`ω_{2k+1} = ω_{2k} + β_0`, `β_0 = 1`), so the odd one is the even one plus the
parent's difference `p_j + p_{j+half}`: `r 2^(r-1)` products instead of `r 2^r` (D16v 32 instead of 64).

**Lever 2.**

- **`σ(t)` and `κ(t)` as one value.** The verifier uses them only in `d_push = α + P(t) + βσ(t)`, `P` holding `κ(t)`:
  as `ξ = κ(t) + βσ(t)`. The setup's halves are `κ` and `κ + σ`, so its one claim at `(w_0, …, w_{m-1}, β)` is
  `(1 + β)κ(t) + β(κ + σ)(t) = ξ`, with no inversion. The setup is honest (`L = 1`) and fixed before `β`: the claim
  binds `ξ` exactly. `ρ` does not enter the setup's claim.
- **`h(t)` not sent.** The verifier keeps every quotient as a fraction and inverts once at the end (§2, steps 5–7):
  the pushes' sum `A/B`, `d_push = D_n/B`, and the identity at `t` as the one combination of `h(t)` and `q(t)` it is,
  `c_h h + c_q q = (1 + 1_S) d_push + d_pull` (`c_h = d_pull d_push`, `c_q = w_m`). `Q`'s claim is that combination,
  normalised: `(1 + ρ')h(t) + ρ'q(t)` at `ρ' = c_q/(c_h + c_q)`. This is exactly the identity at `t`, so `t`'s error is
  unchanged (`5N` over `L_W L_Q`); `ρ` does not enter `Q`'s claim either, and is only `W`'s fold (degree 15 over
  `L_W`). The one inversion is of `S_d Y · w_{m+2} · D`, required nonzero (it covers `t ∈ V_{m+2}`, hence every pair's
  denominator, and the public side's); the digits' inverses follow from `1/w_{m+2}` by `1/w_l = (1 + w_l)/w_{l+1}`.
  The batched inversion is gone.
- **D8v (rows of 8, 8 fold values: −192 B) is dropped.** With `Q = 15N` words, `N` must stay `2^24` (`2^25` gives
  `2^28.9`). At the reference shape's 116 permutations and 0.48M other positions, a Keccak-f must fit in about 140K
  positions, 7% more than D16v's 130,944. A χ output reads three `b = A + D` of its plane, so a row of 8 holds the
  inputs of at most two outputs, or must materialise `b` (one more position a state bit, and its forwards): about 2×
  D16v's positions a round, well past 140K.
