<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# π2's PIOP: prover, verifier, contract, gas

π2 proves that π1's recorded verifier (the Keccak VM's π1-rec4, `SPEC-REC.md` §1) accepts and outputs its PCS claims.
Its circuit is `SPEC-REC.md` §10's; this file is its PIOP, **π2v4** (transcript `leanvm-rec-pi2v4`,
`pi2::verifier::NAME`): the ports out of the copy argument, `P` committed in `Q`, `q` below `2N` (§1, §7), on the EIP
draft's PCS claims (§2, §8), the copy argument's sum forced by `Q`'s layout rather than claimed (§2, §7: two claims on
`Q`; π2v3 had a third). Code in `crates/leanvm/rec/src/pi2/`. The Lean (`formal/RecCompose`) states π2v3 as of
commit `f96a7938`, over π1-rec3 with π1's claims encoded by the contract (§10). Numbers are **measured** unless marked
modelled; superseded versions (π2v1, π2v2 before the PCS claims) are in `docs/HISTORY.md`, "leanVM".

```sh
export RUSTFLAGS="-C target-cpu=native"   # the field's native SIMD paths (AVX-512/GFNI on x86)
cargo test --release -p leanvm_rec --lib pi2                                                  # indicators, Φ's basis, inverse, WHIR queries
cargo test --release -p leanvm_rec --test pi2 -- --nocapture                                   # synthetic circuits, contract parity
cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_gas            # the real circuits' gas
cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_end_to_end     # 2^24 prover, end to end
PI2_VECTOR=keccak_rec4 cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_end_to_end   # 400 signatures
LEANVM_TRACE=<trace> cargo test --release -p leanvm_rec --test pipeline -- --ignored --nocapture                     # trace → π1 → π2, timed
cargo test --release -p leanvm_rec --test pi2 -- --ignored --nocapture gas_report               # the synthetic target shapes
```

## 0. Results

At the reference shape (128 signatures; `real_end_to_end`, `SPEC-REC.md` §6):

- **Calldata** 577 B (4 zero): the public input, `W`'s and `Q`'s commitments, the 18 values at `t`, the frame's index.
- **Gas**: 31,212 execution; frame transaction standard 40,396, floor 36,928; **63,328** with the frame of the 7 PCS
  claims (225 B) and the PCS gas (12,000; the floor binds: `64 · (577 + 225) + 12,000`, 7,332 of execution to spare).
  At 400 signatures: 35,452 execution, 63,328 (3,104 to spare). π2v3: 31,524 and 66,376 (eight claims).
- **The contract**: 14,328 B (16,287 at 400), 798 `FIELD_MUL`s; four claims encoded (π2's), at payloads 3 … 6.
- **The prover** (`tests/pipeline.rs` via `bench.sh`, 8 threads of an AMD EPYC 9355P): 2.29 s a proof (π2's proof 0.74 s, its four
  openings 0.51 s; peak RSS 15.6 GB), against π2v3's 2.52 s (0.75 s, five openings 0.73 s): one opening of `Q`'s `2^28`
  words fewer, and `H = x h` (`mul_x`) within the noise of π2's proof. Interleaved A/B on h3 (`bench.sh`'s protocol, 8
  threads, cores 0-7, under the bench lock), four runs each, totals (each the median of five passes): π2v3 2.588,
  2.780, 2.516, 2.515 s; π2v4 2.576, 2.584, 2.290, 2.292 s; the first two pairs ran on a busy host (the idle check
  timed out: π1's unchanged proof 0.88–0.98 s there), the last two on an idle one (π1 0.86 s on both).

## 1. What π2 proves

`crate::circuit::spec` is the interface (SPEC-REC.md §10.1); `pi2::adapt` turns it into the PIOP's
`pi2::circuit::Circuit`:

- `N = 2^m` positions on `V_m`, rows of `2^r` (D16v: `r = 4`); position `i` at `ω_i`.
- **Internal positions.** Every position but the **holes** pulls `(w(ω_i), ω_i)` and pushes `(P_v(ω_i) + κ(ω_i),
  σ(ω_i))`, `σ(ω_i)` a position (inside `V_m`, never a hole): `P_v = w + Σ_int I_p (E_p + w)`, `I_p` the indicator of
  pair `p`'s coset (an internal pair: a (block, role) pair whose formula is not a forward nor a port; its formula `E_p`
  of the row's cells is in `K`), `κ` the setup's constants.
- **Holes.** A hole is a port's own position: its push is the port's fingerprint `E_p` of its row's limbs, which must
  be the public value `F_J` of its port `J` (`σ` sends it to the outside tag `ω_{N+J}`); no formula reads a hole.

So π2 checks two things on `V_m`:

1. **The copy argument, over the internal positions:** `h = (1 + 1_S)(1/(α + w + βx) + 1/(α + P_v + κ + βσ))`, `1_S`
   the holes' indicator (the sum of the port pairs'), and `Σ_V h = 0`. Both sides are sets of (value, tag) pairs: the
   pulls' tags are the non-hole positions, the pushes' are `σ`'s values (injective, the non-hole positions).
2. **The ports:** `T = Σ_port I_p (E_p + Φ_{k_p})` vanishes on `V_m`, with `Φ_k(x) = Σ_J F_J w_m(x) / (w_r(x) + ω_{y_J})`
   over the ports `J` of role `k` and nonzero value, `y_J` the hole's row. In the Cantor basis `w_r(ω_i) = ω_{i >> r}`,
   `w_m = w_{m-r} ∘ w_r`, and `w_{m-r}' = 1` (`w_{m-r}` is linearised, its linear coefficient 1): `w_{m-r}(z) / (z +
   ω_y)` is `V_{m-r}`'s Lagrange basis at `ω_y`, so `Φ_k` is `F_J` on the hole's row `y_J` (every role of it) and zero
   on the other rows; `I_p` keeps the hole. At a hole `T = E_p + F_J`, elsewhere `0`. A port of value zero (π1's zero
   checks, their padding) is in no `Φ`: its `T` is its fingerprint. (`Φ`'s basis is tested: `the_ports_lagrange_basis`.)

One identity holds both, `h d_pull d_push + (1 + 1_S)(d_push + d_pull) + T = q Z_V`, with `d_pull = α + w + βx` and
`d_push = α + P + κ + βσ`, where `P` is `P_v`'s interpolation (degree below `N`), committed: off the holes it is the
copy argument's, at a hole it reads `h d_pull d_push = T` (§7). `P`'s definition is a second identity, `P = P_v + Z_V
q_P`. Degrees: `h`, `P`, `w`, `σ`, `κ`, `I_p`, `Φ_k` below `N`, the formulas below `2N` (a port's, linear, below `N`),
so `T` below `2N`, `P_v` below `3N`, both identities below `3N`, and `q`, `q_P` below `2N` (checked on the real circuit
by its claims: §6).

## 2. The protocol

**Transcript** (`KeccakChannel`): the seed `keccak(NAME ‖ IV ‖ public input ‖ frame words)`, `NAME =
"leanvm-rec-pi2v4"`, the frame words the Keccak-256s of π1's claims hashed in the circuit (all three at 128 and 400
signatures: payloads 0, 1, 2 of the frame of PCS claims, `Read::Frame`; `SPEC-REC.md` §2.4.6), then the stream:

1. the public data of the claims the contract encodes (none when the circuit hashes all three; with the fallback,
   π1's root `C2` (32 bytes, as it is, §8) and the distinct elements of the claims the contract encodes: `C2`'s
   out-of-domain answer, the narrow challenges as their low 20 bytes, the values, 24 bytes each);
2. `W`'s commitment: its root, then its out-of-domain answer; `α, β, γ`;
3. `Q`'s commitment; `t`;
4. the `2^r` fold values `a_k`, `ξ = κ(t) + β σ(t)` and `s = P(t)` (18 values for D16v); `ρ`.

The first challenge hashes the state and everything before it: the public data is bound there, not by a separate
`keccak(public data)`. Each commitment is the EIP draft's (`crates/pcs_claim`, `docs/PCS_CLAIM.md`): a root and the
out-of-domain answer `f(z)`, `z` derived from the root, which binds the root to one polynomial; the challenges after
it are drawn knowing both. The **IV** is `keccak("leanvm-rec-iv-v3" ‖ π1's contract IV ‖ the setup root ‖ the setup's
out-of-domain answer ‖ the circuit's digest ‖ log_n)` (`prover::iv`), a constant of the code.

**The stacks.** Every commitment is of a whole stack (the EIP's committed polynomial: its `2^n` words, the zero tail
included), and every claim a point of it.

| stack | content | variables | words | basis |
|---|---|---:|---|---|
| `W` | `w` | `max(m, 24)` | `2^m`, its leading lanes | `B` (`B_k = Π_l (w_l or 1 + w_l)`) |
| `Q` | sixteen slots of `N` (`verifier::QUOTIENT_SLOTS`): `H = x h` (below `N`, three limbs), `q` (below `2N`: two chunks, three limbs), `P` (below `N`, in `K`), `q_P` (below `2N`, in `K`), four zero slots (`G`, `S`) | `m + 4` | all 64 lanes | novel |
| setup | `κ` then `κ + σ` | `max(m + 1, 24)` | `2^(m+1)`, its leading lanes | `B` |

`Q`'s slot is `b_0 + 2 b_1 + 4 limb`:

| slot bits `(b_0, b_1)` | limbs `l < 3` (an element of `E`): slots `4 l + b_0 + 2 b_1` | limb code 3 (`K`): slots `12 + b_0 + 2 b_1` |
|---|---|---|
| `(0, 0)` | `H = x h` (one digit) | `P` |
| `(1, 0)` | `q`'s digit 0 | `q_P`'s digit 0 |
| `(0, 1)` | `q`'s digit 1 | `q_P`'s digit 1 |
| `(1, 1)` | `G`, zero | `S`, zero |

(`verifier::{h_slot, q_slot, P_SLOT, QP_SLOT, EMPTY_SLOTS}`; a two-digit polynomial's digits are contiguous slots, on
the slot bits' anti-diagonal.) A point of `Q`'s stack is then `(position (m), b_0, b_1, limb bit 0, limb bit 1)`, and
its weight on the slots is a product over these bits: the claims below choose them so as to weigh what each needs. The stacks are at least `2^24` words, the smallest leanerVM's
certified parameters cover; every opening is the PCS version 1's (leanVM's WHIR at rate `1/2` on its ladder). Small
test circuits take `2^15` stacks.

**The verifier at `t`** (`verifier::reduce`, generic over `Scalar`):

1. the digits `w_0 … w_m`, `w_{l+1} = w_l² + w_l`;
2. the row's cells `v_c = w(t + ω_c) = Σ_k a_k eq(k, (w_l + ω_{c>>l})_{l<r})`, folding the top variable first, the odd
   cell of each pair from the even one (§9, lever 3a): `r · 2^(r-1)` products;
3. the normalised block polynomials `Ẑ_s(t)`, `Ẑ_s = Ẑ_{s-1} + c_s Ẑ_{s-1}²`, so that
   `I_p(t) = w_m / (Ẑ_s(t) + Ẑ_s(c_p))`: `w_m` factors out of every indicator;
4. each group's indicators (pairs of one role, one formula) summed as one fraction `N_g / D_g`;
5. the internal pushes `A / B = Σ_g (N_g/D_g)(E_g(v_{c⊕k_g}) + v_0)` over the pulling groups, accumulated as one fraction
   (a one-pair group adds `X/d`, three products; a larger one `N_g X / D_g`, four): `P_v(t) = v_0 + w_m A / B`;
6. the ports: `Φ_k(t) = w_m G_n / G_d`, `G_n / G_d = Σ_J F_J / (w_r + ω_{y_J})` (three products a port of nonzero value),
   and `R_n / R_d = Σ_g (N_g/D_g)(E_g + Δ + Φ_{k_g})` over the port groups, `Δ = d_pull + d_push`, `d_pull = α + v_0 +
   βt`, `d_push = α + s + ξ`: the identity's right side `(1 + 1_S) Δ + T` is `Δ + w_m R_n / R_d`;
7. `Q`'s claims (below), and one inversion, of `R_d Y_1 Y_2 · B · w_m · Y_3 · c_h D_n` (required nonzero; `Y_1 = c_h +
   t w_m`, `Y_2 = c_h + t w_m²`, `Y_3 = 1 + ρ (1 + w_m)`), by the norm (two Frobenius maps from the limbs' shifts, 76
   products); `1/w_m` and the others from it, and `1/w_l = (1 + w_l)/w_{l+1}` down to `l = 0`. `c_h = d_pull d_push`
   nonzero makes `1 + z_0 = c_h / Y_1` and `1 + z_1 = c_h / Y_2` nonzero, so that the identity's claim binds `H(t)`;
   `D_n = (α + v_0 + ξ) B + w_m A = B (α + P_v(t) + ξ)` is there for the contract (its graph then computes `A` and `B`
   together: §4 item 13); `B` (the pushes' denominator) is required nonzero on its own since the claims divide by it
   (an honest proof fails it only at a `t` where a pull group's denominator vanishes). A nonzero `w_m` puts `t` off
   `V_m`, so every group's and port's denominator is nonzero too.

**Q's claims.** The identity at `t` is `c_h h(t) + w_m q(t) = Δ + w_m R_n / R_d = num_1 / R_d`, `num_1 = Δ R_d + w_m
R_n`. `P`'s definition is `w_m q_P(t) = s + P_v(t) = num_3 / B`, `num_3 = (s + v_0) B + w_m A = D_n + d_push B`. A
slot's weighted value at the position coordinates `u` is `(t / w_m)` times its polynomial's value at `t` (`Π_{l < m}
(1 + w_l)^{-1}` telescopes); the slot bits weigh `(1 + z_j, z_j)`, ratio `r_j = z_j / (1 + z_j)`; the limbs' `(y_0,
y_1)` (`verifier::extension`, as `crates/membership/quotient`) weigh limb `l` by `scale · Y^l`, limb code 3 by `scale ·
Y³`. Each claim on `Q` is a point of its whole stack, a product weight on the slots' bits (§9: why two):

- **the identity's**, at `(u, z_0, z_1, y_0, y_1)`, `z_0 = t w_m / Y_1`, `z_1 = t w_m² / Y_2`: ratios `r_0 = a = t w_m /
  c_h`, `r_1 = a w_m`, so `H + a q = t h + a q = (t / c_h) num_1 / R_d` (the identity times `t / c_h`), `G` weighs `a
  r_1 = t² w_m³ / c_h²`, and limb code 3 `P + a q_P + a r_1 S`; value `scale · t c_h (t num_1 B + Y³ R_d (c_h s B + t
  num_3)) / (w_m Y_1 Y_2 R_d B)`;
- **the pushes'**, at `(u, ρ, z'_1, 1, 1)`, `z'_1 = ρ w_m / Y_3`: limb code 3 alone, ratios `ρ / (1 + ρ)` and `w_m ρ /
  (1 + ρ)`: `P(t) + (ρ / (1 + ρ)) q_P(t) + (ρ² w_m / (1 + ρ)²) S(t)`; value `t (1 + ρ)((1 + ρ) w_m s B + ρ num_3) /
  (w_m² B Y_3)`.

`ρ` is drawn after `s`: the pushes' claim binds `P(t) = s`, the definition and `S(t) = 0` (degree 2 in `ρ`); with them
the identity's claim is the identity as `I = D² H + x Z_V D q + x² Z_V³ G + x D R`, which forces `H(0) = 0` and so
`Σ_V h = 0` (§7, "The copy sum from `Q`'s layout"). No claim reads the sum. The two claims share their position
coordinates (the contract writes them once). The honest prover leaves `G` and `S` zero; any prover's are handled by
§7's argument (`G` enters `I` as `x² Z_V³ G`; `S(t) = 0` is in the pushes' claim).

**The claims** (4, after π1's 3), each a point of its stack (past the table's coordinates, zeros):

- `W` at `(ρ, ρ², …, ρ^{2^{r-1}}, w_r, …, w_{m-1})`, value `Σ_k eq(ρ⃗, k) a_k`;
- the setup at `(w_0, …, w_{m-1}, β)`, value `ξ` (its halves `κ`, `κ + σ`: `(1 + β) κ + β (κ + σ) = κ + βσ`);
- `Q` at `(u_0, …, u_{m-1}, z_0, z_1, y_0, y_1)`, `u_l = w_l/(1 + w_l) = 1 + 1/w_l + 1/w_{l+1}`, the identity's value;
  at `(u_0, …, u_{m-1}, ρ, z'_1, 1, 1)`, the pushes'.

**The contract** (`contract`): reads π1's three claims' hashes from the frame's payloads 0 … 2 into the seed (π2's
circuit computes them from π1's run), reads the stream, runs the verifier, then checks π2's four claims declared at
payloads 3 … 6, each the EIP draft's PCS claim (`evm_link::declared_claims`: its `82 + 24 n` bytes packed and hashed,
the hash a payload of the frame): `W`'s, the setup's (its commitment a constant) and `Q`'s two. With the fallback
(`SPEC-REC.md` §2.4.6) it encodes the claims the circuit does not hash, from the stream and constants.

## 3. The prover (`prover`)

1. `w`'s novel coefficients (`quotient::ntt`), its `B` coefficients (subset sums): `W`, committed.
2. `α, β, γ`; on `V_m` (`h_on_v`, eight rows at a time, one batched inversion a run of 4,096), in `Q`'s stack: `P_v`
   (a pair's formula of its row, a forward's or a hole's own value) and `h` (zero at a hole; in `G`'s slots until step
   4), its sum checked to be zero (as `h`'s top novel coefficient), and the ports checked (`T` zero at every hole; for
   any other `w`, `prove_with` sets `h = T/(d_pull d_push)` at a dishonest hole, so the identity still holds, the sum is
   not zero, and the identity's claim is false: §6); `h`'s and `P`'s novel coefficients.
3. On `D = β_{m+1} + V_{m+1}` (`2N` points, disjoint from `V_m`), one coset of `V_m` at a time: `w`, `h`, `P` by
   transforms (five of `2^m` a coset), `σ`, `κ` with the setup (fixed by the circuit). Eight points at a time: the
   row's cells (`x + ω_c` stays in `D`), every pair's indicator (a chunk of 4,096 points at a time: a pair whose block
   spans the chunk is periodic in it, one batched inversion), `P_v` (the internal groups as one quadratic form of the
   cells), the ports' `T` (each port group's formula plus its role's `Φ`, which is one value a row: per chunk, its rows'
   `Φ` by one batched inversion of `rows × ports` denominators, eight rows a vector), `d_pull`, `d_push`,
   `q = (h d_pull d_push + (1 + 1_S)(d_push + d_pull) + T) / Z_V` and `q_P = (P + P_v) / Z_V` (`Z_V` takes two values
   on `D`). Their novel coefficients: degree below `2N`, `2N` points determine them.
4. `H = x h` by `quotient::protocol::mul_x` (the novel basis' product by `x`, no multiplication; `h`'s top coefficient,
   zero, dropped) into `H`'s slots, `G`'s zeroed: no fix-up, no completeness condition (`q` and `q_P` are read through
   `Z_V` itself). `Q`, committed (its stack built in place, the setup's from one proof to the next; `Q` and `W` keep
   their codewords until their openings, which read the queried rows from them; the all-zero lanes, which `pcs_claim::commit_words`
   finds in the stack itself (here `G`'s and `S`'s slots), left out of the encodes and the kept codeword); `t`; the fold values, `ξ` and `s = P(t)`; `ρ`; the verifier's four claims, each opened by its own
   PCS opening (`pcs_claim`: leanVM's WHIR unchanged, rate 1/2; `Q`'s two by `open_words_batch`, one pass of their lane
   rounds for two proofs, each the one it would be alone). `PI2_PROFILE=1` prints the phases.

## 4. Decisions and deviations from SPEC-REC's design

1. **Holes are out of the copy argument** (the design added the holes' sums `Σ 1/D(0, ω_h)` to the target). Pulls and
   pushes are weighted by `1 + 1_S`: the copy argument is over the internal positions, its sum is zero, and the ports
   are `T`'s (§1). A hole's value is unconstrained: `adapt` checks that no formula of a port's region reads a hole (the
   circuit compiler never places a value there), and panics otherwise; `Circuit::validate` is asserted on the setup
   path (`Spec::of`, `Setup::new`, `contract::Instance::new`) too.
2. **The ports' fingerprints are not `Σ γ^l L_l`.** Three limbs (an element, a zero check) are `L_0 + Y L_1 + Y² L_2`:
   the element itself. Four limbs (the statement, a root, a claim's hash) are `(L_0 + Y L_1) + γ (L_2 + Y L_3)`: a
   32-byte word's two 16-byte halves as `next_root` reads them, one product. Both bind the limbs (injective on `K³`;
   for all but one `γ` on `K⁴`), as `spec::Circuit::check` compares them.
3. **`h(t)` is not sent** (§9, lever 2): `Q`'s claim is the identity's combination of `H(t)` and `q(t)`, and the
   verifier inverts once at the end.
4. **`W` and the setup in the `B` basis, `Q` in the novel basis.** The `B` basis makes a claim at the digits themselves
   (no inversion); `Q`'s novel basis makes `H = x h` a pass of additions (`mul_x`) and `Z_V`'s digits plain chunks, so
   its point takes the `u_l`.
5. **`ρ` is `W`'s fold and `Q`'s pushes' combination.** `W`'s claim is a polynomial of degree `2^r − 1` in `ρ`, `Q`'s
   pushes' one of degree 2 (§2); the setup's and the identity's take no `ρ`.
6. **The extension coset is `2N`.**
7. **The public data is in the seed and the stream**, absorbed by the first challenge (the design: a separate
   `D = keccak(public data)`).
8. **No row counts among the public terms** (SPEC-REC §10.4 item 3).
9. **Stacks of at least `2^24` words** at the target shapes (§2).
10. **The verifier's arithmetic** (§2): normalised indicators, fractions by groups, the inverse by the norm. Measured on
    the synthetic D16v target: 56.3K → 46.2K execution, before §9's levers.
11. **`P` is committed in `Q`**, after `α, β`: its definition pins it on `V_m` to `P_v`, a function of `W` (§7).
    `d_push` then takes `P`, below `N`, and the identity is below `3N`. `P` is in `K` (the internal pushes are,
    `Circuit::validate`): one limb.
12. **`Φ` by rows.** The ports' public values enter as `Φ_k`, one per port role (the real circuit's ports are all at
    role 15), interpolated over the rows by `w_r` rather than over the positions: the verifier's cost is the same (a
    fraction a port of nonzero value), and the prover's `Φ` is one value a row of `2^r` points. The zero ports drop out.
13. **`D_n` in the inversion.** The contract's code computes a value where it is first read, keeps one read again in
    memory, and computes the checks first. Without `D_n` the check reads `B` (through `z`'s or `1/B`'s product) before
    `A`, and every group's denominator waits in memory for `A`'s chain (measured when it was made: 480 words of memory
    against 230, about 1K more execution). `D_n` reads `A` and `B` together; its being nonzero costs completeness
    `3N/2^192` at most.
14. **The copy sum from `Q`'s layout** (π2v4; §7): one claim fewer than π2v3's sum claim at `h`'s top coefficient.

## 5. The synthetic circuits (`synth`)

Before the real circuit existed, `synth` built circuits with every row kind of SPEC-REC §2.4 (χ formulas, D units, XORs,
packings, free bits, `E` products and sums, constants, ports of every source) and a witness satisfying them by
construction (FIFO wiring), small (`2^11`, `2^12` positions; the design's `2^24` target shape, `target_d16v`, is gone
with the real circuit). They remain the PIOP's and the contract's tests. The real D16v circuit of the Keccak VM's
π1-rec4 has 176 pairs at the reference shape (its ports all at role 15).

## 6. Tests

- `lib`: an indicator is one on its coset and zero on `V_m`'s rest (every alignment and size); `Φ`'s basis (`w_r(ω_i)
  = ω_{i >> r}`, `w_m = w_{m-r} ∘ w_r`, `V_{m-r}`'s Lagrange basis sums to one off `V_m`); the inverse; the stacks'
  `Q`'s slots are their bits (`quotient_slots_are_their_bits`).
- `tests/pi2.rs`, D16v synthetic circuits and the interface's own example (padded, through `adapt`):
  - the honest proof's four claims hold and their openings verify (`pcs_claim::verify_claim`);
  - witness mutations (random constrained positions): a false claim;
  - a changed element, a changed public input (a dishonest port, the identity kept by the prover): exactly the
    identity's claim is false, `[true, true, false, true]` (§7's lemmas at work);
  - `the_copy_sum_from_the_layout` (`prover::prove_cheating`, `Cheat`): on a witness the cheats that act on the sum
    are the honest proof (every claim holds, both layouts' relations hold); a dishonest port with `x h`'s coefficient
    `N` dropped (`None`: `h(0)` moved by `σ`), kept in `q`'s second digit (`OverflowInQ`) or dropped with `σ` in `G`
    (`AbsorbInG`): `[true, true, false, true]`; **the negative control** (`identity_relations`, `Q` read slot by slot
    at `t`): `AbsorbInG` meets the relation of the layout that would read `G` through `Z_V` (§7) and not this one's;
    `G` filled: `[true, true, false, true]`; `S` filled: `[true, true, false, false]`; `s` sent off `P(t)`: the
    pushes' claim false; a constant added to `H` (`ConstH`): `[true, true, false, true]`; `S = c` with `G = Y³ c`,
    which cancel in the identity's claim (`SinG`): `[true, true, true, false]`, the pushes' claim alone catching it;
    `P`'s constant moved after `q_P` (`ConstP`): `[true, true, false, false]`. The cheats are the `test-support`
    feature's (`prover::{Cheat, prove_cheating}`), which `tests/pi2.rs` turns on; the production API has none;
  - flipped stream bytes: claims the openings do not prove;
  - the contract equals the Rust verifier word for word, on the honest stream and a random one; it accepts the honest
    proof with its frame declaring exactly its claims, and rejects flipped bytes.
- `tests/pi2_real.rs`, the real circuits (`PI2_VECTOR=keccak128_rec4`, the default, or `keccak_rec4`; the
  `keccak*_rec3` vectors give π2 over π1-rec3 with `C1`'s claim alone hashed): `real_gas`, the gas, deployment and
  parity of D16v; `real_end_to_end` (`SPEC-REC.md` §11: the openings, the frame and calldata attacks). The claims
  holding on the real tables are the degrees' check (§1): a `q` or `q_P` of a degree above `2N` would not be determined
  by `D`'s `2N` points, and its claim would fail.
- `tests/pipeline.rs`: the prover timed from a trace, π2's proof and openings among its stages (§0).
- `tests/pi2_real.rs`, `real_gas`: π1-rec4 (`leanvm_rec::PI1`) at 128 and 400 signatures compiled into D16v on the
  real proofs, the contract's gas and parity.
- `tests/lean_pi2_prover.rs`: vectors for the Lean honest prover's differential test (`formal/RecCompose`, of π2v3 as
  of `f96a7938`: §10).

## 7. Soundness (as SPEC-REC §5)

**The ports' lemma.** Fix `W`'s list element `w` (committed before `α, β, γ`) and `γ`. If the identity and `P`'s
definition hold as polynomials (else `t` errs, below) then on `V_m`: `P = P_v` (a function of `w`), off the holes `h =
1/d_pull + 1/d_push` (`T` is zero there), and at a hole `x_0` of port `J`, `h(x_0) d_pull(x_0) d_push(x_0) = T(x_0) =
E_p(x_0) + F_J`, where `d_pull(x_0) = α + w(x_0) + β x_0` and `d_push(x_0) = α + w(x_0) + β τ_J` (`P_v`, `κ` at a hole:
`w`, `0`). So, unless a denominator on `V_m` vanishes,

`Σ_V h = Σ_internal (1/(α + w + βx) + 1/(α + P_v + κ + βσ)) + Σ_holes T(x_0) / ((α + w(x_0) + β x_0)(α + w(x_0) + β τ_J))`,

a rational function `R(α, β)` with at most `2N` distinct linear factors in its denominator. If a port is dishonest,
`T(x_0) ≠ 0`, and the linear form `α + w(x_0) + β x_0` divides one denominator only: the other pulls' tags are other
positions, no push targets a hole (`Circuit::validate`), and `τ_J` is outside `V_m`. Its residue `T(x_0) / (β (x_0 +
τ_J))` is nonzero, so `R ≠ 0`. If the ports are honest, `R` is the logarithmic derivative's difference over the internal
positions, both sides sets: `R ≠ 0` unless every internal pull is the push sent to it. The sum is zero (below), so
`R(α, β) = 0`: probability at most `2N/2^192` for a nonzero `R` (its numerator's degree), and `2N/2^192` that a
denominator vanishes on `V_m`: `4N/2^192` over `W`'s list. The prover's side (`tests/pi2.rs`): a dishonest port with
the identity kept makes exactly the identity's claim false.

**The copy sum from `Q`'s layout.** Fix `w`, `α, β, γ` and `Q`'s list element: sixteen polynomials of degree below `N`,
all the prover's: `H_l, A_{0,l}, A_{1,l}, G_l` (slots `4 l … 4 l + 3`), `P, B_0, B_1, S` (`12 … 15`); `H = Σ Y^l H_l`,
`A = A_0 + Z_V A_1`, `G = Σ Y^l G_l`, `q_P = B_0 + Z_V B_1`; `D = (α + w + βx)(α + P + κ + βσ)`, `R = (1 + 1_S)(d_pull
+ d_push) + T` (with the committed `P`), as polynomials. All are fixed before `t`.

1. `W`'s claim and the setup's give the row's cells and `ξ = κ(t) + βσ(t)` (as before: `15/|E|` over `ρ`; the setup
   honest, fixed before `β`).
2. The pushes' claim times `(Z / t) Y_3` (`Y_3 ≠ 0` required) is `(1 + ρ)² e_1 + ρ (1 + ρ) e_2 + ρ² e_3 = 0`, `e_1 =
   P(t) − s`, `e_2 = q_P(t) − (s + P_v(t)) / Z`, `e_3 = Z S(t)`: degree 2 in `ρ`, coefficients `e_1`, `e_2`, `e_1 + e_2
   + e_3`, all fixed before `ρ`. So `P(t) = s`, `Z q_P(t) = P(t) + P_v(t)`, `S(t) = 0`, but with probability `2/|E|`.
3. With 2., the identity's claim's limb-code-3 share is the verifier's, `c_h = D(t)` and the verifier's `num_1 / R_d`
   is `R(t)`; what remains, `H(t) + a A(t) + a r_1 G(t) = (t / c_h) R(t)`, times `c_h²` is `I(t) = 0` for
   `I = D² H + x Z_V D A + x² Z_V³ G + x D R` (characteristic 2), of degree below `5N`.
4. `I` and `J = Z_V q_P + P + P_v` (below `3N`) are fixed before `t` and vanish at `t`: both are zero as polynomials,
   but with probability `5N/|E|` (the larger degree).
5. `J = 0`: `P = P_v` on `V_m`, so `P(0) = P_v(0)`. `I = 0` at `x = 0`: `D(0)² H(0) = 0`, and `D(0) = (α + w(0))(α +
   P_v(0) + κ(0) + βσ(0))` is the copy argument's pull and push denominators at position 0 (at a hole the same linear
   forms: `P_v = w`, `κ = 0` there), nonzero but with the probability above ("a denominator on `V_m` vanishes"). So
   `H(0) = 0`, `h = H / x` is a polynomial of degree at most `N − 2`, and **`Σ_V h = 0`** (only `x^(N−1)` has a nonzero
   sum over the `F_2`-subspace `V_m` of `N` points).
6. `I / x = D² h + Z_V D A + x Z_V³ G + D R = 0`; on `V_m`, `D (D h + R) = 0` and `D ≠ 0`: `h D + R = 0` there.

5. and 6. are what π2v3's identity's and sum's claims gave, with the committed `h` replaced by `H / x`: the ports'
lemma above applies unchanged (it uses `h` on `V_m` and its sum only).

*Why `G` must weigh `x² Z_V³`* (the negative control). The fourth `E` slot is the prover's in any layout. If `q`'s
digits sat at one slot bit (contiguous slots of one kind), `H` and `G` would sit at the other, `G` weighing `Z_V`
against `H`: `I' = D H + x Z_V A + D Z_V G + x R`. A dishonest port (`Σ_V h = σ ≠ 0`, `h D + R = q Z_V` kept) passes
it: `H = x h + σ Z_V` (`x h` without its coefficient `N`, which is `x (h + σ L_0)`, `L_0 = Z_V / x` the Lagrange
polynomial of `0`: `w_m'(0) = 1`) and `G = σ` give `I' = 0`. Here the same `G` leaves `I = σ Z_V (D + x Z_V)² ≠ 0`;
`x² Z_V³ G` vanishes at `0` past `Z_V`'s order, so `G` moves neither `H(0)` nor `h` on `V_m`. The anti-diagonal is
the one placement of `q`'s digits (ratio `Z_V`) that leaves `G` diagonal to `H` (ratio `a r_1`). (The membership's
`x h` reads its second digit through `ζ = Z x` and must zero a coefficient of `q` by a blinding term,
`docs/membership/PROTOCOL.md`; here `q_P`, a function of `w`, shares the digit coordinate and has no free term, which
this layout avoids.)

*Completeness*: the honest `Q` meets both claims exactly; the nonzero requirement adds `Y_1 = (D + x Z_V)(t)`, `Y_2 =
(D + x Z_V²)(t)` (nonzero polynomials, below `2N + 2`) and `Y_3` (one `ρ`), and drops π2v3's `Y` and `w_{m+1}`:
about `2^-165` in all, as before.

**Committing `P` after `α, β`** is sound for the same reason: `P`'s values on `V_m` are pinned to `P_v`'s by its
definition, so `d_push` on `V_m` is fixed by `W` before `α, β`.

**The rounds** (`params/leanvm_rec_params.py`, `pi2_rounds`; `N = 2^24`, lists `L_W` 9,952, `L_Q` 3,564; bits alone,
then after the union):

| round | error | alone | after |
|---|---|---:|---:|
| the copy argument `(α, β, γ)`: `2N` fractions, the ports' poles, the four-limb ports' fingerprints (degree 1 in `γ`) | `(4N + 4)/2^192` over `L_W` | 166.0 | 152.7 |
| `t`: the copy identity as the identity's claim reads it (`I`, below `5N`) and `P`'s definition (below `3N`), both must vanish | `5N/2^192` over `L_W L_Q` | 165.7 | **140.6** |
| `ρ`: `W`'s fold (degree 15) | `15/2^192` over `L_W L_Q` | 188.1 | 163.0 |
| `ρ`: `Q`'s pushes' claim (degree 2) | `2/2^192` over `L_W L_Q` | 191.0 | 165.9 |

(π2v3: `t` at `4N`, 140.9 bits, its third claim on `Q` at `ρ` of degree 3.) The Lean (`formal/RecPiop`'s `err`)
states π2v3's rounds, coarser: `(4N − 1 + Σ_j d_j)/|E|` for the copy argument and
the ports, `(4N − 1)/|E|` at `t`, `2^r/|E|` at `ρ`. These depend only on `N` and the stacks. With the openings charged
once (`269 · 2^-137` a query; seven openings), π2 keeps 128.93 bits as `Q/ε` at `Q = 2^64` (`RecCompose.pi2Bound`,
`pi2Bound_le_bits`), the recursion 127.86.

## 8. The claims' encoding, the IVs, the setup path

- **One encoding for the seven claims**: the EIP draft's PCS claim (`crates/pcs_claim`, `docs/PCS_CLAIM.md`), `version
  || n || root || ood || point || value`, `82 + 24 n` bytes, its Keccak-256 a payload of the transaction's frame of PCS
  claims:
  - every root is the commitment's 32 bytes as they are: π1's prover sends a root's bytes, so π1's stream carries
    `C1`'s and `C2`'s as the claims encode them, and π2's circuit reads the stream's bytes as they are
    (`circuit::compile`); π2's `W` and `Q` roots are in calldata so; π1's setup root `F` and π2's setup root are
    constants so;
  - every out-of-domain answer is an element: π1's two are elements of its stream, π2's two after their roots, the
    setups' constants;
  - every claim is a point of its commitment's whole stack (`n` its variables), its value the polynomial's there;
  - **one PCS version** (1): leanVM's WHIR at rate `1/2` on its ladder (`pcs::whir::DEPLOYED_SCHEDULE`), every opening
    one claim's (`pcs_claim::open_words`, `verify_claim`); the stacks' leading lanes are committed alone (the
    commitment of the whole stack), the opening's rows padded back (`pcs_claim::commit_words`).
- **The mock frame** (`leanvm_statement::evm::machine::PcsFrame`) declares encoded claims; a measuring run declares any
  well-formed one. The end-to-end tests declare π1's claims from the vector (written by π1's prover from its openings)
  and π2's from the proof's commitments and reduction (`prover::claims`), so a claim in another format fails them.
- **The holes on the setup path.** `Spec::of` and `Setup::new` assert `Circuit::validate`, which also requires `κ` zero
  off the expression slots.
- **Derived instances.** The circuit compiler takes the program's IV (`compile::Inputs::program_iv`) and derives
  π1's contract IV from the recorded verifier (`Recorded::iv`: its shape, setup roots and variant), kept as
  `Compiled::pi1_iv`. `contract::Instance::new` builds the instance from the validated circuit, its spec, the setup
  root, π1's IV and calls, and computes π2's IV.
- **π1's IV binds its variant.** `leanvm_univariate::contract::contract_iv` hashes `variant_bytes` (the tag
  `"keccak-vm"`, the skip and the Fiat–Shamir shape's code), so a π1-rec4 proof is not a main-line or π1-rec3 proof.

## 9. Optimisation levers

Each lever is in the code. π1's levers (the narrow batch challenges, the paired batch, no claims on Flock's matrices,
π1-rec4's wide draws) are in `docs/leanvm/univariate/SPEC.md` §13; π2's circuit's (the trimmed last rounds, the hashed
claims) in `SPEC-REC.md` §2.4.1, §2.4.6.

**Lever 3c: the zero checks as no term.** π1's zero checks are ports of value 0. The circuit compiler makes them the
first ports, padded with constant-zero ports (`spec::Source::Pad`) to a power of two `2^k`, so that their outside tags
are the aligned coset `ω_N + V_k`. A zero port is in no `Φ` (§1): it costs the verifier nothing, the padding included
(kept from π2v1, whose verifier summed the coset in closed form).

**Lever 3b: the claims' words written once** (`evm_link::claim_outputs`, `Ending::Claims`). The
claims' fields are written as the distinct words in first appearance, so claims sharing a point's coordinates write
them once: π2's claims are ordered `W`, the setup, `Q`, so the setup's point reuses `W`'s digits `w_4 … w_{m-1}`, and
`Q`'s identity and pushes claims share their position coordinates. A word written once is read once, so it is not
kept in a memory slot either. (`evm_link::front::Source::reuse`, the inputs of the `PCS_OPEN` era's calls written
once, remains in `evm_link` unused.)

**Lever 3a: the fold's siblings.** At every level of the row's fold, the cells `2k` and `2k + 1` fold their parent at
`z = w_l + ω_{2k}` and `z + 1` (`ω_{2k+1} = ω_{2k} + β_0`, `β_0 = 1`), so the odd one is the even one plus the
parent's difference `p_j + p_{j+half}`: `r 2^(r-1)` products instead of `r 2^r` (D16v 32 instead of 64).

**Lever 2.**

- **`σ(t)` and `κ(t)` as one value.** The verifier uses them only in `d_push`: as `ξ = κ(t) + βσ(t)`. The setup's halves
  are `κ` and `κ + σ`, so its one claim at `(w_0, …, w_{m-1}, β)` is `(1 + β)κ(t) + β(κ + σ)(t) = ξ`, with no
  inversion. The setup is honest (`L = 1`) and fixed before `β`: the claim binds `ξ` exactly. `ρ` does not enter the
  setup's claim.
- **`h(t)` not sent.** The verifier keeps every quotient as a fraction and inverts once at the end (§2): the identity
  at `t` is the one combination of `h(t)` and `q(t)` it is, `c_h h + c_q q = Δ + w_m R_n/R_d`, and `Q`'s claim takes
  it normalised, `(1 + ρ')h(t) + ρ'q(t)` at `ρ' = c_q/(c_h + c_q)` (with `P(t) = s` and `P`'s definition, §2).

**Not taken.**

- **D8v** (rows of 8, 8 fold values: −192 B). With `Q = 12N` words, `N` must stay `2^24` (`2^25` gives `2^28.58`). A
  χ output reads three `b = A + D` of its plane, so a row of 8 holds the inputs of at most two outputs, or must
  materialise `b` (one more position a state bit, and its forwards): about 2× D16v's positions a round, past the room
  `2^24` leaves.
- **One claim for `Q`'s identity and pushes** (−3,048 gas). A claim whose position coordinates read `Q` at `t` is a
  rank-one weight on the slot bits times the limbs'; the limbs' are fixed (`h`, `q` are read as elements of `E`), so
  the claim is a rank-one `2 × 2` tensor over four super-slots (an `E` polynomial plus `Y³` times a `K` one). The
  identity involves three `E` polynomials (`H`, `q`'s two digits) at fixed ratios, three entries of that tensor, which
  then has no free coordinate. Combining it with `P(t) = s` and the definition needs a coordinate drawn after `s`;
  pinned, the prover solves for `s` (the claim's equation is `ε + (s − p) β(s) = 0`, `ε` the identity's error, `p =
  P(t)`, `β` of degree 1: a quadratic, solvable about half the time). Around it: `q` below `N` (the identity is below
  `3N`); the copy argument split into `1/d_pull` and `1/d_push` (four `E` polynomials, two identities whose ratios rank
  one ties together, the push identity still bilinear in `b(t) P(t)`); `d_push` from `P_v` (π2v1: no `s`, but `q`
  below `4N`, five `E` polynomials against four super-slots, and 32 slots are `2^29` words, past WHIR's certified
  `2^28`); `P`, `q_P` in `W` (`W`'s claim reads the row's fold, not `P(t)`: another claim on `W`); a product `b P`
  committed (checked bilinearly again). Two claims on `Q` are this PIOP's minimum.
- **Fewer values at `t`** (1,536 gas each). The 16 fold values: `P_v(t)` and the ports' terms are a quadratic form of
  the row's 16 cells with coefficients the prover learns with `t` (the groups' indicator sums), and the formulas'
  products (χ's, the `E` units' limb products) read every cell at some role, so all 16 are needed (`W`'s claim binds
  them with `eq(ρ⃗, ·)`, which spans the whole space; the membership's conic binding three forms needs them to span a
  plane). `ξ` is the setup claim's value, which `d_push` and the definition need (committing `P + κ + βσ` moves it
  into the definition, not out); `s` is the bilinear term's (above). The out-of-domain answers are the EIP's format.
- **The membership's `x h` layout** (`H`'s second digit a blinding constant solving `q`'s coefficient `N`, the digit
  coordinate `Z x`): `q_P` shares the digit coordinate and its coefficient `N` has no free term (a second digit of `P`
  would lift `d_push` to `2N` and the identity to `4N`). π2v4's layout needs no fix-up.
- **The frame's index byte** (−64): the convention π2 shares with the membership contract (`evm_link::declared`).

## 10. The Lean side

`formal/RecPiop`, `RecStatement` and `RecCompose` state and prove π2v3 on the EIP draft's PCS claims as of commit
`f96a7938`: over π1-rec3, π1's three claims encoded by the contract (from the stream and constants), 24-byte narrow
challenges, a selector. The contract model checks the eight declared claims (π1's three, π2's five), each a root, its
out-of-domain answer, a point and a value, opened by one PCS opening (`WhirBridge.Pcs`), the eight charged once
(`pcs_union_sound_oracle`); `Q`'s three claims are bound to one table by its answer (`qOodBinding`); `Q`'s empty slots
are the prover's, handled as §2 says ("The empty slots"), at round 1's error `(4N − 1)/|E|`. The end theorems
(`RecCompose.recKnowledgeSoundness_reduction_real`, `Pi1K.recCompleteness_real_K_fs_bits`) give `pi2Bound Q ≤ 2^-64` at
`Q ≤ 2^64` (128.93 bits as `Q/ε`) and completeness `δ1 + δh + 2^-164`. π2's Lean prover agrees with the Rust on the
`lean_pi2_prover` vectors; `rec-circuit-keccak`, `rec-view-check` and `rec-real-check` hold
(`formal/RecCompose/README.md`). What the Lean needs for the deployed π2 (π1-rec4, the hashed claims, the frame reads,
no selector, π2v4's layout and two claims on `Q`): `docs/LEAN_PORT.md`, "leanVM".
