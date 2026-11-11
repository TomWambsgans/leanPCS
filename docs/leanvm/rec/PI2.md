<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# π2's PIOP: prover, verifier, contract, gas

π2 proves that π1's recorded verifier (the Keccak VM's π1-rec4 since [`PERF_GAS2.md`](PERF_GAS2.md), π1-rec3 before,
`SPEC-REC.md` §1) accepts and outputs its PCS claims. Its circuit is `SPEC-REC.md` §10's; this file is its PIOP,
**π2v3** (transcript `leanvm-rec-pi2v3`, `pi2::verifier::NAME`): π2v2's PIOP (the ports out of the copy argument, `P`
committed in `Q`, `q` below `2N`; §1, §7) on the EIP draft's PCS claims (§2, §8). Code in `crates/leanvm/rec/src/pi2/`;
the Lean proofs are in `formal/RecCompose`, of π2v3 as of commit `f96a7938` (over π1-rec3, π1's claims encoded by the
contract; §10). Numbers are **measured** unless marked modelled.

```sh
export RUSTFLAGS="-C target-cpu=native"   # the field's native SIMD paths (AVX-512/GFNI on x86)
cargo test --release -p leanvm_rec --lib pi2                                                  # indicators, Φ's basis, inverse, WHIR queries
cargo test --release -p leanvm_rec --test pi2 -- --nocapture                                   # synthetic circuits, contract parity
cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_gas            # the real circuits' gas
cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_end_to_end     # 2^24 prover, end to end (peak about 12.7 GB)
PI2_VECTOR=keccak_rec4 cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_end_to_end   # 400 signatures
LEANVM_TRACE=<trace> cargo test --release -p leanvm_rec --test pipeline -- --ignored --nocapture                     # trace → π1 → π2, timed
cargo test --release -p leanvm_rec --test pi2 -- --ignored --nocapture gas_report               # the synthetic target shapes
```

## 0. Results

**With π1-rec4 and π1's three claims hashed in π2's circuit** ([`PERF_GAS2.md`](PERF_GAS2.md); `real_end_to_end` on
h3): 577 B of calldata, 31,524 execution; floor 36,928, with the frame of PCS claims and the PCS gas 66,376 (89,672
before, 99,912 on `f96a7938`). The figures below predate it.

**With π1's claim on `C1` hashed in π2's circuit, narrow challenges as 20 bytes, no selector** ([`PERF_GAS.md`](PERF_GAS.md);
`real_end_to_end` on h3): 941 B of calldata, 37,406 execution; floor 60,224, with the frame of PCS claims and the PCS
gas 89,672 (99,912 before). The rest of this section predates it.

**With the EIP draft's PCS claims** (§2, §8; `real_end_to_end`, this Mac, 2026-11-10): 1,101 B of calldata (61 zero),
32,794 execution at 128 signatures (33,740 at 400); as an EIP-8141 frame transaction (EIP-7976's floor, without the base
and per-frame costs) standard 49,678, floor 70,464; with the frame of PCS claims (257 B, 8 claims) and the PCS gas
(13,000 on both sides) 99,912. The prover (`tests/pipeline.rs` via `bench.sh`, M4 Max in high power mode, median of 5): π2's proof
0.95 s and its five openings 1.25 s, each opening one claim on leanVM's ladder. The figures below predate the PCS claims.

**The contract, on the real circuit** (D16v × π1-rec3, `real_end_to_end` on `keccak128_rec3.txt`; no 21,000 base),
measured with `PCS_OPEN`, its claims priced `c = 0`. With the frame of claims (`AGENTS.md`): 1,005 B, 28,459
execution, 43,819 EIP-7623 and 64,320 EIP-7976 at 128 signatures; 29,257 and 44,593 at 400; apart from the frame
(193 B) and the claims' 11,000 intrinsic gas:

| | 128 signatures (reference) | 400 signatures |
|---|---:|---:|
| calldata (zero bytes) | 1,004 B (59) | 1,004 B (61) |
| execution | **27,641** | 28,421 |
| code | 13,219 B, one contract | 13,639 B |
| claims / calls | 7 / 6 | 7 / 6 |
| **EIP-7623** | **42,997** (floor 38,390) | 43,753 |
| with the 21,000 base | 63,997 | 64,753 |
| EIP-7976 | 64,256 | 64,256 |

At `c = 0` the standard price binds (`16 · 945 + 4 · 59 + 27,641`). The contract at the reference shape: 753
`FIELD_MUL`s, 818 `XOR`s, 6 Keccak-256 (1,208 B), 230 words of memory, 210 words written for the claims; one
contract of 13.2 KB, within EIP-170. The execution depends on the circuit alone: `real_gas` and `tests/keccak_vm_rec.rs`
measure it on a sample stream (4 zero bytes: 43,657 at 128 signatures, 44,437 at 400).

Against π2v1 (§10, at opening version 2: 980 B with 66 zero bytes, 28,325 execution, 43,213; 44,041 at 400): 24 B
more calldata (`s`), 684 less execution (the public side's walk and zero coset gone, the identity's fractions fewer),
and the version-3 proofs' bytes, so EIP-7623 −216 at 128 signatures and −288 at 400; EIP-7976, where the floor binds,
+1,536 (62,720 → 64,256).

**The prover** on the real witness (128 signatures, `tests/pi2_bench.rs`, since removed: `tests/pipeline.rs` times the same stages; a 64-thread Zen 5 box shared with other
jobs, `RUSTFLAGS="-C target-cpu=x86-64-v4 -C target-feature=+gfni,+vpclmulqdq,+vaes,+pclmulqdq,+avx512vbmi,+aes,+bmi2"`,
2026-11-08; π2v1 and π2v2 interleaved, 4 runs each at load 12–26, medians of the 20 passes; `PI2_PROFILE=1`):

| | π2v1 | **π2v2** |
|---|---:|---:|
| `W`: transform, commit | 0.018 s | 0.018 s |
| `h` (and `P`) on `V_m`, their coefficients | 0.032 s | 0.035 s |
| on `D`: `w`, `h` (and `P`) by transforms | 0.065 s (`4N`) | 0.041 s (`2N`) |
| on `D`: the numerators over `Z_V` | 0.069 s | 0.039 s |
| `q`'s (and `q_P`'s) coefficients | 0.033 s | 0.031 s |
| `Q`: table, commit | 0.099 s (`15N`) | 0.086 s (`12N`) |
| **prove** | **0.321 s** | **0.255 s** |
| open (`Q`'s opening) | 0.141 s (0.113 s) | 0.139 s (0.109 s) |
| peak memory | 8.5 GB | 7.3 GB |

End to end (`tests/pipeline.rs` on a 128-signature trace, `PIPELINE_REPEAT=5`, the same box, 4 interleaved runs each,
medians): π2's proof 0.327 → 0.258 s, its openings 0.148 → 0.141 s, the pipeline (π1-rec3's proof and openings,
π2's proof and openings) 1.385 → 1.281 s (π1's share, unchanged code, 0.91 and 0.87 s). `q`'s coefficients gain
little (four transforms of `2N` against three of `4N`): `quotient::ntt`'s transform was slower a word at `2^25` words
than at `2^24` or `2^26` (a microbenchmark: 9.5 ms at `2^25`, 3.7 ms at `2^24`, 11.8 ms at `2^26`; since fixed by
thread-affine dispatches, 4.4–5.5 ms: `PROVER.md`'s "Measured").

Since then (2026-11-09, the same box, `tests/pi2_bench.rs`, median of 5, load 10–15): **prove 0.196 s, open 0.104 s**
(`W` 0.013; `h`, `P` on `V_m` 0.018; on `D` 0.087, of which transforms 0.027, numerators 0.040, coefficients 0.020;
`Q`'s table and commit 0.074; openings `W` 0.010, `Q` 0.081, setup 0.013), peak 9.9 GB: `Q` and `W` keep their
codewords until their openings (+1.8 GB in the pipeline), `Q`'s stack is the setup's from one proof to the next, the
transforms are `quotient::ntt`'s multi-column ones, and the copy sum is checked as `h`'s top coefficient. End to end,
the pipeline took 0.69 s a proof (π2's proof 0.195 s, its openings 0.106 s); with opening version 3 (§8) its openings
take 0.051 s and the pipeline 0.59 s (`KECCAK.md`).

**Opening version 3** (§8: WHIR's deeper levels on the recursion's ladder; 2026-11-09, the same box, interleaved
against the version-2 build, load 14–42 from other jobs): π2's openings 0.100 → 0.048 s in their quiet passes (`W`
0.009 → 0.006, `Q` 0.079 → 0.033, setup 0.012 → 0.008; `pi2_bench`, medians 0.100–0.109 → 0.047–0.055 s), their
proofs 284,920 / 314,200 / 296,680 → 347,320 / 405,432 / 365,224 bytes; π1-rec3's three openings 0.064 → 0.033 s
(`keccak_prover_benchmark`), 272,272 / 267,544 / 218,024 → 354,096 / 343,512 / 276,232 bytes. The pipeline, 8 runs of 5
passes each: medians 0.857 → 0.637 s, best passes 0.678 → 0.590 s (π2's openings 0.108 → 0.054 s, π1's proof and
openings 0.426 → 0.378 s), peak RSS 13.8 → 12.0 GB. The gas is the version's alone through the calldata's zero bytes:
27,641 execution, 42,973 transaction then (61 zero bytes; 43,729 at 400 signatures); on main, at the π1 contract IV
without the BLAKE2s-era words (regenerated proofs), 42,997 (59 zero bytes) and 43,753.

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
"leanvm-rec-pi2v3"`, the frame words the Keccak-256s of π1's claims hashed in the circuit (all three at 128 and 400
signatures: payloads 0, 1, 2 of the frame of PCS claims, `Read::Frame`; [`PERF_GAS.md`](PERF_GAS.md) §3,
[`PERF_GAS2.md`](PERF_GAS2.md) §4), then the stream:

1. the public data of the claims the contract encodes (none when the circuit hashes all three; else, as on `main`
   with `C1`'s alone: π1's root `C2` (32 bytes, as it is, §8), the distinct elements of π1's claims the contract encodes
   (`C2`'s out-of-domain answer, 13 narrow challenges as their low 20 bytes, `C2`'s and `F`'s values, 24 bytes each));
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
| `Q` | sixteen slots of `N` (`verifier::QUOTIENT_SLOTS`): `h` (below `N`, three limbs), `q` (below `2N`: two chunks, three limbs), `P` (below `N`, in `K`), `q_P` (below `2N`, in `K`), four zero slots | `m + 4` | all 64 lanes | novel |
| setup | `κ` then `κ + σ` | `max(m + 1, 24)` | `2^(m+1)`, its leading lanes | `B` |

`Q`'s slot is `digit + 2 kind + 4 limb`: `h`'s limb `l` at `(0, 0, l)`, `q`'s at `(digit, 1, l)` (`l < 3`); at limb
code 3, `P` at `(1, 0, 3)` (its one chunk at digit 1) and `q_P` at `(digit, 1, 3)`; slots `1, 5, 9` (`h`'s second
digit) and `12` are zero (`verifier::{h_slot, q_slot, P_SLOT, QP_SLOT, EMPTY_SLOTS}`). A point of `Q`'s stack is then
`(position (m), digit, kind, limb bit 0, limb bit 1)`, and its weight on the slots is a product over these bits: the
claims below choose them so as to weigh what each needs. The stacks are at least `2^24` words, the smallest leanerVM's
certified parameters cover; every opening is the PCS version 1's (leanVM's WHIR at rate `1/2` on its ladder). Small
test circuits take `2^15` stacks.

**The verifier at `t`** (`verifier::reduce`, generic over `Scalar`):

1. the digits `w_0 … w_{m+1}`, `w_{l+1} = w_l² + w_l`;
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
7. `Q`'s claims (below), and one inversion, of `R_d Y · w_{m+1} · B · c_h D_n` (required nonzero), by the norm (two
   Frobenius maps from the limbs' shifts, 76 products); `1/w_{m+1}` and `1/B` from it, and `1/w_l = (1 + w_l)/w_{l+1}`
   down to `l = 0`. `c_h = d_pull d_push` nonzero makes `1 + ρ'` nonzero, so that the claim binds `h(t)`; `D_n = (α +
   v_0 + ξ) B + w_m A = B (α + P_v(t) + ξ)` is there for the contract (its graph then computes `A` and `B` together:
   §4 item 13); `B` (the pushes' denominator) is required nonzero on its own since the claims divide by it (an honest
   proof fails it only at a `t` where a pull group's denominator vanishes). A nonzero `w_{m+1}` puts `t` off
   `V_{m+1}`, so every group's and port's denominator is nonzero too.

**Q's claims.** The identity at `t` is `c_h h(t) + c_q q(t) = Δ + w_m R_n / R_d` (`c_q = w_m`), normalised: `(1 + ρ')
h(t) + ρ' q(t) = num_1 / (R_d Y)` at `ρ' = c_q / Y`, `Y = c_h + c_q`, `num_1 = Δ R_d + w_m R_n`. `P`'s definition is
`w_m q_P(t) = s + P_v(t) = num_3 / B`, `num_3 = (s + v_0) B + w_m A = D_n + d_push B`. A slot's weighted value is `D`
times its polynomial's value at `t`, `D = s_E t / w_{m+1}` (`(y_0, y_1)` and `s_E` the limbs' coordinates and scale, as
`crates/membership/quotient`; `Π_{l ≤ m} (1 + w_l)^{-1}` telescopes to `t / w_{m+1}`), at the digit coordinate `u_m`
(weights `1 + u_m`, `u_m`), the limbs' `L_l = eq((y_0, y_1), l)`. Each claim on `Q` is a point of its whole stack, a
product weight on the slots' bits, so one claim cannot carry the three relations with fresh randomness between them;
two claims at the position `u` do:

- **the identity's**, at `(u, ρ', y_0, y_1)`: `h` and `q` at the kind coordinate `ρ'` (the identity's own ratio) and
  the limbs' `L_l`, and limb code 3 at `y_0 y_1`, which weighs `P` (at digit 1: `u_m (1 + ρ')`) and `q_P`
  (`ρ'`, digits): value `(D / Y)(num_1 / R_d + c_3 (c_h w_m s + num_3 / B))`, `c_3 = y_0 y_1 / L_0`
  (`u_m / (1 + u_m) = w_m`);
- **the pushes'**, at `(u, ρ, 1, 1)`: limb code 3 alone (`P` by `u_m (1 + ρ)`, `q_P` by `ρ`, digits): value
  `(D / L_0)((1 + ρ) w_m s + ρ num_3 / (w_m B))`.

`ρ` is drawn after `s`: a false `P(t) = s` or a false definition leaves the pushes' claim a nonzero polynomial of
degree 1 in `ρ` (both errors are fixed before `ρ`), false but with probability `1/|E|`; with those two true, the
identity's claim holds exactly when the identity does (`P`'s and `q_P`'s share in it is then the verifier's, from `s`
and `num_3`). The third claim, `h`'s top coefficient `Σ_V h = 0`, is at `(1^m, 0, 0, y_0, y_1)`: digit 0 and kind 0
weigh `h`'s three limbs and, at limb code 3, slot `12`, which is zero for the honest prover and, for any
prover, but with probability `4N/|E|` ("The empty slots" below). The identity's and the pushes' claims share their
position coordinates (the contract writes them once).

**The empty slots are not constrained, and need not be.** With plain PCS claims `Q`'s commitment is its sixteen-slot
stack, so the prover chooses slots `1, 5, 9, 12` too; the honest prover leaves them zero. Slots `1, 5, 9` are `h`'s
second digit `h_1` (`h = h_0 + Z_V h_1`): in the identity `c_h Z_V h_1` joins the quotient (`q + c_h h_1`, still below
`2N`), and `Σ_V h = Σ_V h_0`, so a cheating prover gains nothing: the identity, read at the random `t` as a polynomial
identity in `t` (every committed polynomial fixed before `t`; degree below `4N`, error `4N/|E|`), is the honest one with
that quotient. Slot `12`, `S` (below `N`), sits at `P`'s limb code and kind, at digit 0: the pushes' claim (exact but for
`1/|E|`, as above) then reads `S(t) + w_m P(t) = w_m s` and the definition `w_m q_P(t) = s + P_v(t)`, so
`w_m² q_P = w_m P + S + w_m P_v` at `t`, every term fixed before `t`: as polynomials, but with probability below
`4N/|E|`, so `w_m` (degree `N`) divides `S` (degree below `N`), and `S = 0`. Both terms are below `2^-165` at the
reference shape; `formal/RecPiop`'s soundness carries them (the honest `Q` the plain stack, its empty slots zero).

**The claims** (5, after π1's 3), each a point of its stack (past the table's coordinates, zeros):

- `W` at `(ρ, ρ², …, ρ^{2^{r-1}}, w_r, …, w_{m-1})`, value `Σ_k eq(ρ⃗, k) a_k`;
- the setup at `(w_0, …, w_{m-1}, β)`, value `ξ` (its halves `κ`, `κ + σ`: `(1 + β) κ + β (κ + σ) = κ + βσ`);
- `Q` at `(u_0, …, u_m, ρ', y_0, y_1)`, `u_l = w_l/(1 + w_l) = 1 + 1/w_l + 1/w_{l+1}`, the identity's value; at
  `(u_0, …, u_m, ρ, 1, 1)`, the pushes'; at `(1^m, 0, 0, y_0, y_1)`, value `0`.

**The contract** (`contract`): reads π1's three claims' hashes from the frame's payloads 0 … 2 into the seed (π2's
circuit computes them from π1's run, since [`PERF_GAS2.md`](PERF_GAS2.md)), reads the stream, runs the verifier, then
checks π2's five claims declared at payloads 3 … 7, each the EIP draft's PCS claim (`evm_link::declared_claims`: its
`82 + 24 n` bytes packed and hashed, the hash a payload of the frame): `W`'s, the setup's (its commitment a constant)
and `Q`'s three. (Before `PERF_GAS.md` it encoded π1's three claims too, from the stream and constants; `PERF_GAS.md`
hashed `C1`'s in the circuit, at payload 0.)

## 3. The prover (`prover`)

1. `w`'s novel coefficients (`quotient::ntt`), its `B` coefficients (subset sums): `W`, committed.
2. `α, β, γ`; on `V_m` (`h_on_v`, eight rows at a time, one batched inversion a run of 4,096), in `Q`'s stack: `P_v`
   (a pair's formula of its row, a forward's or a hole's own value) and `h` (zero at a hole), its sum checked to be zero (as `h`'s top novel coefficient),
   and the ports checked (`T` zero at every hole; for any other `w`, `prove_with` sets `h = T/(d_pull d_push)` at a
   dishonest hole, so the identity still holds and only the sum's claim is false: §6); `h`'s and `P`'s novel
   coefficients.
3. On `D = β_{m+1} + V_{m+1}` (`2N` points, disjoint from `V_m`), one coset of `V_m` at a time: `w`, `h`, `P` by
   transforms (five of `2^m` a coset), `σ`, `κ` with the setup (fixed by the circuit). Eight points at a time: the
   row's cells (`x + ω_c` stays in `D`), every pair's indicator (a chunk of 4,096 points at a time: a pair whose block
   spans the chunk is periodic in it, one batched inversion), `P_v` (the internal groups as one quadratic form of the
   cells), the ports' `T` (each port group's formula plus its role's `Φ`, which is one value a row: per chunk, its rows'
   `Φ` by one batched inversion of `rows × ports` denominators, eight rows a vector), `d_pull`, `d_push`,
   `q = (h d_pull d_push + (1 + 1_S)(d_push + d_pull) + T) / Z_V` and `q_P = (P + P_v) / Z_V` (`Z_V` takes two values
   on `D`). Their novel coefficients: degree below `2N`, `2N` points determine them.
4. `Q`, committed (its stack built in place, the setup's from one proof to the next; `Q` and `W` keep their codewords
   until their openings, which read the queried rows from them); `t`; the fold values, `ξ` and `s = P(t)`; `ρ`; the verifier's claims,
   opened by `quotient::opening` (leanVM's WHIR unchanged, rate 1/2, the claims on one commitment in one opening).
   `PI2_PROFILE=1` prints the phases.

## 4. Decisions and deviations from SPEC-REC's design

1. **Holes are out of the copy argument** (the design added the holes' sums `Σ 1/D(0, ω_h)` to the target; π2v1 left
   the holes' pulls out and kept their pushes to outside tags, against a public target). π2v2 weights pulls and pushes
   by `1 + 1_S`: the copy argument is over the internal positions, its sum is zero, and the ports are `T`'s (§1). A
   hole's value is unconstrained: `adapt` checks that no formula of a port's region reads a hole (the circuit compiler
   never places a value there), and panics otherwise; `Circuit::validate` is asserted on the setup path (`Spec::of`,
   `Setup::new`, `contract::Instance::new`) too.
2. **The ports' fingerprints are not `Σ γ^l L_l`.** Three limbs (an element, a zero check) are `L_0 + Y L_1 + Y² L_2`:
   the element itself. Four limbs (the statement, a root) are `(L_0 + Y L_1) + γ (L_2 + Y L_3)`: a root's two 16-byte
   halves as `next_root` reads them, one product. Both bind the limbs (injective on `K³`; for all but one `γ` on `K⁴`),
   as `spec::Circuit::check` compares them.
3. **`h(t)` is not sent** (§9, lever 2): `Q`'s claim is the identity's combination of `h(t)` and `q(t)`, and the
   verifier inverts once at the end. (The first build sent it, with `σ(t)` and `κ(t)` apart: `2^r + 3` values.)
4. **`W` and the setup in the `B` basis, `Q` in the novel basis.** The `B` basis makes a claim at the digits themselves
   (no inversion); `Q` needs the novel basis for `Σ_V h` to be one entry (the top coefficient), so its point takes the
   `u_l`.
5. **`ρ` is `W`'s fold and `Q`'s combination.** `W`'s claim is a polynomial of degree `2^r − 1` in `ρ`, `Q`'s one of
   degree 3 (§2); the setup's takes no `ρ`.
6. **The extension coset is `2N`** (π2v1: `4N`, for `q` below `4N`).
7. **The public data is in the stream**, absorbed by the first challenge, the statement in the seed (the design: a
   separate `D = keccak(public data)`).
8. **No row counts among the public terms** (SPEC-REC §10.4 item 3).
9. **Stacks of at least `2^24` words** at the target shapes (§2).
10. **The verifier's arithmetic** (§2): normalised indicators, fractions by groups, the inverse by the norm. Measured on
    the synthetic D16v target: 56.3K → 46.2K execution, before §9's levers.
11. **`P` is committed in `Q`** (π2v2), after `α, β`: its definition pins it on `V_m` to `P_v`, a function of `W`
    (§7). `d_push` then takes `P`, below `N`, and the identity is below `3N` (π2v1: `P` of degree below `3N` inside
    `d_push`, the identity below `5N`). `P` is in `K` (the internal pushes are, `Circuit::validate`): one limb.
12. **`Φ` by rows** (π2v2). The ports' public values enter as `Φ_k`, one per port role (the real circuit's ports are all
    at role 15), interpolated over the rows by `w_r` rather than over the positions: the verifier's cost is the same (a
    fraction a port of nonzero value), and the prover's `Φ` is one value a row of `2^r` points. The zero ports drop out.
13. **`D_n` in the inversion** (π2v2). The contract's code computes a value where it is first read, keeps one read
    again in memory, and computes the checks first. Without `D_n` the check reads `B` (through `z`'s or `1/B`'s
    product) before `A`, and every group's denominator waits in memory for `A`'s chain (the first build: 480 words of
    memory, 28,670 execution, against 230 and 27,641). `D_n` reads `A` and `B` together; its being nonzero costs
    completeness `3N/2^192` at most.
14. **`z = ρ² B`** (π2v2): `q_P`'s weight carries `B`, so `B` is not inverted (it is nonzero whenever `w_{m+1}` is).

## 5. The synthetic circuits (`synth`)

Before the real circuit existed, `synth` built circuits with every row kind of SPEC-REC §2.4 (χ formulas, D
units, XORs, packings, free bits, `E` products and sums, constants, ports of every source) and a witness satisfying them
by construction (FIFO wiring), small (`2^11`, `2^12` positions) and at the design's target shape (`2^24`, about 200
pairs, `target_d16v`). They remain the PIOP's tests and `gas_report`'s shapes. The real
D16v circuit of the Keccak VM's π1 has 133 pairs at the reference shape (4 port pairs; 20 ports of nonzero value, all
at role 15).

## 6. Tests

- `lib`: an indicator is one on its coset and zero on `V_m`'s rest (every alignment and size); `Φ`'s basis (`w_r(ω_i)
  = ω_{i >> r}`, `w_m = w_{m-r} ∘ w_r`, `V_{m-r}`'s Lagrange basis sums to one off `V_m`); the inverse; the stacks'
  `Q`'s slots are their bits (`quotient_slots_are_their_bits`).
- `tests/pi2.rs`, D16v synthetic circuits and the interface's own example (padded, through `adapt`):
  - the honest proof's five claims hold and their openings verify (`pcs_claim::verify_claim`);
  - witness mutations (random constrained positions): a false claim;
  - a changed element, a changed public input (a dishonest port, the identity kept by the prover): exactly the sum's
    claim is false, `[true, true, true, true, false]` (§7's lemma at work);
  - flipped stream bytes: claims the openings do not prove;
  - the contract equals the Rust verifier word for word, on the honest stream and a random
    one; it accepts the honest proof with its frame declaring exactly its claims, and rejects flipped bytes.
- `tests/pi2_real.rs`, the real circuits (`PI2_VECTOR=keccak128_rec4`, the default, or `keccak_rec4`; the
  `keccak*_rec3` vectors give `PERF_GAS.md`'s π2, 941 B and 89,672 with the frame): `real_gas`, the
  gas, deployment and parity of D16v; `real_end_to_end` as in §0. The claims holding on the real tables are the degrees' check (§1): a `q` or
  `q_P` of a degree above `2N` would not be determined by `D`'s `2N` points, and its claim would fail.
- `tests/pipeline.rs`: the prover timed from a trace, π2's proof and openings among its stages (§0).
- `tests/keccak_vm_rec.rs`: π1-rec4 (`leanvm_rec::PI1`) at 128 and 400 signatures compiled into D16v on a sample stream, the contract's gas
  and parity.
- `tests/lean_pi2_prover.rs`: vectors for the Lean honest prover's differential test (`formal/RecCompose`, of π2v3
  as of `f96a7938`: §10).

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
positions, both sides sets: `R ≠ 0` unless every internal pull is the push sent to it. The sum's claim is `R(α, β) = 0`:
probability at most `2N/2^192` for a nonzero `R` (its numerator's degree), and `2N/2^192` that a denominator vanishes on
`V_m`: `4N/2^192` over `W`'s list, as π2v1's copy argument. The prover's side (`tests/pi2.rs`): a dishonest port with the
identity kept makes exactly the sum's claim false.

**Committing `P` after `α, β`** is sound for the same reason: `P`'s values on `V_m` are pinned to `P_v`'s by its
definition, so `d_push` on `V_m` is fixed by `W` before `α, β`.

**The rounds** (`params/leanvm_rec_params.py`, `pi2_rounds`; `N = 2^24`, lists `L_W` 9,952, `L_Q` 3,564; bits alone,
then after the union):

| round | error | alone | after |
|---|---|---:|---:|
| the copy argument `(α, β, γ)`: `2N` fractions, the ports' poles, the four-limb ports' fingerprints (degree 1 in `γ`) | `(4N + 3)/2^192` over `L_W` | 166.0 | 152.7 |
| `t`: the copy identity and `P`'s definition, both must vanish; below `3N` for the honest `Q`, below `4N` with its prover-filled empty slots (§2) | `4N/2^192` over `L_W L_Q` | 166.0 | **140.9** |
| `ρ`: `W`'s fold (degree 15) | `15/2^192` over `L_W L_Q` | 188.1 | 163.0 |
| `ρ`: `Q`'s claim (degree 3) | `3/2^192` over `L_W L_Q` | 190.4 | 165.3 |

π2v1's rounds (§10) were the copy argument `(3N + 2)/2^192` (153.1 bits), `t` the identity below `5N` (140.6) and
`ρ` (163.0). The Lean (`formal/RecPiop`'s `err`) states π2v3's, coarser: `(4N − 1 + Σ_j d_j)/|E|` for the copy
argument and the ports, `(4N − 1)/|E|` at `t`, `2^r/|E|` at `ρ`. These depend only on `N` and the stacks. With the
three openings charged once (`269 · 2^-137` a query), π2 keeps 128.93 bits as `Q/ε` at `Q = 2^64`, as π2v1
(`RecCompose.pi2Bound`, `pi2Bound_le_bits`, proved for π2v1).

## 8. The claims' encoding, the IVs, the setup path

- **One encoding for the eight claims**: the EIP draft's PCS claim (`crates/pcs_claim`, `docs/PCS_CLAIM.md`), `version
  || n || root || ood || point || value`, `82 + 24 n` bytes, its Keccak-256 a payload of the transaction's frame of PCS
  claims:
  - every root is the commitment's 32 bytes as they are: π1's prover sends a root's bytes, so π1's stream carries
    `C1`'s and `C2`'s as the claims encode them, and the circuit's root ports pack the stream's bytes as they are
    (`circuit::compile`); π2's `W` and `Q` roots are in calldata so; π1's setup root `F` and π2's setup root are
    constants so;
  - every out-of-domain answer is an element: π1's two are elements of its stream (public elements of π2), π2's two
    after their roots, the setups' constants;
  - every claim is a point of its commitment's whole stack (`n` its variables), its value the polynomial's there;
  - **one PCS version** (1): leanVM's WHIR at rate `1/2` on its ladder (`pcs::whir::DEPLOYED_SCHEDULE`), every opening
    one claim's (`pcs_claim::open`, `verify_claim`); the stacks' leading lanes are committed alone (the
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

**Lever 3c: the zero checks as no term** (π2v2; π2v1 summed them in closed form). π1's zero checks are ports of value
0. The circuit compiler makes them the first ports, padded with constant-zero ports (`spec::Source::Pad`) to a power of
two `2^k`, so that their outside tags are the aligned coset `ω_N + V_k`: π2v1's verifier added their public sum
`Σ_(u ∈ V_k) 1/(Y + βu) = β^(2^k − 1)/F(Y)` in closed form (`F = β^(2^k) w_k(X/β)`), about 15 products instead of one
fraction a check. In π2v2 a zero port is in no `Φ` (§1): it costs the verifier nothing, the padding included (kept, so
that the circuit is π2v1's).

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

- **`σ(t)` and `κ(t)` as one value.** The verifier uses them only in `d_push`: as `ξ = κ(t) + βσ(t)`. The setup's halves
  are `κ` and `κ + σ`, so its one claim at `(w_0, …, w_{m-1}, β)` is `(1 + β)κ(t) + β(κ + σ)(t) = ξ`, with no
  inversion. The setup is honest (`L = 1`) and fixed before `β`: the claim binds `ξ` exactly. `ρ` does not enter the
  setup's claim.
- **`h(t)` not sent.** The verifier keeps every quotient as a fraction and inverts once at the end (§2): the identity
  at `t` is the one combination of `h(t)` and `q(t)` it is, `c_h h + c_q q = Δ + w_m R_n/R_d`, and `Q`'s claim takes
  it normalised, `(1 + ρ')h(t) + ρ'q(t)` at `ρ' = c_q/(c_h + c_q)` (with `P(t) = s` and `P`'s definition, §2).
- **D8v (rows of 8, 8 fold values: −192 B) is dropped.** With `Q = 12N` words (π2v1: `15N`), `N` must stay `2^24`
  (`2^25` gives `2^28.58`). At the reference shape's 116 permutations and 0.48M other positions, a Keccak-f must fit in
  about 140K positions, 7% more than D16v's 130,944. A χ output reads three `b = A + D` of its plane, so a row of 8
  holds the inputs of at most two outputs, or must materialise `b` (one more position a state bit, and its forwards):
  about 2× D16v's positions a round, well past 140K.

## 10. π2v1, and the Lean side

π2v1 (transcript `leanvm-rec-pi2v1`, up to commit 0c6fcf3) pushed the ports' fingerprints to outside tags inside the
copy argument (`h`'s sum the public target `Σ_J 1/(α + F_J + β τ_J)`, the zero checks' coset in closed form, the
others' `β ω_τ` along a walk of the tags' bits), kept `P` (degree below `3N`) inside `d_push`, so that the identity
`h d_pull d_push + (1 + 1_S) d_push + d_pull = q Z_V` was below `5N`, `q` below `4N` on a `4N` coset, and `Q` was `h`
and `q`'s four chunks (`15N` words, `m + 5` variables); `2^r + 1` values; `Q`'s claims at `(u_0, …, u_{m+1}, ρ', y_0,
y_1)` and `(1^m, 0, 0, 0, y_0, y_1)`, value the target. Its measured figures: 980 B, 28,325 execution, 43,213 EIP-7623
at 128 signatures (44,041 at 400), 62,720 EIP-7976 (at the π1 contract IV without the BLAKE2s-era words; 43,309 and
44,113 before it).

**The Lean side** (`formal/RecPiop`, `RecStatement`, `RecCompose`) states and proves the protocol of this note: π2v3
on the EIP draft's PCS claims. The contract model checks the eight declared claims (π1's three, π2's five), each a
root, its out-of-domain answer, a point and a value, opened by one PCS opening (`WhirBridge.Pcs`), the eight charged
once (`pcs_union_sound_oracle`); `Q`'s three claims are bound to one table by its answer (`qOodBinding`); `Q`'s empty
slots are the prover's, handled as §2 says ("The empty slots"), at round 1's error `(4N − 1)/|E|`. The end theorems
(`RecCompose.recKnowledgeSoundness_reduction_real`, `Pi1K.recCompleteness_real_K_fs_bits`) keep their bounds:
`pi2Bound Q ≤ 2^-64` at `Q ≤ 2^64` (128.93 bits as `Q/ε`), completeness `δ1 + δh + 2^-164`. π2's Lean prover agrees
with the Rust on the `lean_pi2_prover` vectors; `rec-circuit-keccak`, `rec-view-check` and `rec-real-check` hold
(`formal/RecCompose/README.md`).
