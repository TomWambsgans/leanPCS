# Zero knowledge of the membership proof

**ZK assuming a zero-knowledge PCS opening; the reference openings are not yet ZK-WHIR.** The EIP draft's PCS is
assumed zero-knowledge (ZK-WHIR): an opening reveals nothing beyond its claim. The reference implementation opens
with leanVM's WHIR (`crates/pcs_claim`), which is not zero-knowledge. What the protocol must provide on its own is
that everything public besides the openings can be simulated from the statement:
- the roots;
- the commitments' out-of-domain answers;
- the reduction's scalars;
- the claims' values.

This note says how (`crates/membership/quotient`, `protocol.rs`), and what the test checks (`src/hiding.rs`).

## What is public

A proof publishes, in its stream (`protocol::reduce`):
- four commitments, each a root and an out-of-domain answer: the witness table `W`, and the quotient table's parts
  `H`, `Q`, `G`;
- the row values `a_0 .. a_3` at the point `t`;
- `next`, the public wiring table's value;
- `Q`'s and `G`'s values at their points.

Its six claims add nothing:
- `W`'s value is a function of the `a_j`;
- the wiring's is `next`;
- `H`'s follows from `Q`'s, `G`'s and the quotient table's value (`T(P) = w_H H + w_Q Q + w_G G`), which the verifier
  computes from public data;
- the claim on `H` at the sum point is the statement's public sum.

## The randomness

Three sources, each used only where the PIOP's identities allow it:
- **The masks** (12 `K`-words, as before): a random multiple of the rows' vanishing polynomial added to each row
  polynomial, in `W`'s second chunk.
- **The random rows** (`circuit::RANDOM_ROWS = 16`): idle rows of the circuit made free-`K` rows (`X` reads the row's
  output, `Y = 1`, `C = 0`, so `V = V` holds for any value). The prover fills each with a fresh value. They change
  `W`'s cells and, through the gate, the gate quotient, linearly. The copy argument sees them as two-cell cycles.
- **The blinding of `h`** (`protocol::H_BLIND = 8` coefficients per limb): `h + X_{2^m}·b_e`, coefficients
  `2^m .. 2^m + 8` of the sum's polynomial (`H`'s digit 1). `X_{2^m}` vanishes on the cells, so `h` is unchanged
  there and the copy argument holds; the copy quotient `q` absorbs the change.

## The argument

Fix the challenges. Each group below is affine in its randomness once the groups before it are fixed, and the next
one does not touch it:

1. **`a_1`, `a_2`** depend only on the masks of `Y` and `C` (6 `K`-words), linearly, with full rank: this is F1, as
   before.
2. **`a_0`, `a_3`, `W`'s and `G`'s out-of-domain answers, and `G`'s value** depend on the masks of `X` and `V` and on
   the random rows (`6 + 16` words). **This group is not affine** (below, "Group 2, measured"): the masks of `X` and
   `V` meet in `G` (`Y` and `C` are shifts of the one interleaved witness polynomial, so `Y·C` multiplies them), and
   a random row enters `G` through `v²`.
3. **`H`'s and `Q`'s out-of-domain answers and `Q`'s value** depend on the blinding (24 words), with everything above
   fixed. The dependence is affine: `q` changes by the blinding times the copy argument's denominators. The rank is 9.

So, whatever the witness, the revealed scalars of groups 1 and 3 are uniform, and those of group 2 are as far as the
tests below measure. `H`'s value is then the one the public relation forces.
The **simulator** samples the scalars of groups 1 to 3 uniformly, computes `H`'s value from the relation, and
simulates the openings with the ZK-PCS simulator.

**The conditions, tested.** `hiding::revealed_scalars_are_uniform` fixes the challenges and the out-of-domain
points (test hooks in `transcript.rs` and `opening.rs`) and proves on the toy circuit (`2^17` rows). It changes one
randomness word at a time and checks over `K` that groups 1 and 3, which are affine, have full rank (6 and 9). It is a
check at random challenges, not a proof for every challenge. A rank falls short only on a set of challenges where some
determinant of the challenges vanishes: probability at most its degree over `|E| = 2^192`. That bound is not written
out here.

**Group 2, measured** (`hiding::group_a_over_the_random_rows`, `group_a_over_fresh_randomness`, ignored by default:
`cargo test --release -p quotient --lib hiding -- --ignored`, about seven minutes on 16 cores). The out-of-domain
points must be fixed with the challenges: each is derived from its table's root, so any change of the randomness moves
it, and the answers are then not even `GF(2)`-affine in the randomness (the earlier test, which fixed only the
challenges, measured a map that moves its own point).
- With the masks fixed, the map is `GF(2)`-affine in the random rows' `1,024` bits (checked on two-flip differences),
  and its rank is `960 − 193`. The rows never reach `a_3` (192 bits: only `V`'s mask does, `K`-linearly), and they
  miss one functional `ψ` of `G`'s value. A row moves `G`'s value by `v α + v² β` with `β = γ α²` for one `γ` shared
  by all rows, i.e. by `γ^-1 (u + u²)` at `u = γ α v`: an Artin–Schreier image, on which `Tr(γ ·)` vanishes. `ψ` is
  `Tr(γ ·)`.
- That bit and `a_3` are left to the masks, which reach them quadratically. Over fresh uniform masks and rows (1,408
  draws, one witness), the affine hull of the revealed bits of groups 1 and 2 (1,344 bits) is the whole space: no
  `GF(2)`-affine relation among them holds for a fixed witness. `ψ` (taken at the base masks) is balanced (within four
  standard deviations).

So group 2's uniformity is supported by measurement, not argued: the earlier grouping (the masks of `X` and `V`
affine once those of `Y` and `C` are fixed) is false. A protocol in which it is argued would blind `G` the way `h` is
blinded.

**The random rows and the gate quotient.** A random row `k` holds its value `v` in its `X` and `V` cells, so the
witness polynomial changes by `v·(L_{4k} + L_{4k+3})` (`L_i` the cells' Lagrange basis). The gate quotient reads the
cells through the shifts of the row (`(V + X + C + Y·C)/Z_rows`, `Y` and `C` the witness shifted by one and two
cells), and both shifts of `L_{4k} + L_{4k+3}` are `M = L_{4k+1} + L_{4k+2}`. So `Y·C` changes by
`v·M·(Y + C) + v²·M²`, and `G` (hence `G`'s out-of-domain answer and value) by a term in `v²` that does not vanish
off the rows. In characteristic two `v ↦ v²` is `GF(2)`-linear (the Frobenius), not `K`-linear: with the masks fixed, group 2's
map is `GF(2)`-affine in the random rows' bits, not `K`-affine in their values. A unit change of a word (`v ↦ v + 1`)
measures a `K`-rank, which does not establish uniformity; "Group 2, measured" above gives the exact `GF(2)` rank (the
rows miss `a_3` and the one bit `ψ`) and what the masks add. Group 2's uniformity is therefore measured, not argued, as
is the whole of this section's conclusion in the Lean statement
(`RevealedUniform`, below).

**The roots** hide in the random-oracle model as long as each committed table has enough min-entropy given
everything else revealed:
- `W` and `G`: 1,024 bits of random rows, against 15 elements revealed from 22 words, so at least 448 bits are left;
- `H` and `Q`: 1,536 bits of blinding, against 9 revealed, so at least 960 bits are left.

With a ZK-WHIR whose leaves are salted, the roots hide without this.

## What is not covered

- **The openings themselves.** leanVM's WHIR reveals Merkle rows and sumcheck messages that are functions of the
  tables. The reference openings are therefore **not** zero-knowledge; the EIP assumes ZK-WHIR. The hidden layouts
  this repository had before (a random first piece per lane, a gadget) made leanVM's WHIR openings hide, but they
  need claims on a layout. The EIP's claims are plain point evaluations of the whole committed multilinear, so that
  design is gone (`EIP_CLAIMS.md`).
- **The Lean proof** (`formal/EndToEnd/ZK`, `PcsQuotient.EndToEnd.zeroKnowledge_pcs_closed`, sorry-free, standard
  axioms): zero knowledge in the programmable random-permutation model for the explicit simulator `zkSimulator`
  (`formal/Statement/PcsQuotient/Zk.lean`: uniform roots, uniform revealed scalars, the chain's challenges computed
  from them, the wiring opening real, the secret openings by the PCS simulator), within `εpcs Q + εr + εfs₀`,
  `εfs₀ ≤ 2^-162`, under two hypotheses: `PcsZeroKnowledge` (the ZK PCS: the real experiment within `εpcs` of the
  honest prover over an ideal PCS) and `RevealedUniform` (this section's conclusion at all but `εr` of the uniform
  challenges, not proved: see the random rows above). Proved: the hybrid argument with adaptive challenges (the
  revealed scalars are hashed into the challenges they depend on), the prover over the ideal PCS as the simulator's
  program with the prover's answers (its recomputed chain replayed in the lazy permutation, the roots read back from
  their halves), and the Fiat–Shamir freshness bound (`fiatShamirUniform_closed`: the simulator's `113` challenge
  calls against independent uniform answers, each input injective in a value drawn just before it).
- Deployed randomness is ChaCha12 and a Keccak-256 KDF (`Randomness::derive`), so zero knowledge is computational.
