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
The protocol is the one of [`PERF_GAS2.md`](PERF_GAS2.md): one quotient, in one table `T` with `x h`, the sum's
polynomial times `x`, three claims, the row of `t` revealed as `X`, `C` and `V + Y` (on [`PERF_GAS.md`](PERF_GAS.md)'s
protocol). The previous protocols' arguments (commit `f96a7938`: the masks, three groups, the measured group; then
four claims, the four `a_j`) are in this file's history.

## What is public

A proof publishes, in its stream (`protocol::reduce`):
- two commitments, each a root and an out-of-domain answer: the witness table `W` and the quotient table `T`;
- the row values `X`, `C` and `V + Y` at the point `t` (three linear forms of the row polynomials' values there);
- `next`, the public wiring table's value.

Its three claims add nothing:
- `W`'s value is a linear combination of the three row values, its weights the challenges';
- the wiring's is `next`;
- `T`'s claim at `t` is `t (d + d' + μ Z g) / (Z t + d d')`, up to public scales, a function of the row values,
  `next`, the challenges and the statement.

## The randomness

Two sources, each used only where the PIOP's identities allow it:
- **The random rows** (`circuit::RANDOM_ROWS = 16`): idle rows made rows of two free cells, each its own cycle of
  the wiring, in three shapes (`circuit::RandomShape`): `(X, Y, C, V) = (0, r, s, r + s)`, `(s, r, 0, r)`,
  `(1, r, s, r)`. The gate `V = Y + C + X·C` holds for any `r, s`, and every cell is affine in them. The prover
  draws two fresh words a row (`Randomness::rows`, 32 words). There are no masks: the witness polynomial `w` keeps
  degree `< n`, which the quotient's degree needs (`PERF_GAS.md`).
- **The blinding of `h`** (`protocol::H_BLIND = 3` coefficients per limb): `h + X_{2^m}·(b_0 + b_1 X_1 + b_2 X_2)`,
  coefficients `2^m .. 2^m + 2` of the sum's polynomial (`T`'s kind 1, digit 1, as `x h`'s `B_1`). `X_{2^m}`
  vanishes on the cells, so `h` is unchanged there and the identity holds; the quotient `q` absorbs the change,
  `q ↦ q + b d d'`. `b_0, b_1` are drawn (`Randomness::blind`, 6 words); `b_2` is solved for so that `q`'s
  coefficient `n` is zero, which `T`'s layout needs (`PERF_GAS2.md`): a linear condition, so `b_2` is affine in
  `b_0, b_1` (and the witness, fixed here).

## The argument

Fix the challenges. Each group below is affine in its randomness once the groups before it are fixed, and the next
one does not touch it:

1. **`X`, `C`, `V + Y` at `t` and `W`'s out-of-domain answer** are `K`-linear in the cells, hence affine in the 32
   random-row words, with rank 12 (all of their `K`-coordinates).
2. **`T`'s out-of-domain answer** is affine in the 6 free blinding words, everything above fixed. The blinding
   enters `x h`'s digit 1 directly and `q` through `b d d'` (`b_2` affine in `b_0, b_1`), and `μ g` does not depend
   on it. The rank is 3.

So, whatever the witness, the revealed scalars are uniform at the challenges where both ranks are full. Both groups
are affine, and no group is measured instead of argued. The previous protocol had one: the masks of `X` and `V`
met in the gates' quotient `G` through `Y·C`, and a random row entered `G` through `v²`. That group is gone with `G`'s
separate commitment and its revealed value.

The **simulator** samples the out-of-domain answers and the three row values uniformly, computes the claims' values
from them,
and simulates the openings with the ZK-PCS simulator.

**The conditions, tested.** `hiding::revealed_scalars_are_uniform` fixes the challenges and the out-of-domain points
(test hooks in `transcript.rs` and `opening.rs`) and proves on the toy circuit (`2^17` rows). It changes one
randomness word at a time and checks over `K` that both groups have full rank (12 and 3). It checks that both maps
are affine: two words changed together move the scalars by the sum of their own changes, and a word scaled by an
element of `K` by that multiple. `revealed_scalars_are_uniform_on_membership` (ignored by default, about 50 s on 64
threads: `cargo test --release -p quotient --lib hiding -- --ignored`) checks the same on the membership circuit at
`2^22` rows. It is a check at random challenges, not a proof for every challenge. A rank falls
short only on a set of challenges where some determinant of the challenges vanishes: probability at most its degree
over `|E| = 2^192`. That bound is not written out here, but both maps being affine, it is a determinant's degree to
bound, where the previous protocol's measured group had no such argument.

**The roots** hide in the random-oracle model as long as each committed table has enough min-entropy given
everything else revealed:
- `W`: 2,048 bits of random rows, against 12 `K`-coordinates revealed, so at least 1,280 bits are left;
- `T`: 384 bits of free blinding, against 3 revealed, so at least 192 bits are left.

With a ZK-WHIR whose leaves are salted, the roots hide without this.

## What is not covered

- **The openings themselves.** leanVM's WHIR reveals Merkle rows and sumcheck messages that are functions of the
  tables. The reference openings are therefore **not** zero-knowledge; the EIP assumes ZK-WHIR.
- **The Lean proof** (`formal/EndToEnd/ZK`, `PcsQuotient.EndToEnd.zeroKnowledge_pcs_closed`) is of the previous
  protocol, with its `RevealedUniform` hypothesis over that protocol's revealed scalars. Porting it to this one is
  listed in `PERF_GAS.md` and `PERF_GAS2.md`. `RevealedUniform` should then become provable from the two rank
  conditions, since both groups are affine.
- Deployed randomness is a Keccak-256 KDF (`Randomness::derive`: the random rows' words, then the blinding), so zero
  knowledge is computational.
