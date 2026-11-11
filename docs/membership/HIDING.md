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
The protocol is the one of [`PERF_GAS.md`](PERF_GAS.md): one quotient, in one table `T` with the sum's polynomial.
The previous protocol's argument (commit `f96a7938`: the masks, three groups, the measured group) is in this file's
history.

## What is public

A proof publishes, in its stream (`protocol::reduce`):
- two commitments, each a root and an out-of-domain answer: the witness table `W` and the quotient table `T`;
- the row values `a_0 .. a_3` at the point `t`;
- `next`, the public wiring table's value.

Its four claims add nothing:
- `W`'s value is a function of the `a_j`;
- the wiring's is `next`;
- `T`'s claim at `t` is `(d + d' + μ Z g) / (Z + d d')`, up to public scales, a function of the `a_j`, `next`, the
  challenges and the statement;
- `T`'s claim at `h`'s top coefficient is zero.

## The randomness

Two sources, each used only where the PIOP's identities allow it:
- **The random rows** (`circuit::RANDOM_ROWS = 16`): idle rows made rows of two free cells, each its own cycle of
  the wiring, in three shapes (`circuit::RandomShape`): `(X, Y, C, V) = (r, 0, s, r + s)`, `(r, s, 0, r)`,
  `(r, 1, s, r)`. The gate `V = X + C + Y·C` holds for any `r, s`, and every cell is affine in them. The prover
  draws two fresh words a row (`Randomness::rows`, 32 words). There are no masks: the witness polynomial `w` keeps
  degree `< n`, which the quotient's degree needs (`PERF_GAS.md`).
- **The blinding of `h`** (`protocol::H_BLIND = 2` coefficients per limb): `h + X_{2^m}·b_e`, coefficients
  `2^m, 2^m + 1` of the sum's polynomial (`T`'s kind 1, digit 1). `X_{2^m}` vanishes on the cells, so `h` is
  unchanged there and the identity holds; the quotient `q` absorbs the change, `q ↦ q + b d d'`.

## The argument

Fix the challenges. Each group below is affine in its randomness once the groups before it are fixed, and the next
one does not touch it:

1. **`a_0 .. a_3` and `W`'s out-of-domain answer** are `K`-linear in the cells, hence affine in the 32 random-row
   words, with rank 15 (all of their `K`-coordinates).
2. **`T`'s out-of-domain answer** is affine in the 6 blinding words, everything above fixed. The blinding enters
   `h`'s slots directly and `q` through `b d d'`, and `μ g` does not depend on it. The rank is 3.

So, whatever the witness, the revealed scalars are uniform at the challenges where both ranks are full. Both groups
are affine, and no group is measured instead of argued. The previous protocol had one: the masks of `X` and `V`
met in the gates' quotient `G` through `Y·C`, and a random row entered `G` through `v²`. That group is gone with `G`'s
separate commitment and its revealed value.

The **simulator** samples the out-of-domain answers and the `a_j` uniformly, computes the claims' values from them,
and simulates the openings with the ZK-PCS simulator.

**The conditions, tested.** `hiding::revealed_scalars_are_uniform` fixes the challenges and the out-of-domain points
(test hooks in `transcript.rs` and `opening.rs`) and proves on the toy circuit (`2^17` rows). It changes one
randomness word at a time and checks over `K` that both groups have full rank (15 and 3). It checks that both maps
are affine: two words changed together move the scalars by the sum of their own changes, and a word scaled by an
element of `K` by that multiple. `revealed_scalars_are_uniform_on_membership` (ignored by default, about 100 s on 64 threads:
`cargo test --release -p quotient --lib hiding -- --ignored`) checks the same on the membership circuit at `2^22`
rows. It is a check at random challenges, not a proof for every challenge. A rank falls
short only on a set of challenges where some determinant of the challenges vanishes: probability at most its degree
over `|E| = 2^192`. That bound is not written out here, but both maps being affine, it is a determinant's degree to
bound, where the previous protocol's measured group had no such argument.

**The roots** hide in the random-oracle model as long as each committed table has enough min-entropy given
everything else revealed:
- `W`: 2,048 bits of random rows, against 15 elements revealed, so at least 1,088 bits are left;
- `T`: 384 bits of blinding, against 3 revealed, so at least 192 bits are left. This is less than before (960), and
  it is still above 128.

With a ZK-WHIR whose leaves are salted, the roots hide without this.

## What is not covered

- **The openings themselves.** leanVM's WHIR reveals Merkle rows and sumcheck messages that are functions of the
  tables. The reference openings are therefore **not** zero-knowledge; the EIP assumes ZK-WHIR.
- **The Lean proof** (`formal/EndToEnd/ZK`, `PcsQuotient.EndToEnd.zeroKnowledge_pcs_closed`) is of the previous
  protocol, with its `RevealedUniform` hypothesis over that protocol's revealed scalars. Porting it to this one is
  listed in `PERF_GAS.md`. `RevealedUniform` should then become provable from the two rank conditions, since both
  groups are affine.
- Deployed randomness is a Keccak-256 KDF (`Randomness::derive`: the random rows' words, then the blinding), so zero
  knowledge is computational.
