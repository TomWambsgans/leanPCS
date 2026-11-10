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
   the random rows (`6 + 16` words). With the masks of `Y` and `C` fixed (they enter the gate quotient through `Y·C`),
   the dependence is affine. The map's rank is 15 (five elements of `E`).
3. **`H`'s and `Q`'s out-of-domain answers and `Q`'s value** depend on the blinding (24 words), with everything above
   fixed. The dependence is affine: `q` changes by the blinding times the copy argument's denominators. The rank is 9.

So, whatever the witness, the revealed scalars are uniform. `H`'s value is then the one the public relation forces.
The **simulator** samples the scalars of groups 1 to 3 uniformly, computes `H`'s value from the relation, and
simulates the openings with the ZK-PCS simulator.

**The condition, tested.** `hiding::revealed_scalars_are_uniform` fixes the challenges (a test hook in
`transcript.rs`) and proves on the toy circuit (`2^17` rows). It changes one randomness word at a time and checks
over `K` that each group's map has full rank (6, 15 and 9). It is a check at random challenges, not a proof for every
challenge. A rank falls short only on a set of challenges where some determinant of the challenges vanishes:
probability at most its degree over `|E| = 2^192`. That bound is not written out here.

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
- **The Lean proof.** `formal/` still proves zero knowledge for the hidden layouts (`zeroKnowledge_closed`). Its
  statement must be moved to this argument.
- Deployed randomness is ChaCha12 and a Keccak-256 KDF (`Randomness::derive`), so zero knowledge is computational.
