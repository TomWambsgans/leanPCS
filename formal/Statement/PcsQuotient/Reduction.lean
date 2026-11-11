-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Transcribed from `crates/membership/quotient/src/protocol.rs` (`reduce`, `verify`, `label`, `sum_point`,
-- `bit_weight`, `coordinate_weight`, `extension`), adapted from leanVM's `flock::quotient` (branch
-- PCS-openings-aggregation, commit 651453c6). Fields and Keccak-256 are leanerVM's (branch `mumbai`,
-- commit 6175f1a0, MIT OR Apache-2.0).
module

public import PcsQuotient.Relation
public import PcsQuotient.Domain
public import PcsQuotient.Transcript

/-!
# The reduction: four commitments and seven field elements to six claims

The verifier of the reduction (`reduce` and `verify`, `protocol.rs`): from the statement and
the reduction's proof (four commitments, each a root and its out-of-domain answer, and seven elements of
`E`), the four commitments it names and **six claims**, each a PCS claim (a plain multilinear evaluation
at one point) on a committed table: one on the witness table `W`, one on the circuit's wiring table, two on
`H` (the quotient point and the sum point), one on `Q`, one on `G` (`Claims`). `H`, `Q`, `G` are the three
parts of the quotient table `T` (`quotientParts`). It rejects only a size the commitments do not take
(`Supported`: `2^13` to `2^22` rows), a malformed root (halves with a top limb) or a challenge at which a
denominator vanishes; the claims carry the rest, and the openings (`Opening.lean`) check them.

**The protocol** (`doc/quotient/main.tex` of leanVM's branch). The circuit has `2^m` cells,
`m = logRows + 2`, cell `i` at the point `B(i)` of the Cantor basis (`Domain.lean`), four a row
(`X, Y, C, V`), its gate `V = X + C + Y·C`. The prover commits the witness table (the cells'
polynomial in the novel basis, and masks), receives `α, β, γ`, commits the quotient table's three parts
(`H`: the sum's polynomial `h` with its blinding; `Q`: the copy quotient; `G`: the gate's quotient), each
commitment a root and its out-of-domain answer, receives `t`, and sends the four values `a_j` of the row
polynomials at `t` and `next`, the wiring polynomial at `t`; `ρ` batches; then `Q`'s and `G`'s values at
their points. Since a multilinear claim at the point `(w_k(t))_k` is a univariate evaluation, each identity
is one claim on `T`, which the verifier reads through its parts: `H`'s value follows from `Q`'s and `G`'s.

**Transcription.** The Rust is generic in its scalar (so that the same code is the EVM contract);
here the scalar is `E`. Two forms differ without changing a value: the proof is a structure
(`ReductionProof`, nineteen scalars in the stream's order) rather than a stream (a stream of another
length, which the Rust rejects as exhausted or trailing, is no `ReductionProof`); and the inverses are
taken one by one (`x⁻¹`) where the Rust inverts one product (by the norm to `K`, `protocol.rs`)
and unwinds it, after the same check that no denominator is zero.
-/

@[expose] public section

namespace PcsQuotient

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open PcsQuotient.Domain PcsQuotient.Transcript

/-! ### Constants -/

/-- `REGION` (`protocol.rs`): the public bits are the cells of the span of `11` basis vectors,
the `X` and `Y` cells of the `512` public rows. -/
def region : ℕ := 11

/-- `cell_vars` (`protocol.rs`): the cells' variables, `m = logRows + 2` (four cells a row).
-/
def cellVars (logRows : ℕ) : ℕ := logRows + 2

/-- `LOG_ROWS` (`circuit.rs:22`): the membership circuit has `2^22` rows, so `2^24` cells. -/
def logRows : ℕ := 22

/-- `MIN_LOG_ROWS` (`protocol.rs`): below `2^13` rows the wiring table (`m` variables) is smaller than the
`2^15` words WHIR commits. -/
def minLogRows : ℕ := 13

/-- `MAX_LOG_ROWS` (`protocol.rs`): above `2^22` rows the table `Q` (`m + 4` variables) exceeds WHIR's
`2^28` words. -/
def maxLogRows : ℕ := 22

/-- `supported` (`protocol.rs`): the sizes the commitments take; the verifier rejects any other
(`VerifyError::Shape`). -/
def Supported (logRows : ℕ) : Prop := minLogRows ≤ logRows ∧ logRows ≤ maxLogRows

instance (logRows : ℕ) : Decidable (Supported logRows) := inferInstanceAs (Decidable (_ ∧ _))

/-- `bit_weight` (`protocol.rs`): the weight of bit `j < 128` of a public word, `x^j` in limb
`0` below `64` and `x^(j−64)` in limb `1` above: the weighted bits of a word sum to the element it is
read as. -/
def bitWeight (j : ℕ) : E :=
  if j < 64 then E.ofLimbs (K.ofBits (2 ^ j)) 0 0 else E.ofLimbs 0 (K.ofBits (2 ^ (j - 64))) 0

/-- `coordinate_weight` (`protocol.rs`): `m_k` for coordinate `k` of the public region, the
region's weight being `∏_k (1 + x_k (1 + m_k))`; `none` for `k ≥ 8`, where it is a power of `γ`. -/
def coordinateWeight (k : ℕ) : Option E :=
  if k = 0 then some (bitWeight 1)
  else if k = 1 then some 0
  else if k < 8 then some (bitWeight (2 ^ (k - 1)))
  else none

/-- `F192::Y`: the element `y`, limb `1`. -/
def ey : E := E.ofLimbs 0 1 0

/-- `extension` (`protocol.rs`): the two coordinates `(y/(1+y), y²/(1+y²))` of the extension
over the base field, and the scale `1/((1+y)(1+y²))` of the weights `(1, y, y², y³)` they give. -/
def extension : (E × E) × E :=
  let d0 := 1 + ey
  let d1 := 1 + ey * ey
  ((ey * d0⁻¹, ey * ey * d1⁻¹), (d0 * d1)⁻¹)

/-- `sum_point` (`protocol.rs`): the point of the claim on `H` at the top coefficient of the sum's polynomial:
coefficient `2^m − 1` of digit `0` (`m` ones, then a zero), its limbs weighed by the extension's coordinates. -/
def sumPoint (logRows : ℕ) : List E :=
  List.replicate (cellVars logRows) 1 ++ [0, extension.1.1, extension.1.2]

/-- **A commitment** as the claims name it (`opening::Commitment`): the Merkle root of the table's WHIR
commitment and its out-of-domain answer, the table's multilinear at the point derived from the root
(`Opening.lean`'s `oodPointWith`). -/
structure Commitment where
  root : Digest
  ood : E
  deriving DecidableEq

/-- **`element_bytes`** (`pcs_claim`): an element of `E` as `24` bytes, its limbs `c2, c1, c0`, each
big-endian. -/
def elementBytes (x : E) : List UInt8 :=
  beBytes (x.limb 2).lane ++ beBytes (x.limb 1).lane ++ beBytes (x.limb 0).lane

/-- `label` (`protocol.rs`): the transcript's seed, `"pcs-quotient-kc1"`, the circuit's commitment (its
root, then its out-of-domain answer as `element_bytes`) and the statement (`136` bytes). -/
def label (index : Commitment) (stmt : Statement) : List UInt8 :=
  "pcs-quotient-kc1".toUTF8.toList ++ digestBytes index.root ++ elementBytes index.ood ++
    stmt.y.toList ++ stmt.root.toList

/-- `halves` (`statement.rs:62-67`): a 32-byte value as two elements of `E`, sixteen bytes each read
as a big-endian number in limbs `0` (low) and `1` (high). -/
def halves (b : Bytes32) : E × E :=
  let half (h : ℕ) : E :=
    E.ofLimbs (K.ofLane (beWord b.toList (16 * h + 8))) (K.ofLane (beWord b.toList (16 * h))) 0
  (half 0, half 1)

/-- `Statement::halves` (`statement.rs:33-37`): `y` then `root`, each as its two halves. -/
def Statement.halves (stmt : Statement) : List E :=
  [(PcsQuotient.halves stmt.y).1, (PcsQuotient.halves stmt.y).2,
    (PcsQuotient.halves stmt.root).1, (PcsQuotient.halves stmt.root).2]

/-- **The statement embedding**: the eight public words `J < 8` the circuit's public rows hold (`finish`,
`circuit.rs`; `Circuit.lean`), each a 128-bit word in the low two limbs of `E`: `y` and `root` as their
halves, big-endian (`halves`), then word `4`, the constant one (bit `0` set: the row that pins `1`), and
words `5 … 7`, zero (the rows that pin `0`). The public bits must sum to `Σ_J γ^J · word_J`. -/
def statementWords (stmt : Statement) : List E := stmt.halves ++ [1, 0, 0, 0]

/-! ### Roots as scalars -/

/-- `root_halves` (`transcript.rs`): a root as the two scalars the membership stream carries it as, its
128-bit halves, each a big-endian number (`c1` its first eight bytes, `c0` the next eight): the root's bytes
read as `halves` reads a statement's 32 bytes. -/
def rootHalves (root : Digest) : E × E := halves (Digest.toBytes root)

/-- `halves_root` (`transcript.rs`): the root two scalars stand for, if neither has a top limb
(`TranscriptError::NotARoot` otherwise): half `h`'s bytes are its limb `1`'s eight big-endian bytes, then its
limb `0`'s, and the digest's four words are the 32 bytes read little-endian. -/
def rootOfHalves (s : E × E) : Option Digest :=
  if s.1.limb 2 = 0 ∧ s.2.limb 2 = 0 then
    let b := beBytes (s.1.limb 1).lane ++ beBytes (s.1.limb 0).lane ++ beBytes (s.2.limb 1).lane ++
      beBytes (s.2.limb 0).lane
    some #v[leLane b 0, leLane b 1, leLane b 2, leLane b 3]
  else none

/-! ### The proof and the claims -/

/-- **A commitment as the reduction's proof carries it**: the root's two halves (`rootHalves`), then the
out-of-domain answer, the three scalars the prover sends (`send_root`, then `send(ood)`, `protocol.rs`). -/
structure CommitmentScalars where
  root : E × E
  ood : E

/-- The three scalars, in the order sent. -/
def CommitmentScalars.stream (c : CommitmentScalars) : List E := [c.root.1, c.root.2, c.ood]

/-- **The reduction's proof**: the witness table's commitment, the three parts' (`H`, `Q`, `G`), each as its
three scalars; the four row values `a_j` at `t` and `next`, the wiring polynomial at `t`; then `Q`'s and
`G`'s values at their points. The Rust stream is `witness, h, q, g, values, next, qValue, gValue`, in this
order (`prove`, `protocol.rs`). -/
structure ReductionProof where
  witness : CommitmentScalars
  h : CommitmentScalars
  q : CommitmentScalars
  g : CommitmentScalars
  values : Vector E 4
  next : E
  qValue : E
  gValue : E

/-- The stream of nineteen scalars, in the order sent. -/
def ReductionProof.stream (p : ReductionProof) : List E :=
  p.witness.stream ++ p.h.stream ++ p.q.stream ++ p.g.stream ++ p.values.toList ++
    [p.next, p.qValue, p.gValue]

/-- The proof a stream of exactly nineteen scalars is; `none` for any other length (which the Rust
rejects: `Exhausted`, `Trailing`). -/
def ReductionProof.ofStream : List E → Option ReductionProof
  | [w0, w1, wo, h0, h1, ho, q0, q1, qo, g0, g1, go, a0, a1, a2, a3, n, vq, vg] =>
    some ⟨⟨(w0, w1), wo⟩, ⟨(h0, h1), ho⟩, ⟨(q0, q1), qo⟩, ⟨(g0, g1), go⟩, #v[a0, a1, a2, a3], n, vq,
      vg⟩
  | _ => none

/-- **A claim** (`opening::Claim`): the table's multilinear extension at `point` is `value`. -/
structure Claim where
  point : List E
  value : E
  deriving DecidableEq

/-- **The six claims** (`Claims`, `protocol.rs`): on the witness table `W`, on the circuit's wiring table,
on the quotient table's parts `H`, `Q`, `G` at their points, and on `H` at the fixed point `sumPoint`. -/
structure Claims where
  witness : Claim
  wiring : Claim
  h : Claim
  q : Claim
  g : Claim
  sum : Claim
  deriving DecidableEq

/-- **The four commitments a proof names** (`Commitments`, `protocol.rs`). -/
structure Commitments where
  witness : Commitment
  h : Commitment
  q : Commitment
  g : Commitment
  deriving DecidableEq

/-- What the reduction leaves: the four commitments it names and the six claims. -/
structure Reduced where
  commitments : Commitments
  claims : Claims

/-! ### The claims at given challenges (`protocol.rs`) -/

/-- **`quotient_parts`** (`protocol.rs`): the quotient table `T` has `m + 6` variables (a coefficient, then
a chunk's digit, kind and limb, two bits each) and is committed as three subcubes; for a point `P` of `T`,
each part's point (the free coordinates of `P`) and weight (the `eq` of the fixed ones), so that
`T(P) = w_H H(P_H) + w_Q Q(P_Q) + w_G G(P_G)`: `H` the kind `0` and digit bit `1` zero, `Q` the kind `1`, `G`
the kind `2`, digit bit `1` zero and limb `0`. -/
def quotientParts (point : List E) (m : ℕ) : (List E × E) × (List E × E) × (List E × E) :=
  let low := point.take m
  let at_ (k : ℕ) : E := point.getD (m + k) 0
  let (d0, d1, k0, k1, e0, e1) := (at_ 0, at_ 1, at_ 2, at_ 3, at_ 4, at_ 5)
  ((low ++ [d0, e0, e1], (1 + d1) * (1 + k0) * (1 + k1)),
    (low ++ [d0, d1, e0, e1], k0 * (1 + k1)),
    (low ++ [d0], (1 + d1) * (1 + k0) * k1 * (1 + e0) * (1 + e1)))

/-- **The claims of a proof at the challenges** `α, β, γ, t, ρ`, the values `a`, `next` and the parts'
values `qValue`, `gValue`, or `none` if a denominator vanishes (`VerifyError::Degenerate`). Line by line
`reduce` after its transcript reads. -/
def claimsAt (logRows : ℕ) (stmt : Statement) (α β γ t ρ : E) (a : Vector E 4) (next qValue gValue : E) :
    Option Claims :=
  let m := cellVars logRows
  -- `w_k(t)`, `k ≤ m + 1`: up to the two digits past the cells.
  let w : List E := (List.range (m + 1)).foldl (fun ws _ ↦ ws ++ [ws.getLastD t * ws.getLastD t +
    ws.getLastD t]) [t]
  let wAt (k : ℕ) : E := w.getD k 0
  -- The four cells of the row of `t`, and its gate `V + X + C + Y·C`.
  let theta := betaAt 1
  let cell (shift : K) (second : Bool) : E :=
    let first := t + ofK shift
    let second := if second then wAt 1 + 1 else wAt 1
    a[0] + first * a[1] + second * (a[2] + first * a[3])
  let x := cell 0 false
  let y := cell 1 false
  let c := cell theta true
  let v := cell (theta + 1) true
  let gate := v + x + c + y * c
  -- The public weight at `t`, and what the weighted public bits must sum to.
  let b := coordinates region
  let gamma2 := γ * γ
  let gammas : List E := [γ, gamma2, gamma2 * gamma2]
  let outside := (List.range' region (m - region)).foldl (fun acc k ↦ acc * (1 + wAt k)) 1
  let publicWeight := (List.range region).foldl
    (fun acc k ↦
      let coordinate := (List.range' (k + 1) (region - (k + 1))).foldl
        (fun s j ↦ s + ofK (b.getD (j - k) 0) * wAt j) (wAt k)
      let slope := match coordinateWeight k with
        | some weight => 1 + weight
        | none => 1 + gammas.getD (k - 8) 0
      acc * (1 + coordinate * slope))
    outside
  -- `Σ_J γ^J · word_J` by Horner's rule; the Rust writes it `s₀ + γ s₁ + γ²(s₂ + γ s₃) + γ⁴`, the same value.
  let target := (statementWords stmt).foldr (fun word acc ↦ word + γ * acc) 0
  -- The rows' polynomial at `t`, the copy identity's denominator.
  let tau := rowVanishing m
  let rows := (List.range (m - 1)).foldl (fun acc k ↦ acc + ofK (tau.getD k 0) * wAt k) 0
  let d := α + x + β * t
  let dNext := α + x + β * next
  let product := d * dNext
  let copies := d + dNext + publicWeight * x * product
  -- Every `1 + w_k`, the copy identity's denominator, the rows' polynomial, the product and `1 + ρ`, inverted.
  let denominators := w.map (1 + ·) ++ [product + wAt m, rows, product, 1 + ρ]
  if denominators.any (· = 0) then none
  else
    let inv (k : ℕ) : E := (denominators.getD k 1)⁻¹
    let u : List E := (List.range (m + 2)).map fun k ↦ wAt k * inv k
    let copyInverse := inv (m + 2)
    let rowsInverse := inv (m + 3)
    let productInverse := inv (m + 4)
    let rhoInverse := inv (m + 5)
    let middle := (List.range' 3 (m - 3)).foldl (fun acc k ↦ acc * inv k) (inv 2)
    let wiringScale := middle * inv 0 * inv 1
    let quotientScale := wiringScale * inv m * inv (m + 1)
    let rho2 := ρ * ρ
    let opened := (1 + rho2) * (a[0] + ρ * (a[0] + a[1])) + rho2 * (a[2] + ρ * (a[2] + a[3]))
    let identities := (1 + ρ) * copies * rows + ρ * product * gate
    -- The quotient table's claim, through its parts: `H`'s value from `T(P) = w_H H + w_Q Q + w_G G`, with
    -- `w_H⁻¹ = (1 + w_(m+1)) (product + w_m) / (product (1 + ρ))`.
    let quotientPoint := u ++ [wAt m * copyInverse, ρ, extension.1.1, extension.1.2]
    let quotientValue := extension.2 * quotientScale * copyInverse * rowsInverse * identities
    let ((hPoint, _), (qPoint, qWeight), (gPoint, gWeight)) := quotientParts quotientPoint m
    let hInverse := (1 + wAt (m + 1)) * (product + wAt m) * productInverse * rhoInverse
    let hValue := (quotientValue + qWeight * qValue + gWeight * gValue) * hInverse
    some
      { witness := ⟨[ρ, rho2] ++ (u.drop 2).take (m - 1), opened * middle * inv m⟩
        wiring := ⟨u.take m, next * wiringScale⟩
        h := ⟨hPoint, hValue⟩
        q := ⟨qPoint, qValue⟩
        g := ⟨gPoint, gValue⟩
        sum := ⟨sumPoint logRows, extension.2 * target⟩ }

/-! ### The reduction's verifier, over a permutation -/

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- Read a commitment: its three scalars absorbed (`next_root`, then `next`); the commitment, or `none` if
the root's halves have a top limb (`TranscriptError::NotARoot`). -/
def readCommitment (c : Chain) (s : CommitmentScalars) : Option (Commitment × Chain) :=
  (rootOfHalves s.root).map fun r ↦ (⟨r, s.ood⟩, ((c.absorb s.root.1).absorb s.root.2).absorb s.ood)

/-- **The reduction's verifier** over the permutation `F` (`verify` and `reduce`, `protocol.rs`), on the
circuit committed as `index`: read the witness table's commitment (root, out-of-domain answer), draw
`α, β, γ`; read `H`'s, `Q`'s and `G`'s commitments, draw `t`; read the four values and `next`, draw `ρ`; read
`Q`'s and `G`'s values (absorbed, no challenge follows them); then the claims. `none` on a size the
commitments do not take (`Shape`), a root whose halves have a top limb (`NotARoot`, at once, as the Rust
reads it) or a vanishing denominator (`Degenerate`). -/
def reduceWith (logRows : ℕ) (index : Commitment) (stmt : Statement) (p : ReductionProof) :
    m (Option Reduced) := do
  if ¬ Supported logRows then return none
  let c ← Chain.startWith F (label index stmt)
  let some (witness, c) := readCommitment c p.witness | return none
  let (α, c) ← c.squeezeWith F
  let (β, c) ← c.squeezeWith F
  let (γ, c) ← c.squeezeWith F
  let some (h, c) := readCommitment c p.h | return none
  let some (q, c) := readCommitment c p.q | return none
  let some (g, c) := readCommitment c p.g | return none
  let (t, c) ← c.squeezeWith F
  let c := (p.values.toList.foldl Chain.absorb c).absorb p.next
  let (ρ, _) ← c.squeezeWith F
  return (claimsAt logRows stmt α β γ t ρ p.values p.next p.qValue p.gValue).map
    fun claims ↦ ⟨⟨witness, h, q, g⟩, claims⟩

end With

end PcsQuotient

end
