-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Transcribed from `crates/membership/quotient/src/protocol.rs` (`reduce`, `verify`, `label`, `pins`,
-- `row_values`, `witness_conic`, `witness_weights`, `copy_point`, `extension`, `table_slot`) and
-- `crates/membership/quotient/src/circuit.rs` (`PUBLIC_ROWS`, `anchor_cell`, `anchor_values`, `THREE`), adapted
-- from leanVM's `flock::quotient` (branch PCS-openings-aggregation, commit 651453c6). Fields and Keccak-256 are
-- leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0).
module

public import PcsQuotient.Relation
public import PcsQuotient.Domain
public import PcsQuotient.Transcript

/-!
# The reduction: two commitments and six field elements to three claims

The verifier of the reduction (`reduce` and `verify`, `protocol.rs`; `docs/membership/PROTOCOL.md`): from the
statement and the reduction's proof (two commitments, each a root and its out-of-domain answer, and four
elements of `E`), the two commitments it names and **three claims**, each a PCS claim (a plain multilinear
evaluation at one point) on a committed table: on the witness table `W`, on the circuit's wiring table, and on
the quotient table `T` (`Claims`). It rejects only a size the commitments do not take (`Supported`: `2^13` to
`2^22` rows), a malformed root (halves with a top limb) or a challenge at which a denominator vanishes; the
claims carry the rest, and the openings (`PcsOpening.lean`) check them.

**The protocol.** The circuit has `n = 2^m` cells, `m = logRows + 2`, cell `i` at the point `B(i)` of the
Cantor basis (`Domain.lean`), four a row (`X, Y, C, V`), its gate `V = Y + C + X·C`. The prover commits the
witness table `W` (the cells' polynomial `w` in the novel basis, `deg w < n`), receives `α, β, μ`, commits the
quotient table `T` (the quotient `q` and `x h`, `h` the copy argument's sum polynomial, both read through
`ζ = Z x` past their first `n` coefficients: `table_slot`), receives `t`, and sends the three values the gate
reads at `t` (`X`, `C`, `V + Y`: `row_values`) and `next`, the wiring polynomial at `t`; `ρ` places the
witness claim on the row polynomials' conic (`witness_conic`). With `d = α + w + β x`, `d' = α + w + β σ` and
`g = gate / Z_R + (w + v) / Z_P` (`Z_R` vanishing on the rows' first cells, `Z_P` on the eleven pinned cells,
`v` the public values' interpolant on them), the copy claim reads `(1 + κ) q + κ (x h)` at `t`,
`κ = d d' / (ζ + d d')`, which the identity `x Z q + d d' (x h) = x (d + d' + μ Z g)` sets to
`t (d + d' + μ Z g) / (ζ + d d')`. No table value is sent.

**Transcription.** The Rust is generic in its scalar (so that the same code is the EVM contract); here the
scalar is `E`. Two forms differ without changing a value: the proof is a structure (`ReductionProof`, ten
scalars in the stream's order) rather than a stream (a stream of another length, which the Rust rejects as
exhausted or trailing, is no `ReductionProof`); and the inverses are taken one by one (`x⁻¹`) where the Rust
inverts one product (by the norm to `K`, `protocol.rs`) and unwinds it, after the same check that no
denominator is zero.
-/

@[expose] public section

namespace PcsQuotient

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open PcsQuotient.Domain PcsQuotient.Transcript

/-! ### Constants -/

/-- `cell_vars` (`protocol.rs`): the cells' variables, `m = logRows + 2` (four cells a row). -/
def cellVars (logRows : ℕ) : ℕ := logRows + 2

/-- `LOG_ROWS` (`circuit.rs`): the membership circuit has `2^22` rows, so `2^24` cells. -/
def logRows : ℕ := 22

/-- `MIN_LOG_ROWS` (`protocol.rs`): below `2^13` rows the witness and wiring tables (`m` variables) are smaller
than the `2^15` words WHIR commits. -/
def minLogRows : ℕ := 13

/-- `MAX_LOG_ROWS` (`protocol.rs`): above `2^22` rows the quotient table (`m + 4` variables) exceeds WHIR's
`2^28` words. -/
def maxLogRows : ℕ := 22

/-- `supported` (`protocol.rs`): the sizes the commitments take; the verifier rejects any other
(`VerifyError::Shape`). -/
def Supported (logRows : ℕ) : Prop := minLogRows ≤ logRows ∧ logRows ≤ maxLogRows

instance (logRows : ℕ) : Decidable (Supported logRows) := inferInstanceAs (Decidable (_ ∧ _))

/-- `PUBLIC_WORDS` (`circuit.rs`): the public `K`-words. -/
def publicWords : ℕ := 8

/-- `PUBLIC_ROWS` (`circuit.rs`): the anchor rows, one a public word, then one a constant (`0`, `1`, `3`). -/
def publicRows : ℕ := publicWords + 3

/-- `THREE` (`circuit.rs`): the constant the packing rows read as `X` (`V = Y + C + 3 C = Y + 2 C`), the
word `3` of `K` (`x + 1`). -/
def three : K := K.ofLane 3

/-- `anchor_cell` (`circuit.rs`): the cell the verifier pins for anchor `k`, its `C` cell. -/
def anchorCell (k : ℕ) : ℕ := 4 * k + 2

/-- `anchor_values` (`circuit.rs`): the values of the anchors' cells, the public words, then the constants
`0`, `1`, `3`. -/
def anchorValues (words : List K) (k : ℕ) : K :=
  if k < publicWords then words.getD k 0 else if k = 8 then 0 else if k = 9 then 1 else three

/-- `F192::Y`: the element `y`, limb `1`. -/
def ey : E := E.ofLimbs 0 1 0

/-- `extension` (`protocol.rs`): the two coordinates `(y/(1+y), y²/(1+y²))` of the extension
over the base field, and the scale `1/((1+y)(1+y²))` of the weights `(1, y, y², y³)` they give. -/
def extension : (E × E) × E :=
  let d0 := 1 + ey
  let d1 := 1 + ey * ey
  ((ey * d0⁻¹, ey * ey * d1⁻¹), (d0 * d1)⁻¹)

/-- `table_slot` (`protocol.rs`): the quotient table's word `i + n (digit + 2 limb + 8 kind)` is coefficient `i`
of digit `digit` of limb `limb` of kind `kind` (`0`: the quotient `q`; `1`: `x h`); this is the first word of
the slot `(kind, limb)`, digit `0`. -/
def tableSlot (kind limb n : ℕ) : ℕ := 2 * n * (limb + 4 * kind)

/-! ### The commitments, the roots -/

/-- **A commitment** as the claims name it (`opening::Commitment`): the Merkle root of the table's WHIR
commitment and its out-of-domain answer, the table's multilinear at the point derived from the root
(`PcsOpening.lean`'s `oodPointWith`). -/
structure Commitment where
  root : Digest
  ood : E
  deriving DecidableEq

/-- **`element_bytes`** (`pcs_claim`): an element of `E` as `24` bytes, its limbs `c2, c1, c0`, each
big-endian. -/
def elementBytes (x : E) : List UInt8 :=
  beBytes (x.limb 2).lane ++ beBytes (x.limb 1).lane ++ beBytes (x.limb 0).lane

/-- `NAME` (`protocol.rs`): the protocol's name, the label's first sixteen bytes. -/
def protocolName : List UInt8 := "pcs-quotient-kc3".toUTF8.toList

/-- `label` (`protocol.rs`): the transcript's seed, the protocol's name, the circuit's commitment (its root, then
its out-of-domain answer as `element_bytes`) and the statement (`136` bytes). -/
def label (index : Commitment) (stmt : Statement) : List UInt8 :=
  protocolName ++ digestBytes index.root ++ elementBytes index.ood ++ stmt.y.toList ++ stmt.root.toList

/-- `halves` (`statement.rs` before the words): a 32-byte value as two elements of `E`, sixteen bytes each read
as a big-endian number in limbs `0` (low) and `1` (high). -/
def halves (b : Bytes32) : E × E :=
  let half (h : ℕ) : E :=
    E.ofLimbs (K.ofLane (beWord b.toList (16 * h + 8))) (K.ofLane (beWord b.toList (16 * h))) 0
  (half 0, half 1)

/-- `words` (`statement.rs`): a 32-byte value as four `K`-words, eight bytes each read as a big-endian number. -/
def bytesWords (b : Bytes32) : List K :=
  (List.range 4).map fun k ↦ K.ofLane (beWord b.toList (8 * k))

/-- **The statement's words** (`Statement::words`, `statement.rs`): `y`'s four `K`-words, then `root`'s, the
values the verifier pins the first eight anchors to. -/
def Statement.words (stmt : Statement) : List K := bytesWords stmt.y ++ bytesWords stmt.root

/-- `root_halves` (`transcript.rs`): a root as the two scalars the membership stream carries it as, its
128-bit halves, each a big-endian number (`c1` its first eight bytes, `c0` the next eight). -/
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

/-- **The reduction's proof** (`stream`, `protocol.rs`): the witness table's commitment, the quotient table's,
each as its three scalars; the three values the gate reads at `t` (`X`, `C`, `V + Y`: `row_values`); and
`next`, the wiring polynomial at `t`. -/
structure ReductionProof where
  witness : CommitmentScalars
  table : CommitmentScalars
  values : Vector E 3
  next : E

/-- The stream of ten scalars, in the order sent. -/
def ReductionProof.stream (p : ReductionProof) : List E :=
  p.witness.stream ++ p.table.stream ++ p.values.toList ++ [p.next]

/-- The proof a stream of exactly ten scalars is; `none` for any other length (which the Rust rejects:
`Exhausted`, `Trailing`). -/
def ReductionProof.ofStream : List E → Option ReductionProof
  | [w0, w1, wo, t0, t1, tz, x, c, vy, n] => some ⟨⟨(w0, w1), wo⟩, ⟨(t0, t1), tz⟩, #v[x, c, vy], n⟩
  | _ => none

/-- **A claim** (`opening::Claim`): the table's multilinear extension at `point` is `value`. -/
structure Claim where
  point : List E
  value : E
  deriving DecidableEq

/-- **The three claims** (`Claims`, `protocol.rs`): on the witness table `W`, on the circuit's wiring table, on
the quotient table `T`. -/
structure Claims where
  witness : Claim
  wiring : Claim
  copy : Claim
  deriving DecidableEq

/-- **The two commitments a proof names** (`Commitments`, `protocol.rs`). -/
structure Commitments where
  witness : Commitment
  table : Commitment
  deriving DecidableEq

/-- What the reduction leaves: the two commitments it names and the three claims. -/
structure Reduced where
  commitments : Commitments
  claims : Claims

/-! ### The pieces of `reduce` (`protocol.rs`) -/

/-- `w_k(t)`, `k ≤ count`: `w_0 = t`, `w_{k+1} = w_k² + w_k`. -/
def digitsOf (t : E) (count : ℕ) : List E :=
  (List.range count).foldl (fun ws _ ↦ ws ++ [ws.getLastD t * ws.getLastD t + ws.getLastD t]) [t]

/-- `pins` (`protocol.rs`): the pinned cells' points `p_k = B(anchor_cell k)`, `k < 11`. -/
def pinPoints : List K := (List.range publicRows).map fun k ↦ point (anchorCell k)

/-- `pins` (`protocol.rs`): the pins' Lagrange weights `λ_k = 1 / Π_(j ≠ k) (p_k + p_j)`, so that the
interpolant of values `v_k` on them is `Z_P(x) Σ_k v_k λ_k / (x + p_k)`. -/
def pinWeights : List K :=
  (List.range publicRows).map fun k ↦
    ((List.range publicRows).foldl
      (fun acc j ↦ if j = k then acc else acc * (pinPoints.getD k 0 + pinPoints.getD j 0)) 1)⁻¹

/-- `row_values` (`protocol.rs`): from the row polynomials' values `a` at `t` (`w = a_0 + x a_1 + w_1 (a_2 + x
a_3)`) and `ω = w_1(t)`, the cells `(X, Y, C, V)` of the row of `t` at `t`, `t + 1`, `t + θ`, `t + θ + 1`
(`θ = β_1`), and the three values the verifier reads: `X`, `C`, `V + Y`. -/
def rowValues (a : Vector E 4) (t ω : E) : Vector E 3 :=
  let θ := ofK (betaAt 1)
  let cell (first second : E) : E := a[0] + first * a[1] + second * (a[2] + first * a[3])
  let x := cell t ω
  let y := cell (t + 1) ω
  let c := cell (t + θ) (ω + 1)
  let v := cell (t + θ + 1) (ω + 1)
  #v[x, c, v + y]

/-- `witness_conic` (`protocol.rs`): the witness claim's row point is `(z_0, z_1) = (ρ, a / (a + b))`,
`a = (t + θ ω)(1 + ρ) + ρ`, `b = θ (1 + ρ)`, on the row polynomials' conic; this is `(a, b)`. -/
def witnessConic (t ω ρ : E) : E × E :=
  let θ := ofK (betaAt 1)
  ((t + ω * θ) * (1 + ρ) + ρ, θ * (1 + ρ))

/-- `witness_weights` (`protocol.rs`): the weights `λ` with `e = λ_0 X + λ_1 C + λ_2 (V + Y)` as linear forms
of the row polynomials' values, `e = (1 + z_0, z_0) ⊗ (1 + z_1, z_1)` the row point's weights at `z_0 = ρ`,
`z_1`: the witness claim's value is `λ · (X, C, V + Y)` times the normalisation. -/
def witnessWeights (t ω ρ z1 : E) : Vector E 3 :=
  let θ := ofK (betaAt 1)
  let e00 := (1 + ρ) * (1 + z1)
  let e01 := (1 + ρ) * z1
  let e11 := ρ * z1
  let k3 := t + θ * ω + θ + 1
  let lambda1 := e11 + t * ω * e00 + k3 * (e01 + ω * e00)
  #v[e00 + lambda1, lambda1, e01 + ω * e00 + lambda1]

/-- `copy_point` (`protocol.rs`): the quotient table's claim point, `t`'s coordinates `u` (`m + 1`: the
coefficient's `m`, then the digit's), the extension's two, then `κ`, which weighs `x h` against `q`. -/
def copyPoint (u : List E) (κ : E) : List E := u ++ [extension.1.1, extension.1.2, κ]

/-! ### The claims at given challenges (`reduce`, `protocol.rs`) -/

/-- **The claims of a proof at the challenges** `α, β, μ, t, ρ`, the three values `v = (X, C, V + Y)` and
`next`, or `none` if a denominator vanishes (`VerifyError::Degenerate`). Line by line `reduce` after its
transcript reads. -/
def claimsAt (logRows : ℕ) (stmt : Statement) (α β μ t ρ : E) (v : Vector E 3) (next : E) :
    Option Claims :=
  let m := cellVars logRows
  -- `w_k(t)`, `k ≤ m`: up to the digit past the cells, `w_m = Z`.
  let w := digitsOf t m
  let wAt (k : ℕ) : E := w.getD k 0
  let x := v[0]
  let c := v[1]
  let vy := v[2]
  let gate := vy + c + x * c
  -- The rows' polynomial at `t`.
  let tau := rowVanishing m
  let rows := (List.range (m - 1)).foldl (fun acc k ↦ acc + ofK (tau.getD k 0) * wAt k) 0
  let d := α + x + β * t
  let dNext := α + x + β * next
  let product := d * dNext
  let z := wAt m
  let zeta := z * t
  let (conicA, conicB) := witnessConic t (wAt 1) ρ
  -- One inversion: every `1 + w_k` below the digit, `1 + ζ`, `ζ + d d'`, the rows' polynomial, every
  -- `t + p_k`, and `a + b`.
  let denominators : List E := (List.range m).map (fun k ↦ 1 + wAt k) ++ [1 + zeta, zeta + product, rows] ++
    pinPoints.map (fun p ↦ t + ofK p) ++ [conicA + conicB]
  if denominators.any (· = 0) then none
  else
    let inv (k : ℕ) : E := (denominators.getD k 1)⁻¹
    let u : List E := (List.range m).map (fun k ↦ wAt k * inv k) ++ [zeta * inv m]
    let copyInverse := inv (m + 1)
    let rowsInverse := inv (m + 2)
    let pinInverse (k : ℕ) : E := inv (m + 3 + k)
    let conicInverse := inv (m + 3 + publicRows)
    let middle := (List.range' 3 (m - 3)).foldl (fun acc k ↦ acc * inv k) (inv 2)
    let wiringScale := middle * inv 0 * inv 1
    let tableScale := wiringScale * inv m
    -- `g(t) = gate / Z_R + (w + v) / Z_P`, `v / Z_P = Σ_k v_k λ_k / (t + p_k)`: the words, then the constants
    -- `0` (no term), `1` and `3`.
    let pubWords := stmt.words
    let pinned := (List.range publicRows).foldl
      (fun acc k ↦
        if k < publicWords then acc + ofK (pubWords.getD k 0) * ofK (pinWeights.getD k 0) * pinInverse k
        else if anchorValues pubWords k = 0 then acc
        else acc + ofK (pinWeights.getD k 0 * anchorValues pubWords k) * pinInverse k)
      (x * (List.range publicRows).foldl (fun acc k ↦ acc * pinInverse k) 1)
    let g := gate * rowsInverse + pinned
    -- The identity's combination: `(1 + κ) q + κ (x h)`, `κ = d d' / (ζ + d d')`, is `t (d + d' + μ Z g) / (ζ +
    -- d d')`.
    let kappa := product * copyInverse
    let copyValue := extension.2 * tableScale * t * (d + dNext + μ * z * g) * copyInverse
    -- The witness table's claim on the row's conic.
    let z1 := conicA * conicInverse
    let lam := witnessWeights t (wAt 1) ρ z1
    let opened := lam[0] * x + lam[1] * c + lam[2] * vy
    some
      { witness := ⟨[ρ, z1] ++ (u.drop 2).take (m - 2), opened * middle⟩
        wiring := ⟨u.take m, next * wiringScale⟩
        copy := ⟨copyPoint u kappa, copyValue⟩ }

/-! ### The reduction's verifier, over a permutation -/

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- Read a commitment: its three scalars absorbed (`next_root`, then `next`); the commitment, or `none` if
the root's halves have a top limb (`TranscriptError::NotARoot`). -/
def readCommitment (c : Chain) (s : CommitmentScalars) : Option (Commitment × Chain) :=
  (rootOfHalves s.root).map fun r ↦ (⟨r, s.ood⟩, ((c.absorb s.root.1).absorb s.root.2).absorb s.ood)

/-- **The reduction's verifier** over the permutation `F` (`verify` and `reduce`, `protocol.rs`), on the
circuit committed as `index`: read the witness table's commitment (root, out-of-domain answer), draw
`α, β, μ`; read the quotient table's commitment, draw `t`; read the three values and `next`, draw `ρ`; then the
claims. `none` on a size the commitments do not take (`Shape`), a root whose halves have a top limb
(`NotARoot`, at once, as the Rust reads it) or a vanishing denominator (`Degenerate`). -/
def reduceWith (logRows : ℕ) (index : Commitment) (stmt : Statement) (p : ReductionProof) :
    m (Option Reduced) := do
  if ¬ Supported logRows then return none
  let c ← Chain.startWith F (label index stmt)
  let some (witness, c) := readCommitment c p.witness | return none
  let (α, c) ← c.squeezeWith F
  let (β, c) ← c.squeezeWith F
  let (μ, c) ← c.squeezeWith F
  let some (table, c) := readCommitment c p.table | return none
  let (t, c) ← c.squeezeWith F
  let c := (p.values.toList.foldl Chain.absorb c).absorb p.next
  let (ρ, _) ← c.squeezeWith F
  return (claimsAt logRows stmt α β μ t ρ p.values p.next).map fun claims ↦ ⟨⟨witness, table⟩, claims⟩

end With

end PcsQuotient

end
