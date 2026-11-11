-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Transcribed from `crates/membership/quotient/src/protocol.rs` (`prove_with_randomness`, `open`,
-- `public_weight`, `Randomness`) and `crates/pcs_claim/src/lib.rs` (`commit_words`, `open_words`). The WHIR
-- opening's prover is leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0:
-- `Statement/Prover/Whir.lean`'s `levelsA`, `roundA`, `stackTableA`, `eqKernelA`, run by
-- `Statement/Prover/Run.lean`'s `runFrom`); `pcsOpeningScript` is its `openingFast` with the PCS opening's weight
-- table.
module

public import PcsQuotient.LayoutsProver

/-!
# The honest prover

The prover `Completeness` names (`Security.lean`), an executable program over a permutation `F` in any
monad, Keccak-256 the sponge over `F`: `proveWith F fuel circuit stmt cells coins`, the Rust's `prove` then
`open` (`protocol.rs`) step by step, with its randomness (`Coins`: `Randomness`) given.

1. **The random rows**: the `X` and `V` cells of each random row take its random value.
2. **The witness table** `W` (`m + 1` variables): the cells' polynomial in the novel basis
   (`Domain.coefficients`), then its masks, sixteen entries (entry `4i + j` the coefficient `i` of row
   polynomial `j`); committed (root, out-of-domain answer), sent; `α, β, γ` drawn.
3. **The sum's polynomial** `h`: at cell `i`, `1/(α + w_i + β B(i)) + 1/(α + w_i + β B(σ(i)))`, plus
   the public weight times the cell on the public region; in the novel basis; its limbs blinded by
   `X_{2^m}·b` (coefficients `2^m … 2^m + 7`).
4. **The quotients** on the coset `β_{m+2} + span(β₀ … β_{m+1})`, four times the cells: the copy
   identity's quotient `q = ((h + public)·d·d' + d + d')/Z_cells` and the gate's
   `(V + X + C + Y·C)/Z_rows`, back to the novel basis; the quotient table's three parts `H` (`h`'s limbs
   with their blinding), `Q` (`q`'s limbs), `G` (the gate's quotient's first `2^(m+1)` coefficients),
   each committed and sent; `t` drawn.
5. **The values**: the four row polynomials (with their masks) and the wiring polynomial at `t`; `ρ`
   drawn; then `Q`'s and `G`'s values at the points the verifier's reduction computes.
6. **The openings** (`proveClaimWith`): leanVM's WHIR prover (`pcsOpeningScript`) on each claim's table,
   run against the verifier's own program (mumbai's `runFrom`: the challenges squeezed from the sponge, each
   proof of work the first passing nonce below `fuel`).

The prover branches on no permutation answer other than through the challenges, and its only search is the
nonce search (mumbai's `runFrom`). It does not check that the gate's quotient fits `G` (the Rust's `fits`,
true for a witness); the inverses are taken one by one (`x⁻¹`, `0⁻¹ = 0`) where the Rust batches them, which
differs only at a challenge where a denominator vanishes.
-/

@[expose] public section

namespace PcsQuotient

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open PcsQuotient.Domain PcsQuotient.Transcript

/-! ### The prover's randomness (`Randomness`, `protocol.rs`) -/

/-- `H_BLIND` (`protocol.rs`): the coefficients past `2^m` that blind each limb of the sum's polynomial. -/
def hBlind : ℕ := 8

/-- The witness table's masks: three coefficients of `K` for each of the four row polynomials. -/
abbrev Masks : Type := Fin 4 → Fin 3 → K

/-- **The prover's randomness** (`Randomness`, `protocol.rs`): the masks; the random rows' values, in the
order of `Circuit.randomRows`; and the blinding of the sum's polynomial, `blind e i` coefficient `2^m + i`
of limb `e`. The deployed prover derives them from a fresh 32-byte seed by a Keccak-256 KDF
(`Randomness::derive`); the statement's prover takes them uniform (`Security.lean`'s `sampleCoins`). -/
structure Coins where
  masks : Masks
  rows : Fin randomRows → K
  blind : Fin 3 → Fin hBlind → K

/-- The sixteen mask entries (`prove`, `protocol.rs`): entry `4i + j` is coefficient `i` of row
polynomial `j`, `i < 3`; the last four are zero. -/
def maskEntries (masks : Masks) : Array K :=
  Array.ofFn (n := 16) fun e ↦
    if e.val / 4 < 3 then masks (Fin.ofNat 4 (e.val % 4)) (Fin.ofNat 3 (e.val / 4)) else 0

/-- **The random rows filled** (`prove`, `protocol.rs`): the `X` and `V` cells of the `k`-th random row
(`Circuit.randomRows`) take `rows k`. -/
def randomizeCells (circuit : Circuit) (cells : Array K) (rows : Fin randomRows → K) : Array K :=
  (circuit.randomRows.zipIdx).foldl (fun cs (r, k) ↦
    let v := if h : k < randomRows then rows ⟨k, h⟩ else 0
    (cs.setIfInBounds (4 * r) v).setIfInBounds (4 * r + 3) v) cells

/-- `public_weight` (`protocol.rs`): the weight of cell `i` of the public region, `γ^J` times its
bit's weight, `J = ⌊i / 2^8⌋` the word, or zero off the `X` and `Y` cells. -/
def publicCellWeight (i : ℕ) (γ : E) : E :=
  if i &&& 2 ≠ 0 then 0
  else bitWeight ((i &&& 1) ||| (((i >>> 2) &&& 63) <<< 1)) * γ ^ (i >>> 8)

/-! ### The PCS opening -/

/-- **The weight table of an opening** in WHIR's variable order (`open_words`, `pcs_claim`): entry `i` is the
table position `⌊i / 64⌋ + 2^(n−6)·(i mod 64)`, where the weight is `eq(z, ·) + λ·eq(point, ·)` (the two
equality kernels, `eqKernelA`, coordinate `0` the lowest bit). -/
def pcsWeightTable (n : ℕ) (z point : List E) (lam : E) : Array E :=
  let ez := eqKernelA z
  let ep := eqKernelA point
  Array.ofFn (n := 2 ^ n) fun i ↦
    let pos := i.val / 2 ^ laneFold + 2 ^ (n - laneFold) * (i.val % 2 ^ laneFold)
    ez.getD pos 0 + lam * ep.getD pos 0

/-- **The honest WHIR opening** of a claim on the table `table` (`n` variables), its out-of-domain point
`z`, as a script of the prover's moves (mumbai's `openingFast` with the PCS weight table): receive `λ`, then
run the levels from the batched claim `ood + λ·value` with the table and the weight table. -/
def pcsOpeningScript (n : ℕ) (table : Array K) (z : List E) (c : Commitment) (claim : Claim) :
    Script Unit := do
  let lam ← Script.sampleE
  match Whir.ladder n logInvRate with
  | none => return ()
  | some config =>
    let f₀ := stackTableA n table
    let W₀ := pcsWeightTable n z claim.point lam
    let target := dot (powers lam 2) [c.ood, claim.value]
    let quad ← roundA target W₀ f₀
    levelsA n 0 config ⟨quad, [], []⟩ W₀ f₀

/-- `w_k(t)` for `k ≤ count`. -/
def digitsOf (t : E) (count : ℕ) : List E :=
  (List.range count).foldl (fun ws _ ↦ ws ++ [ws.getLastD t * ws.getLastD t + ws.getLastD t]) [t]

/-! ### The prover's tables, as functions of the witness, the randomness and the challenges -/

/-- **The cells with the random rows filled**, the witness table's coefficients and its masks. -/
def witnessParts (circuit : Circuit) (cells₀ : Array K) (coins : Coins) : Array K × Array K × Array K :=
  let mv := cellVars circuit.logRows
  let cells := randomizeCells circuit cells₀ coins.rows
  (cells, coefficients mv 0 cells, maskEntries coins.masks)

/-- **The witness table** `W` (`m + 1` variables): the cells' coefficients, then the masks. -/
def witnessTable (circuit : Circuit) (cells₀ : Array K) (coins : Coins) : Array K :=
  let n := 2 ^ cellVars circuit.logRows
  let (_, wHat, mask) := witnessParts circuit cells₀ coins
  Array.ofFn (n := 2 * n) fun i ↦ if i.val < n then wHat.getD i.val 0 else mask.getD (i.val - n) 0

/-- **The quotient table's three parts** `H`, `Q`, `G` at the challenges `α, β, γ`. -/
def quotientTables (circuit : Circuit) (cells₀ : Array K) (coins : Coins) (α β γ : E) :
    Array K × Array K × Array K :=
  let mv := cellVars circuit.logRows
  let n := 2 ^ mv
  let big := 4 * n
  let block := 2 ^ region
  let sigmaHat := circuit.wiringTable
  let (cells, wHat, mask) := witnessParts circuit cells₀ coins
  -- 3. The sum's polynomial on the cells, then its coefficients and their blinding.
  let h : Array E := Array.ofFn (n := n) fun i ↦
    let common := α + ofK (cells.getD i.val 0)
    (common + β * ofK (point i.val))⁻¹ + (common + β * ofK (point (circuit.sigma.getD i.val 0)))⁻¹ +
      if i.val < block then publicCellWeight i.val γ * ofK (cells.getD i.val 0) else 0
  let hHat := coefficients mv 0 h
  let blindAt (i : ℕ) : E :=
    if hi : i < hBlind then E.ofLimbs (coins.blind 0 ⟨i, hi⟩) (coins.blind 1 ⟨i, hi⟩) (coins.blind 2 ⟨i, hi⟩)
    else 0
  -- 4. Both quotients, on a coset four times the cells.
  let offset := betaAt (mv + 2)
  let offsets := chain offset (mv + 1)
  let wValues : Array K := values (mv + 2) offset (Array.ofFn (n := big) fun i ↦
    if i.val < n then wHat.getD i.val 0 else mask.getD (i.val - n) 0)
  let sigmaValues : Array K := values (mv + 2) offset (Array.ofFn (n := big) fun i ↦
    sigmaHat.getD i.val 0)
  let q₀ : Array E := values (mv + 2) offset (Array.ofFn (n := big) fun i ↦
    if i.val < n then hHat.getD i.val 0 else blindAt (i.val - n))
  let b := coordinates region
  let tau := rowVanishing mv
  let rowPoly (x : K) : K := ((chain x (mv - 1)).zip tau).foldl (fun acc (w, t) ↦ acc + t * w) 0
  let gammas : List E := [γ, γ * γ, (γ * γ) * (γ * γ)]
  -- Per block of `2^11` coset points: the public weights, `1/Z_cells`, and `1/Z_rows` by role.
  let blocks : Array (Array E × K × Array K) := Array.ofFn (n := big / block) fun hi ↦
    let base := hi.val * block
    let wAt (k : ℕ) : K := offsets.getD k 0 + point (base >>> k)
    let indicator := (List.range' region (mv - region)).foldl (fun acc k ↦ acc * (1 + wAt k)) 1
    let weights : Array E :=
      if indicator = 0 then #[ofK indicator]
      else (List.range region).foldl
        (fun ws k ↦
          let shift := (List.range' k (region - k)).foldl
            (fun acc j ↦ acc + b.getD (j - k) 0 * wAt j) 0
          let slope : E := 1 + (coordinateWeight k).getD (gammas.getD (k - 8) 0)
          let low := 1 + slope * ofK shift
          ws.map (· * low) ++ ws.map (· * (low + slope)))
        #[ofK indicator]
    let rowBase := rowPoly (offset + point base)
    (weights, (wAt mv)⁻¹, Array.ofFn (n := 4) fun r ↦ (rowBase + rowPoly (point r.val))⁻¹)
  let qValues : Array E := Array.ofFn (n := big) fun i ↦
    let (weights, cellVanishing, _) := blocks.getD (i.val / block) (#[], 0, #[])
    let w := wValues.getD i.val 0
    let common := α + ofK w
    let d := common + β * ofK (offset + point i.val)
    let dNext := common + β * ofK (sigmaValues.getD i.val 0)
    let pub := if i.val % block < weights.size then weights.getD (i.val % block) 0 * ofK w else 0
    ((q₀.getD i.val 0 + pub) * d * dNext + d + dNext) * ofK cellVanishing
  let qGateValues : Array K := Array.ofFn (n := big) fun i ↦
    let (_, _, rowInv) := blocks.getD (i.val / block) (#[], 0, #[])
    let at_ (j : ℕ) : K := wValues.getD j 0
    let (x, y, cc, v) := (at_ i.val, at_ (i.val ^^^ 1), at_ (i.val ^^^ 2), at_ (i.val ^^^ 3))
    (v + x + cc + y * cc) * rowInv.getD (i.val % 4) 0
  let qHat := coefficients (mv + 2) offset qValues
  let qGateHat := coefficients (mv + 2) offset qGateValues
  -- The quotient table's three parts: `H` (`h`'s limbs, each `2^m` coefficients then its blinding), `Q` (`q`'s
  -- limbs, `4·2^m` coefficients each), `G` (the gate's quotient's first `2^(m+1)` coefficients).
  let hTable : Array K := Array.ofFn (n := 8 * n) fun i ↦
    let (e, j) := (i.val / (2 * n), i.val % (2 * n))
    if 3 ≤ e then 0
    else if j < n then limbOf (hHat.getD j 0) e
    else if hj : j - n < hBlind ∧ e < 3 then coins.blind ⟨e, hj.2⟩ ⟨j - n, hj.1⟩
    else 0
  let qTable : Array K := Array.ofFn (n := 16 * n) fun i ↦
    let (e, j) := (i.val / big, i.val % big)
    if e < 3 then limbOf (qHat.getD j 0) e else 0
  let gTable : Array K := Array.ofFn (n := 2 * n) fun i ↦ qGateHat.getD i.val 0
  (hTable, qTable, gTable)

/-- **The row values** `a_j` (the four row polynomials with their masks) and `next` (the wiring polynomial) at
`t`. -/
def rowValues (circuit : Circuit) (cells₀ : Array K) (coins : Coins) (t : E) : Vector E 4 × E :=
  let mv := cellVars circuit.logRows
  let (_, wHat, mask) := witnessParts circuit cells₀ coins
  let digits := digitsOf t mv
  let a : Vector E 4 := Vector.ofFn fun j ↦
    novelEval wHat j.val 4 ((digits.drop 2).take (mv - 2)) +
      digits.getD mv 0 * novelEval mask j.val 4 ((digits.drop 2).take 2)
  let next := novelEval circuit.wiringTable 0 1 (digits.take mv)
  (a, next)

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **An opening proof** of `claim` on the commitment `c` of the table `table` (its tree `tree`): the root's
two halves sent first (`ProverState::add_root`), then the script run against the verifier's program from the
opening's sponge, with the table's tree as commitment `0`; `none` if a proof of work finds no nonce below
`fuel`. -/
def proveClaimWith (fuel : ℕ) (tree : Tree) (table : Array K) (c : Commitment) (claim : Claim) :
    m (Option Compile.Proof) := do
  let n := claim.point.length
  let (r0, r1) := digestScalars tree.root
  let sp ← pcsSpongeWith F c claim
  let sp ← absorb F sp r0 dsObserve
  let sp ← absorb F sp r1 dsObserve
  let z ← oodPointWith F n c.root
  let program := verifyStackedOpening n logInvRate (pcsStackClaims z c claim)
  let r ← runFrom F fuel program (some (pcsOpeningScript n table z c claim)) sp [tree]
  return r.map fun t ↦ ⟨r0 :: r1 :: t.1, t.2⟩

/-! ### The reduction's prover -/

/-- A commitment as the stream carries it: its root's halves, then its out-of-domain answer. -/
def CommitmentScalars.of (c : Commitment) : CommitmentScalars := ⟨rootHalves c.root, c.ood⟩

/-- Absorb a commitment's three scalars. -/
def Transcript.Chain.absorbCommitment (c : Chain) (s : CommitmentScalars) : Chain :=
  ((c.absorb s.root.1).absorb s.root.2).absorb s.ood

/-- **The PCS operations the prover uses for its secret tables**: commit to a table of `2^μ` words (a handle
for opening it later, and the commitment: root and out-of-domain answer), and open a claim on a committed
table. The honest prover's are `realPcs` (WHIR, `commitmentWith`, `proveClaimWith`); the zero-knowledge
theorem replaces them by an ideal PCS (`Security.lean`, `formal/EndToEnd/ZK`). -/
structure PcsOps (m : Type → Type) (Hd : Type) where
  commit : ℕ → Array K → m (Hd × Commitment)
  openClaim : Hd → Commitment → Claim → m (Option Compile.Proof)

/-- **The real PCS** over `F`: WHIR's commitment (`commitmentWith`) and opening (`proveClaimWith`, `fuel` nonces
per proof of work), the handle the table's tree and words. -/
def realPcs (fuel : ℕ) : PcsOps m (Tree × Array K) where
  commit μ table := do
    let (tree, c) ← commitmentWith F μ table
    return ((tree, table), c)
  openClaim h c claim := proveClaimWith F fuel h.1 h.2 c claim

/-- **The honest prover with PCS operations `pcs`** for its four secret tables (`W`, `H`, `Q`, `G`) over `F`
(`prove_with_randomness` then `open`, `protocol.rs`): the proof of `stmt` from the cells of a witness of
`circuit`, with the randomness `coins`; the circuit's commitment and the wiring claim's opening (public) are the
real WHIR ones, `fuel` nonces per proof of work; `none` if a proof of work or an opening fails or the reduction
rejects its own challenges (the Rust panics). -/
def proveWithPcs {Hd : Type} (pcs : PcsOps m Hd) (fuel : ℕ) (circuit : Circuit) (stmt : Statement)
    (cells₀ : Array K) (coins : Coins) : m (Option Proof) := do
  let mv := cellVars circuit.logRows
  -- The circuit's commitment, public.
  let sigmaHat := circuit.wiringTable
  let (indexTree, index) ← commitmentWith F mv sigmaHat
  let wTable := witnessTable circuit cells₀ coins
  let (wTree, wCom) ← pcs.commit (mv + 1) wTable
  let c ← Chain.startWith F (label index stmt)
  let wS := CommitmentScalars.of wCom
  let c := c.absorbCommitment wS
  let (α, c) ← c.squeezeWith F
  let (β, c) ← c.squeezeWith F
  let (γ, c) ← c.squeezeWith F
  let (hTable, qTable, gTable) := quotientTables circuit cells₀ coins α β γ
  let (hTree, hCom) ← pcs.commit (mv + 3) hTable
  let (qTree, qCom) ← pcs.commit (mv + 4) qTable
  let (gTree, gCom) ← pcs.commit (mv + 1) gTable
  let (hS, qS, gS) := (CommitmentScalars.of hCom, CommitmentScalars.of qCom, CommitmentScalars.of gCom)
  let c := ((c.absorbCommitment hS).absorbCommitment qS).absorbCommitment gS
  let (t, _) ← c.squeezeWith F
  -- The values at `t`, then `Q`'s and `G`'s values at their points (the verifier's, after `ρ`).
  let (a, next) := rowValues circuit cells₀ coins t
  let proof₀ : ReductionProof := ⟨wS, hS, qS, gS, a, next, 0, 0⟩
  let some r₀ ← reduceWith F circuit.logRows index stmt proof₀ | return none
  let proof : ReductionProof :=
    { proof₀ with qValue := tableEval qTable r₀.claims.q.point,
                  gValue := tableEval gTable r₀.claims.g.point }
  -- 6. The claims, and their openings.
  let some r ← reduceWith F circuit.logRows index stmt proof | return none
  let some oW ← pcs.openClaim wTree r.commitments.witness r.claims.witness | return none
  let some oσ ← proveClaimWith F fuel indexTree sigmaHat index r.claims.wiring | return none
  let some oH ← pcs.openClaim hTree r.commitments.h r.claims.h | return none
  let some oQ ← pcs.openClaim qTree r.commitments.q r.claims.q | return none
  let some oG ← pcs.openClaim gTree r.commitments.g r.claims.g | return none
  let some oS ← pcs.openClaim hTree r.commitments.h r.claims.sum | return none
  return some ⟨proof, ⟨oW, oσ, oH, oQ, oG, oS⟩⟩

/-- **The honest prover** over `F` (`prove_with_randomness` then `open`, `protocol.rs`): `proveWithPcs` with the
real PCS. -/
def proveWith (fuel : ℕ) (circuit : Circuit) (stmt : Statement) (cells₀ : Array K) (coins : Coins) :
    m (Option Proof) :=
  proveWithPcs F (realPcs F fuel) fuel circuit stmt cells₀ coins

/-- **The honest prover of the membership statement** over `F`: `proveWith` on the membership circuit's
cells for the secret `w` (`membershipInputs`, `Circuit.cells`; the random rows zero, filled by the prover). -/
def proverWith (fuel : ℕ) (stmt : Statement) (w : Secret) (coins : Coins) : m (Option Proof) :=
  let circuit := membership logRows
  proveWith F fuel circuit stmt (circuit.cells (membershipInputs w)) coins

end With

end PcsQuotient

end
