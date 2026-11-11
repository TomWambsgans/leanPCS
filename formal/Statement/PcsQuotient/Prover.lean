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
`open` (`protocol.rs`), with its randomness (`Coins`: `Randomness`) given.

1. **The random rows**: the `k`-th random row (`Circuit.randomRows`) takes the cells of its shape for the words
   `2k`, `2k + 1` (`RandomShape.cells`, `Circuit::randomize`).
2. **The witness table** `W` (`m` variables): the cells' polynomial `w` in the novel basis
   (`Domain.coefficients`); committed (root, out-of-domain answer), sent; `α, β, μ` drawn.
3. **The sum's polynomial** `h`: at cell `i`, `1/(α + w_i + β B(i)) + 1/(α + w_i + β B(σ(i)))`, in the novel
   basis (`h_low`, degree `< n`), blinded by `Z (b_0 + b_1 X_1 + b_2 X_2)`.
4. **The quotient** `q = (h d d' + d + d') / Z + μ g`, `g = gate / Z_R + (w + v) / Z_P`, first with `b_2 = 0`
   (`q_0`), on the coset `β_{m+2} + span(β_0 … β_{m+1})` of `4 n` points, where it is exact; then
   `b_2 = q_0[n] / (E[n] + E[2n])`, `E = w_1 d d'` (made on the same coset), so that `q = q_0 + b_2 E` has
   `Q_h(0) = q[n] + q[2n] = 0`, `q = q_low + Z Q_h` (`PROTOCOL.md`, "The honest prover"). The Rust makes the same
   coefficients on a coset of `2 n` points with the corrections `E`'s coefficient `2 n` needs; here the coset is
   large enough for `E` itself.
5. **The quotient table** `T` (`m + 4` variables, `table_slot`): kind `0`, limb `e < 3`, the first `n`
   coefficients `A_0` of `q` (low half) and `A_1 = Q_h / x` (`divX`, high half); kind `1`, `B_0 = x h_low`
   (`mulX`, low half) and `B_1 = (b_0, b_1, b_2)` (high half); limb `3` zero. Committed and sent; `t` drawn.
6. **The values**: the three values the gate reads at `t` (`rowValues` of the row polynomials at `t`) and the
   wiring polynomial at `t`; `ρ` drawn.
7. **The openings** (`proveClaimWith`): leanVM's WHIR prover (`pcsOpeningScript`) on each claim's table, run
   against the verifier's own program (mumbai's `runFrom`: the challenges squeezed from the sponge, each proof of
   work the first passing nonce below `fuel`).

The prover branches on no permutation answer other than through the challenges, and its only search is the
nonce search (mumbai's `runFrom`). The inverses are taken one by one (`x⁻¹`, `0⁻¹ = 0`) where the Rust batches
them, which differs only at a challenge where a denominator vanishes.
-/

@[expose] public section

namespace PcsQuotient

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open PcsQuotient.Domain PcsQuotient.Transcript

/-! ### The prover's randomness (`Randomness`, `protocol.rs`) -/

/-- `H_BLIND` (`protocol.rs`): the coefficients past `2^m` that blind each limb of the sum's polynomial,
`b_0, b_1` drawn and `b_2` solved. -/
def hBlind : ℕ := 3

/-- `FREE_BLIND` (`protocol.rs`): the blinding coefficients a proof draws per limb, `b_0, b_1`. -/
def freeBlind : ℕ := hBlind - 1

/-- **The prover's randomness** (`Randomness`, `protocol.rs`): the random rows' words, two a row in the order of
`Circuit.randomRows`; and the blinding of the sum's polynomial, `blind e i` coefficient `2^m + i` of limb `e`,
`i < 2`. The deployed prover derives them from a fresh 32-byte seed by a Keccak-256 KDF (`Randomness::derive`);
the statement's prover takes them uniform (`Security.lean`'s `sampleCoins`). -/
structure Coins where
  rows : Fin randomWords → K
  blind : Fin 3 → Fin freeBlind → K

/-- **The random rows filled** (`Circuit::randomize`, `circuit.rs`): the `k`-th random row
(`Circuit.randomRows`) takes the cells of its shape (`RandomShape.of k`) for the words `2k`, `2k + 1`. -/
def randomizeCells (circuit : Circuit) (cells : Array K) (rows : Fin randomWords → K) : Array K :=
  (circuit.randomRows.zipIdx).foldl (fun cs (r, k) ↦
    let word (j : ℕ) : K := if h : j < randomWords then rows ⟨j, h⟩ else 0
    let (x, y, c, v) := (RandomShape.of k).cells (word (2 * k)) (word (2 * k + 1))
    (((cs.setIfInBounds (4 * r) x).setIfInBounds (4 * r + 1) y).setIfInBounds (4 * r + 2) c).setIfInBounds
      (4 * r + 3) v) cells

/-! ### Products and quotients by `x` in the novel basis (`mul_x`, `div_x`, `protocol.rs`) -/

/-- `low(j)`, the lowest power of two in `j > 0` (`0` at `0`). -/
def lowBit (j : ℕ) : ℕ := j &&& (2 ^ 64 - j) % 2 ^ 64

/-- **`mul_x`** (`protocol.rs`): `x F` in the novel basis, `F` of `2^k` coefficients: the product's first `2^k`
coefficients (coefficient `0` zero, coefficient `j ≥ 1` `f[j − 1] + f[j + low(j) − 1]`; its coefficient `2^k`,
`F`'s top one, dropped). -/
def mulX {M : Type} [Add M] [Zero M] [Inhabited M] (f : Array M) : Array M :=
  Array.ofFn (n := f.size) fun j ↦
    if j.val = 0 then 0 else f.getD (j.val - 1) 0 + f.getD (j.val + lowBit j.val - 1) 0

/-- **`div_x`** (`protocol.rs`): `F` with `G = x F + G(0)` in the novel basis, `G` of `2^k` coefficients:
`f[2^k − 1] = 0` and `f[i] = g[i + 1] + f[i + low(i + 1)]` (`0` past the end), made from the top down. -/
def divX {M : Type} [Add M] [Zero M] [Inhabited M] (g : Array M) : Array M :=
  let len := g.size
  (List.range len).foldr
    (fun i (f : Array M) ↦
      if i + 1 < len then f.set! i (g.getD (i + 1) 0 + f.getD (i + lowBit (i + 1)) 0) else f)
    (Array.replicate len 0)
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

/-! ### The prover's tables, as functions of the witness, the randomness and the challenges -/

/-- **The cells with the random rows filled**, and the witness table: their coefficients in the novel basis
(`m` variables). -/
def witnessParts (circuit : Circuit) (cells₀ : Array K) (coins : Coins) : Array K × Array K :=
  let cells := randomizeCells circuit cells₀ coins.rows
  (cells, coefficients (cellVars circuit.logRows) 0 cells)

/-- **The witness table** `W` (`m` variables): the cells' coefficients. -/
def witnessTable (circuit : Circuit) (cells₀ : Array K) (coins : Coins) : Array K :=
  (witnessParts circuit cells₀ coins).2

/-- The blinding coefficient `b_i` of `h`, as an element of `E` (its three limbs), `i < 2`; zero past them. -/
def blindAt (coins : Coins) (i : ℕ) : E :=
  if hi : i < freeBlind then E.ofLimbs (coins.blind 0 ⟨i, hi⟩) (coins.blind 1 ⟨i, hi⟩) (coins.blind 2 ⟨i, hi⟩)
  else 0

/-- **The quotient's parts** at the challenges `α, β, μ`: `h_low` (`h`'s coefficients on the cells, `n`), the
quotient `q` (`2 n + 1` coefficients) and `b_2`. -/
def quotientParts (circuit : Circuit) (stmt : Statement) (cells₀ : Array K) (coins : Coins) (α β μ : E) :
    Array E × Array E × E :=
  let mv := cellVars circuit.logRows
  let n := 2 ^ mv
  let big := 4 * n
  let (cells, wHat) := witnessParts circuit cells₀ coins
  let sigmaHat := circuit.wiringTable
  -- The sum's polynomial on the cells, then its coefficients.
  let h : Array E := Array.ofFn (n := n) fun i ↦
    let common := α + ofK (cells.getD i.val 0)
    (common + β * ofK (point i.val))⁻¹ + (common + β * ofK (point (circuit.sigma.getD i.val 0)))⁻¹
  let hHat := coefficients mv 0 h
  -- The quotient with `b_2 = 0`, and `E = w_1 d d'`, on the coset of `4 n` points.
  let offset := betaAt (mv + 2)
  let wValues : Array K := values (mv + 2) offset (Array.ofFn (n := big) fun i ↦ wHat.getD i.val 0)
  let sigmaValues : Array K := values (mv + 2) offset (Array.ofFn (n := big) fun i ↦ sigmaHat.getD i.val 0)
  let hValues : Array E := values (mv + 2) offset (Array.ofFn (n := big) fun i ↦
    if i.val < n then hHat.getD i.val 0 else blindAt coins (i.val - n))
  let tau := rowVanishing mv
  let rowPoly (x : K) : K := ((chain x (mv - 1)).zip tau).foldl (fun acc (w, t) ↦ acc + t * w) 0
  let pubWords := stmt.words
  -- `Z_P(x)` and the pins' interpolant `v(x) = Σ_k v_k λ_k Π_(j ≠ k) (x + p_j)`, over `K`.
  let zPins (x : K) : K := pinPoints.foldl (fun acc p ↦ acc * (x + p)) 1
  let pinPoly (x : K) : K := (List.range publicRows).foldl
    (fun acc k ↦ acc + pinWeights.getD k 0 * anchorValues pubWords k *
      (List.range publicRows).foldl (fun pr j ↦ if j = k then pr else pr * (x + pinPoints.getD j 0)) 1) 0
  let at_ (i : ℕ) : K := wValues.getD i 0
  let parts : Array (E × E) := Array.ofFn (n := big) fun i ↦
    let x := offset + point i.val
    let w := at_ i.val
    let d := α + ofK w + β * ofK x
    let dNext := α + ofK w + β * ofK (sigmaValues.getD i.val 0)
    let z := (chain x (mv + 1)).getD mv 0
    let gate := at_ (i.val ^^^ 3) + at_ (i.val ^^^ 1) + at_ (i.val ^^^ 2) + w * at_ (i.val ^^^ 2)
    let g := ofK (gate * (rowPoly x)⁻¹ + (w + pinPoly x) * (zPins x)⁻¹)
    ((hValues.getD i.val 0 * d * dNext + d + dNext) * ofK z⁻¹ + μ * g, ofK (x * x + x) * d * dNext)
  let q0Hat := coefficients (mv + 2) offset (parts.map (·.1))
  let eHat := coefficients (mv + 2) offset (parts.map (·.2))
  let b2 := q0Hat.getD n 0 * (eHat.getD n 0 + eHat.getD (2 * n) 0)⁻¹
  let qHat : Array E := Array.ofFn (n := 2 * n + 1) fun j ↦ q0Hat.getD j.val 0 + b2 * eHat.getD j.val 0
  (hHat, qHat, b2)

/-- **The quotient table** `T` (`m + 4` variables, `table_slot`) at the challenges `α, β, μ`: word
`i + n (half + 2 limb + 8 kind)` is limb `limb < 3` of coefficient `i` of `A_0` (kind `0`, low half),
`A_1 = Q_h / x` (kind `0`, high half), `B_0 = x h_low` (kind `1`, low half) or `B_1 = (b_0, b_1, b_2)` (kind `1`,
high half); limb `3` zero. -/
def quotientTable (circuit : Circuit) (stmt : Statement) (cells₀ : Array K) (coins : Coins) (α β μ : E) :
    Array K :=
  let n := 2 ^ cellVars circuit.logRows
  let (hHat, qHat, b2) := quotientParts circuit stmt cells₀ coins α β μ
  -- `Q_h` (`q = q_low + Z Q_h`): `q[n + j]` at `j < n`, `q[2n] X_{2n} / Z = q[2n] (X_n + 1)`.
  let qh : Array E := Array.ofFn (n := 2 * n) fun j ↦
    if j.val = 0 then qHat.getD n 0 + qHat.getD (2 * n) 0
    else if j.val < n then qHat.getD (n + j.val) 0
    else if j.val = n then qHat.getD (2 * n) 0
    else 0
  let a1 := divX qh
  let b0 := mulX hHat
  let b1 (i : ℕ) : E := if i < freeBlind then blindAt coins i else if i = freeBlind then b2 else 0
  Array.ofFn (n := 16 * n) fun w ↦
    let i := w.val % n
    let half := w.val / n % 2
    let limb := w.val / (2 * n) % 4
    let kind := w.val / (8 * n)
    let x : E :=
      if kind = 0 then (if half = 0 then qHat.getD i 0 else a1.getD i 0)
      else (if half = 0 then b0.getD i 0 else b1 i)
    if limb < 3 then limbOf x limb else 0

/-- **The values the prover sends at `t`**: the three values the gate reads (`row_values` of the row polynomials
at `t`) and `next`, the wiring polynomial at `t`. -/
def valuesAt (circuit : Circuit) (cells₀ : Array K) (coins : Coins) (t : E) : Vector E 3 × E :=
  let mv := cellVars circuit.logRows
  let wHat := witnessTable circuit cells₀ coins
  let ws := digitsOf t mv
  let a : Vector E 4 := Vector.ofFn fun j ↦ novelEval wHat j.val 4 ((ws.drop 2).take (mv - 2))
  (rowValues a t (ws.getD 1 0), novelEval circuit.wiringTable 0 1 (ws.take mv))
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
theorem replaces them by an ideal PCS (`Zk.lean`, `formal/EndToEnd/ZK`). -/
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

/-- **The honest prover with PCS operations `pcs`** for its two secret tables (`W`, `T`) over `F`
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
  let (wTree, wCom) ← pcs.commit mv (witnessTable circuit cells₀ coins)
  let c ← Chain.startWith F (label index stmt)
  let wS := CommitmentScalars.of wCom
  let c := c.absorbCommitment wS
  let (α, c) ← c.squeezeWith F
  let (β, c) ← c.squeezeWith F
  let (μ, c) ← c.squeezeWith F
  let (tTree, tCom) ← pcs.commit (mv + 4) (quotientTable circuit stmt cells₀ coins α β μ)
  let tS := CommitmentScalars.of tCom
  let c := c.absorbCommitment tS
  let (t, _) ← c.squeezeWith F
  let (vals, next) := valuesAt circuit cells₀ coins t
  let proof : ReductionProof := ⟨wS, tS, vals, next⟩
  -- The claims, and their openings.
  let some r ← reduceWith F circuit.logRows index stmt proof | return none
  let some oW ← pcs.openClaim wTree r.commitments.witness r.claims.witness | return none
  let some oσ ← proveClaimWith F fuel indexTree sigmaHat index r.claims.wiring | return none
  let some oT ← pcs.openClaim tTree r.commitments.table r.claims.copy | return none
  return some ⟨proof, ⟨oW, oσ, oT⟩⟩

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
