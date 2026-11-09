-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the block cost `hashBlocks` and the weight calculus `Common.QueryCostAtMost`; VCVio's `support` of an
-- `OracleComp`; and `formal/EndToEnd/Completeness/E2ECompleteness/Cost.lean`'s cost of the prover's opening
-- (`cost_proveOpeningWithH`, `blockFactor`) and of a commitment (`qc_commitWithH`, `treeCost`).
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/Rec3ProverCost.lean`, `Rec3FlockCost.lean` (its
-- draws) and `Rec3Prob.lean`'s total.
import UniKeccakComplete.K.Rec3Prover
import UniKeccakComplete.K.FlockCost

/-!
# The block count of π1-rec3's honest prover, and the size of its stream

The port of `ProverCost.lean` to π1-rec3's prover (`Rec3Prover.lean`), in its writer calculus (`Cost.WC`). Flock's
prover is the main line's one at `keccakRec3` (`flockProveH`, `FlockCost.lean`: `flockBlocks 32 keccakRec3 = 49`,
its zerocheck coordinates the squares of one challenge), so no Flock lemma is new here.

* **The writer's draws** (from `Rec3FlockCost.lean`): the narrow draw costs one block beyond the bytes it hashes, as
  `sampleW` (`wc_sampleNarrowW`); the run of squares for `α` one block (`wc_drawRunW`).
* **The paired batch** (`wc_batchRounds3`): a pair round sends eight scalars and draws one narrow challenge, its point
  growing by two (`wc_pairRound3`); the last plain round two scalars and one challenge (`wc_plainRound3`); over `vars`
  variables at most `vars` challenges and `96 · vars` bytes, the point growing by `vars`.
* **The stream** (`wc_proveStreamRec3With`): `streamBlocks3` (`C1`'s and `C2`'s trees, the challenges: **one** for
  `α = squares c 4`, `β`, `γ`, `t`, `ρ`, `λ`, at most `batchVarsBound` in the batch, Flock's) beyond `streamBytes3`
  bytes (the row counts, the roots, Flock's, at most `valuesBound` values at `t`, `96` a batch variable, the claims'
  three values); its point claims have at most `batchVarsBound` coordinates (`StreamOK`).
* **The prover** (`costP_proveRec3With`, `uniProverCost3`): the setup's tree, the Keccak contract's IV at
  `keccakRec3` (`163` bytes and the program IV), the seed, the stream, three openings (`Cost.openP`).
* **At the reference shape** (`proverBlocks3_reference`): at most `2^47` block calls (nearly all the three WHIR
  provers'), the stream at most `6904` bytes beyond Flock's (`proverStream3_reference`); for the honest Flock prover
  **`cost_rec3_flockProveH`** (`2^47`) and **`streamSize_rec3_flockProveH`** (`2^14`), and the total
  **`totalCostK3_le`** (`2^48`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open UniStatement

set_option autoImplicit false

namespace UniKeccakComplete.Rec3

open UniComplete UniComplete.Rec3

open UniKeccakComplete.Cost
open E2ECompleteness.Cost (QC qc_pure qc_H_le treeCost)
open Bounds (batchVarsBound valuesBound)

/-! ## The writer's draws -/

/-- **The narrow draw** costs at most one block beyond the bytes it hashes, which the potential holds (as
`Cost.wc_sampleW`). -/
theorem wc_sampleNarrowW : WC (sampleNarrowW callKeccak256) 1 0 fun _ _ ↦ True := by
  intro c hc e
  refine ⟨?_, fun u ↦ ⟨trivial, ?_, ?_, ?_, ?_⟩⟩
  · show (digestBytes c.state ++ (c.stream.extract c.absorbed c.stream.size).toList).length / 136 + 1 ≤
      1 + 0 + wpot c + e
    simp only [List.length_append, Cost.len_digestBytes, Array.length_toList, Array.size_extract, wpot]
    omega
  · show c.stream.size ≤ c.stream.size
    exact le_rfl
  · exact le_rfl
  · show c.stream.size ≤ c.stream.size + 0
    omega
  · show c.stream.size - c.stream.size + e ≤ 1 + 0 + wpot c + e -
      ((digestBytes c.state ++ (c.stream.extract c.absorbed c.stream.size).toList).length / 136 + 1)
    simp only [List.length_append, Cost.len_digestBytes, Array.length_toList, Array.size_extract, wpot]
    omega

/-- **A run of squares**: one challenge (none for an empty run). -/
theorem wc_drawRunW (count : ℕ) : WC (drawRunW callKeccak256 count) 1 0 fun _ _ ↦ True := by
  unfold drawRunW
  split
  · exact wc_mono (wc_pure _) (Nat.zero_le _) le_rfl fun _ _ _ ↦ trivial
  · refine wc_seq wc_sampleW (fun c _ _ ↦ ?_) le_rfl le_rfl
    exact wc_mono (wc_pure _) le_rfl le_rfl fun _ _ _ ↦ trivial

/-! ## The paired batch -/

/-- **A pair round**: eight scalars, one narrow challenge; the point grows by two. -/
theorem wc_pairRound3 (lambda : E) (nq : ℕ) (st : BatchState) :
    WC (pairRound3 callKeccak256 lambda nq st) 1 (24 * 8) fun st' _ ↦ st'.point.length = st.point.length + 2 := by
  unfold pairRound3
  refine wc_seq (wc_sendScalars _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (le_of_eq (by rw [length_msg8]))
  refine wc_seq wc_sampleNarrowW (fun z _ _ ↦ ?_) le_rfl (Nat.zero_le _)
  refine wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ ?_
  subst hb
  simp only [foldAt, List.length_append, List.length_singleton]

/-- **The last plain round**: two scalars, one narrow challenge; the point grows by one. -/
theorem wc_plainRound3 (lambda : E) (nh : ℕ) (st : BatchState) :
    WC (plainRound3 callKeccak256 lambda nh st) 1 48 fun st' _ ↦ st'.point.length = st.point.length + 1 := by
  unfold plainRound3
  refine wc_seq (wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
  refine wc_seq (wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
  refine wc_seq wc_sampleNarrowW (fun r _ _ ↦ ?_) le_rfl (Nat.zero_le _)
  refine wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ ?_
  subst hb
  simp only [foldAt, List.length_append, List.length_singleton]

/-- **π1-rec3's batching sumcheck's rounds**: at most `vars` challenges and `96 · vars` bytes; the point grows by
`vars`. -/
theorem wc_batchRounds3 (lambda : E) (vars : ℕ) (st : BatchState) :
    WC (batchRounds3 callKeccak256 lambda vars st) vars (96 * vars)
      fun r _ ↦ r.length = st.point.length + vars := by
  unfold batchRounds3
  have h := wc_forIn_yield (List.range (vars / 2))
    (fun j s ↦ pairRound3 callKeccak256 lambda (2 ^ (vars - 2 * j - 2)) s)
    (fun i s ↦ s.point.length = st.point.length + 2 * i)
    (fun i a s hs ↦ wc_mono (wc_pairRound3 lambda _ s) le_rfl le_rfl fun s' _ h ↦ by omega) st 0 (by simp)
  rw [List.length_range] at h
  refine wc_seq h (fun s _ hs ↦ ?_) (by omega) (by omega)
  dsimp only
  split
  · refine wc_seq (wc_plainRound3 _ _ _) (fun s' _ hs' ↦ ?_) (by omega) (by omega)
    exact wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ by subst hb; omega
  · exact wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ by subst hb; omega

/-! ## The stream -/

/-- **π1-rec3's stream's blocks beyond its bytes**: `C1`'s and `C2`'s trees, the challenges (one for `α`, `β`, `γ`,
`t`, `ρ`, `λ`, at most one per batch variable), Flock's. -/
def streamBlocks3 (shape : Shape) (kF : ℕ) : ℕ :=
  treeCost (UniKeccak.c1LayoutK shape).vars + 3 + kF +
    treeCost (((UniKeccak.layoutsOfK shape).lookup .c2).getD default).vars + 3 + batchVarsBound shape

/-- **π1-rec3's stream's bytes**: the row counts, the two roots, Flock's, the values at `t`, `96` a batch variable,
the three claims' values. -/
def streamBytes3 (shape : Shape) (rows wF : ℕ) : ℕ :=
  4 * rows + 64 + wF + 24 * valuesBound + 96 * batchVarsBound shape + 72

/-- **π1-rec3's stream's cost**, given Flock's prover's at its `log_n` and `keccakRec3`. -/
theorem wc_proveStreamRec3With (flock : FlockProver (OracleComp KeccakCalls)) (kF wF : ℕ) (tr : Trace)
    (hF : WC (flock (keccakR1csLogSize + tr.shape.heights.getD opSha3 0) UniKeccak.keccakRec3 tr.qflock) kF wF
      fun _ _ ↦ True) :
    WC (proveStreamRec3With callKeccak256 (commitReal callKeccak256) flock tr)
      (streamBlocks3 tr.shape kF) (streamBytes3 tr.shape tr.rows.length wF) (StreamOK (batchVarsBound tr.shape)) := by
  unfold proveStreamRec3With streamBlocks3 streamBytes3
  refine wc_seq (wc_forIn_list (k := 0) (w := 4) _ _ _ fun _ _ ↦ wc_seq (wc_sendInteger _ 4)
    (fun _ _ _ ↦ wc_mono (wc_pure _) le_rfl le_rfl fun _ _ _ ↦ trivial) le_rfl le_rfl)
    (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_lift (qc_commitReal _ _ _)) (fun committed1 _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_sendRoot _) (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_drawRunW 4) (fun alphas _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun beta _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun gamma _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_map some hF) (fun flockOut _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_lift (qc_commitReal _ _ _)) (fun committed2 _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_sendRoot _) (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun t _ _ ↦ ?_) (by omega) (by omega)
  have ha := Bounds.atT_facts tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t flockOut
  have hvars := Bounds.batchVars_atT tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t flockOut
  refine wc_seq (wc_mono (wc_sendScalars _) le_rfl (Nat.mul_le_mul_left 24 ha.values) fun _ _ h ↦ h)
    (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun rho _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun lambda _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_mono (wc_batchRounds3 _ _ _) hvars (Nat.mul_le_mul_left 96 hvars) fun r _ h ↦ h)
    (fun r _ hr ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_mono (wc_sendScalars _) le_rfl (length_claims _ _ _) fun _ _ h ↦ h)
    (fun _ _ _ ↦ ?_) (by omega) (by omega)
  simp only [List.length_nil, Nat.zero_add] at hr
  refine wc_mono (wc_get_pure _ _ fun s ↦ ⟨rfl, ?_⟩) (Nat.zero_le _) (Nat.zero_le _) fun _ _ h ↦ h
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨⟨c, cl⟩, _, rfl⟩ := hx
  dsimp only
  rw [List.length_take]
  omega

/-! ## The prover -/

section Prover

/-- **π1-rec3's honest prover's blocks**: the setup's tree, the IV at `keccakRec3`, the seed, the stream (its blocks
and its bytes), three openings of claims of at most `batchVarsBound` coordinates. -/
def uniProverCost3 (shape : Shape) (programIvLen rows kF wF : ℕ) : ℕ :=
  treeCost (setupLayout shape).vars + ((163 + programIvLen) / 136 + 1) + 1 +
    (streamBlocks3 shape kF + streamBytes3 shape rows wF) + 3 * openP PcsQuotient.nonceFuel (batchVarsBound shape)

/-- **π1-rec3's honest prover's block count**, given Flock's prover's at its `log_n` and `keccakRec3`: and every
proof it returns has a stream of at most `streamBytes3` bytes. -/
theorem costP_proveRec3With (flock : FlockProver (OracleComp KeccakCalls)) (kF wF : ℕ)
    (programIv : List UInt8) (tr : Trace) (hpub : tr.publicInput.length = 32)
    (hF : WC (flock (keccakR1csLogSize + tr.shape.heights.getD opSha3 0) UniKeccak.keccakRec3 tr.qflock) kF wF
      fun _ _ ↦ True) :
    CostP (proveRec3With callKeccak256 callKeccakF1600 PcsQuotient.nonceFuel flock programIv tr)
      (uniProverCost3 tr.shape programIv.length tr.rows.length kF wF)
      fun o _ ↦ ∀ p, o = some p → p.stream.size ≤ streamBytes3 tr.shape tr.rows.length wF := by
  unfold proveRec3With contractIvOf seedOf
  simp only [bind_assoc, pure_bind]
  refine costP_seq_qc (qc_setupTreeOf tr) (fun tree ↦ ?_) (by unfold uniProverCost3; omega)
  refine costP_seq_qc (qc_H_le (k := (163 + programIv.length) / 136 + 1) (by
    simp only [List.length_append, ivTag_length, len_digestBytes, shapeBytes_length, layoutWordsK_length,
      variantBytesK_length]
    omega))
    (fun d ↦ ?_) (by unfold uniProverCost3; omega)
  refine costP_seq_qc (qc_H_le (k := 1) (by
    simp only [List.length_append, name_length, len_digestBytes, hpub]; omega)) (fun seed ↦ ?_)
    (by unfold uniProverCost3; omega)
  have hW := wc_proveStreamRec3With flock kF wF tr hF (Wr.start seed) (by simp [WInv, Wr.start])
    (uniProverCost3 tr.shape programIv.length tr.rows.length kF wF -
      treeCost (setupLayout tr.shape).vars - ((163 + programIv.length) / 136 + 1) - 1 -
      (streamBlocks3 tr.shape kF + streamBytes3 tr.shape tr.rows.length wF))
  rw [show streamBlocks3 tr.shape kF + streamBytes3 tr.shape tr.rows.length wF + wpot (Wr.start seed) +
      (uniProverCost3 tr.shape programIv.length tr.rows.length kF wF -
        treeCost (setupLayout tr.shape).vars - ((163 + programIv.length) / 136 + 1) - 1 -
        (streamBlocks3 tr.shape kF + streamBytes3 tr.shape tr.rows.length wF)) =
      uniProverCost3 tr.shape programIv.length tr.rows.length kF wF -
        treeCost (setupLayout tr.shape).vars - ((163 + programIv.length) / 136 + 1) - 1
      by simp only [wpot, Wr.start, Array.size_empty]; unfold uniProverCost3; omega] at hW
  refine CostP.bind hW fun z rem hz ↦ ?_
  obtain ⟨⟨hstream, hc0⟩, -, -, hsize, hrem⟩ := hz
  have hS : z.1.stream.size ≤ streamBytes3 tr.shape tr.rows.length wF := by
    rw [hstream]
    simpa [Wr.start] using hsize
  have hc : ∀ c pt v, (c, pt, v) ∈ z.1.claims → pt.length ≤ batchVarsBound tr.shape :=
    fun c pt v h ↦ hc0 _ h
  refine CostP.mono_budget (n := 3 * openP PcsQuotient.nonceFuel (batchVarsBound tr.shape)) ?_
    (by unfold uniProverCost3 at hrem; omega)
  obtain ⟨out, _⟩ := z
  dsimp only at hS hc ⊢
  generalize h1 : List.find? (fun x ↦ x.1 == Commitment.c1) out.claims = o1
  generalize h2 : List.find? (fun x ↦ x.1 == Commitment.c2) out.claims = o2
  generalize h3 : List.find? (fun x ↦ x.1 == Commitment.setup) out.claims = o3
  rcases o1 with _ | ⟨_, pt1, v1⟩ <;> rcases o2 with _ | ⟨_, pt2, v2⟩ <;> rcases o3 with _ | ⟨_, pt3, v3⟩ <;>
    repeat open_step

end Prover

/-! ## The deployed honest prover -/

section Deployed

/-- **π1-rec3's deployed honest prover's block count**, at `rows` row counts, Flock's prover's costs `k`, `w`. -/
def proverBlocks3 (D : UniKeccak.KDeployment) (rows : ℕ) (k w : ℕ → UniKeccak.KeccakVariant → ℕ) : ℕ :=
  uniProverCost3 D.shape D.programIv.length rows (k (flockLogN D.shape) UniKeccak.keccakRec3)
    (w (flockLogN D.shape) UniKeccak.keccakRec3)

/-- **π1-rec3's honest stream's bytes**, at most. -/
def proverStream3 (D : UniKeccak.KDeployment) (rows : ℕ) (w : ℕ → UniKeccak.KeccakVariant → ℕ) : ℕ :=
  streamBytes3 D.shape rows (w (flockLogN D.shape) UniKeccak.keccakRec3)

/-- **π1-rec3's deployed honest prover over the two calls makes at most `proverBlocks3` block calls, and every proof
it returns has a stream of at most `proverStream3` bytes**, given Flock's prover's cost. -/
theorem costP_uniProverRec3With (flock : FlockProverH) (k w : ℕ → UniKeccak.KeccakVariant → ℕ)
    (hF : FlockCost flock k w) (D : UniKeccak.KDeployment) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) :
    CostP (uniProverRec3With callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q)
      (proverBlocks3 D rows.length k w)
      fun o _ ↦ ∀ proof, o = some proof → proof.stream.size ≤ proverStream3 D rows.length w :=
  costP_proveRec3With (flock callKeccak256) _ _ _ _ D.programIv (honestTrace D input rows q)
    (by simp [honestTrace]) (hF _ _ _)

/-- **π1-rec3's deployed honest prover over the two calls makes at most `proverBlocks3` block calls.** -/
theorem cost_uniProverRec3With (flock : FlockProverH) (k w : ℕ → UniKeccak.KeccakVariant → ℕ)
    (hF : FlockCost flock k w) (D : UniKeccak.KDeployment) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) :
    Common.QueryCostAtMost (uniProverRec3With callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q)
      hashBlocks (proverBlocks3 D rows.length k w) :=
  (costP_uniProverRec3With flock k w hF D input rows q).toQC

end Deployed

/-! ## At the reference shape -/

section Reference

open LeanVM.Protocol.Verifier (whirBound costHeight)
open E2ECompleteness.Cost (blockFactor)
open UniKeccakSound (keccakRefShape)

/-- **π1-rec3's honest prover's blocks at the reference shape: at most `2^47`**, for six row counts, a program IV of
at most `2^16` bytes, Flock's prover at `log_n = 32` of at most `2^32` blocks beyond its bytes and `2^32` bytes. -/
theorem proverBlocks3_reference (D : UniKeccak.KDeployment) (hD : D.shape = keccakRefShape)
    (hIv : D.programIv.length ≤ 2 ^ 16) (k w : ℕ → UniKeccak.KeccakVariant → ℕ)
    (hk : k 32 UniKeccak.keccakRec3 ≤ 2 ^ 32) (hw : w 32 UniKeccak.keccakRec3 ≤ 2 ^ 32) :
    proverBlocks3 D 6 k w ≤ 2 ^ 47 := by
  obtain ⟨h1, h2, h3, h4⟩ := reference_stackVars
  unfold proverBlocks3 uniProverCost3 streamBlocks3 streamBytes3
  rw [hD, reference_flockLogN, h1, h2, h3, h4]
  rw [valuesBound_eq]
  unfold openP
  norm_num [treeCost, blockFactor, whirBound, costHeight, PcsQuotient.nonceFuel]
  omega

/-- **π1-rec3's honest stream at the reference shape**: the six row counts (`24`), the two roots (`64`), the `173`
values at `t`, `27` batch variables (`96` bytes each), the claims' three values: `6904` bytes, and Flock's. -/
theorem proverStream3_reference (D : UniKeccak.KDeployment) (hD : D.shape = keccakRefShape)
    (w : ℕ → UniKeccak.KeccakVariant → ℕ) :
    proverStream3 D 6 w = 6904 + w 32 UniKeccak.keccakRec3 := by
  obtain ⟨-, -, -, h4⟩ := reference_stackVars
  unfold proverStream3 streamBytes3
  rw [hD, reference_flockLogN, h4, valuesBound_eq]
  omega

end Reference

/-! ## π1-rec3's prover with the honest Flock prover -/

open UniKeccakSound (keccakRefShape)

/-- **π1-rec3's honest prover with Flock's honest prover makes at most `2^47` block calls** at the reference shape
(a program IV of at most `2^16` bytes; the π1-rec3 analogue of `Prob.ProverCost`). -/
theorem cost_rec3_flockProveH (D : UniKeccak.KDeployment) (hD : D.shape = keccakRefShape)
    (hIv : D.programIv.length ≤ 2 ^ 16) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)
    (hfit : D.shape.RowsFit rows) (_ : D.HonestRelation KeccakFlock.keccakFlockSpec rows input q) :
    Common.QueryCostAtMost
      (uniProverRec3With callKeccak256 callKeccakF1600 (flockProveH callKeccak256) D input rows q) hashBlocks
      (2 ^ 47) := by
  have h := cost_uniProverRec3With flockProveH flockBlocks flockBytes flockCost_flockProveH D input rows q
  rw [hfit.1] at h
  exact h.mono (proverBlocks3_reference D hD hIv flockBlocks flockBytes
    (by rw [flockBlocks_rec3_reference]; norm_num) (by rw [flockBytes_rec3_reference]; norm_num))

/-- **Every proof π1-rec3's honest prover can output has a stream of at most `2^14` bytes** at the reference shape
(`6904 + 3696`; the π1-rec3 analogue of `Prob.ProverStreamSize`). -/
theorem streamSize_rec3_flockProveH (D : UniKeccak.KDeployment) (hD : D.shape = keccakRefShape)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (hfit : D.shape.RowsFit rows)
    (_ : D.HonestRelation KeccakFlock.keccakFlockSpec rows input q) (π : UniKeccak.KeccakProof)
    (hπ : some π ∈ support
      (uniProverRec3With callKeccak256 callKeccakF1600 (flockProveH callKeccak256) D input rows q)) :
    π.stream.size ≤ 2 ^ 14 := by
  have h := CostP.mem_support (costP_uniProverRec3With flockProveH flockBlocks flockBytes
    flockCost_flockProveH D input rows q) _ hπ π rfl
  rw [hfit.1, proverStream3_reference D hD, flockBytes_rec3_reference] at h
  exact h.trans (by norm_num)

end UniKeccakComplete.Rec3

namespace UniKeccakComplete

open UniKeccak
open UniKeccakSound (keccakRefShape)

/-- **The block count of π1-rec3's run at the reference shape**: the setup (one tree, `5 · 2^18`), the prover's
`2^47`, π1-rec3's verifier on streams of `2^14` bytes: at most `2^48` (for a program IV of at most `2^16` bytes). -/
theorem totalCostK3_le (D : KDeployment) (hD : D.shape = keccakRefShape) (hiv : D.programIv.length ≤ 2 ^ 16) :
    Cost.setupCost D + (2 ^ 47 + Cost.verifierCost D keccakRec3 (2 ^ 14)) ≤ 2 ^ 48 := by
  have h3 := Cost.reference_stackVars.2.2.1
  have ho := Cost.openCost_le
  have hivc : (163 + D.programIv.length) / 136 ≤ 163 + 2 ^ 16 := (Nat.div_le_self _ _).trans (by omega)
  unfold Cost.setupCost Cost.verifierCost Cost.ivCost
  rw [Cost.walkCost_rec3, hD, h3]
  norm_num
  omega

end UniKeccakComplete

/-! ## Axioms -/

/-- info: 'UniKeccakComplete.Rec3.cost_uniProverRec3With' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec3.cost_uniProverRec3With

/-- info: 'UniKeccakComplete.Rec3.cost_rec3_flockProveH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec3.cost_rec3_flockProveH

/-- info: 'UniKeccakComplete.Rec3.streamSize_rec3_flockProveH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec3.streamSize_rec3_flockProveH

/-- info: 'UniKeccakComplete.totalCostK3_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.totalCostK3_le
