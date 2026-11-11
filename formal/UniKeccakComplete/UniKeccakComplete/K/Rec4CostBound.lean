-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π1-rec4's analogue of `Rec3ProverCost.lean`
-- (`wc_proveStreamRec3With`, `costP_proveRec3With`, `proverBlocks3_reference`, `totalCostK3_le`) and of
-- `VerifierHCost.lean` (`cc_reduceWithKH`, `costP_runWithKH`, `costP_verifyWithKH`, `cost_verifierWithH`), at
-- `H = callKeccak256`, `W = rateSigma` (`Rec4Cost.lean`); uses leanerVM (https://github.com/Verified-zkEVM/leanerVM,
-- branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the block cost `hashBlocks`, the weight calculus.
import UniKeccakComplete.K.Rec4Cost

/-!
# π1-rec4's block counts at the reference shape

At `H = callKeccak256`, `W = rateSigma` (a rate call read as a digest query and a permutation call):

* **a wide draw** costs two blocks beyond the bytes it hashes on the prover's side (`wc_sampleWideW_sigma`), three on
  the verifier's (`cc_sampleWideH_sigma`);
* **the prover** (`costP_proveRec4With`): at most `2^47` blocks at the reference shape (`proverBlocks4_reference`),
  its streams at most `6952 + 3696 ≤ 2^14` bytes (`proverStream4_reference`);
* **the verifier** (`cost_verifierWith4H`): at most `verifierCost4 D S` blocks on a stream of `S` bytes;
* **the experiment** (`expCost4_reference`): at most `2^48` blocks, hence `ExpCost4 D (2^48)`.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open UniStatement UniKeccak
open UniKeccakComplete.Cost (WC wc_seq wc_mono wc_pure wc_bind wc_sampleW wc_sendScalar wc_sendScalars wc_sendRoot
  wc_sendInteger wc_lift wc_forIn_list wc_get_pure WInv wpot CostP costP_query_bind CC CCAt cc_seq cc_free cc_pure
  cc_mono cc_bind cc_throw_bind cc_sampleH cc_nextScalar cc_nextScalars cc_nextRoot cc_countBits cc_sumcheckH
  cc_sumcheckPairsDrawnH cc_requireZero cc_forIn_list cc_tablePart cc_finish pot Inv StreamOK qc_commitReal
  length_claims costP_seq_qc qc_setupTreeOf openP qc_pcsProve1 stream_of_some len_digestBytes ivTag_length
  shapeBytes_length elementBytes24_length variantBytesK_length name_length CostP.mem_support CostP.mono_budget
  CostP.bind CostP.toQC CostP.weaken costP_of_qc openCost qc_pcsOpenKH qc_forIn_list ivCost ivInput_length
  setupCost cc_ite cc_map)
open E2ECompleteness.Cost (QC qc_pure qc_H_le treeCost)
open UniKeccakComplete.Bounds (batchVarsBound valuesBound)

set_option autoImplicit false

namespace UniKeccakComplete.Rec4

open UniComplete UniKeccakComplete.Rec3

/-! ## The wide draw -/

/-- **A wide draw on the prover's side**: two blocks beyond the bytes it hashes (the hash's last, the permutation
call). -/
theorem wc_sampleWideW_sigma (count : ℕ) : WC (sampleWideW rateSigma count) 2 0 fun _ _ ↦ True := by
  intro c hc e
  refine ⟨?_, fun u ↦ ⟨?_, fun st ↦ ⟨trivial, ?_, ?_, ?_, ?_⟩⟩⟩
  · show (digestBytes c.state ++ (c.stream.extract c.absorbed c.stream.size).toList).length / 136 + 1 ≤
      2 + 0 + wpot c + e
    simp only [List.length_append, len_digestBytes, Array.length_toList, Array.size_extract, wpot]
    omega
  · show 1 ≤ 2 + 0 + wpot c + e -
      ((digestBytes c.state ++ (c.stream.extract c.absorbed c.stream.size).toList).length / 136 + 1)
    simp only [List.length_append, len_digestBytes, Array.length_toList, Array.size_extract, wpot]
    omega
  · show c.stream.size ≤ c.stream.size
    exact le_rfl
  · exact le_rfl
  · show c.stream.size ≤ c.stream.size + 0
    omega
  · show c.stream.size - c.stream.size + e ≤ 2 + 0 + wpot c + e -
      ((digestBytes c.state ++ (c.stream.extract c.absorbed c.stream.size).toList).length / 136 + 1) - 1
    simp only [List.length_append, len_digestBytes, Array.length_toList, Array.size_extract, wpot]
    omega

/-! ## Flock at π1-rec4 -/

/-- **The zerocheck at π1-rec4**: the skip, `7 + (log_n − k − 7)` rounds, `v_a`, `v_b`. -/
theorem wc_zerocheckW4 (logN k : ℕ) (c : E) (wit : FlockP.Wit) :
    WC (zerocheckW4 callKeccak256 logN k c wit) (1 + (Flock.nFixed + (logN - k - Flock.nFixed)))
      (24 * 2 ^ k + 48 * (Flock.nFixed + (logN - k - Flock.nFixed)) + 48) fun _ _ ↦ True := by
  unfold zerocheckW4
  have hr : (Flock.fixedChallenges ++ squares c (logN - k - Flock.nFixed)).length =
      Flock.nFixed + (logN - k - Flock.nFixed) := by
    rw [List.length_append, FlockP.length_squares, FlockP.length_fixedChallenges]
  refine wc_seq (FlockP.wc_skipW _ _ _) (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (FlockP.wc_zcRounds _ _ _ _ _) (fun _ _ _ ↦ ?_) (by rw [hr]; omega) (by rw [hr]; omega)
  refine wc_seq (wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
  refine wc_seq (wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
  exact wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial

/-- **Flock's blocks at π1-rec4**: the skip's `z`, the zerocheck's rounds, `α`, the lincheck's `11`. -/
def flockBlocks4 (logN : ℕ) (v : KeccakVariant) : ℕ :=
  1 + (Flock.nFixed + (logN - v.skip - Flock.nFixed)) + 1 + lincheckRoundsK

/-- **Flock's honest prover at π1-rec4**: at most `flockBlocks4` blocks beyond its bytes, at most `flockBytes`
bytes (π1-rec3's). -/
theorem wc_flockProve4 (logN : ℕ) (v : KeccakVariant) (c : E) (q : Array K) :
    WC (flockProve4 callKeccak256 logN v c q) (flockBlocks4 logN v) (flockBytes logN v) fun _ _ ↦ True := by
  unfold flockProve4 frontW4 flockBlocks4 flockBytes
  simp only [bind_assoc, pure_bind]
  refine wc_seq (wc_zerocheckW4 _ _ _ _) (fun zc _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun alpha _ _ ↦ ?_) (by omega) (Nat.zero_le _)
  refine wc_seq (FlockP.wc_lcRounds _ _ _ _) (fun lc _ hlc ↦ ?_) (by omega) (by omega)
  have hz : lc.z.toList.length = Flock.kBits := by
    rw [Array.length_toList, hlc, FlockP.size_lcWitnessOf, FlockP.slices_count]
  refine wc_seq (wc_sendScalars _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by rw [hz]; omega)
  exact wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial

theorem flockBlocks4_reference : flockBlocks4 32 keccakRec4 = 42 := by decide +kernel

theorem flockBytes_rec4_reference : flockBytes 32 keccakRec4 = 3696 := by decide +kernel

/-! ## The stream -/

/-- **From Flock to `C2`'s root.** -/
theorem wc_midB4 (tr : Trace) (bus : List E) :
    WC (midB4 callKeccak256 (commitReal callKeccak256) tr bus)
      (flockBlocks4 ((keccakR1csLogSize + tr.shape.heights.getD opSha3 0)) keccakRec4 + treeCost (((layoutsOfK tr.shape).lookup .c2).getD default).vars)
      (flockBytes ((keccakR1csLogSize + tr.shape.heights.getD opSha3 0)) keccakRec4 + 56) fun _ _ ↦ True := by
  unfold midB4
  refine wc_seq (wc_flockProve4 _ _ _ _) (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_lift (qc_commitReal _ _ _)) (fun _ _ _ ↦ ?_) (by omega) (Nat.zero_le _)
  refine wc_seq (wc_sendRoot _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
  refine wc_seq (wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
  exact wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial

/-- **From the point draw on**: the values, the late draw, the batch, the claims' values. -/
theorem wc_tailT4 (tr : Trace) (committed1 : Committed) (bus : List E) (fl : List E × List E)
    (committed2 : Committed) (pointDraw : List E) :
    WC (tailT4 callKeccak256 rateSigma tr committed1 bus fl committed2 pointDraw)
      (2 + batchVarsBound tr.shape) (24 * valuesBound + 96 * batchVarsBound tr.shape + 72)
      fun out s ↦ StreamOK (batchVarsBound tr.shape) out s := by
  unfold tailT4
  have ha := Bounds.atT_facts tr (c2DataOf tr (eqKernel (squares (bus.getD 0 0) 4)) (bus.getD 1 0) (bus.getD 2 0))
    (squares (bus.getD 0 0) 4) (bus.getD 1 0) (bus.getD 2 0) (pointDraw.getD 0 0) none
  refine wc_seq (wc_mono (wc_sendScalars _) le_rfl (Nat.mul_le_mul_left 24 ha.values) fun _ _ h ↦ h)
    (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
  refine wc_seq (wc_sampleWideW_sigma 4) (fun late _ _ ↦ ?_) (by omega) (Nat.zero_le _)
  have hvars := Bounds.batchVars_atT tr
    (c2DataOf tr (eqKernel (squares (bus.getD 0 0) 4)) (bus.getD 1 0) (bus.getD 2 0)) (squares (bus.getD 0 0) 4)
    (bus.getD 1 0) (bus.getD 2 0) (pointDraw.getD 0 0)
    (some (flockOut4 fl (pointDraw.drop 1 ++ [late.getD 2 0, late.getD 3 0])))
  refine wc_seq (wc_mono (Rec3.wc_batchRounds3 _ _ _) hvars (Nat.mul_le_mul_left 96 hvars) fun r _ h ↦ h)
    (fun r _ hr ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_mono (wc_sendScalars _) le_rfl (length_claims _ _ _) fun _ _ h ↦ h)
    (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
  simp only [List.length_nil, Nat.zero_add] at hr
  refine wc_mono (wc_get_pure _ _ fun s ↦ ⟨rfl, ?_⟩) (Nat.zero_le _) (Nat.zero_le _) fun _ _ h ↦ h
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨⟨c, cl⟩, _, rfl⟩ := hx
  dsimp only
  rw [List.length_take]
  omega

/-- **π1-rec4's stream's blocks beyond its bytes**: `C1`'s and `C2`'s trees, two a wide draw, Flock's, one per
batch variable. -/
def streamBlocks4 (shape : UniStatement.Shape) : ℕ :=
  treeCost (c1LayoutK shape).vars + 2 + (flockBlocks4 ((keccakR1csLogSize + shape.heights.getD opSha3 0)) keccakRec4 +
    treeCost (((layoutsOfK shape).lookup .c2).getD default).vars) + 2 + (2 + batchVarsBound shape)

/-- **π1-rec4's stream's bytes**: the row counts, the two roots and out-of-domain answers, Flock's, the values at
`t`, `96` a batch variable, the claims' three values (π1-rec3's). -/
def streamBytes4 (shape : UniStatement.Shape) (rows : ℕ) : ℕ :=
  4 * rows + 112 + flockBytes ((keccakR1csLogSize + shape.heights.getD opSha3 0)) keccakRec4 + 24 * valuesBound + 96 * batchVarsBound shape + 72

/-- **π1-rec4's stream's cost.** -/
theorem wc_proveStreamRec4With (tr : Trace) :
    WC (proveStreamRec4With callKeccak256 rateSigma (commitReal callKeccak256) tr)
      (streamBlocks4 tr.shape) (streamBytes4 tr.shape tr.rows.length)
      (StreamOK (batchVarsBound tr.shape)) := by
  unfold proveStreamRec4With streamBlocks4 streamBytes4
  refine wc_seq (wc_forIn_list (k := 0) (w := 4) _ _ _ fun _ _ ↦ wc_seq (wc_sendInteger _ 4)
    (fun _ _ _ ↦ wc_mono (wc_pure _) le_rfl le_rfl fun _ _ _ ↦ trivial) le_rfl le_rfl)
    (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_lift (qc_commitReal _ _ _)) (fun committed1 _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_sendRoot _) (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_sendScalar _) (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_sampleWideW_sigma 4) (fun bus _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_midB4 _ _) (fun x _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_sampleWideW_sigma 5) (fun pd _ _ ↦ ?_) (by omega) (by omega)
  exact wc_mono (wc_tailT4 _ _ _ _ _ _) (by omega) (by omega) fun _ _ h ↦ h

/-! ## The prover -/

/-- **π1-rec4's honest prover's blocks**: the setup's tree, the IV, the seed, the stream (its blocks and its bytes),
three openings of claims of at most `batchVarsBound` coordinates. -/
def uniProverCost4 (shape : UniStatement.Shape) (programIvLen rows : ℕ) : ℕ :=
  treeCost (setupLayout shape).vars + ((163 + programIvLen) / 136 + 1) + 1 +
    (streamBlocks4 shape + streamBytes4 shape rows) + 3 * openP PcsQuotient.nonceFuel (batchVarsBound shape)

/-- **π1-rec4's honest prover's block count**: and every proof it returns has a stream of at most `streamBytes4`
bytes. -/
theorem costP_proveRec4With (programIv : List UInt8) (tr : Trace) (hpub : tr.publicInput.length = 32) :
    CostP (proveRec4With callKeccak256 rateSigma callKeccakF1600 PcsQuotient.nonceFuel programIv tr)
      (uniProverCost4 tr.shape programIv.length tr.rows.length)
      fun o _ ↦ ∀ p, o = some p → p.stream.size ≤ streamBytes4 tr.shape tr.rows.length := by
  unfold proveRec4With contractIvOf seedOf
  simp only [bind_assoc, pure_bind]
  refine costP_seq_qc (qc_setupTreeOf tr) (fun tree ↦ ?_) (by unfold uniProverCost4; omega)
  refine costP_seq_qc (qc_H_le (k := (163 + programIv.length) / 136 + 1) (by
    simp only [List.length_append, ivTag_length, len_digestBytes, shapeBytes_length, elementBytes24_length,
      variantBytesK_length]
    omega))
    (fun d ↦ ?_) (by unfold uniProverCost4; omega)
  refine costP_seq_qc (qc_H_le (k := 1) (by
    simp only [List.length_append, name_length, len_digestBytes, hpub]; omega)) (fun seed ↦ ?_)
    (by unfold uniProverCost4; omega)
  have hW := wc_proveStreamRec4With tr (Wr.start seed) (by simp [WInv, Wr.start])
    (uniProverCost4 tr.shape programIv.length tr.rows.length -
      treeCost (setupLayout tr.shape).vars - ((163 + programIv.length) / 136 + 1) - 1 -
      (streamBlocks4 tr.shape + streamBytes4 tr.shape tr.rows.length))
  rw [show streamBlocks4 tr.shape + streamBytes4 tr.shape tr.rows.length + wpot (Wr.start seed) +
      (uniProverCost4 tr.shape programIv.length tr.rows.length -
        treeCost (setupLayout tr.shape).vars - ((163 + programIv.length) / 136 + 1) - 1 -
        (streamBlocks4 tr.shape + streamBytes4 tr.shape tr.rows.length)) =
      uniProverCost4 tr.shape programIv.length tr.rows.length -
        treeCost (setupLayout tr.shape).vars - ((163 + programIv.length) / 136 + 1) - 1
      by simp only [wpot, Wr.start, Array.size_empty]; unfold uniProverCost4; omega] at hW
  refine CostP.bind hW fun z rem hz ↦ ?_
  obtain ⟨⟨hstream, hc0⟩, -, -, hsize, hrem⟩ := hz
  have hS : z.1.stream.size ≤ streamBytes4 tr.shape tr.rows.length := by
    rw [hstream]
    simpa [Wr.start] using hsize
  have hc : ∀ c pt v, (c, pt, v) ∈ z.1.claims → pt.length ≤ batchVarsBound tr.shape :=
    fun c pt v h ↦ hc0 _ h
  refine CostP.mono_budget (n := 3 * openP PcsQuotient.nonceFuel (batchVarsBound tr.shape)) ?_
    (by unfold uniProverCost4 at hrem; omega)
  obtain ⟨out, _⟩ := z
  unfold Rec3.openingsTail3
  dsimp only at hS hc ⊢
  generalize h1 : List.find? (fun x ↦ x.1 == Commitment.c1) out.claims = o1
  generalize h2 : List.find? (fun x ↦ x.1 == Commitment.c2) out.claims = o2
  generalize h3 : List.find? (fun x ↦ x.1 == Commitment.setup) out.claims = o3
  rcases o1 with _ | ⟨_, pt1, v1⟩ <;> rcases o2 with _ | ⟨_, pt2, v2⟩ <;> rcases o3 with _ | ⟨_, pt3, v3⟩ <;>
    dsimp only <;> (try simp only [pure_bind]) <;> repeat open_step

/-! ## The verifier -/

/-- **A wide draw on the verifier's side**: three blocks beyond the bytes it hashes. -/
theorem cc_sampleWideH_sigma (count : ℕ) : CC (sampleWideH rateSigma count) 3 0 fun _ ↦ True := by
  intro c hc e
  refine ⟨?_, fun u ↦ ⟨?_, fun st a _ ↦ ⟨trivial, ?_, ?_⟩⟩⟩
  · show (digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList).length / 136 + 1 ≤ 3 + pot c + e
    simp only [List.length_append, len_digestBytes, Array.length_toList, Array.size_extract, pot]
    have := hc.1; have := hc.2
    omega
  · show 1 ≤ 3 + pot c + e - ((digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList).length / 136 + 1)
    simp only [List.length_append, len_digestBytes, Array.length_toList, Array.size_extract, pot]
    have := hc.1; have := hc.2
    omega
  · exact ⟨le_rfl, hc.2⟩
  · show 3 * (c.data.size - c.cursor) + (c.cursor - c.cursor) + 0 + e ≤
      3 + pot c + e - ((digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList).length / 136 + 1) - 1
    simp only [List.length_append, len_digestBytes, Array.length_toList, Array.size_extract, pot]
    have := hc.1; have := hc.2
    omega

/-- **Flock's zerocheck at π1-rec4**: the skip's `z`; its rounds paid by their reads. -/
theorem cc_zerocheckFirstH (logN k : ℕ) (c : E) :
    CC (Flock.zerocheckFirstH callKeccak256 logN k c) 2 0 fun _ ↦ True := by
  unfold Flock.zerocheckFirstH
  dsimp only
  split
  · refine cc_free (cc_nextScalars _) fun _ _ ↦ ?_
    refine cc_seq cc_sampleH (fun _ _ ↦ ?_) (by omega)
    refine cc_free (cc_pure (P := fun _ ↦ True) trivial 0) fun p _ ↦ ?_
    obtain ⟨zSkip, claim⟩ := p
    refine cc_free (cc_sumcheckH _ 3 (by norm_num) _) fun q _ ↦ ?_
    obtain ⟨chi, running⟩ := q
    refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    exact cc_pure trivial _
  · refine cc_free (cc_pure (P := fun _ ↦ True) trivial 0) fun p _ ↦ ?_
    obtain ⟨zSkip, claim⟩ := p
    refine cc_free (cc_sumcheckH _ 3 (by norm_num) _) fun q _ ↦ ?_
    obtain ⟨chi, running⟩ := q
    refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    exact cc_pure trivial _

/-- **Flock walked at π1-rec4**: the zerocheck, its `α`, the structured terminal (a zero collected). -/
theorem cc_verifyWalkedKH4 (logN : ℕ) (v : KeccakVariant) (c : E) :
    CC (verifyWalkedKH4 callKeccak256 logN v c) 4 0 fun _ ↦ True := by
  unfold verifyWalkedKH4 frontKH4
  simp only [bind_assoc]
  refine cc_seq (cc_zerocheckFirstH _ _ _) (fun _ _ ↦ ?_) (by omega)
  repeat cc_step

/-- **The batch at π1-rec4** (`λ` given): its rounds paid by their reads; at most one opening per combined claim. -/
theorem cc_batchKH4 (lambda : E) (combined : List (Commitment × Combined))
    (layouts : List (Commitment × StackLayout)) (ringMap : Option (List E)) :
    CC (batchKH4 callKeccak256 lambda combined layouts ringMap) 0 0 fun z ↦ z.length ≤ combined.length := by
  unfold batchKH4
  try dsimp only
  refine cc_free (cc_sumcheckPairsDrawnH _ _ _ (by norm_num) _) fun x _ ↦ ?_
  obtain ⟨r, _, last⟩ := x
  try dsimp only
  refine cc_free (cc_nextScalars _) fun values _ ↦ ?_
  try dsimp only
  refine cc_free (cc_requireZero _) fun _ _ ↦ ?_
  refine cc_pure ?_ _
  simp only [Array.length_toList]
  refine Cost.fold_openings_size3 _ _ _ fun acc x ↦ ?_
  obtain ⟨s1, s2, os⟩ := acc
  obtain ⟨⟨c, claim⟩, v⟩ := x
  simp

/-- π1-rec4's walk's challenges, but the sumchecks' rounds: three wide draws (three each), Flock's `z` and `α` (two
each). -/
def walkCost4 : ℕ := 13

/-- **π1-rec4's walk, point claims**: at most `walkCost4` blocks beyond the potential, and at most three openings. -/
theorem cc_reduceWithKH4 (shape : UniStatement.Shape) (publicWords : List E) (v : KeccakVariant) :
    CC (reduceWithKH4 callKeccak256 rateSigma shape publicWords v .point) walkCost4 0
      fun r ↦ r.openings.length ≤ 3 := by
  unfold reduceWithKH4 walkCost4
  dsimp only
  split
  · exact cc_throw_bind _ _ _ _ _
  · refine cc_free (cc_countBits _) fun _ _ ↦ ?_
    refine cc_free cc_nextRoot fun _ _ ↦ ?_
    refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    refine cc_seq (cc_sampleWideH_sigma 4) (fun _ _ ↦ ?_) (by omega)
    refine cc_seq (cc_verifyWalkedKH4 _ _ _) (fun x _ ↦ ?_) (by omega)
    obtain ⟨point, slices⟩ := x
    dsimp only
    refine cc_free cc_nextRoot fun _ _ ↦ ?_
    refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    refine cc_seq (cc_sampleWideH_sigma 5) (fun _ _ ↦ ?_) (by omega)
    refine cc_free (cc_mono (cc_forIn_list (k := 0) _ _ _ fun _ _ ↦ cc_free (cc_tablePart _ _ _ _ _) fun _ _ ↦
      cc_pure (P := fun _ ↦ True) trivial 0) (by simp) le_rfl fun _ h ↦ h) fun _ _ ↦ ?_
    iterate 7 refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    refine cc_seq (cc_sampleWideH_sigma 4) (fun _ _ ↦ ?_) (by omega)
    try dsimp only
    refine cc_seq (cc_batchKH4 _ _ _ _) (fun z hz ↦ ?_) (by omega)
    exact cc_pure (P := fun r : Reduced ↦ r.openings.length ≤ 3) (hz.trans (List.length_filterMap_le _ _)) _

/-- **π1-rec4's walk** from the start of a stream: the potential is three per byte. -/
theorem costP_walk4 (shape : UniStatement.Shape) (publicWords : List E) (v : KeccakVariant) (seed : Digest)
    (stream : Array UInt8) (m : ℕ) :
    CostP ((do
        let r ← reduceWithKH4 callKeccak256 rateSigma shape publicWords v .point
        finish (m := OracleComp KeccakCalls)
        return r : Cost.CM Reduced).run.run (Chan.start seed stream))
      (walkCost4 + 3 * stream.size + m) fun z rem ↦
        ∀ a, z.1 = .ok a → a.openings.length ≤ 3 ∧ m ≤ rem := by
  have h := cc_mono (k' := walkCost4) (g' := 0)
    (cc_bind (k₂ := 0) (g₂ := 0) (cc_reduceWithKH4 shape publicWords v) fun r hr ↦
      cc_free cc_finish fun _ _ ↦ cc_pure (P := fun r : Reduced ↦ r.openings.length ≤ 3) hr 0) (by omega) le_rfl
    fun _ h ↦ h
  have h2 := h (Chan.start seed stream) ⟨le_rfl, Nat.zero_le _⟩ m
  rw [show walkCost4 + pot (Chan.start seed stream) + m = walkCost4 + 3 * stream.size + m
    by simp [pot, Chan.start]] at h2
  exact h2.mono fun z rem hz a ha ↦ ⟨(hz a ha).1, by have := (hz a ha).2.2; omega⟩

/-- **π1-rec4's run on calldata**: the seed, then the walk; at most three openings, `m` blocks left. -/
theorem costP_runWithKH4 (shape : UniStatement.Shape) (iv publicInput : List UInt8) (stream : Array UInt8)
    (v : KeccakVariant) (m : ℕ) :
    CostP (runWithKH4 callKeccak256 rateSigma shape iv publicInput stream v .point)
      ((16 + iv.length + publicInput.length) / 136 + 1 + (walkCost4 + 3 * stream.size + m))
      fun o rem ↦ ∀ r, o.result = .ok r → r.openings.length ≤ 3 ∧ m ≤ rem := by
  unfold runWithKH4 seedWithH callKeccak256
  rw [costP_query_bind]
  refine ⟨?_, fun seed ↦ ?_⟩
  · show (name ++ iv ++ publicInput).length / 136 + 1 ≤ _
    simp only [List.length_append, name_length]
    omega
  · rw [show (16 + iv.length + publicInput.length) / 136 + 1 + (walkCost4 + 3 * stream.size + m) -
        hashBlocks (Sum.inl (name ++ iv ++ publicInput)) = walkCost4 + 3 * stream.size + m by
      show _ - ((name ++ iv ++ publicInput).length / 136 + 1) = _
      simp only [List.length_append, name_length]
      omega]
    exact (costP_walk4 shape _ v seed stream m).bind fun z rem hz r hr ↦ hz r hr

/-- **π1-rec4's verifier**: the run, then at most three openings. -/
theorem costP_verifyWithKH4 (shape : UniStatement.Shape) (v : KeccakVariant) (iv : List UInt8) (roots : SetupRootsK)
    (publicInput : Vector UInt8 32) (proof : KeccakProof) :
    CostP (verifyWithKH4 callKeccak256 rateSigma callKeccakF1600 shape v iv roots publicInput proof)
      ((16 + iv.length + 32) / 136 + 1 + (walkCost4 + 3 * proof.stream.size + 3 * openCost))
      fun _ _ ↦ True := by
  unfold verifyWithKH4
  rw [show 16 + iv.length + 32 = 16 + iv.length + publicInput.toList.length by simp]
  refine CostP.bind (costP_runWithKH4 shape iv publicInput.toList proof.stream v (3 * openCost))
    fun o rem ho ↦ ?_
  split
  · trivial
  · split
    · trivial
    · rename_i r hr
      obtain ⟨hl, hrem⟩ := ho r hr
      refine CostP.weaken (n := 3 * openCost + 0) ((costP_of_qc ?_ 0).mono fun _ _ _ ↦ trivial) (by omega)
      refine (qc_forIn_list (c := openCost) _ _ _ fun x s ↦ ?_).bind_le (b := 0) (fun s ↦ ?_) ?_
      · split
        split
        · exact (qc_pcsOpenKH _ _ _ _ _ _).bind_le (fun _ ↦ qc_pure _ 0) (by omega)
        · exact qc_pure _ _
      · split <;> exact qc_pure _ _
      · have : r.openings.length * openCost ≤ 3 * openCost := Nat.mul_le_mul_right _ hl
        omega

/-- **π1-rec4's deployed verifier's block count** on a proof of a stream of at most `S` bytes. -/
def verifierCost4 (D : KDeployment) (S : ℕ) : ℕ := ivCost D + 1 + walkCost4 + 3 * S + 3 * openCost

/-- **π1-rec4's deployed verifier makes at most `verifierCost4 D S` block calls** on any proof whose stream has at
most `S` bytes, whatever its opening proofs. -/
theorem cost_verifierWith4H (D : KDeployment) (roots : SetupRootsK) (input : Vector UInt8 32) (proof : KeccakProof)
    (S : ℕ) (hS : proof.stream.size ≤ S) :
    Common.QueryCostAtMost (KDeployment.verifierWith4H callKeccak256 rateSigma callKeccakF1600 D roots input proof)
      hashBlocks (verifierCost4 D S) := by
  refine CostP.toQC (Q := fun _ _ ↦ True) ?_
  unfold KDeployment.verifierWith4H KDeployment.ivWithH contractIvKWithH callKeccak256
  rw [bind_assoc, costP_query_bind]
  refine ⟨?_, fun d ↦ ?_⟩
  · show (ivTag ++ D.programIv ++ digestBytes roots.f ++ elementBytes24 roots.fOod ++
      shapeBytes D.shape ++ variantBytesK keccakRec4).length / 136 + 1 ≤ _
    rw [ivInput_length]
    unfold verifierCost4 ivCost
    omega
  · rw [pure_bind]
    refine (costP_verifyWithKH4 D.shape keccakRec4 (digestBytes d) roots input proof).weaken ?_
    show _ ≤ verifierCost4 D S - ((ivTag ++ D.programIv ++ digestBytes roots.f ++ elementBytes24 roots.fOod ++
      shapeBytes D.shape ++ variantBytesK keccakRec4).length / 136 + 1)
    rw [ivInput_length, len_digestBytes]
    unfold verifierCost4 ivCost
    omega

/-! ## At the reference shape -/

section Reference

open LeanVM.Protocol.Verifier (whirBound costHeight)
open E2ECompleteness.Cost (blockFactor)
open UniKeccakSound (keccakRefShape)

/-- **π1-rec4's honest prover's blocks at the reference shape: at most `2^47`**, for six row counts and a program IV
of at most `2^16` bytes. -/
theorem proverBlocks4_reference (D : KDeployment) (hD : D.shape = keccakRefShape)
    (hIv : D.programIv.length ≤ 2 ^ 16) : uniProverCost4 D.shape D.programIv.length 6 ≤ 2 ^ 47 := by
  obtain ⟨h1, h2, h3, h4⟩ := Cost.reference_stackVars
  have hL : keccakR1csLogSize + keccakRefShape.heights.getD opSha3 0 = 32 := Cost.reference_flockLogN
  have hk : flockBlocks4 (keccakR1csLogSize + keccakRefShape.heights.getD opSha3 0) keccakRec4 ≤ 2 ^ 32 := by
    rw [hL, flockBlocks4_reference]; norm_num
  have hw : flockBytes (keccakR1csLogSize + keccakRefShape.heights.getD opSha3 0) keccakRec4 ≤ 2 ^ 32 := by
    rw [hL, flockBytes_rec4_reference]; norm_num
  unfold uniProverCost4 streamBlocks4 streamBytes4
  rw [hD, h1, h2, h3, h4, Cost.valuesBound_eq]
  generalize flockBlocks4 (keccakR1csLogSize + keccakRefShape.heights.getD opSha3 0) keccakRec4 = kF at hk ⊢
  generalize flockBytes (keccakR1csLogSize + keccakRefShape.heights.getD opSha3 0) keccakRec4 = wF at hw ⊢
  unfold openP
  norm_num [treeCost, blockFactor, whirBound, costHeight, PcsQuotient.nonceFuel]
  omega

/-- **π1-rec4's honest stream at the reference shape**: `6952 + 3696` bytes. -/
theorem proverStream4_reference (D : KDeployment) (hD : D.shape = keccakRefShape) :
    streamBytes4 D.shape 6 = 10648 := by
  obtain ⟨-, -, -, h4⟩ := Cost.reference_stackVars
  have hL : keccakR1csLogSize + keccakRefShape.heights.getD opSha3 0 = 32 := Cost.reference_flockLogN
  unfold streamBytes4
  rw [hD, hL, flockBytes_rec4_reference, h4, Cost.valuesBound_eq]

/-- **The block count of π1-rec4's run at the reference shape**: the setup's `5 · 2^18`, the prover's `2^47`, the
verifier's on streams of `2^14` bytes: at most `2^48`. -/
theorem totalCostK4_le (D : KDeployment) (hD : D.shape = keccakRefShape) (hiv : D.programIv.length ≤ 2 ^ 16) :
    setupCost D + (2 ^ 47 + verifierCost4 D (2 ^ 14)) ≤ 2 ^ 48 := by
  have h3 := Cost.reference_stackVars.2.2.1
  have ho := Cost.openCost_le
  have hivc : (163 + D.programIv.length) / 136 ≤ 163 + 2 ^ 16 := (Nat.div_le_self _ _).trans (by omega)
  unfold setupCost verifierCost4 ivCost walkCost4
  rw [hD, h3]
  norm_num
  omega

end Reference

/-! ## The experiment -/

open UniKeccakSound (keccakRefShape)

/-- **π1-rec4's experiment at `H = callKeccak256`, `W = rateSigma` makes at most `2^48` block calls** at the reference
shape (a program IV of at most `2^16` bytes). -/
theorem cost_expSigma (D : KDeployment) (hD : D.shape = keccakRefShape) (hiv : D.programIv.length ≤ 2 ^ 16)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (hfit : D.shape.RowsFit rows) :
    Common.QueryCostAtMost (expW4 callKeccak256 rateSigma callKeccakF1600 D input rows q) hashBlocks (2 ^ 48) := by
  have hP : CostP (uniProverRec4With callKeccak256 rateSigma callKeccakF1600 D input rows q)
      (uniProverCost4 D.shape D.programIv.length 6)
      fun o _ ↦ ∀ p, o = some p → p.stream.size ≤ streamBytes4 D.shape 6 := by
    have h := costP_proveRec4With D.programIv (honestTrace D input rows q) (by simp [honestTrace])
    have hr : (honestTrace D input rows q).rows.length = 6 := hfit.1
    rw [hr] at h
    exact h
  refine (?_ : Common.QueryCostAtMost _ hashBlocks (setupCost D + (2 ^ 47 + verifierCost4 D (2 ^ 14)))).mono
    (totalCostK4_le D hD hiv)
  unfold expW4
  refine Common.QueryCostAtMost.bind (Cost.cost_setupTreeKWithH D) fun tree ↦ ?_
  refine Prob.qc_bind_support (hP.toQC.mono (proverBlocks4_reference D hD hiv)) fun o ho ↦ ?_
  cases o with
  | none => trivial
  | some π =>
    have hs := CostP.mem_support hP _ ho π rfl
    rw [proverStream4_reference D hD] at hs
    exact cost_verifierWith4H D _ input π (2 ^ 14) (hs.trans (by norm_num))

/-- **`ExpCost4` at the reference shape**, `2^48` blocks. -/
theorem expCost4_reference (D : KDeployment) (hD : D.shape = keccakRefShape) (hiv : D.programIv.length ≤ 2 ^ 16) :
    ExpCost4 D (2 ^ 48) :=
  expCost4_of D fun input rows q hfit _ ↦ cost_expSigma D hD hiv input rows q hfit

end UniKeccakComplete.Rec4

/-- info: 'UniKeccakComplete.Rec4.expCost4_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.expCost4_reference
