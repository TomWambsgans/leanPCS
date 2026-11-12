-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π1-rec4's analogue of `Rec3ProbK.lean`
-- (`stagedU3_holds`, `uniCompletenessKeccakRec3_of_core`) and of `Rec3ProbExp.lean`'s `hashA_stagedU3`; uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the proof-of-work
-- miss probability `missProb`, `rpmError`, the weight calculus.
import UniKeccakComplete.K.Rec4Grind

/-!
# Completeness of π1-rec4, from named hypotheses

**`uniCompletenessKeccakRec4_of_core`**: π1-rec4's honest prover (`uniProverRec4RP`) is rejected with probability at
most

  `δ₄ = (2^22 − 1)/2^192 + (2^15/2^192 + εt) + 2^-304 + rpmError N`

from: the deterministic core (`CoreAccepts4`, `CoreFailsOnlyAtPow4`), the bad sets' counts (the main line's
`BadFpCard`, `BadTCard`), the point draw's freshness (`TQueryFresh4 D εt`), and, over π1-rec4's calls, the
experiment's block count `N ≤ 2^48` (`ExpCost4`) and its duplex discipline (`ExpDuplex4`), given a program IV of `32`
to `2^16` bytes. The pieces proved here:

* **Stage A** of the five-digest reading (`stagedU4`'s setup and `proverA4` at `hash5`) is leanerVM's two-call stage A
  read through `iota5` (`stagedU4_A_eq`), which hashes short inputs of other lengths than `32` and `112`
  (`hashS_stageA4`: the trees' `512`- and `64`-byte inputs, the IV's `91 + |IV|`, the seed's `80`), so it hashes
  `GoodL5` inputs (**`hashA_stagedU4`**);
* **the query count** of the five-digest reading is at most five per block of the experiment over π1-rec4's calls
  (`qc_tauW`), so at most `5 N ≤ 2^51` (**`totalQuery_stagedU4`**), and the grinding is below `2^-304`
  (`grinding_le51`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol.Compile.Rom (missProb implH implF simulateQ_queryH)
open UniStatement UniKeccak
open E2ECompleteness (ro HashOK hashOK_callKeccak256)
open UniKeccakComplete.Prob (GoodL BadT BadFpCard BadTCard ProverA firstInput ivTag_length len_digestBytes
  shapeBytes_length elementBytes24_length variantBytesK_length name_length)
open scoped ENNReal

set_option autoImplicit false

namespace UniKeccakComplete.Rec4

/-! ## Stage A -/

/-- **A Merkle tree** of rows of `64` words hashes `512`-byte leaves and `64`-byte nodes. -/
theorem hashOK_buildTreeP (P : Bytes → Prop) (h512 : ∀ m : Bytes, m.length = 512 → P m)
    (h64 : ∀ m : Bytes, m.length = 64 → P m) (height : ℕ) (word : LeanVM.Protocol.Compile.Word)
    (hw : ∀ p, (word p).length = 64) :
    HashOK P (LeanVM.Prover.buildTreeWithHash callKeccak256 height word) := by
  unfold LeanVM.Prover.buildTreeWithHash
  refine E2ECompleteness.HashOK.bind ?_ fun leaves ↦ E2ECompleteness.HashOK.bind ?_ fun _ ↦
    E2ECompleteness.HashOK.pure _ _
  · unfold LeanVM.Prover.leafDigestsWithHash
    refine E2ECompleteness.HashOK.arrayMapM _ (fun i ↦ hashOK_callKeccak256 (h512 _ ?_)) _
    rw [E2ECompleteness.length_flatMap_kBytes, hw]
  · suffices h : ∀ k (level : Array Digest),
        HashOK P (LeanVM.Prover.levelsWithHash callKeccak256 k level) from h _ _
    intro k
    induction k with
    | zero => intro level; exact E2ECompleteness.HashOK.pure _ _
    | succ k ih =>
      intro level
      unfold LeanVM.Prover.levelsWithHash
      refine E2ECompleteness.HashOK.bind ?_ fun up ↦ E2ECompleteness.HashOK.bind (ih up) fun _ ↦
        E2ECompleteness.HashOK.pure _ _
      unfold LeanVM.Prover.parentsWithHash
      refine E2ECompleteness.HashOK.arrayMapM _ (fun j ↦ hashOK_callKeccak256 (h64 _ ?_)) _
      rw [List.length_append, E2ECompleteness.length_digestBytes, E2ECompleteness.length_digestBytes]

/-- **What stage A hashes**: short inputs of other lengths than `32` and `112`. -/
def GoodS (m : Bytes) : Prop := Short m ∧ GoodL 112 m

theorem goodS_of_length {m : Bytes} (h : m.length = 512 ∨ m.length = 64 ∨ m.length = 80 ∨
    (113 ≤ m.length ∧ m.length < 2 ^ 20)) : GoodS m :=
  ⟨by unfold Short lenB; omega, by refine ⟨?_, ?_⟩ <;> omega⟩

theorem hashOK_commitWithHS (μ : ℕ) (stack : Array K) :
    HashOK GoodS (E2ECompleteness.commitWithH callKeccak256 μ stack) :=
  hashOK_buildTreeP GoodS (fun _ h ↦ goodS_of_length (Or.inl h)) (fun _ h ↦ goodS_of_length (Or.inr (Or.inl h)))
    _ _ (E2ECompleteness.length_stackWordFast μ 1 stack)

variable (D : KDeployment)

/-- leanerVM's two-call stage A: the setup's tree and the prover before the bus draw. -/
def stageA4 (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    OracleComp KeccakCalls (LeanVM.Prover.Tree × ProverA) := do
  let tree ← setupTreeKWithH callKeccak256 callKeccakF1600 D
  let a ← proverA4 callKeccak256 D input rows q
  return (tree, a)

theorem simulateQ_proverA4 {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    simulateQ impl (proverA4 callKeccak256 D input rows q) = proverA4 (implH impl) D input rows q := by
  simp only [proverA4, setupTreeOf, contractIvOf, seedOf, simulateQ_bind, simulateQ_pure,
    E2ECompleteness.simulateQ_commitWithH, simulateQ_queryH]

/-- **Stage A of the five-digest reading is leanerVM's read through `iota5`.** -/
theorem stagedU4_A_eq (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    (stagedU4 D input rows q).A = simulateQ iota5 (stageA4 D input rows q) := by
  rw [show (stagedU4 D input rows q).A = (do
      let tree ← setupTreeKWithH hash5 callKeccakF1600 D
      let a ← proverA4 hash5 D input rows q
      return (tree, a)) from rfl]
  simp only [stageA4, simulateQ_bind, simulateQ_pure, simulateQ_setupTreeKWithH, simulateQ_proverA4]
  rfl

/-- **leanerVM's two-call stage A hashes `GoodS` inputs** (a program IV of `32` to `2^16` bytes). -/
theorem hashS_stageA4 (hiv : D.programIv.length ≤ 2 ^ 16) (hpiv : 32 ≤ D.programIv.length)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) : HashOK GoodS (stageA4 D input rows q) := by
  simp only [stageA4, proverA4, setupTreeOf, setupTreeKWithH, contractIvOf, seedOf, bind_assoc, pure_bind]
  refine E2ECompleteness.HashOK.bind (hashOK_commitWithHS _ _) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_commitWithHS _ _) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_callKeccak256 (goodS_of_length (Or.inr (Or.inr (Or.inr ?_))))) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_callKeccak256 (goodS_of_length (Or.inr (Or.inr (Or.inl ?_))))) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_commitWithHS _ _) fun _ ↦ E2ECompleteness.HashOK.pure _ _
  · simp only [List.length_append, ivTag_length, len_digestBytes, shapeBytes_length, elementBytes24_length,
      variantBytesK_length, honestTrace]
    omega
  · simp [name_length, len_digestBytes, honestTrace]

/-- **Stage A of the five-digest reading hashes `GoodL5` inputs.** -/
theorem hashA_stagedU4 (hiv : D.programIv.length ≤ 2 ^ 16) (hpiv : 32 ≤ D.programIv.length)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) : HashOK GoodL5 (stagedU4 D input rows q).A := by
  rw [stagedU4_A_eq]
  exact hashOK_iota5 (fun _ h ↦ h.1) (hashS_stageA4 D hiv hpiv input rows q)

/-! ## The query count -/

theorem qc_scale {α : Type} {X : OracleComp KeccakCallsW α} {N : ℕ} (c : ℕ)
    (h : Common.QueryCostAtMost X hashBlocksW N) : Common.QueryCostAtMost X (fun t ↦ c * hashBlocksW t) (c * N) := by
  induction X using OracleComp.inductionOn generalizing N with
  | pure a => trivial
  | query_bind t k ih =>
    rw [Common.isWeightBound_query_bind_iff] at h ⊢
    refine ⟨Nat.mul_le_mul_left c h.1, fun u ↦ ?_⟩
    rw [← Nat.mul_sub]
    exact ih u (h.2 u)

theorem qc_rate5 (x : Bytes) : Common.QueryCostAtMost (rate5 x) (fun _ ↦ 1) 5 := by
  unfold rate5
  exact Common.QueryCostAtMost.bind (b := 4) (Common.isWeightBound_query _ _) fun _ ↦
    Common.QueryCostAtMost.bind (b := 3) (Common.isWeightBound_query _ _) fun _ ↦
    Common.QueryCostAtMost.bind (b := 2) (Common.isWeightBound_query _ _) fun _ ↦
    Common.QueryCostAtMost.bind (b := 1) (Common.isWeightBound_query _ _) fun _ ↦
    Common.QueryCostAtMost.bind (b := 0) (Common.isWeightBound_query _ _) fun _ ↦ trivial

/-- **The five-digest reading makes at most five queries per block.** -/
theorem qc_tauW {α : Type} {X : OracleComp KeccakCallsW α} {N : ℕ} (h : Common.QueryCostAtMost X hashBlocksW N) :
    Common.QueryCostAtMost (simulateQ tauW X) (fun _ ↦ 1) (5 * N) := by
  refine isWeightBound_simulateQ' tauW (fun t ↦ 5 * hashBlocksW t) (fun _ ↦ 1) (fun t ↦ ?_) (qc_scale 5 h)
  rcases t with x | s
  · exact (qc_rate5 x).mono (by simp only [hashBlocksW]; omega)
  · exact (Common.isWeightBound_query (spec := KeccakCalls) (fun _ ↦ 1) (.inr s)).mono
      (by simp only [hashBlocksW]; omega)

theorem isTotalQueryBound_of_unit {α : Type} {oa : OracleComp KeccakCalls α} {N : ℕ}
    (h : Common.QueryCostAtMost oa (fun _ ↦ 1) N) : IsTotalQueryBound oa N := by
  induction oa using OracleComp.inductionOn generalizing N with
  | pure x => trivial
  | query_bind t mx ih =>
    obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).1 h
    have ht' : 1 ≤ N := ht
    have hk' : ∀ u, Common.QueryCostAtMost (mx u) (fun _ ↦ 1) (N - 1) := hk
    exact isTotalQueryBound_query_bind_iff.2 ⟨by omega, fun u ↦ ih u (hk' u)⟩

/-- **The block count of π1-rec4's experiment over its calls** (named). -/
def ExpCost4 (N : ℕ) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation KeccakFlock.keccakFlockSpec rows input q →
    Common.QueryCostAtMost (expW4 hashW callRate callFW D input rows q) hashBlocksW N

/-- **The duplex discipline of π1-rec4's experiment over its calls** (named). -/
def ExpDuplex4 : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation KeccakFlock.keccakFlockSpec rows input q → DuplexW (expW4 hashW callRate callFW D input rows q) []

/-- **The point draw's freshness for π1-rec4** (named; `Rec4TFresh.lean` proves it at the reference shape). -/
def TQueryFresh4 (εt : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation KeccakFlock.keccakFlockSpec rows input q →
    Pr{let p ← (simulateQ ro (stagedU4 D input rows q).pre).run ∅}[
      p.2 (.inl ((stagedU4 D input rows q).tin p.1.1)) ≠ none] ≤ εt

/-- **The staged run's query count**: at most `5 N`. -/
theorem totalQuery_stagedU4 {N : ℕ} (hcost : ExpCost4 D N) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation KeccakFlock.keccakFlockSpec rows input q) :
    IsTotalQueryBound (stagedU4 D input rows q).run (5 * N) := by
  have h := isTotalQueryBound_of_unit (qc_tauW (hcost input rows q hfit hrel))
  rw [simulateQ_tauW_expWW, expW4_eq_staged4] at h
  exact (isQueryBound_map_iff _ _ _ _ _).1 h

/-! ## The end -/

/-- **π1-rec4's staged run's conditions at `deltaK`'s numbers**, from the named hypotheses. -/
theorem stagedU4_good {N : ℕ} {εt : ℝ≥0∞} (hacc : CoreAccepts4 D) (hpow : CoreFailsOnlyAtPow4 D)
    (hcost : ExpCost4 D N) (hN : N ≤ 2 ^ 48)
    (hbad : BadFpCard D (2 ^ 22 - 1)) (hbadT : BadTCard D.shape (2 ^ 15)) (htf : TQueryFresh4 D εt)
    (hiv : D.programIv.length ≤ 2 ^ 16) (hpiv : 32 ≤ D.programIv.length)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation KeccakFlock.keccakFlockSpec rows input q) :
    (stagedU4 D input rows q).Good (BadFp (honestTrace D input rows q)) (BadT D.shape) (2 ^ 22 - 1) (2 ^ 15)
      εt ((2 : ℝ≥0∞)⁻¹ ^ 304) := by
  refine ⟨fun a ↦ Prob.firstInput_length hfit.1 a.2, hashA_stagedU4 D hiv hpiv input rows q,
    hbad input rows q hfit hrel, hbadT, htf input rows q hfit hrel, ?_⟩
  refine (rejectGood4 D hacc hpow input rows q hfit hrel (totalQuery_stagedU4 D hcost input rows q hfit hrel)).trans ?_
  calc ((5 * N : ℕ) : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel
      ≤ ((2 ^ 51 : ℕ) : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel := by
        gcongr
        omega
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 304 := grinding_le51

/-- **Completeness of the Keccak π1 at π1-rec4's shape**, from the named hypotheses. -/
theorem uniCompletenessKeccakRec4_of_core {N : ℕ} {εt : ℝ≥0∞} (hacc : CoreAccepts4 D)
    (hpow : CoreFailsOnlyAtPow4 D) (hcost : ExpCost4 D N) (hN : N ≤ 2 ^ 48) (hdup : ExpDuplex4 D)
    (hbad : BadFpCard D (2 ^ 22 - 1)) (hbadT : BadTCard D.shape (2 ^ 15)) (htf : TQueryFresh4 D εt)
    (hiv : D.programIv.length ≤ 2 ^ 16) (hpiv : 32 ≤ D.programIv.length) :
    UniCompletenessKeccakRec4 KeccakFlock.keccakFlockSpec D (uniProverRec4RP D)
      (((2 ^ 22 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 + (((2 ^ 15 : ℕ) : ℝ≥0∞) / 2 ^ 192 + εt) + (2 : ℝ≥0∞)⁻¹ ^ 304 +
        rpmError N) :=
  uniCompletenessKeccakRec4_of_staged4 (by omega) hcost hdup fun input rows q hfit hrel ↦
    ⟨stagedU4 D input rows q, _, _, expW4_eq_staged4 D input rows q,
      stagedU4_good D hacc hpow hcost hN hbad hbadT htf hiv hpiv input rows q hfit hrel⟩

end UniKeccakComplete.Rec4

/-- info: 'UniKeccakComplete.Rec4.uniCompletenessKeccakRec4_of_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.uniCompletenessKeccakRec4_of_core
