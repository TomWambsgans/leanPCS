-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- The verifier's and the setup's part of `formal/EndToEnd/Completeness/E2ECompleteness/PcsCost.lean` (at the
-- protocol of `f96a7938`: its generic calculus `QC`, `cost_runWithHash`, `qc_buildTree`, `qc_openAll` copied), for
-- the deployed protocol's verifier (`Soundness/PcsVH.lean`). Uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the block
-- cost `hashBlocks` and the weight calculus `Common.QueryCostAtMost`; the cost calculus of the verifier's programs
-- (`Prog.Costs`, `costs_verifyStackedOpening`, `ladder_cost`, `costHeight`, `whirBound`); the widths of WHIR's
-- commitments (`WidthsLE`, `widthsLE_verifyWhir`); mumbai's `allQ_run`, `allQ_openAll` (`Rpm/Cost.lean`).
import Soundness.PcsVH
import E2ECompleteness.Chain
import Common.Lemmas
import Common.Lanes
import LeanVM.Protocol.Rpm.Cost
import LeanVM.Protocol.Verifier.Cost
import LeanVM.Protocol.EndToEnd.Sound.Moves

/-!
# The block count of the deployed verifier and setup

The cost is weighted (`hashBlocks`: a Keccak-256 of `n` bytes costs `⌊n / 136⌋ + 1`, a Keccak-f[1600] one), as in
the previous protocol's `Cost.lean`:

* **the setup's commitment** (`qc_commitmentWithH`): a tree of `5 · 2^(μ - 5)` blocks and `μ` out-of-domain hashes
  (`comCost`);
* **the verifier's run** (`cost_runWithHash`): at most `3 · n` blocks for a program of `n` quarters;
* **the verifier** (`cost_verifyWithH`): the reduction's six hashes (`8` blocks: the label `136` bytes, the
  commitments' inputs `128`, the values' `160`), then the three openings (`vOpen` each: the IV of at most
  `82 + 24 · 28` bytes, the seed, the root's absorptions, the out-of-domain point, WHIR).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Rpm (hashBlocks)
open LeanVM.Prover (Tree Script)
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript

set_option autoImplicit false

namespace PcsKS.VH

open E2ECompleteness (length_digestBytes)

namespace Cost

/-! ## Helpers -/

theorem length_scalarBytes (x : E) : (scalarBytes x).length = 32 := by
  simp [scalarBytes, beBytes, wordBytes]

theorem length_flatMap_scalarBytes (l : List E) : (l.flatMap scalarBytes).length = 32 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, length_scalarBytes, List.length_cons]
    ring

theorem foldl_absorb (l : List E) (c : Chain) : l.foldl Chain.absorb c = ⟨c.state, c.pending ++ l⟩ := by
  induction l generalizing c with
  | nil => simp
  | cons x l ih => simp [List.foldl_cons, ih, Chain.absorb, List.append_assoc]


/-- At most `n` block calls. -/
abbrev QC {α : Type} (X : OracleComp KeccakCalls α) (n : ℕ) : Prop :=
  Common.QueryCostAtMost X hashBlocks n

/-! ## The calculus -/

theorem qc_pure {α : Type} (a : α) (n : ℕ) : QC (pure a : OracleComp KeccakCalls α) n := trivial

theorem QC.mono {α : Type} {X : OracleComp KeccakCalls α} {a b : ℕ} (h : QC X a) (hab : a ≤ b) :
    QC X b :=
  Common.QueryCostAtMost.mono h hab

theorem QC.bind {α β : Type} {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β}
    {a b : ℕ} (hX : QC X a) (hf : ∀ x, QC (f x) b) : QC (X >>= f) (a + b) :=
  Common.QueryCostAtMost.bind hX hf

theorem QC.bind_le {α β : Type} {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β}
    {a b c : ℕ} (hX : QC X a) (hf : ∀ x, QC (f x) b) (h : a + b ≤ c) : QC (X >>= f) c :=
  (hX.bind hf).mono h

theorem QC.map {α β : Type} {X : OracleComp KeccakCalls α} (f : α → β) {a : ℕ} (hX : QC X a) :
    QC (f <$> X) a :=
  Common.isWeightBound_map f hX

theorem qc_F (s : KeccakState) : QC (callKeccakF1600 s) 1 :=
  Common.isWeightBound_query hashBlocks (Sum.inr s)

theorem qc_H (x : Bytes) : QC (callKeccak256 x) (x.length / 136 + 1) :=
  Common.isWeightBound_query hashBlocks (Sum.inl x)

/-- A hash of at most `136 · k - 1` bytes costs at most `k` blocks. -/
theorem qc_H_le {x : Bytes} {k : ℕ} (hx : x.length < 136 * k) : QC (callKeccak256 x) k :=
  (qc_H x).mono (by omega)

/-! ## The sponge -/

theorem qc_duplex (sp : Sponge) : QC (duplex callKeccakF1600 sp) 1 :=
  ((qc_F _).bind fun _ ↦ qc_pure _ 0).mono le_rfl

theorem qc_absorb (sp : Sponge) (x : E) (tag : ℕ) :
    QC (Compile.absorb callKeccakF1600 sp x tag) 1 := by
  unfold Compile.absorb
  split
  · exact (qc_duplex sp).bind_le (fun _ ↦ qc_pure _ 0) le_rfl
  · exact (qc_pure _ 1).bind_le (fun _ ↦ qc_pure _ 0) le_rfl

theorem qc_squeeze (sp : Sponge) : QC (squeeze callKeccakF1600 sp) 1 :=
  (qc_duplex sp).bind_le (fun _ ↦ qc_pure _ 0) le_rfl

theorem qc_powStepM (sp : Sponge) (n : E) : QC (LeanVM.Prover.powStepM callKeccakF1600 sp n) 2 :=
  (qc_absorb _ _ _).bind_le (fun _ ↦ qc_squeeze _) le_rfl

theorem qc_searchM (bits : ℕ) (sp : Sponge) :
    ∀ (count n : ℕ), QC (LeanVM.Prover.searchM callKeccakF1600 bits sp n count) (2 * count)
  | 0, _ => trivial
  | count + 1, n => by
    simp only [LeanVM.Prover.searchM]
    refine (qc_powStepM _ _).bind_le (fun r ↦ ?_) (show 2 + 2 * count ≤ 2 * (count + 1) by omega)
    split
    · exact qc_pure _ _
    · exact qc_searchM bits sp count (n + 1)

theorem qc_findNonceM (bits : ℕ) (sp : Sponge) (fuel : ℕ) :
    QC (LeanVM.Prover.findNonceM callKeccakF1600 bits sp fuel) (2 * fuel) := by
  unfold LeanVM.Prover.findNonceM
  split
  · exact qc_pure _ _
  · exact qc_searchM _ _ _ _

/-! ## Merkle trees -/

theorem qc_listMapM {β γ : Type} (f : β → OracleComp KeccakCalls γ) (c : ℕ)
    (hf : ∀ a, QC (f a) c) : ∀ l : List β, QC (l.mapM f) (l.length * c)
  | [] => by rw [List.mapM_nil]; exact qc_pure _ _
  | a :: l => by
    rw [List.mapM_cons, List.length_cons]
    exact (hf a).bind_le (fun _ ↦ (qc_listMapM f c hf l).bind_le (fun _ ↦ qc_pure _ 0) le_rfl)
      (by rw [Nat.succ_mul]; omega)

theorem qc_arrayMapM {β γ : Type} (f : β → OracleComp KeccakCalls γ) (c : ℕ)
    (hf : ∀ a, QC (f a) c) (xs : Array β) : QC (xs.mapM f) (xs.size * c) := by
  rw [Array.mapM_eq_mapM_toList, ← Array.length_toList]
  exact (qc_listMapM f c hf _).map _

theorem qc_parents (level : Array Digest) (n : ℕ) :
    QC (LeanVM.Prover.parentsWithHash callKeccak256 level n) n := by
  unfold LeanVM.Prover.parentsWithHash
  refine (qc_arrayMapM _ 1 (fun j ↦ qc_H_le ?_) _).mono (by simp)
  rw [List.length_append, length_digestBytes, length_digestBytes]
  omega

theorem qc_levels : ∀ (k : ℕ) (level : Array Digest),
    QC (LeanVM.Prover.levelsWithHash callKeccak256 k level) (2 ^ k)
  | 0, _ => qc_pure _ _
  | k + 1, level => by
    simp only [LeanVM.Prover.levelsWithHash]
    exact (qc_parents _ _).bind_le (fun _ ↦ (qc_levels k _).bind_le (fun _ ↦ qc_pure _ 0)
      le_rfl) (by rw [pow_succ]; omega)

theorem length_flatMap_kBytes (row : List K) : (row.flatMap kBytes).length = 8 * row.length := by
  induction row with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    simp only [kBytes, LeanVM.Rpm.wordBytes_len]
    ring

/-- **A Merkle tree** of rows of fewer than `136 · c` bytes: `2^height` leaves of at most `c`
blocks, fewer than `2^height` nodes of one. -/
theorem qc_buildTree (height : ℕ) (word : Word) (c : ℕ)
    (hw : ∀ p, 8 * (word p).length < 136 * c) :
    QC (LeanVM.Prover.buildTreeWithHash callKeccak256 height word) ((c + 1) * 2 ^ height) := by
  unfold LeanVM.Prover.buildTreeWithHash LeanVM.Prover.leafDigestsWithHash
  refine (qc_arrayMapM _ c (fun i ↦ qc_H_le ?_) _).bind_le (fun _ ↦ (qc_levels _ _).bind_le
    (fun _ ↦ qc_pure _ 0) le_rfl) (by rw [Array.size_range]; ring_nf; omega)
  rw [length_flatMap_kBytes]
  exact hw i

theorem length_stackWordFast (μ R : ℕ) (stack : Array K) (p : ℕ) :
    (LeanVM.Prover.stackWordFast μ R stack p).length = 64 := by
  unfold LeanVM.Prover.stackWordFast LeanVM.Prover.stackWordFast.stackWordOf
  split <;> simp

/-- A table's tree: `2^(μ − 5)` leaves of `64` words (`4` blocks) and its nodes. -/
theorem qc_commitWithH (μ : ℕ) (stack : Array K) :
    QC (commitWithH callKeccak256 μ stack) (5 * 2 ^ (μ - 6 + 1)) :=
  qc_buildTree _ _ 4 fun p ↦ by rw [length_stackWordFast]; omega

/-! ## The out-of-domain points and the commitments -/

theorem length_oodInput (n : ℕ) (root : Digest) (j : ℕ) : (oodInput n root j).length = 46 := by
  have h11 : oodTag.length = 11 := by decide +kernel
  simp only [oodInput, List.length_append, h11, length_digestBytes, List.length_cons,
    List.length_nil]

/-- **The out-of-domain point** of `n` coordinates: `n` hashes of `46` bytes. -/
theorem qc_oodPointWithH (n : ℕ) (root : Digest) : QC (oodPointWithH callKeccak256 n root) n := by
  unfold oodPointWithH
  refine (qc_listMapM _ 1 (fun j ↦ (qc_H_le (k := 1) ?_).bind_le (fun _ ↦ qc_pure _ 0) le_rfl)
    _).mono (by simp)
  rw [length_oodInput]; omega

/-- The block cost of a table's commitment on `2^μ` words: its tree and its out-of-domain point. -/
def comCost (μ : ℕ) : ℕ := 5 * 2 ^ (μ - 6 + 1) + μ

theorem qc_commitmentWithH (μ : ℕ) (table : Array K) :
    QC (commitmentWithH callKeccak256 μ table) (comCost μ) := by
  unfold commitmentWithH comCost
  exact (qc_commitWithH _ _).bind_le (fun _ ↦ (qc_oodPointWithH _ _).bind_le
    (fun _ ↦ qc_pure _ 0) le_rfl) le_rfl

/-! ## The honest script commits rows of at most `192` words -/

/-- Every matrix the script commits has rows of at most `W` words. -/
theorem qc_climb : ∀ (node : Digest) (q : ℕ) (ss : List Digest),
    QC (climbWithHash callKeccak256 node q ss) ss.length
  | _, _, [] => qc_pure _ _
  | node, q, s :: ss => by
    simp only [climbWithHash, List.length_cons]
    have hn (a b : Digest) : QC (callKeccak256 (digestBytes a ++ digestBytes b)) 1 :=
      qc_H_le (by rw [List.length_append, length_digestBytes, length_digestBytes]; omega)
    rw [Nat.add_comm]
    split <;> exact (hn _ _).bind fun _ ↦ qc_climb _ _ ss

/-- One opening: a leaf of at most `192` words (`12` blocks) and its path. -/
theorem qc_openOne (root : Digest) (height width q : ℕ) (o : Compile.Opening)
    (hw : width ≤ 192) :
    QC (openOneWithHash callKeccak256 root height width q o) (12 + height) := by
  unfold openOneWithHash
  split
  · rename_i h
    refine (qc_H_le (k := 12) ?_).bind_le (fun _ ↦ (qc_climb _ _ _).bind_le
      (fun _ ↦ qc_pure _ 0) le_rfl) (by rw [h.2]; omega)
    rw [length_flatMap_kBytes, h.1]
    omega
  · exact qc_pure _ _

theorem qc_openAll (root : Digest) (height width : ℕ) (hw : width ≤ 192) :
    ∀ (ps : List ℕ) (os : List Compile.Opening),
      QC (openAllWithHash callKeccak256 root height width ps os) (ps.length * (12 + height))
  | [], _ => qc_pure _ _
  | _ :: _, [] => qc_pure _ _
  | q :: qs, o :: os => by
    simp only [openAllWithHash, List.length_cons]
    refine (qc_openOne root height width q o hw).bind_le (b := qs.length * (12 + height))
      (fun b ↦ ?_) (by rw [Nat.succ_mul]; omega)
    split
    · exact (qc_openAll root height width hw qs os).bind_le (fun _ ↦ qc_pure _ 0) le_rfl
    · exact qc_pure _ _

/-- **The verifier's run**, of a program of cost `n` quarters at height `height` whose
commitments have width at most `192`, from roots of height at most `12 · height` and width at
most `192`, makes at most `3 · n` block calls. -/
theorem cost_runWithHash (height : ℕ) {α : Type} :
    ∀ (P : Prog α) (s : ProgState) (n : ℕ) (Q : α → Prop), P.Costs height n Q →
      LeanVM.Rpm.WidthsLE LeanVM.Rpm.maxWidth P →
      (∀ r ∈ s.roots, r.2.1 ≤ 12 * height ∧ r.2.2 ≤ 192) →
      QC (runWithHash callKeccak256 callKeccakF1600 P s) (3 * n)
  | .ret _, _, _, _, _, _, _ => qc_pure _ _
  | .fail, _, _, _, _, _, _ => qc_pure _ _
  | .read k, s, n, Q, hp, hW, hr => by
    simp only [runWithHash]
    split
    · exact qc_pure _ _
    · exact (qc_absorb _ _ _).bind_le (fun sp ↦ cost_runWithHash height _ _ (n - 1) Q (hp.2 _)
        (hW _) hr) (by have := hp.1; omega)
  | .sample k, s, n, Q, hp, hW, hr => by
    simp only [runWithHash]
    refine (qc_squeeze _).bind_le (b := 3 * (n - 4)) (fun r ↦ ?_) (by have := hp.1; omega)
    obtain ⟨c, sp⟩ := r
    exact cost_runWithHash height _ _ (n - 4) Q (hp.2 _) (hW _) hr
  | .grind bits k, s, n, Q, hp, hW, hr => by
    simp only [runWithHash]
    split
    · exact qc_pure _ _
    · refine (qc_absorb _ _ _).bind_le (fun sp ↦ (qc_squeeze _).bind_le (b := 3 * (n - 5))
        (fun r ↦ ?_) le_rfl) (by have := hp.1; omega)
      obtain ⟨c, sp'⟩ := r
      dsimp only
      split
      · exact cost_runWithHash height _ _ (n - 5) Q hp.2 hW hr
      · exact qc_pure _ _
  | .commit ht w k, s, n, Q, hp, hW, hr => by
    simp only [runWithHash]
    split
    · refine (qc_absorb _ _ _).bind_le (fun sp ↦ (qc_absorb _ _ _).bind_le (b := 3 * (n - 2))
        (fun sp' ↦ ?_) le_rfl) (by have := hp.2.1; omega)
      split
      · refine cost_runWithHash height _ _ (n - 2) Q hp.2.2 hW.2 fun r hr' ↦ ?_
        rcases List.mem_append.mp hr' with h | h
        · exact hr r h
        · simp only [List.mem_singleton] at h
          subst h
          exact ⟨by have := hp.1; dsimp only; omega, hW.1⟩
      · exact qc_pure _ _
    · exact qc_pure _ _
  | .query i ps k, s, n, Q, hp, hW, hr => by
    simp only [runWithHash]
    split
    · exact qc_pure _ _
    · next root h' w hi =>
      have hrw := hr _ (List.mem_of_getElem? hi)
      refine (qc_openAll root h' w hrw.2 ps s.openings).bind_le
        (b := 3 * (n - Prog.openCost height ps.length)) (fun o ↦ ?_) ?_
      · split
        · exact cost_runWithHash height _ _ _ Q (hp.2 _) (hW _) hr
        · exact qc_pure _ _
      · have h1 := hp.1
        have hm : ps.length * h' ≤ ps.length * (12 * height) := Nat.mul_le_mul_left _ hrw.1
        have e1 : ps.length * (12 + h') = 12 * ps.length + ps.length * h' := by ring
        have e2 : ps.length * (12 * height) = 12 * (ps.length * height) := by ring
        have e3 : Prog.openCost height ps.length = 4 * ps.length + 4 * (ps.length * height) := by
          unfold Prog.openCost; ring
        rw [e1]
        rw [e2] at hm
        rw [e3] at h1 ⊢
        omega

/-- The stacked opening's cost in quarters. -/
abbrev whirQ : ℕ := 4 + (2 + whirBound)

/-- The stacked opening's cost: the batching challenge and WHIR, at height `26` (mumbai's
`costs_verifyStackedOpening` with `ladder_cost`). -/
theorem costs_vso (logN R : ℕ) (claims : List StackClaim) :
    Prog.Costs costHeight (verifyStackedOpening logN R claims) whirQ fun _ ↦ True :=
  costs_verifyStackedOpening (height := costHeight) logN R claims whirBound fun levels h ↦
    ⟨(ladder_cost _ _ levels h).1, (ladder_cost _ _ levels h).2.2.1,
      (ladder_cost _ _ levels h).2.2.2⟩

/-- The stacked opening's commitments have width at most `192` (mumbai's
`widthsLE_verifyWhir`). -/
theorem widthsLE_vso (logN R : ℕ) (claims : List StackClaim) :
    LeanVM.Rpm.WidthsLE LeanVM.Rpm.maxWidth (verifyStackedOpening logN R claims) := by
  rw [verifyStackedOpening_eq_target]
  exact LeanVM.Rpm.WidthsLE.seq (LeanVM.Rpm.WidthsLE.of_moves (g := fun _ ↦ True)
    LeanVM.Protocol.EndToEnd.Sound.MovesOK.sampleE) fun _ ↦ LeanVM.Rpm.widthsLE_verifyWhir _ _ _ _

/-! ## The openings' IVs -/

theorem length_elementBytes (x : E) : (elementBytes x).length = 24 := by
  simp [elementBytes, beBytes, LeanVM.Rpm.wordBytes_len]

theorem length_flatMap_elementBytes (l : List E) :
    (l.flatMap elementBytes).length = 24 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, length_elementBytes, List.length_cons]
    ring

/-- `PCS_claim`: `82 + 24 · n` bytes. -/
theorem length_pcsClaimBytes (c : Commitment) (claim : Claim) :
    (pcsClaimBytes c claim).length = 82 + 24 * claim.point.length := by
  simp only [pcsClaimBytes, List.length_append, List.length_cons, List.length_nil,
    length_digestBytes, length_elementBytes, length_flatMap_elementBytes]
  omega

/-- The opening's sponge: the IV's hash and one permutation. -/
theorem qc_pcsSpongeWithH (c : Commitment) (claim : Claim) (B : ℕ)
    (hB : 82 + 24 * claim.point.length < 136 * B) :
    QC (pcsSpongeWithH callKeccak256 callKeccakF1600 c claim) (B + 1) := by
  unfold pcsSpongeWithH
  refine (qc_H_le (k := B) ?_).bind_le (fun iv ↦ (qc_F _).bind_le (fun _ ↦ qc_pure _ 0) le_rfl)
    le_rfl
  rw [length_pcsClaimBytes]
  exact hB

/-- The verifier's cost of one opening: its IV (`6` blocks), its seed's permutation, the root's two
absorptions, the out-of-domain point (at most `28` hashes) and the run. -/
def vOpen : ℕ := 6 + 1 + 2 + 28 + 3 * whirQ

/-- **The verifier's opening**: the claim has at most `maxVars = 28` coordinates, or it is rejected
at once. -/
theorem cost_pcsOpeningWithH (c : Commitment) (claim : Claim) (proof : Compile.Proof) :
    QC (pcsOpeningWithH callKeccak256 callKeccakF1600 c claim proof) vOpen := by
  unfold pcsOpeningWithH
  by_cases hn : minVars ≤ claim.point.length ∧ claim.point.length ≤ maxVars
  · simp only [hn, and_self, ↓reduceIte]
    have hn' : claim.point.length ≤ 28 := hn.2
    refine (qc_pcsSpongeWithH c claim 6 (by omega)).bind_le (b := 2 + (28 + 3 * whirQ))
      (fun sp ↦ ?_) (by unfold vOpen; omega)
    split
    · refine (qc_absorb _ _ _).bind_le (fun sp ↦ (qc_absorb _ _ _).bind_le
        (b := 28 + 3 * whirQ) (fun sp ↦ ?_) le_rfl) (by omega)
      split
      · refine ((qc_oodPointWithH _ _).mono hn').bind_le (b := 3 * whirQ) (fun z ↦ ?_) le_rfl
        refine (cost_runWithHash costHeight _ _ _ _ (costs_vso _ _ _) (widthsLE_vso _ _ _)
          ?_).bind_le (b := 0) (fun r ↦ ?_) (by omega)
        · intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          refine ⟨?_, show 2 ^ laneFold ≤ 192 by decide⟩
          show claim.point.length - laneFold + logInvRate ≤ 12 * costHeight
          simp only [laneFold, logInvRate, costHeight]
          omega
        · split <;> exact qc_pure _ _
      · exact qc_pure _ _
    · exact qc_pure _ _
  · simp only [hn, ↓reduceIte]
    exact qc_pure _ _

/-- The verifier's openings, one after another. -/
theorem cost_checkAllWithH : ∀ l : List (Commitment × Claim × Compile.Proof),
    QC (checkAllWithH callKeccak256 callKeccakF1600 l) (l.length * vOpen)
  | [] => qc_pure _ _
  | (c, claim, proof) :: rest => by
    simp only [checkAllWithH, List.length_cons]
    refine (cost_pcsOpeningWithH c claim proof).bind_le (b := rest.length * vOpen)
      (fun b ↦ ?_) (by rw [Nat.succ_mul]; omega)
    split
    · exact qc_pure _ _
    · exact cost_checkAllWithH rest

/-- **The prover's opening**: its IV (at most `B` blocks), its seed's permutation, the root's two
absorptions, the out-of-domain point (at most `v` hashes), and the runner on the stacked opening at
height `26` from the honest script. -/
theorem length_label (index : Commitment) (stmt : Statement) : (label index stmt).length = 136 := by
  simp only [label, List.length_append, length_digestBytes, length_elementBytes,
    Vector.length_toList]
  have h16 : protocolName.length = 16 := by decide +kernel
  omega

/-- The three claims' points have at most `v` coordinates. -/
def ClaimsLen (v : ℕ) (cl : Claims) : Prop :=
  cl.witness.point.length ≤ v ∧ cl.wiring.point.length ≤ v ∧ cl.copy.point.length ≤ v

/-- What the reduction may return: claims whose points have at most `m + 4` coordinates. -/
def RedOK (logRows : ℕ) (o : Option Reduced) : Prop :=
  ∀ r, o = some r → ClaimsLen (cellVars logRows + 4) r.claims

/-- **The claims' points**: `W`'s and the wiring's `m` coordinates, `T`'s `m + 4`. -/
theorem claimsAt_len {logRows : ℕ} {stmt : Statement} {α β μ t ρ : E} {v : Vector E 3}
    {next : E} {cl : Claims} (h : claimsAt logRows stmt α β μ t ρ v next = some cl) :
    ClaimsLen (cellVars logRows + 4) cl := by
  obtain ⟨h1, h2, h3⟩ := claimsAt_lengths h
  exact ⟨by omega, by omega, by omega⟩

theorem redOK_none (logRows : ℕ) : RedOK logRows none := fun _ h ↦ by cases h

theorem redOK_map {logRows : ℕ} {stmt : Statement} {α β μ t ρ : E} {a : Vector E 3}
    {next : E} (cs : Commitments) :
    RedOK logRows ((claimsAt logRows stmt α β μ t ρ a next).map
      fun claims ↦ (⟨cs, claims⟩ : Reduced)) := by
  intro r hr
  rcases hc : claimsAt logRows stmt α β μ t ρ a next with _ | cl
  · rw [hc] at hr
    cases hr
  · rw [hc] at hr
    cases hr
    exact claimsAt_len hc

/-- A commitment read adds its three scalars to the pending ones. -/
theorem readCommitment_pending {c c' : Chain} {s : CommitmentScalars} {com : Commitment}
    (h : readCommitment c s = some (com, c')) :
    c'.state = c.state ∧ c'.pending.length = c.pending.length + 3 := by
  unfold readCommitment at h
  rcases hr : rootOfHalves s.root with _ | r
  · rw [hr] at h
    cases h
  · rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [Chain.absorb]

theorem length_squeezeIn (c : Chain) :
    (digestBytes c.state ++ c.pending.flatMap scalarBytes).length = 32 + 32 * c.pending.length := by
  rw [List.length_append, length_digestBytes, length_flatMap_scalarBytes]

/-- **The reduction's transcript**, then a continuation charged only at what the reduction may
return: the label (`136` bytes, two blocks), `α` after three scalars (`128` bytes), `β`, `μ`, `t`
after three scalars (`128` bytes), `ρ` after four values (`160` bytes, two blocks). -/
theorem qc_reduceWithH_bind {β : Type} (logRows : ℕ) (index : Commitment) (stmt : Statement)
    (p : ReductionProof) (f : Option Reduced → OracleComp KeccakCalls β) (b : ℕ)
    (hf : ∀ o, RedOK logRows o → QC (f o) b) :
    QC (reduceWithH callKeccak256 logRows index stmt p >>= f) (8 + b) := by
  by_cases hs : Supported logRows
  · simp only [reduceWithH, hs, not_true_eq_false, ↓reduceIte, startWithH, squeezeWithH,
      bind_assoc, pure_bind]
    refine (qc_H_le (k := 2) ?_).bind_le (b := 6 + b) (fun s₀ ↦ ?_) (by omega)
    · rw [length_label]; omega
    split
    next w c₁ hc₁ =>
      have e₁ := (readCommitment_pending hc₁).2
      simp only [bind_assoc]
      refine (qc_H_le (k := 1) ?_).bind_le (b := 5 + b) (fun s₁ ↦ ?_) (by omega)
      · rw [length_squeezeIn, e₁]; simp
      refine (qc_H_le (k := 1) ?_).bind_le (b := 4 + b) (fun s₂ ↦ ?_) (by omega)
      · simp [length_digestBytes]
      refine (qc_H_le (k := 1) ?_).bind_le (b := 3 + b) (fun s₃ ↦ ?_) (by omega)
      · simp [length_digestBytes]
      split
      next h c₂ hc₂ =>
        have e₂ := (readCommitment_pending hc₂).2
        simp only [bind_assoc]
        refine (qc_H_le (k := 1) ?_).bind_le (b := 2 + b) (fun s₄ ↦ ?_) (by omega)
        · rw [length_squeezeIn, e₂]; simp
        refine (qc_H_le (k := 2) ?_).bind_le (b := b) (fun s₅ ↦ ?_) (by omega)
        · rw [length_squeezeIn]
          simp only [Chain.absorb, foldl_absorb, List.length_append, List.nil_append,
            Vector.length_toList, List.length_cons, List.length_nil]
          omega
        rw [pure_bind]
        exact hf _ (redOK_map _)
      next => rw [pure_bind]; exact (hf none (redOK_none _)).mono (by omega)
    next => rw [pure_bind]; exact (hf none (redOK_none _)).mono (by omega)
  · simp only [reduceWithH, hs, not_false_eq_true, ↓reduceIte, pure_bind]
    exact (hf none (redOK_none _)).mono (by omega)

/-! ## The verifier -/

/-- **The verifier**: the reduction, then the three openings. -/
theorem cost_verifyWithH (logRows : ℕ) (index : Commitment) (stmt : Statement)
    (proof : PcsQuotient.Proof) :
    QC (verifyWithH callKeccak256 callKeccakF1600 logRows index stmt proof) (8 + 3 * vOpen) := by
  unfold verifyWithH
  refine qc_reduceWithH_bind _ _ _ _ _ _ fun o _ ↦ ?_
  split
  · exact qc_pure _ _
  · exact (cost_checkAllWithH _).mono (by simp [Reduced.checks])

end Cost

end PcsKS.VH
