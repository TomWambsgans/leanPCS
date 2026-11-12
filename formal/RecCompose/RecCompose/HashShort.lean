-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The walks of
-- `formal/EndToEnd/Completeness/E2ECompleteness/Cost.lean` (`cost_runFromWithHash`, `cost_proveOpeningWithH`,
-- `qc_findNonceM`), redone for the lengths of the hashed inputs; uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls
-- `KeccakCalls`, the block cost `hashBlocks`, the weight calculus `Common.QueryCostAtMost`, VCVio's `IsQueryBound`.
-- Split from `Pi2AlphaLen.lean` (its generic part), so that π1's census (`Pi1Rec4Census`) does not depend on π2's run.
import UniKeccakComplete.K.Rec4End
import E2ECompleteness.Cost
import RecStatement.Security

/-!
# Short hash inputs: the calculus

Every Keccak-256 query of a computation shorter than `2^26` bytes (`Short`, the length of π2's `σ` hash): from a block
count (**`hashOK_of_qc`**), with a postcondition (`LenP`), in a writer's walk (`WS`: every query short, the stream at
most `2^14` bytes; `ws_of_wc` from UniComplete's `WC` costs, `ws_seq`, `ws_lift`); Merkle trees of rows of at most `192`
words (`hashOK_buildTree`, `hashOK_commitWithH`, `hashOK_commitReal`); WHIR openings (**`hashOK_proveOpeningWithH`**,
**`hashOK_pcsProveH`**: the seed, the trees, the sponge and the proof-of-work search through the permutation only).
`Pi2AlphaLen.lean` applies it to π2's stage A, `Pi1Rec4Census.lean` to π1-rec4's prover.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile
open LeanVM.Prover (Tree Script)
open RecStatement
open UniStatement
open E2ECompleteness (HashOK hashOK_callKeccak256 hashOK_callKeccakF1600)
open E2ECompleteness.Cost (qc_absorb qc_squeeze qc_powStepM qc_openingSpongeWithH OWordsLE
  oWordsLE_afterSend oWordsLE_afterSample oWordsLE_afterGrind oWordsLE_afterCommit oWordsLE_afterQuery
  length_wordOf_le wordsLE_openingScript)
open UniKeccakComplete.Cost (CostP costP_query_bind WC WInv wpot)

namespace RecCompose.Pi2A

/-- Shorter than π2's σ hash input (`4 · 2^24 = 2^26` bytes). -/
def Short (m : List UInt8) : Prop := m.length < 2 ^ 26

theorem two26 : (2 : ℕ) ^ 26 = 67108864 := by norm_num

/-- A short query: a hash of a short input, or a permutation. -/
def ShortQ : List UInt8 ⊕ KeccakState → Prop
  | .inl x => Short x
  | .inr _ => True

/-! ## From a block count -/

/-- **A computation of at most `n` block calls, `136 · n ≤ 2^26`, hashes only short inputs.** -/
theorem hashOK_of_qc {α : Type} {X : OracleComp KeccakCalls α} {n : ℕ}
    (h : Common.QueryCostAtMost X LeanVM.Rpm.hashBlocks n) (hn : 136 * n ≤ 2 ^ 26) : HashOK Short X := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [Common.isWeightBound_query_bind_iff] at h
    refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨?_, fun u ↦ ih u (h.2 u)
      ((Nat.mul_le_mul_left 136 (Nat.sub_le _ _)).trans hn)⟩
    rcases t with x | s
    · have h1 := h.1
      simp only [LeanVM.Rpm.hashBlocks] at h1
      show x.length < 2 ^ 26
      rw [two26] at hn ⊢
      omega
    · trivial

/-! ## Short queries with a postcondition -/

/-- **Every query short on every path**, each outcome satisfying `Q`. -/
def LenP {α : Type} : OracleComp KeccakCalls α → (α → Prop) → Prop
  | .pure a, Q => Q a
  | .liftBind t k, Q => ShortQ t ∧ ∀ u, LenP (k u) Q

section LenP

variable {α β : Type}

theorem lenP_query_bind (t : List UInt8 ⊕ KeccakState) (k : KeccakCalls.Range t → OracleComp KeccakCalls α)
    (Q : α → Prop) : LenP (liftM (KeccakCalls.query t) >>= k) Q ↔ ShortQ t ∧ ∀ u, LenP (k u) Q :=
  Iff.rfl

theorem LenP.bind {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β} {Q : α → Prop}
    {R : β → Prop} (hX : LenP X Q) (hf : ∀ a, Q a → LenP (f a) R) : LenP (X >>= f) R := by
  induction X using OracleComp.inductionOn with
  | pure a => simpa using hf a hX
  | query_bind t k ih =>
    rw [bind_assoc]
    rw [lenP_query_bind] at hX ⊢
    exact ⟨hX.1, fun u ↦ ih u (hX.2 u)⟩

theorem LenP.mono {X : OracleComp KeccakCalls α} {Q R : α → Prop} (hX : LenP X Q) (h : ∀ a, Q a → R a) :
    LenP X R := by
  induction X using OracleComp.inductionOn with
  | pure a => exact h a hX
  | query_bind t k ih =>
    rw [lenP_query_bind] at hX ⊢
    exact ⟨hX.1, fun u ↦ ih u (hX.2 u)⟩

theorem LenP.toHashOK {X : OracleComp KeccakCalls α} {Q : α → Prop} (h : LenP X Q) : HashOK Short X := by
  induction X using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [lenP_query_bind] at h
    refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨?_, fun u ↦ ih u (h.2 u)⟩
    rcases t with x | s
    · exact h.1
    · trivial

theorem lenP_of_hashOK {X : OracleComp KeccakCalls α} (h : HashOK Short X) : LenP X fun _ ↦ True := by
  induction X using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).1 h
    rw [lenP_query_bind]
    refine ⟨?_, fun u ↦ ih u (hk u)⟩
    rcases t with x | s
    · exact ht
    · trivial

/-- **A cost with no extra budget**: a query costs at most the blocks left. -/
theorem lenP_of_costP {X : OracleComp KeccakCalls α} {n : ℕ} {Q : α → ℕ → Prop} (h : CostP X n Q)
    (hn : 136 * n ≤ 2 ^ 26) : LenP X fun a ↦ ∃ r, Q a r := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a => exact ⟨n, h⟩
  | query_bind t k ih =>
    rw [costP_query_bind] at h
    rw [lenP_query_bind]
    refine ⟨?_, fun u ↦ ih u (h.2 u) ((Nat.mul_le_mul_left 136 (Nat.sub_le _ _)).trans hn)⟩
    rcases t with x | s
    · have h1 := h.1
      simp only [LeanVM.Rpm.hashBlocks] at h1
      show x.length < 2 ^ 26
      rw [two26] at hn ⊢
      omega
    · trivial

end LenP

/-! ## The writer's calculus -/

/-- **`x` hashes only short inputs and writes at most `w` bytes**, from any state of at most `2^14 − w` bytes. -/
def WS {α : Type} (x : UniKeccakComplete.PM α) (w : ℕ) (P : α → UniComplete.Wr → Prop) : Prop :=
  ∀ c, WInv c → c.stream.size + w ≤ 16384 → LenP (x.run c) fun z ↦
    P z.1 z.2 ∧ WInv z.2 ∧ c.stream.size ≤ z.2.stream.size ∧ z.2.stream.size ≤ c.stream.size + w

section WS

variable {α β : Type}

/-- **A piece of at most `2^14` blocks beyond its bytes.** -/
theorem ws_of_wc {x : UniKeccakComplete.PM α} {k w : ℕ} {P : α → UniComplete.Wr → Prop} (h : WC x k w P)
    (hk : k ≤ 16384) : WS x w P := by
  intro c hc hs
  refine (lenP_of_costP (h c hc 0) ?_).mono fun z ⟨_, hz⟩ ↦ ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1⟩
  have : wpot c ≤ c.stream.size := Nat.sub_le _ _
  rw [two26]
  omega

theorem ws_seq {x : UniKeccakComplete.PM α} {f : α → UniKeccakComplete.PM β} {w₁ w : ℕ} {P : α → UniComplete.Wr → Prop}
    {Q : β → UniComplete.Wr → Prop} (hx : WS x w₁ P) (hf : ∀ a s, P a s → WS (f a) (w - w₁) Q) (hw : w₁ ≤ w) :
    WS (x >>= f) w Q := by
  intro c hc hs
  rw [StateT.run_bind]
  refine (hx c hc (by omega)).bind fun z hz ↦ ?_
  obtain ⟨hP, hI, h1, h2⟩ := hz
  exact (hf z.1 z.2 hP z.2 hI (by omega)).mono fun z' h ↦ ⟨h.1, h.2.1, by omega, by omega⟩

/-- **A lifted computation** of short queries writes nothing. -/
theorem ws_lift {X : OracleComp KeccakCalls α} (hX : HashOK Short X) :
    WS (StateT.lift X : UniKeccakComplete.PM α) 0 fun _ _ ↦ True := by
  intro c hc _
  rw [StateT.run_lift]
  exact (lenP_of_hashOK hX).bind fun a _ ↦ ⟨trivial, hc, le_rfl, Nat.le_add_right _ _⟩

end WS

/-! ## Merkle trees -/

theorem hashOK_buildTree (height : ℕ) (word : Word) (hw : ∀ p, (word p).length ≤ 192) :
    HashOK Short (LeanVM.Prover.buildTreeWithHash callKeccak256 height word) := by
  unfold LeanVM.Prover.buildTreeWithHash
  refine E2ECompleteness.HashOK.bind ?_ fun leaves ↦ E2ECompleteness.HashOK.bind ?_ fun _ ↦
    E2ECompleteness.HashOK.pure _ _
  · unfold LeanVM.Prover.leafDigestsWithHash
    refine E2ECompleteness.HashOK.arrayMapM _ (fun i ↦ hashOK_callKeccak256 ?_) _
    show _ < 2 ^ 26
    rw [E2ECompleteness.length_flatMap_kBytes, two26]
    have := hw i
    omega
  · suffices h : ∀ k (level : Array Digest),
        HashOK Short (LeanVM.Prover.levelsWithHash callKeccak256 k level) from h _ _
    intro k
    induction k with
    | zero => intro level; exact E2ECompleteness.HashOK.pure _ _
    | succ k ih =>
      intro level
      unfold LeanVM.Prover.levelsWithHash
      refine E2ECompleteness.HashOK.bind ?_ fun up ↦ E2ECompleteness.HashOK.bind (ih up) fun _ ↦
        E2ECompleteness.HashOK.pure _ _
      unfold LeanVM.Prover.parentsWithHash
      refine E2ECompleteness.HashOK.arrayMapM _ (fun j ↦ hashOK_callKeccak256 ?_) _
      show _ < 2 ^ 26
      rw [List.length_append, E2ECompleteness.length_digestBytes, E2ECompleteness.length_digestBytes, two26]
      omega

theorem hashOK_commitWithH (μ : ℕ) (stack : Array K) :
    HashOK Short (E2ECompleteness.commitWithH callKeccak256 μ stack) :=
  hashOK_buildTree _ _ fun p ↦ by rw [E2ECompleteness.length_stackWordFast]; norm_num

theorem hashOK_commitReal (c : Commitment) (vars : ℕ) (stack : Array K) :
    HashOK Short (UniKeccakComplete.commitReal callKeccak256 c vars stack) := by
  unfold UniKeccakComplete.commitReal
  exact E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦ E2ECompleteness.HashOK.pure _ _

/-! ## The WHIR openings -/

theorem hashOK_searchM (bits : ℕ) (sp : Sponge) :
    ∀ (count n : ℕ), HashOK Short (LeanVM.Prover.searchM callKeccakF1600 bits sp n count)
  | 0, _ => trivial
  | count + 1, n => by
    simp only [LeanVM.Prover.searchM]
    refine E2ECompleteness.HashOK.bind (hashOK_of_qc (qc_powStepM _ _) (by norm_num)) fun r ↦ ?_
    split
    · exact E2ECompleteness.HashOK.pure _ _
    · exact hashOK_searchM bits sp count (n + 1)

theorem hashOK_findNonceM (bits : ℕ) (sp : Sponge) (fuel : ℕ) :
    HashOK Short (LeanVM.Prover.findNonceM callKeccakF1600 bits sp fuel) := by
  unfold LeanVM.Prover.findNonceM
  split
  · exact E2ECompleteness.HashOK.pure _ _
  · exact hashOK_searchM _ _ _ _

/-- **The prover's runner** hashes only its trees' rows (at most `192` words) and nodes. -/
theorem hashOK_runFromWithHash (fuel : ℕ) {α β : Type} :
    ∀ (P : Prog α) (S : Option (Script β)) (sp : Sponge) (cs : List Tree), OWordsLE 192 S →
      HashOK Short (LeanVM.Prover.runFromWithHash callKeccak256 callKeccakF1600 fuel P S sp cs) := by
  intro P
  induction P with
  | ret a => intros; exact E2ECompleteness.HashOK.pure _ _
  | fail => intros; exact E2ECompleteness.HashOK.pure _ _
  | read k ih =>
    intro S sp cs hS
    simp only [LeanVM.Prover.runFromWithHash]
    exact E2ECompleteness.HashOK.bind (hashOK_of_qc (qc_absorb _ _ _) (by norm_num)) fun _ ↦
      E2ECompleteness.HashOK.bind (ih _ _ _ cs (oWordsLE_afterSend hS)) fun _ ↦ E2ECompleteness.HashOK.pure _ _
  | sample k ih =>
    intro S sp cs hS
    simp only [LeanVM.Prover.runFromWithHash]
    exact E2ECompleteness.HashOK.bind (hashOK_of_qc (qc_squeeze _) (by norm_num)) fun r ↦
      ih _ _ _ cs (oWordsLE_afterSample _ hS)
  | grind bits k ih =>
    intro S sp cs hS
    simp only [LeanVM.Prover.runFromWithHash]
    refine E2ECompleteness.HashOK.bind (hashOK_findNonceM _ _ _) fun o ↦ ?_
    split
    · exact E2ECompleteness.HashOK.pure _ _
    · exact E2ECompleteness.HashOK.bind (hashOK_of_qc (qc_powStepM _ _) (by norm_num)) fun _ ↦
        E2ECompleteness.HashOK.bind (ih _ _ cs (oWordsLE_afterGrind hS)) fun _ ↦ E2ECompleteness.HashOK.pure _ _
  | commit ht w k ih =>
    intro S sp cs hS
    simp only [LeanVM.Prover.runFromWithHash]
    exact E2ECompleteness.HashOK.bind (hashOK_buildTree ht _ (length_wordOf_le hS)) fun _ ↦
      E2ECompleteness.HashOK.bind (hashOK_of_qc (qc_absorb _ _ _) (by norm_num)) fun _ ↦
      E2ECompleteness.HashOK.bind (hashOK_of_qc (qc_absorb _ _ _) (by norm_num)) fun _ ↦
      E2ECompleteness.HashOK.bind (ih _ _ _ (oWordsLE_afterCommit hS)) fun _ ↦ E2ECompleteness.HashOK.pure _ _
  | query i ps k ih =>
    intro S sp cs hS
    simp only [LeanVM.Prover.runFromWithHash]
    split
    · exact E2ECompleteness.HashOK.pure _ _
    · exact E2ECompleteness.HashOK.bind (ih _ _ _ cs (oWordsLE_afterQuery _ hS)) fun _ ↦
        E2ECompleteness.HashOK.pure _ _

/-- **A WHIR opening** of claims of at most `v` coordinates, its seed's input of at most `2^20` bytes. -/
theorem hashOK_proveOpeningWithH (fuel : ℕ) (L : PcsQuotient.Layout) (tree : Tree) (stack : Array K)
    (claims : List PcsQuotient.Claim) (v : ℕ) (hv : ∀ c ∈ claims, c.point.length ≤ v)
    (hB : 76 + 24 * (claims.length * (v + 1)) ≤ 1048576) :
    HashOK Short (E2ECompleteness.proveOpeningWithH callKeccak256 callKeccakF1600 fuel L tree stack claims) := by
  unfold E2ECompleteness.proveOpeningWithH
  split
  exact E2ECompleteness.HashOK.bind (hashOK_of_qc (qc_openingSpongeWithH L claims v 7712 hv
      (lt_of_le_of_lt hB (by norm_num))) (by norm_num)) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_of_qc (qc_absorb _ _ _) (by norm_num)) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_of_qc (qc_absorb _ _ _) (by norm_num)) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_runFromWithHash _ _ _ _ _ (wordsLE_openingScript L stack claims)) fun _ ↦
      E2ECompleteness.HashOK.pure _ _

/-- One point claim of at most `v ≤ 2^14` coordinates. -/
theorem hashOK_proveOpening1 (fuel : ℕ) (L : PcsQuotient.Layout) (tree : Tree) (stack : Array K)
    (pt : List E) (value : E) {v : ℕ} (hv : pt.length ≤ v) (hv' : v ≤ 16384) :
    HashOK Short (E2ECompleteness.proveOpeningWithH callKeccak256 callKeccakF1600 fuel L tree stack [⟨pt, value⟩]) :=
  hashOK_proveOpeningWithH fuel L tree stack _ v
    (fun c hc ↦ by
      simp only [List.mem_singleton] at hc
      subst hc
      exact hv)
    (by simp only [List.length_singleton, Nat.one_mul]; omega)

/-- **A PCS claim's honest opening** of a point of at most `2^14` coordinates: its seed's input (the claim's
`82 + 24 n` bytes), the root's absorption, the opening script's trees and sponge. -/
theorem hashOK_pcsProveH (fuel n : ℕ) (tree : Tree) (stack : Array K) (pt : List E) (v : E)
    (hv : pt.length ≤ 16384) :
    HashOK Short (UniKeccakComplete.pcsProveH callKeccak256 callKeccakF1600 fuel n tree stack pt v) := by
  unfold UniKeccakComplete.pcsProveH
  split
  · rename_i hpt
    refine E2ECompleteness.HashOK.bind (hashOK_of_qc (UniKeccakComplete.qc_pcsSpongeH _ ((82 + 24 * 16384) / 136 + 1)
      (by rw [WhirBridge.Pcs.claimBytes_length]; omega)) (by norm_num)) fun _ ↦
      E2ECompleteness.HashOK.bind (hashOK_of_qc (qc_absorb _ _ _) (by norm_num)) fun _ ↦
      E2ECompleteness.HashOK.bind (hashOK_of_qc (qc_absorb _ _ _) (by norm_num)) fun _ ↦
      E2ECompleteness.HashOK.bind (hashOK_runFromWithHash _ _ _ _ _ (wordsLE_openingScript _ stack _)) fun _ ↦
        E2ECompleteness.HashOK.pure _ _
  · exact E2ECompleteness.HashOK.pure _ _

/-- **The out-of-domain point hashes its `n` inputs `oodInput n r j`** (`46` bytes each). -/
theorem hashOK_oodPointM {P : List UInt8 → Prop} (n : ℕ) (r : Digest)
    (hP : ∀ j, P (WhirBridge.Pcs.oodInput n r j)) : HashOK P (WhirBridge.Pcs.oodPointM callKeccak256 n r) := by
  unfold WhirBridge.Pcs.oodPointM
  generalize List.range n = l
  induction l with
  | nil => exact E2ECompleteness.HashOK.pure _ _
  | cons j l ih =>
    rw [List.mapM_cons]
    exact E2ECompleteness.HashOK.bind (E2ECompleteness.HashOK.bind (E2ECompleteness.hashOK_callKeccak256 (hP j))
      fun _ ↦ E2ECompleteness.HashOK.pure _ _) fun _ ↦ E2ECompleteness.HashOK.bind ih fun _ ↦
        E2ECompleteness.HashOK.pure _ _

theorem oodInput_length (n : ℕ) (r : Digest) (j : ℕ) : (WhirBridge.Pcs.oodInput n r j).length = 46 := by
  simp [WhirBridge.Pcs.oodInput, WhirBridge.Pcs.oodTag, WhirBridge.Pcs.digestBytes_length']

end RecCompose.Pi2A
