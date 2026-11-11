-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `E2ECompleteness/HashLen.lean` (the previous protocol's two stages) to the PCS claims'
-- stages (`PcsStaging.lean`): the out-of-domain inputs and the `136`-byte label, and stage C's chain
-- inputs. Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the Merkle tree with a hash (`buildTreeWithHash`, `leafDigestsWithHash`,
-- `parentsWithHash`, `levelsWithHash`).
import E2ECompleteness.PcsStaging

/-!
# What the stages hash (the PCS claims)

Before `α` and between `γ` and `t` the honest run hashes Merkle leaves (a row of `64` words of `K`,
`512` bytes), Merkle nodes (two digests, `64` bytes), out-of-domain inputs (`oodInput`, `46` bytes)
and the label (`136` bytes): never `32`, `128`, `320` or `192` bytes, the lengths of the chain's
queries (`Good4`). Between `t` and `ρ` (stage C) it hashes the label and the chain's own inputs
(`128`, `32`, `320` bytes): never `192` (`GoodC`).

**`hashOK_stageAG`**, **`hashOK_stageBG`**, **`hashOK_stageCG`**, **`hashOK_setupWithH`**.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Prover (Tree)
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript

set_option autoImplicit false

namespace E2ECompleteness.Pcs

/-! ## Generic -/

theorem HashOK.mapM {P : Bytes → Prop} {α β : Type} (f : α → OracleComp KeccakCalls β)
    (hf : ∀ a, HashOK P (f a)) : ∀ l : List α, HashOK P (l.mapM f)
  | [] => HashOK.pure _ _
  | a :: l => by
    rw [List.mapM_cons]
    exact HashOK.bind (hf a) fun _ ↦ HashOK.bind (HashOK.mapM f hf l) fun _ ↦ HashOK.pure _ _

theorem HashOK.arrayMapM {P : Bytes → Prop} {α β : Type} (f : α → OracleComp KeccakCalls β)
    (hf : ∀ a, HashOK P (f a)) (xs : Array α) : HashOK P (xs.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  exact HashOK.map _ (HashOK.mapM f hf _)

/-- The lengths the commitments and the label hash: leaves, nodes, out-of-domain inputs, the label. -/
def CommitLen (m : Bytes) : Prop :=
  m.length = 512 ∨ m.length = 64 ∨ m.length = 46 ∨ m.length = 136

theorem good4_of_commitLen {m : Bytes} (h : CommitLen m) : Good4 m := by
  unfold CommitLen at h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-! ## Lengths -/

theorem length_flatMap_kBytes (row : List K) : (row.flatMap kBytes).length = 8 * row.length := by
  induction row with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    simp only [kBytes, LeanVM.Rpm.wordBytes_len]
    ring

theorem length_stackWordFast (μ R : ℕ) (stack : Array K) (p : ℕ) :
    (LeanVM.Prover.stackWordFast μ R stack p).length = 64 := by
  unfold LeanVM.Prover.stackWordFast LeanVM.Prover.stackWordFast.stackWordOf
  split <;> simp

theorem length_elementBytes (x : E) : (elementBytes x).length = 24 := by
  simp [elementBytes, beBytes, LeanVM.Rpm.wordBytes_len]

theorem length_oodTag : oodTag.length = 11 := by
  unfold oodTag
  decide +kernel

/-- An out-of-domain input is `11 + 2 + 32 + 1 = 46` bytes. -/
theorem length_oodInput (n : ℕ) (root : Digest) (j : ℕ) : (oodInput n root j).length = 46 := by
  simp only [oodInput, List.length_append, length_oodTag, length_digestBytes, List.length_cons,
    List.length_nil]

/-- The label is `16 + 32 + 24 + 32 + 32 = 136` bytes. -/
theorem length_label (index : Commitment) (stmt : Statement) : (label index stmt).length = 136 := by
  simp only [label, List.length_append, length_digestBytes, length_elementBytes,
    Vector.length_toList]
  have h16 : "pcs-quotient-kc1".toUTF8.toList.length = 16 := by decide +kernel
  omega

/-! ## The commitments -/

section Commit

variable {P : Bytes → Prop} (hP : ∀ m, CommitLen m → P m)
include hP

/-- A Merkle tree of rows of `64` words hashes `512`-byte leaves and `64`-byte nodes. -/
theorem hashOK_buildTree (height : ℕ) (word : LeanVM.Protocol.Compile.Word)
    (hw : ∀ p, (word p).length = 64) :
    HashOK P (LeanVM.Prover.buildTreeWithHash callKeccak256 height word) := by
  unfold LeanVM.Prover.buildTreeWithHash
  refine HashOK.bind ?_ fun leaves ↦ HashOK.bind ?_ fun _ ↦ HashOK.pure _ _
  · unfold LeanVM.Prover.leafDigestsWithHash
    refine HashOK.arrayMapM _ (fun i ↦ hashOK_callKeccak256 (hP _ (Or.inl ?_))) _
    rw [length_flatMap_kBytes, hw]
  · suffices h : ∀ k (level : Array Digest),
        HashOK P (LeanVM.Prover.levelsWithHash callKeccak256 k level) from h _ _
    intro k
    induction k with
    | zero => intro level; exact HashOK.pure _ _
    | succ k ih =>
      intro level
      unfold LeanVM.Prover.levelsWithHash
      refine HashOK.bind ?_ fun up ↦ HashOK.bind (ih up) fun _ ↦ HashOK.pure _ _
      unfold LeanVM.Prover.parentsWithHash
      refine HashOK.arrayMapM _
        (fun j ↦ hashOK_callKeccak256 (hP _ (Or.inr (Or.inl ?_)))) _
      rw [List.length_append, length_digestBytes, length_digestBytes]

theorem hashOK_commitWithH (μ : ℕ) (table : Array K) :
    HashOK P (commitWithH callKeccak256 μ table) :=
  hashOK_buildTree hP _ _ (length_stackWordFast _ _ table)

/-- The out-of-domain point hashes `46`-byte inputs. -/
theorem hashOK_oodPointWithH (n : ℕ) (root : Digest) :
    HashOK P (oodPointWithH callKeccak256 n root) := by
  unfold oodPointWithH
  refine HashOK.mapM _ (fun j ↦ ?_) _
  exact HashOK.bind (hashOK_callKeccak256 (hP _ (Or.inr (Or.inr (Or.inl (length_oodInput _ _ _))))))
    fun _ ↦ HashOK.pure _ _

theorem hashOK_commitmentWithH (μ : ℕ) (table : Array K) :
    HashOK P (commitmentWithH callKeccak256 μ table) :=
  HashOK.bind (hashOK_commitWithH hP _ _) fun _ ↦
    HashOK.bind (hashOK_oodPointWithH hP _ _) fun _ ↦ HashOK.pure _ _

end Commit

/-! ## The stages -/

/-- **The setup hashes nothing of the chain's lengths.** -/
theorem hashOK_setupWithH : HashOK Good4 (setupWithH callKeccak256) :=
  hashOK_commitmentWithH (fun _ h ↦ good4_of_commitLen h) _ _

/-- **The first stage hashes nothing of the chain's lengths.** -/
theorem hashOK_stageAG (setup : OracleComp KeccakCalls (Tree × Commitment))
    (hs : HashOK Good4 setup) (circuit : Circuit) (cells₀ : Array K) (coins : Coins)
    (stmt : Statement) :
    HashOK Good4 (stageAG setup circuit cells₀ coins stmt) := by
  have hP : ∀ m, CommitLen m → Good4 m := fun _ h ↦ good4_of_commitLen h
  unfold stageAG
  refine HashOK.bind (HashOK.map _ hs) fun _ ↦
    HashOK.bind (hashOK_commitmentWithH hP _ _) fun x ↦ ?_
  rcases x with ⟨_, _⟩
  refine HashOK.bind (hashOK_commitmentWithH hP _ _) fun y ↦ ?_
  rcases y with ⟨_, _⟩
  exact HashOK.bind (hashOK_callKeccak256 (hP _ (Or.inr (Or.inr (Or.inr (length_label _ _))))))
    fun _ ↦ HashOK.pure _ _

/-- **The second stage hashes nothing of the chain's lengths.** -/
theorem hashOK_stageBG (circuit : Circuit) (cells₀ : Array K) (coins : Coins) :
    ∀ a s₁ s₂ s₃, HashOK Good4 (stageBG circuit cells₀ coins a s₁ s₂ s₃) := by
  have hP : ∀ m, CommitLen m → Good4 m := fun _ h ↦ good4_of_commitLen h
  intro a s₁ s₂ s₃
  unfold stageBG
  refine HashOK.bind (hashOK_commitmentWithH hP _ _) fun x ↦ ?_
  rcases x with ⟨_, _⟩
  refine HashOK.bind (hashOK_commitmentWithH hP _ _) fun y ↦ ?_
  rcases y with ⟨_, _⟩
  refine HashOK.bind (hashOK_commitmentWithH hP _ _) fun z ↦ ?_
  rcases z with ⟨_, _⟩
  exact HashOK.pure _ _

/-- **The third stage hashes nothing of `ρ`'s length**: the label (`136` bytes) and the chain's own
inputs (`128`, `32`, `32`, `320` bytes). -/
theorem hashOK_stageCG (circuit : Circuit) (cells₀ : Array K) (coins : Coins) (stmt : Statement) :
    ∀ a b s₁ s₂ s₃ s₄, HashOK GoodC (stageCG circuit cells₀ coins stmt a b s₁ s₂ s₃ s₄) := by
  intro a b s₁ s₂ s₃ s₄
  unfold stageCG
  refine HashOK.bind (hashOK_callKeccak256 ?_) fun _ ↦ HashOK.bind (hashOK_callKeccak256 ?_)
    fun _ ↦ HashOK.bind (hashOK_callKeccak256 ?_) fun _ ↦ HashOK.bind (hashOK_callKeccak256 ?_)
    fun _ ↦ HashOK.bind (hashOK_callKeccak256 ?_) fun _ ↦ HashOK.pure _ _
  · show (label _ _).length ≠ 192; rw [length_label]; omega
  · show (in3 _ _).length ≠ 192; rw [length_in3]; omega
  · show (digestBytes _).length ≠ 192; rw [length_digestBytes]; omega
  · show (digestBytes _).length ≠ 192; rw [length_digestBytes]; omega
  · show (in9 _ _).length ≠ 192; rw [length_in9]; omega

/-- info: 'E2ECompleteness.Pcs.hashOK_stageAG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hashOK_stageAG

/-- info: 'E2ECompleteness.Pcs.hashOK_stageBG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hashOK_stageBG

/-- info: 'E2ECompleteness.Pcs.hashOK_stageCG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hashOK_stageCG

/-- info: 'E2ECompleteness.Pcs.hashOK_setupWithH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hashOK_setupWithH

end E2ECompleteness.Pcs
