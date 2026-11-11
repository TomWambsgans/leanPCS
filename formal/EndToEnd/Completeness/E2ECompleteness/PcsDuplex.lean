-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `E2ECompleteness/Duplex.lean` (the previous protocol's openings and stages) to the PCS
-- claims (`PcsWithHash.lean`, `PcsStaging.lean`): one opening a claim, each from its claim's seed.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the duplex discipline (`LeanVM.Rpm.DuplexVm`, `DuplexP`, `HOnly`) and its
-- rules for the sponge, the runners and the Merkle trees (`duplexP_absorb`, `duplexP_run`,
-- `duplexP_findNonceM`, `duplexP_powStepM`, `hOnly_buildTreeM`, `hOnly_mapM`,
-- `admissibleVm_seedInput`).
import E2ECompleteness.PcsStaging
import LeanVM.Protocol.Rpm.Duplex

/-!
# The duplex discipline of the deployed staged run (the PCS claims)

Every Keccak-f[1600] call of the honest run either continues a duplex (its capacity, lanes
`16 … 24`, an earlier answer's) or starts one at a zero capacity (an opening's seed,
`F(seedInput iv 0)`, `iv` the claim's hash): mumbai's `DuplexVm`. The commitments, their
out-of-domain points and the reduction only hash (`HOnly`); each opening, the prover's
(`proveClaimWithH`) and the verifier's (`pcsOpeningWithH`), starts its own duplex, so every piece
is disciplined from any earlier answers (`Disc`), and so is their sequence.
**`duplexVm_stagedRun`**.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover (Tree)
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript

set_option autoImplicit false

namespace E2ECompleteness.Pcs

/-! ## Disciplined from any earlier answers -/

/-- Disciplined from any earlier answers. -/
def Disc {α : Type} (X : OracleComp KeccakCalls α) : Prop :=
  ∀ h : List KeccakState, DuplexP X h fun _ _ ↦ True

theorem Disc.bind {α β : Type} {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β}
    (hX : Disc X) (hf : ∀ a, Disc (f a)) : Disc (X >>= f) :=
  fun h ↦ (hX h).bind fun a h' _ ↦ hf a h'

theorem disc_pure {α : Type} (a : α) : Disc (pure a : OracleComp KeccakCalls α) := fun _ ↦ trivial

theorem disc_of_hOnly {α : Type} {X : OracleComp KeccakCalls α} (hX : HOnly X) : Disc X :=
  fun h ↦ (hX.duplexP h).mono fun _ _ _ ↦ trivial

theorem Disc.map {α β : Type} {X : OracleComp KeccakCalls α} (f : α → β) (hX : Disc X) :
    Disc (f <$> X) := by
  rw [map_eq_bind_pure_comp]
  exact hX.bind fun _ ↦ disc_pure _

theorem hOnly_map {α β : Type} {X : OracleComp KeccakCalls α} (f : α → β) (hX : HOnly X) :
    HOnly (f <$> X) := by
  rw [map_eq_bind_pure_comp]
  exact hX.bind fun _ ↦ hOnly_pure _

/-! ## The hash-only pieces -/

theorem hOnly_startWithH (label : List UInt8) : HOnly (startWithH callKeccak256 label) :=
  (hOnly_queryH _).bind fun _ ↦ hOnly_pure _

theorem hOnly_squeezeWithH (c : Chain) : HOnly (squeezeWithH callKeccak256 c) :=
  (hOnly_queryH _).bind fun _ ↦ hOnly_pure _

theorem hOnly_reduceWithH (logRows : ℕ) (index : Commitment) (stmt : Statement)
    (p : ReductionProof) : HOnly (reduceWithH callKeccak256 logRows index stmt p) := by
  unfold reduceWithH
  split
  · exact hOnly_pure _
  · refine (hOnly_startWithH _).bind fun c ↦ ?_
    split
    · refine (hOnly_squeezeWithH _).bind fun ⟨α, c₁⟩ ↦ ?_
      refine (hOnly_squeezeWithH _).bind fun ⟨β, c₂⟩ ↦ ?_
      refine (hOnly_squeezeWithH _).bind fun ⟨γ, c₃⟩ ↦ ?_
      dsimp only
      split
      · split
        · split
          · refine (hOnly_squeezeWithH _).bind fun ⟨t, c₄⟩ ↦ ?_
            dsimp only
            exact (hOnly_squeezeWithH _).bind fun ⟨ρ, _⟩ ↦ hOnly_pure _
          · exact hOnly_pure _
        · exact hOnly_pure _
      · exact hOnly_pure _
    · exact hOnly_pure _

theorem hOnly_oodPointWithH (n : ℕ) (root : Digest) : HOnly (oodPointWithH callKeccak256 n root) :=
  hOnly_mapM _ (fun _ ↦ (hOnly_queryH _).bind fun _ ↦ hOnly_pure _) _

theorem hOnly_commitWithH (μ : ℕ) (table : Array K) : HOnly (commitWithH callKeccak256 μ table) :=
  hOnly_buildTreeM _ _

theorem hOnly_commitmentWithH (μ : ℕ) (table : Array K) :
    HOnly (commitmentWithH callKeccak256 μ table) :=
  (hOnly_commitWithH _ _).bind fun _ ↦ (hOnly_oodPointWithH _ _).bind fun _ ↦ hOnly_pure _

theorem hOnly_setupWithH : HOnly (setupWithH callKeccak256) :=
  hOnly_commitmentWithH _ _

/-! ## The openings -/

/-- An opening's seed `F(seedInput iv 0)` starts a duplex at a zero capacity. -/
theorem duplexP_pcsSpongeWithH (c : Commitment) (claim : Claim) (h : List KeccakState) :
    DuplexP (pcsSpongeWithH callKeccak256 callKeccakF1600 c claim) h
      fun sp h' ↦ sp.state ∈ h' := by
  unfold pcsSpongeWithH
  refine ((hOnly_queryH _).duplexP h).bind fun iv h' hh ↦ ?_
  subst hh
  exact (duplexP_queryF_bind _ _ _ _).mpr
    ⟨admissibleVm_seedInput _ _ _, fun y ↦ List.mem_cons_self⟩

/-- **The verifier's opening is disciplined.** -/
theorem disc_pcsOpeningWithH (c : Commitment) (claim : Claim) (proof : Compile.Proof) :
    Disc (pcsOpeningWithH callKeccak256 callKeccakF1600 c claim proof) := by
  intro h
  unfold pcsOpeningWithH
  dsimp only
  split
  · refine (duplexP_pcsSpongeWithH c claim h).bind fun sp h₁ hs ↦ ?_
    split
    · refine (duplexP_absorb hs _ _).bind fun sp h₂ hs ↦ ?_
      refine (duplexP_absorb hs _ _).bind fun sp h₃ hs ↦ ?_
      split
      · refine ((hOnly_oodPointWithH _ _).duplexP h₃).bind fun z h₄ hh ↦ ?_
        subst hh
        exact (duplexP_run _ _ _ hs).bind fun o _ _ ↦ by split <;> trivial
      · trivial
    · trivial
  · trivial

/-- **The verifier's openings are disciplined.** -/
theorem disc_checkAllWithH : ∀ l : List (Commitment × Claim × Compile.Proof),
    Disc (checkAllWithH callKeccak256 callKeccakF1600 l)
  | [] => disc_pure _
  | (c, claim, proof) :: rest => by
    unfold checkAllWithH
    refine (disc_pcsOpeningWithH c claim proof).bind fun b ↦ ?_
    split
    · exact disc_pure _
    · exact disc_checkAllWithH rest

/-- **The verifier is disciplined.** -/
theorem disc_verifyWithH (logRows : ℕ) (index : Commitment) (stmt : Statement)
    (proof : PcsQuotient.Proof) :
    Disc (verifyWithH callKeccak256 callKeccakF1600 logRows index stmt proof) := by
  unfold verifyWithH
  refine (disc_of_hOnly (hOnly_reduceWithH _ _ _ _)).bind fun o ↦ ?_
  split
  · exact disc_pure _
  · exact disc_checkAllWithH _

/-- **The prover's script runner keeps the discipline**, from a sponge whose state is an earlier
answer (mumbai's `duplexP_proveFromM`, for `runFromWithHash`). -/
theorem duplexP_runFromWithHash (fuel : ℕ) {α β : Type} (P : Prog α) :
    ∀ (S : Option (LeanVM.Prover.Script β)) (sp : Sponge) (cs : List Tree) (h : List KeccakState),
      sp.state ∈ h →
      DuplexP (LeanVM.Prover.runFromWithHash callKeccak256 callKeccakF1600 fuel P S sp cs) h
        fun _ _ ↦ True := by
  induction P with
  | ret a => intro S sp cs h _; trivial
  | fail => intro S sp cs h _; trivial
  | read k ih =>
    intro S sp cs h hs
    simp only [LeanVM.Prover.runFromWithHash]
    exact (duplexP_absorb hs _ _).bind fun sp' h' hsp ↦
      (ih _ _ _ _ _ hsp).bind fun _ _ _ ↦ trivial
  | sample k ih =>
    intro S sp cs h hs
    simp only [LeanVM.Prover.runFromWithHash]
    exact (duplexP_squeeze hs).bind fun r h' hr ↦ ih _ _ _ _ _ hr
  | grind bits k ih =>
    intro S sp cs h hs
    simp only [LeanVM.Prover.runFromWithHash]
    refine (duplexP_findNonceM bits hs fuel).bind fun r h' hr ↦ ?_
    split
    · trivial
    · exact (duplexP_powStepM hr _).bind fun r' h'' hr' ↦
        (ih _ _ _ _ hr').bind fun _ _ _ ↦ trivial
  | commit ht w k ih =>
    intro S sp cs h hs
    simp only [LeanVM.Prover.runFromWithHash]
    refine ((hOnly_buildTreeM _ _).duplexP h).bind fun tree h' hh ↦ ?_
    subst hh
    exact (duplexP_absorb hs _ _).bind fun sp0 h0 hs0 ↦ (duplexP_absorb hs0 _ _).bind
      fun sp1 h1 hs1 ↦ (ih _ _ _ _ hs1).bind fun _ _ _ ↦ trivial
  | query i ps k ih =>
    intro S sp cs h hs
    simp only [LeanVM.Prover.runFromWithHash]
    split
    · trivial
    · exact (ih _ _ _ _ _ hs).bind fun _ _ _ ↦ trivial

/-- **The prover's opening is disciplined.** -/
theorem disc_proveClaimWithH (fuel : ℕ) (tree : Tree) (table : Array K) (c : Commitment)
    (claim : Claim) :
    Disc (proveClaimWithH callKeccak256 callKeccakF1600 fuel tree table c claim) := by
  intro h
  unfold proveClaimWithH
  refine (duplexP_pcsSpongeWithH c claim h).bind fun sp h₁ hs ↦ ?_
  refine (duplexP_absorb hs _ _).bind fun sp h₂ hs ↦ ?_
  refine (duplexP_absorb hs _ _).bind fun sp h₃ hs ↦ ?_
  refine ((hOnly_oodPointWithH _ _).duplexP h₃).bind fun z h₄ hh ↦ ?_
  subst hh
  exact (duplexP_runFromWithHash _ _ _ _ _ _ hs).bind fun _ _ _ ↦ trivial

/-! ## The stages -/

section Stages

variable (circuit : Circuit) (cells₀ : Array K) (coins : Coins) (fuel vLogRows : ℕ)
  (stmt : Statement)

theorem hOnly_stageAG (setup : OracleComp KeccakCalls (Tree × Commitment)) (hs : HOnly setup) :
    HOnly (stageAG setup circuit cells₀ coins stmt) := by
  unfold stageAG
  refine (hOnly_map _ hs).bind fun _ ↦ (hOnly_commitmentWithH _ _).bind fun x ↦ ?_
  rcases x with ⟨_, _⟩
  refine (hOnly_commitmentWithH _ _).bind fun y ↦ ?_
  rcases y with ⟨_, _⟩
  exact (hOnly_queryH _).bind fun _ ↦ hOnly_pure _

theorem hOnly_stageBG (a : AuxA) (s₁ s₂ s₃ : Digest) :
    HOnly (stageBG circuit cells₀ coins a s₁ s₂ s₃) := by
  unfold stageBG
  refine (hOnly_commitmentWithH _ _).bind fun x ↦ ?_
  rcases x with ⟨_, _⟩
  refine (hOnly_commitmentWithH _ _).bind fun y ↦ ?_
  rcases y with ⟨_, _⟩
  refine (hOnly_commitmentWithH _ _).bind fun z ↦ ?_
  rcases z with ⟨_, _⟩
  exact hOnly_pure _

theorem hOnly_stageCG (a : AuxA) (b : AuxB) (s₁ s₂ s₃ s₄ : Digest) :
    HOnly (stageCG circuit cells₀ coins stmt a b s₁ s₂ s₃ s₄) := by
  unfold stageCG
  exact (hOnly_queryH _).bind fun _ ↦ (hOnly_queryH _).bind fun _ ↦ (hOnly_queryH _).bind fun _ ↦
    (hOnly_queryH _).bind fun _ ↦ (hOnly_queryH _).bind fun _ ↦ hOnly_pure _

theorem disc_proverTailG (a : AuxA) (b : AuxB) (c : AuxC) (s₁ s₂ s₃ s₄ s₅ : Digest) :
    Disc (proverTailG circuit cells₀ coins fuel stmt a b c s₁ s₂ s₃ s₄ s₅) := by
  unfold proverTailG
  dsimp only
  split
  · refine (disc_of_hOnly (hOnly_reduceWithH _ _ _ _)).bind fun o ↦ ?_
    split
    · refine (disc_proveClaimWithH _ _ _ _ _).bind fun o₁ ↦ ?_
      split
      · refine (disc_proveClaimWithH _ _ _ _ _).bind fun o₂ ↦ ?_
        split
        · refine (disc_proveClaimWithH _ _ _ _ _).bind fun o₃ ↦ ?_
          split
          · refine (disc_proveClaimWithH _ _ _ _ _).bind fun o₄ ↦ ?_
            split
            · refine (disc_proveClaimWithH _ _ _ _ _).bind fun o₅ ↦ ?_
              split
              · refine (disc_proveClaimWithH _ _ _ _ _).bind fun o₆ ↦ ?_
                split <;> exact disc_pure _
              · exact disc_pure _
            · exact disc_pure _
          · exact disc_pure _
        · exact disc_pure _
      · exact disc_pure _
    · exact disc_pure _
  · exact disc_pure _

theorem disc_stageDG (a : AuxA) (b : AuxB) (c : AuxC) (s₁ s₂ s₃ s₄ s₅ : Digest) :
    Disc (stageDG circuit cells₀ coins fuel vLogRows stmt a b c s₁ s₂ s₃ s₄ s₅) := by
  unfold stageDG
  refine (disc_proverTailG _ _ _ _ _ _ _ _ _ _ _ _ _).bind fun o ↦ ?_
  split
  · exact disc_pure _
  · exact disc_verifyWithH _ _ _ _

end Stages

/-- A computation of the chain's shape is disciplined when its stages are. -/
theorem disc_staged4 {α β γ δ : Type} (chal : Digest → E)
    (A : OracleComp KeccakCalls (α × Digest × CommitmentScalars))
    (B : α → Digest → Digest → Digest → OracleComp KeccakCalls (β × Scalars9))
    (C : α → β → Digest → Digest → Digest → Digest →
      OracleComp KeccakCalls (γ × Digest × (Vector E 4 × E)))
    (D : α → β → γ → Digest → Digest → Digest → Digest → Digest → OracleComp KeccakCalls δ)
    (hA : Disc A) (hB : ∀ a s₁ s₂ s₃, Disc (B a s₁ s₂ s₃))
    (hC : ∀ a b s₁ s₂ s₃ s₄, Disc (C a b s₁ s₂ s₃ s₄))
    (hD : ∀ a b c s₁ s₂ s₃ s₄ s₅, Disc (D a b c s₁ s₂ s₃ s₄ s₅)) :
    Disc (staged4 chal A B C D) := by
  unfold staged4
  exact hA.bind fun _ ↦ (disc_of_hOnly (hOnly_queryH _)).bind fun _ ↦
    (disc_of_hOnly (hOnly_queryH _)).bind fun _ ↦ (disc_of_hOnly (hOnly_queryH _)).bind fun _ ↦
      (hB _ _ _ _).bind fun _ ↦ (disc_of_hOnly (hOnly_queryH _)).bind fun _ ↦
        (hC _ _ _ _ _ _).bind fun _ ↦ (disc_of_hOnly (hOnly_queryH _)).bind fun _ ↦
          (hD _ _ _ _ _ _ _ _).bind fun _ ↦ disc_pure _

theorem disc_stagedRunG (setup : OracleComp KeccakCalls (Tree × Commitment)) (hs : HOnly setup)
    (circuit : Circuit) (cells₀ : Array K) (coins : Coins) (fuel vLogRows : ℕ) (stmt : Statement) :
    Disc (stagedRunG setup circuit cells₀ coins fuel vLogRows stmt) :=
  disc_staged4 _ _ _ _ _ (disc_of_hOnly (hOnly_stageAG _ _ _ _ setup hs))
    (fun _ _ _ _ ↦ disc_of_hOnly (hOnly_stageBG _ _ _ _ _ _ _))
    (fun _ _ _ _ _ _ ↦ disc_of_hOnly (hOnly_stageCG _ _ _ _ _ _ _ _ _ _))
    (fun _ _ _ _ _ _ _ _ ↦ disc_stageDG _ _ _ _ _ _ _ _ _ _ _ _ _ _)

/-- **The deployed staged run follows the duplex discipline.** -/
theorem duplexVm_stagedRun : ∀ stmt w coins, DuplexVm (stagedRun stmt w coins) [] :=
  fun _ _ _ ↦ (duplexVm_iff_duplexP _ _).mpr
    (disc_stagedRunG _ hOnly_setupWithH _ _ _ _ _ _ [])

/-- info: 'E2ECompleteness.Pcs.duplexVm_stagedRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms duplexVm_stagedRun

end E2ECompleteness.Pcs
