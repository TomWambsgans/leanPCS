-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- The verifier's and the setup's part of `formal/EndToEnd/Completeness/E2ECompleteness/PcsDuplex.lean` (at the
-- protocol of `f96a7938`), for the deployed protocol's verifier (`Soundness/PcsVH.lean`).
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the duplex discipline (`LeanVM.Rpm.DuplexVm`, `DuplexP`, `HOnly`) and its
-- rules for the sponge, the runners and the Merkle trees (`duplexP_absorb`, `duplexP_run`,
-- `duplexP_findNonceM`, `duplexP_powStepM`, `hOnly_buildTreeM`, `hOnly_mapM`,
-- `admissibleVm_seedInput`).
import Soundness.PcsVH
import LeanVM.Protocol.Rpm.Duplex

/-!
# The duplex discipline of the deployed verifier (the PCS claims)

Every Keccak-f[1600] call of the verifier either continues a duplex (its capacity, lanes `16 … 24`, an earlier
answer's) or starts one at a zero capacity (an opening's seed, `F(seedInput iv 0)`, `iv` the claim's hash):
mumbai's `DuplexVm`. The setup's commitment, its out-of-domain point and the reduction only hash (`HOnly`); each
opening starts its own duplex, so the verifier is disciplined from any earlier answers (**`disc_verifyWithH`**).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover (Tree)
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript

set_option autoImplicit false

namespace PcsKS.VH

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
      refine (hOnly_squeezeWithH _).bind fun ⟨μ, c₃⟩ ↦ ?_
      dsimp only
      split
      · refine (hOnly_squeezeWithH _).bind fun ⟨t, c₄⟩ ↦ ?_
        dsimp only
        exact (hOnly_squeezeWithH _).bind fun ⟨ρ, _⟩ ↦ hOnly_pure _
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


end PcsKS.VH
