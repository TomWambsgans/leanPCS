-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the duplex discipline (`LeanVM.Rpm.DuplexVm`, `DuplexP`, `HOnly`) and its
-- rules for the sponge, the runners and the Merkle trees (`duplexP_absorb`, `duplexP_run`,
-- `duplexP_findNonceM`, `duplexP_powStepM`, `hOnly_buildTreeM`, `admissibleVm_seedInput`).
import E2ECompleteness.HashLen
import E2ECompleteness.WithHash
import E2ECompleteness.End
import CompPoly.Fields.Binary.BF64.Ext3
import CompPoly.Fields.Binary.BF64.Impl
import CompPoly.Fields.Extension.Arithmetic
import LeanVM.Protocol.Compile.Rom.Bridge
import LeanVM.Protocol.Compile.Rom.Prover
import LeanVM.Protocol.ExperimentBridge
import LeanVM.Protocol.LeanVMRpm
import LeanVM.Protocol.Rpm.Duplex
import LeanVM.Protocol.WithHash
import LeanVM.Protocol.WithHashBridge
import PcsQuotient.Security

/-!
# The layout opening only calls the permutation through the sponge

`Disc` (a computation's permutation calls are all sponge duplexes) through binds, the commitment
(`hOnly_commitWithH`), the opening's sponge (`duplexP_openingSpongeWithH`), the verifier
(`disc_openingWithH`) and the prover (`duplexP_runFromWithHash`, `disc_proveOpeningWithH`).

Pruned to what the leanVM line uses (`formal/Uni*`, `formal/Rec*`); the previous membership protocol's declarations
that were here are in the git history.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover (Tree)
open scoped ENNReal
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript

set_option autoImplicit false

namespace E2ECompleteness

/-- Disciplined from any earlier answers. -/
def Disc {α : Type} (X : OracleComp KeccakCalls α) : Prop :=
  ∀ h : List KeccakState, DuplexP X h fun _ _ ↦ True

theorem Disc.bind {α β : Type} {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β}
    (hX : Disc X) (hf : ∀ a, Disc (f a)) : Disc (X >>= f) :=
  fun h ↦ (hX h).bind fun a h' _ ↦ hf a h'

theorem disc_pure {α : Type} (a : α) : Disc (pure a : OracleComp KeccakCalls α) := fun _ ↦ trivial

theorem disc_of_hOnly {α : Type} {X : OracleComp KeccakCalls α} (hX : HOnly X) : Disc X :=
  fun h ↦ (hX.duplexP h).mono fun _ _ _ ↦ trivial

/-! ## The hash-only pieces -/

theorem hOnly_commitWithH (μ : ℕ) (stack : Array K) : HOnly (commitWithH callKeccak256 μ stack) :=
  hOnly_buildTreeM _ _

/-! ## The openings -/

theorem duplexP_openingSpongeWithH (L : PcsQuotient.Layout) (claims : List PcsQuotient.Claim)
    (h : List KeccakState) :
    DuplexP (openingSpongeWithH callKeccak256 callKeccakF1600 L claims) h
      fun sp h' ↦ sp.state ∈ h' := by
  unfold openingSpongeWithH
  refine (((hOnly_queryH _).duplexP h)).bind fun iv h' hh ↦ ?_
  subst hh
  exact (duplexP_queryF_bind _ _ _ _).mpr
    ⟨admissibleVm_seedInput _ _ _, fun y ↦ List.mem_cons_self⟩

/-- **The verifier's opening is disciplined.** -/
theorem disc_openingWithH (L : PcsQuotient.Layout) (root : Digest)
    (claims : List PcsQuotient.Claim) (proof : Compile.Proof) :
    Disc (openingWithH callKeccak256 callKeccakF1600 L root claims proof) := by
  intro h
  unfold openingWithH
  split
  · split
    · refine (duplexP_openingSpongeWithH L claims h).bind fun sp h₁ hs ↦ ?_
      refine (duplexP_absorb hs _ _).bind fun sp h₂ hs ↦ ?_
      refine (duplexP_absorb hs _ _).bind fun sp h₃ hs ↦ ?_
      split
      · split
        · exact (duplexP_run _ _ _ hs).bind fun z _ _ ↦ by split <;> trivial
        · trivial
      · trivial
    · trivial
  · trivial

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
theorem disc_proveOpeningWithH (fuel : ℕ) (L : PcsQuotient.Layout) (tree : Tree)
    (stack : Array K) (claims : List PcsQuotient.Claim) :
    Disc (proveOpeningWithH callKeccak256 callKeccakF1600 fuel L tree stack claims) := by
  intro h
  unfold proveOpeningWithH
  refine (duplexP_openingSpongeWithH L claims h).bind fun sp h₁ hs ↦ ?_
  refine (duplexP_absorb hs _ _).bind fun sp h₂ hs ↦ ?_
  refine (duplexP_absorb hs _ _).bind fun sp h₃ hs ↦ ?_
  exact (duplexP_runFromWithHash _ _ _ _ _ _ hs).bind fun _ _ _ ↦ trivial

end E2ECompleteness
