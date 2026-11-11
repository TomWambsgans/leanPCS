-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Uses leanerVM `mumbai`'s cost lemmas (https://github.com/Verified-zkEVM/leanerVM, commit
-- 6175f1a0, MIT OR Apache-2.0, `lean_vm/LeanVM/Protocol/Rpm/Cost.lean`): `Short`,
-- `hashBlocks_le_of_short`, `WidthsLE`, `widthsLE_commitStack`, `widthsLE_verifyWhir`,
-- `allQ_runProof`, `isWeightBound_of_isTotalQueryBound`, as `isWeightBound_verifier` there.
import Compose.Claims
import Compose.Rpm
import PcsQuotient.Security
import QuotientSecurity.Deployed
import Shared.SoundnessDefs

/-!
# Cost lemmas of the openings' verifier

The widths of a variant's verifier program (`widthsLE_variantProg`), the lengths of the claims' bytes
(`length_claimsBytes`, `length_flat`), and every query of an opening's verifier is a permutation call
(`allQ_ourVerifier`).

Pruned to what the leanVM line uses (`formal/Uni*`, `formal/Rec*`); the previous membership protocol's declarations
that were here are in the git history.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp

namespace Soundness

open QuotientRpm QuotientSecurity Compose Compose.Reduce LeanVM LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile WhirBridge
open LeanVM.Rpm (Short hashBlocks WidthsLE maxWidth)

/-- Every commitment of the opening's program has width at most `192`. -/
theorem widthsLE_variantProg (S : Stacking) (R : ℕ) (cs : List Claim) :
    WidthsLE maxWidth (variantProg S R cs) := by
  unfold variantProg
  refine LeanVM.Rpm.WidthsLE.seq (LeanVM.Rpm.widthsLE_commitStack _ _) fun _ => ?_
  refine LeanVM.Rpm.WidthsLE.seq ?_ fun _ => trivial
  rw [Stacking.check_eq_ite]
  split_ifs
  · rw [LeanVM.Protocol.Verifier.verifyStackedOpening_eq_target]
    exact LeanVM.Rpm.WidthsLE.seq
      (LeanVM.Rpm.WidthsLE.of_moves (g := fun _ ↦ True) LeanVM.Protocol.EndToEnd.Sound.MovesOK.sampleE)
      fun _ ↦ LeanVM.Rpm.widthsLE_verifyWhir _ _ _ _
  · trivial

theorem length_claimsBytes (cs : List Claim) :
    (claimsBytes cs).length = 24 * (flat cs).length := by
  simp [claimsBytes, List.length_flatMap, scalarBytes_length, Nat.mul_comm]

theorem length_flat (cs : List Claim) : (flat cs).length = (cs.map fun c => c.point.length + 1).sum := by
  simp [flat, List.length_flatMap]

/-- **An opening of at most two claims of at most `2^30` coordinates makes short queries only.** -/
theorem allQ_ourVerifier (L : Layout) (R : ℕ) (w : (Digest × Stmt L.stacking) × Proof)
    (h2 : w.1.2.claims.length ≤ 2) (hv : L.vars ≤ 2 ^ 30) :
    AllQueriesSatisfy (ourVerifier L R w) Short := by
  rw [ourVerifier_eq]
  by_cases hne : w.1.2.claims.isEmpty = false
  swap
  · simp only [hne]; trivial
  simp only [hne, ↓reduceIte]
  refine allQueriesSatisfy_bind (allQueriesSatisfy_bind (LeanVM.Rpm.allQ_queryH ?_)
    fun _ => LeanVM.Rpm.allQ_queryF _) fun seed => ?_
  · rw [List.length_append, openingPrefix_length, length_claimsBytes, length_flat]
    have hpt : ∀ c ∈ w.1.2.claims, c.point.length + 1 ≤ 2 ^ 30 + 1 := fun c hc => by
      have := w.1.2.wide c hc
      simp only [Layout.stacking] at this
      omega
    have hs := List.sum_le_length_nsmul (w.1.2.claims.map fun c => c.point.length + 1)
      (2 ^ 30 + 1) (by simpa using hpt)
    simp only [List.length_map, smul_eq_mul] at hs
    have : w.1.2.claims.length * (2 ^ 30 + 1) ≤ 2 * (2 ^ 30 + 1) := Nat.mul_le_mul_right _ h2
    omega
  · by_cases hr : WhirBridge.rootOf w.2 = some w.1.1
    · simp only [hr, ↓reduceIte]
      exact LeanVM.Rpm.allQ_runProof _ seed _ (widthsLE_variantProg _ _ _)
    · simp only [hr, ↓reduceIte]; trivial

end Soundness
