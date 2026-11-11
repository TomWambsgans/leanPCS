-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Completeness.Read
import Compose.Claims
import Compose.Rpm
import LeanVM.Protocol.Compile.Rom.Bridge
import LeanVM.Protocol.Rpm.Paths
import LeanVM.Protocol.WithHashBridge
import LeanVM.Prover.Ntt
import PcsQuotient.Security
import QuotientSecurity.DeployedBasis
import QuotientSecurity.DeployedConcrete
import Soundness.Cost
import Soundness.TreeLog
import Soundness.Extract
import Soundness.EarlyStop
import Bridge.Setup
import Bridge.Verifier
import Bridge.Ntt
import Bridge.Opening
import Bridge.Chain
import Bridge.Claims.Constants

/-!
# Two steps of the soundness argument

`prEvent_le_of_continuations`: two games that share a prefix and whose continuations compare compare; and
`ofB_toB_root`: Compose's 32 bytes of a digest spell the digest back.

Pruned to what the leanVM line uses (`formal/Uni*`, `formal/Rec*`); the previous membership protocol's declarations
that were here are in the git history.
-/

set_option linter.unusedSectionVars false
set_option simprocs false

open OracleSpec OracleComp
open scoped ENNReal

namespace Soundness

open QuotientRpm QuotientSecurity Compose Compose.Reduce LeanVM LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile WhirBridge

/-! ## The experiments, a common prefix then the verifier -/

/-- **A comparison of the verifiers, run last, survives the common prefix** of two games against
the lazily sampled permutation. -/
theorem prEvent_le_of_continuations {α β₁ β₂ γ₁ γ₂ : Type}
    (X : OracleComp Common.RandomPermutationOracles α)
    (V₁ : α → OracleComp Common.RandomPermutationOracles β₁)
    (V₂ : α → OracleComp Common.RandomPermutationOracles β₂)
    (g₁ : α → β₁ → γ₁) (g₂ : α → β₂ → γ₂) (P₁ : γ₁ → Prop) (P₂ : γ₂ → Prop)
    (h : ∀ a s, Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles (V₁ a)).run' s}[
        P₁ (g₁ a v)] ≤
      Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles (V₂ a)).run' s}[P₂ (g₂ a v)]) :
    Pr{let z ← Common.runWithRandomPermutation (X >>= fun a => V₁ a >>= fun v => pure (g₁ a v))}[
        P₁ z] ≤
      Pr{let z ← Common.runWithRandomPermutation (X >>= fun a => V₂ a >>= fun v => pure (g₂ a v))}[
        P₂ z] := by
  unfold Common.runWithRandomPermutation
  refine mono_bind _ X _ _ _ _ (fun a s => ?_) []
  have e : ∀ {β γ : Type} (V : OracleComp Common.RandomPermutationOracles β) (g : β → γ),
      (simulateQ Common.lazyRandomPermutationOracles (V >>= fun v => pure (g v))).run' s =
        g <$> (simulateQ Common.lazyRandomPermutationOracles V).run' s := by
    intro β γ V g
    have hm : (V >>= fun v => pure (g v)) = g <$> V := by
      rw [map_eq_bind_pure_comp]
      rfl
    rw [hm, simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map,
      Functor.map_map, Functor.map_map]
  rw [e, e, prEvent_map, prEvent_map]
  exact h a s

/-! ## The constants, the instance, the wire, the setup -/

/-- Compose's bytes of a digest spell it back. -/
theorem ofB_toB_root (d : Digest) : ofB (toB d) = d := LeanVM.Rpm.digestOfRpm_toRpm d

end Soundness
