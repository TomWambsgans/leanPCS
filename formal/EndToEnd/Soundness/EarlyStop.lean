-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Compose.Claims
import Compose.Rpm
import PcsQuotient.Security
import QuotientSecurity.DeployedConcrete
import Shared.SoundnessDefs

/-!
# Simulated computations: generic steps

The generic steps of the early-stop comparison: a comparison of continuations survives a common simulated
prefix (`mono_bind`, with `run'_bind`, `run'_pure`, `le_pure`), and an event no output of a computation meets has
probability zero under any stateful simulation (`zero_of_support`, `zero_pure`).

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

section Sim

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ : Type}
  (impl : QueryImpl spec (StateT σ ProbComp))

theorem run'_bind {α β : Type} (oa : OracleComp spec α) (k : α → OracleComp spec β) (s : σ) :
    (simulateQ impl (oa >>= k)).run' s =
      (simulateQ impl oa).run s >>= fun p => (simulateQ impl (k p.1)).run' p.2 := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

/-- **A comparison of continuations survives a common simulated prefix.** -/
theorem mono_bind {α β γ : Type} (oa : OracleComp spec α) (k₁ : α → OracleComp spec β)
    (k₂ : α → OracleComp spec γ) (E₁ : β → Prop) (E₂ : γ → Prop)
    (h : ∀ x s, Pr{let y ← (simulateQ impl (k₁ x)).run' s}[E₁ y] ≤
      Pr{let y ← (simulateQ impl (k₂ x)).run' s}[E₂ y]) (s : σ) :
    Pr{let y ← (simulateQ impl (oa >>= k₁)).run' s}[E₁ y] ≤
      Pr{let y ← (simulateQ impl (oa >>= k₂)).run' s}[E₂ y] := by
  rw [run'_bind, run'_bind]
  exact prEvent_bind_mono_of_forall_le _ _ _ _ _ fun p => h p.1 p.2

theorem run'_pure {α : Type} (x : α) (s : σ) :
    (simulateQ impl (pure x : OracleComp spec α)).run' s = pure x := by
  rw [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]

/-- An event the returned value misses has probability zero. -/
theorem zero_pure {α : Type} (x : α) (E : α → Prop) (hx : ¬ E x) (s : σ) :
    Pr{let y ← (simulateQ impl (pure x : OracleComp spec α)).run' s}[E y] = 0 := by
  rw [run'_pure]
  exact prEvent_eq_zero_of_forall_mem_support _ _ fun y hy => by
    rw [support_pure, Set.mem_singleton_iff] at hy
    exact hy ▸ hx

/-- Pure continuations are ordered by their events. -/
theorem le_pure {α β : Type} (x : α) (y : β) (E₁ : α → Prop) (E₂ : β → Prop)
    (h : E₁ x → E₂ y) (s : σ) :
    Pr{let z ← (simulateQ impl (pure x : OracleComp spec α)).run' s}[E₁ z] ≤
      Pr{let z ← (simulateQ impl (pure y : OracleComp spec β)).run' s}[E₂ z] := by
  classical
  rw [run'_pure, run'_pure, prEvent_pure, prEvent_pure]
  split_ifs with h1 h2 <;> simp_all

/-- **An event no output of a computation meets has probability zero**, under any stateful
simulation. -/
theorem zero_of_support {α : Type} (oa : OracleComp spec α) (E : α → Prop)
    (h : ∀ x ∈ support oa, ¬ E x) (s : σ) :
    Pr{let y ← (simulateQ impl oa).run' s}[E y] = 0 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => exact zero_pure impl a E (h a (by rw [support_pure]; rfl)) s
  | query_bind t k ih =>
    rw [run'_bind]
    refine le_antisymm (prEvent_bind_le_of_forall_le _ _ _ fun p => ?_) bot_le
    refine (ih p.1 (fun x hx => h x ?_) p.2).le
    rw [mem_support_bind_iff]
    exact ⟨p.1, mem_support_query t p.1, hx⟩

end Sim

end Soundness
