-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Generalizes the staging of `formal/Compose/Compose/{Deployed,DeployedWired}.lean` of this repository (each
-- opening's stage logged from the start, its doom an event of `romExperiment`, through
-- `Compose/Coupling.lean`) to any number of stages; `romExperiment` is leanerVM `mumbai`'s
-- (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR Apache-2.0).
import SoundPcs.Imports

/-!
# Stages: a run of openings, each logged from the start

The deployed verifier runs six openings one after the other. Each opening's soundness (F2) is an event of
`romExperiment` (the run up to the opening as its adversary, the opening as its verifier, the oracle's cache at
the opening's end), so the composed run is built in **stages**: `stage pre V` runs `pre`, then the verdict
`V a`, and logs every Keccak-256 query of both from the start (`Compose.logImplKC`), so the cache at the end of
`V` is read off the stage's transcript (`Compose.Coupling`).

* **`prEvent_stage_now`**: an event of the stage's result, verdict and the cache its transcript records is the
  same event of `romExperiment pre V` (`Compose.prEvent_loggedPrefix`);
* **`prEvent_stage_keep`**: a later stage changes no event of the earlier result;
* **`stage_run`**: against a table, the stage asks what `pre` asks, then what `V` asks; its transcript is the
  Keccak-256 part of both;
* **`prEvent_logged_cache`**: an event of the cache the transcript of a logged run records is the event of the
  oracle's final cache (the binding of `PcsBindingCoords` is an event of the final cache);
* **`prEvent_optV_le`**: an opening run only on some inputs (`optV`) is bounded by the opening run on all.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace SoundPcs

open Compose QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Protocol.Rom (romExperiment romExperiment_map romExperiment_eq)

/-! ## A stage -/

/-- **A stage**: the run so far `pre`, then the verdict `V a`, every Keccak-256 query of both logged from the
start: `((a, b), t)`. -/
def stage {α : Type} (pre : OracleComp KeccakCalls α) (V : α → OracleComp KeccakCalls Bool) :
    OracleComp KeccakCalls ((α × Bool) × Transcript) :=
  (simulateQ logImplKC (pre >>= fun a => (a, ·) <$> V a)).run []

/-- **An event of the stage's verdict at its end is an event of `romExperiment`.** -/
theorem prEvent_stage_now {α : Type} (pre : OracleComp KeccakCalls α)
    (V : α → OracleComp KeccakCalls Bool) (E : α → Bool → KeccakCalls.QueryCache → Prop)
    (hE : ReadsInl E) :
    Pr{let z ← (simulateQ randomOracle (stage pre V)).run' ∅}[E z.1.1 z.1.2 (cacheOfTr z.2)] =
      Pr{let z ← romExperiment pre V}[E z.1.1 z.1.2 z.2] :=
  prEvent_loggedPrefix pre V E hE

/-- **A stage keeps the earlier result**: an event of it has the probability it had before. -/
theorem prEvent_stage_keep {α : Type} (pre : OracleComp KeccakCalls α)
    (V : α → OracleComp KeccakCalls Bool) (E : α → Prop) :
    Pr{let z ← (simulateQ randomOracle (stage pre V)).run' ∅}[E z.1.1] =
      Pr{let z ← (simulateQ randomOracle pre).run' ∅}[E z] := by
  rw [show (fun z : (α × Bool) × Transcript => E z.1.1) = fun z => (fun w : α × Bool => E w.1) z.1
    from rfl]
  rw [stage, prEvent_run'_loggedKC (pre >>= fun a => (a, ·) <$> V a) [] ∅ (fun w : α × Bool => E w.1)]
  exact prEvent_run'_bind_keep pre V ∅ E

theorem isTotalQueryBound_stage {α : Type} (pre : OracleComp KeccakCalls α)
    (V : α → OracleComp KeccakCalls Bool) (Qp QV : ℕ) (hp : IsTotalQueryBound pre Qp)
    (hV : ∀ a, IsTotalQueryBound (V a) QV) : IsTotalQueryBound (stage pre V) (Qp + QV) :=
  isTotalQueryBound_loggedKC_run _ _ _ (isTotalQueryBound_bind (ob := fun a => (a, ·) <$> V a) hp
    fun a => (isQueryBound_map_iff (V a) (fun b => (a, b)) QV _ _).mpr (hV a))

/-- **A stage against a table**: it asks what `pre` asks, then what the verdict asks; its result is `pre`'s
and the verdict's, its transcript the Keccak-256 part of both logs. -/
theorem stage_run {α : Type} (pre : OracleComp KeccakCalls α) (V : α → OracleComp KeccakCalls Bool)
    (T : KTable) :
    tableQueryLog (stage pre V) T = tableQueryLog pre T ++
        tableQueryLog (V (evalWithAnswerFn (QueryImpl.ofFn T) pre)) T ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (stage pre V) =
        ((evalWithAnswerFn (QueryImpl.ofFn T) pre,
          evalWithAnswerFn (QueryImpl.ofFn T) (V (evalWithAnswerFn (QueryImpl.ofFn T) pre))),
          (tableQueryLog pre T ++
            tableQueryLog (V (evalWithAnswerFn (QueryImpl.ofFn T) pre)) T).filterMap inlEntry) := by
  obtain ⟨h1l, h1e⟩ := run_keep pre V T
  obtain ⟨h2l, h2e⟩ := run_logged (pre >>= fun a => (a, ·) <$> V a) T
  refine ⟨?_, ?_⟩
  · show tableQueryLog ((simulateQ logImplKC (pre >>= fun a => (a, ·) <$> V a)).run []) T = _
    rw [h2l, h1l]
  · show evalWithAnswerFn (QueryImpl.ofFn T)
      ((simulateQ logImplKC (pre >>= fun a => (a, ·) <$> V a)).run []) = _
    rw [h2e, h1e, h1l]

/-! ## The final cache -/

/-- **An event of the cache a logged run's transcript records is the event of the oracle's final cache**, for
an event that reads Keccak-256's answers only. -/
theorem prEvent_logged_cache {α : Type} (v : OracleComp KeccakCalls α)
    (E : KeccakCalls.QueryCache → Prop)
    (hE : ∀ c c' : KeccakCalls.QueryCache, (∀ x, c (.inl x) = c' (.inl x)) → (E c ↔ E c')) :
    Pr{let z ← (simulateQ randomOracle ((simulateQ logImplKC v).run [])).run' ∅}[E (cacheOfTr z.2)] =
      Pr{let z ← (simulateQ randomOracle v).run ∅}[E z.2] := by
  rw [StateT.run'_eq, prEvent_map]
  refine (prEvent_congr_of_support _
    (fun z : (α × Transcript) × KeccakCalls.QueryCache => E (cacheOfTr z.1.2))
    (fun z => E z.2) fun z hz => hE _ _
    fun x => (consistent_run_loggedKC _ [] ∅ consistent_nil z hz x).symm).trans ?_
  refine (prEvent_map _ (fun z : (α × Transcript) × KeccakCalls.QueryCache => (z.1.1, z.2))
    (fun w => E w.2)).symm.trans ?_
  rw [map_run_loggedKC]

/-! ## Openings run on some inputs only -/

/-- **An opening run on an input if there is one**, rejecting otherwise. -/
def optV {β : Type} (V : β → OracleComp KeccakCalls Bool) : Option β → OracleComp KeccakCalls Bool
  | some w => V w
  | none => pure false

/-- The doom of an opening run on an input, if there is one. -/
def OptDoom {β : Type} (D : β → KeccakCalls.QueryCache → Prop) :
    Option β → KeccakCalls.QueryCache → Prop
  | some w, c => D w c
  | none, _ => False

theorem isTotalQueryBound_optV {β : Type} (V : β → OracleComp KeccakCalls Bool) (QV : ℕ)
    (hV : ∀ w, IsTotalQueryBound (V w) QV) (o : Option β) : IsTotalQueryBound (optV V o) QV := by
  cases o with
  | some w => exact hV w
  | none => trivial

theorem readsInl_optDoom {α β : Type} (f : α → Option β) (D : β → KeccakCalls.QueryCache → Prop)
    (hD : ∀ w (c c' : KeccakCalls.QueryCache), (∀ x, c (.inl x) = c' (.inl x)) → (D w c ↔ D w c')) :
    ReadsInl fun (a : α) (b : Bool) (c : KeccakCalls.QueryCache) => b = true ∧ OptDoom D (f a) c := by
  intro a b c c' h
  cases hf : f a with
  | none => simp [hf, OptDoom]
  | some w => simp only [hf, OptDoom]; rw [hD w c c' h]

/-- **An opening run on some inputs only is bounded by the opening run on all**, the adversary's output mapped
to the input (a default where there is none). -/
theorem prEvent_optV_le {α β : Type} [Inhabited β] (A : OracleComp KeccakCalls α) (f : α → Option β)
    (V : β → OracleComp KeccakCalls Bool) (D : β → KeccakCalls.QueryCache → Prop) :
    Pr{let z ← romExperiment A (fun a => optV V (f a))}[z.1.2 = true ∧ OptDoom D (f z.1.1) z.2] ≤
      Pr{let z ← romExperiment ((fun a => (f a).getD default) <$> A) V}[
        z.1.2 = true ∧ D z.1.1 z.2] := by
  rw [romExperiment_map, prEvent_map, romExperiment_eq, romExperiment_eq]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun p => ?_
  rw [prEvent_map, prEvent_map]
  cases hf : f p.1 with
  | none =>
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun r _ hev => ?_) bot_le
    simp only [hf, OptDoom] at hev
    exact hev.2
  | some w =>
    simp only [hf, optV, Option.getD_some, OptDoom]
    exact le_rfl

end SoundPcs
