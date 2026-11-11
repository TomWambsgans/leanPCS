-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here. The model is leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0:
-- `Statement/RandomPermutation.lean`).
import ZK.PcsTrace
import LeanVM.Parameters.Field

/-!
# The model's coins

The prover's randomness (`sampleCoins`), a uniform element of `E` (`coinE`) and a uniform digest
(`sampleDigest`) ask only coins. Run by an oracle that answers coins as `ProbComp` does and leaves its state
(`edgeOracle`, mumbai's `lazyRandomPermutationOracles`), they leave the state and draw as `ProbComp` runs them
(`coinsOf`): `edge_sampleCoins`, `edge_coinE`, `runWithRandomPermutation_coinOnly`.

* **`prEvent_coinEs`**: `n` uniform elements, `Pr[coinEs n = rs]` the product of the elements' masses.
* **`prEvent_coinE_ne_zero`**: every element of `E` is a possible `coinE`.
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open scoped ENNReal

namespace PcsQuotient.EndToEnd

/-- The model's coins answered by `ProbComp`'s own (`π` and `π⁻¹` are never asked by the computations below;
they are answered by the zero state). -/
def coinsOf : QueryImpl RandomPermutationOracles ProbComp
  | .inl n => liftM (unifSpec.query n)
  | .inr _ => pure (Vector.replicate 25 0)

/-- **`m` leaves the state and draws as `p`.** -/
def StateIndep {σ α : Type} (m : StateT σ ProbComp α) (p : ProbComp α) : Prop :=
  ∀ s, m.run s = (fun a ↦ (a, s)) <$> p

namespace StateIndep

variable {σ α β : Type}

theorem pure' (a : α) : StateIndep (pure a : StateT σ ProbComp α) (pure a) := fun s ↦ by simp

theorem bind' {m : StateT σ ProbComp α} {p : ProbComp α} {k : α → StateT σ ProbComp β} {q : α → ProbComp β}
    (hm : StateIndep m p) (hk : ∀ a, StateIndep (k a) (q a)) : StateIndep (m >>= k) (p >>= q) := fun s ↦ by
  rw [StateT.run_bind, hm s, bind_map_left, map_bind]
  exact congrArg _ (funext fun a ↦ hk a s)

theorem mapM' {δ : Type} (f : δ → StateT σ ProbComp α) (g : δ → ProbComp α) (hf : ∀ d, StateIndep (f d) (g d)) :
    ∀ l : List δ, StateIndep (l.mapM f) (l.mapM g)
  | [] => by simpa using pure' []
  | d :: l => by
    simp only [List.mapM_cons]
    exact (hf d).bind' fun a ↦ (mapM' f g hf l).bind' fun as ↦ pure' _

end StateIndep

section

variable {σ : Type} (impl : QueryImpl RandomPermutationOracles (StateT σ ProbComp))
  (himpl : ∀ n, StateIndep (impl (.inl n)) (liftM (unifSpec.query n)))
include himpl

theorem indep_coinWord : StateIndep (simulateQ impl coinWord) (simulateQ coinsOf coinWord) := by
  simp only [coinWord, simulateQ_bind, simulateQ_pure, simulateQ_spec_query]
  exact (himpl _).bind' fun _ ↦ StateIndep.pure' _

theorem indep_sampleCoins : StateIndep (simulateQ impl sampleCoins) (simulateQ coinsOf sampleCoins) := by
  simp only [sampleCoins, simulateQ_bind, simulateQ_list_mapM, simulateQ_pure]
  exact (StateIndep.mapM' _ _ (fun _ ↦ indep_coinWord impl himpl) _).bind' fun _ ↦ StateIndep.pure' _

theorem indep_coinE : StateIndep (simulateQ impl coinE) (simulateQ coinsOf coinE) := by
  simp only [coinE, simulateQ_bind, simulateQ_pure]
  exact (indep_coinWord impl himpl).bind' fun _ ↦ (indep_coinWord impl himpl).bind' fun _ ↦
    (indep_coinWord impl himpl).bind' fun _ ↦ StateIndep.pure' _

theorem indep_coinEs (n : ℕ) : StateIndep (simulateQ impl (coinEs n)) (simulateQ coinsOf (coinEs n)) := by
  simp only [coinEs, simulateQ_list_mapM]
  exact StateIndep.mapM' _ _ (fun _ ↦ indep_coinE impl himpl) _

end

theorem edge_coin {A : Type} (n : ℕ) :
    StateIndep (edgeOracle (A := A) (.inl n)) (liftM (unifSpec.query n)) := fun s ↦ by
  rw [show edgeOracle (A := A) (.inl n) = onEdges (lazyRandomPermutationOracles (.inl n)) from rfl]
  show (fun p ↦ (p.1, (p.2, s.2))) <$> (lazyRandomPermutationOracles (.inl n)).run s.1 = _
  simp [lazyRandomPermutationOracles, StateT.run, liftM, monadLift, MonadLift.monadLift, StateT.lift]

theorem lazy_coin (n : ℕ) :
    StateIndep (lazyRandomPermutationOracles (.inl n)) (liftM (unifSpec.query n)) := fun s ↦ by
  simp [lazyRandomPermutationOracles, StateT.run, liftM, monadLift, MonadLift.monadLift, StateT.lift]

/-- A coin-only computation, run in the model, is its run by `coinsOf`. -/
theorem runWithRandomPermutation_of_indep {α : Type} {G : OracleComp RandomPermutationOracles α} {p : ProbComp α}
    (h : StateIndep (simulateQ lazyRandomPermutationOracles G) p) : runWithRandomPermutation G = p := by
  show Prod.fst <$> (simulateQ lazyRandomPermutationOracles G).run [] = p
  rw [h [], Functor.map_map]
  simp

/-- The distribution of the prover's randomness. -/
noncomputable def coinsDist : ProbComp Coins := simulateQ coinsOf sampleCoins

/-- The distribution of a uniform element of `E`. -/
noncomputable def eDist : ProbComp E := simulateQ coinsOf coinE

theorem runWithRandomPermutation_sampleCoins_map {β : Type} (f : Coins → β) :
    runWithRandomPermutation (do return f (← sampleCoins)) = f <$> coinsDist := by
  refine runWithRandomPermutation_of_indep ?_
  rw [show (do return f (← sampleCoins) : OracleComp RandomPermutationOracles β) = sampleCoins >>= fun c ↦ pure (f c)
    from rfl, simulateQ_bind, map_eq_bind_pure_comp]
  exact (indep_sampleCoins _ lazy_coin).bind' fun _ ↦ by simpa using StateIndep.pure' _

theorem runWithRandomPermutation_coinEs (n : ℕ) :
    runWithRandomPermutation (coinEs n) = (List.range n).mapM fun _ ↦ eDist := by
  refine runWithRandomPermutation_of_indep ?_
  have := indep_coinEs _ lazy_coin n
  simpa [coinEs, simulateQ_list_mapM, eDist] using this

/-- An expectation over an image. -/
theorem tsum_map {γ δ : Type} (X : ProbComp γ) (f : γ → δ) (g : δ → ℝ≥0∞) :
    ∑' o, Pr{let y ← f <$> X}[y = o] * g o = ∑' a, Pr{let y ← X}[y = a] * g (f a) := by
  rw [map_eq_bind_pure_comp, tsum_prEvent_bind_mul]
  refine tsum_congr fun a ↦ ?_
  congr 1
  rw [Function.comp_apply]
  classical
  simp only [RProg.prEvent_pure_eq]
  rw [tsum_eq_single (f a) fun b hb ↦ by rw [ite_eq_right (Ne.symm hb), zero_mul]]
  simp

/-! ### Products of uniform draws -/

theorem prEvent_mapM_const {δ α : Type} (X : ProbComp α) :
    ∀ (l : List δ) (rs : List α), rs.length = l.length →
      Pr{let y ← l.mapM fun _ ↦ X}[y = rs] = (rs.map fun r ↦ Pr{let y ← X}[y = r]).prod
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | d :: l, r :: rs, h => by
    classical
    simp only [List.mapM_cons, List.map_cons, List.prod_cons]
    rw [prEvent_bind_eq_tsum]
    have hterm : ∀ a, Pr{let z ← X}[z = a] *
        Pr{let y ← (do let as ← l.mapM fun _ ↦ X; pure (a :: as))}[y = r :: rs] =
        if a = r then Pr{let z ← X}[z = r] * (rs.map fun r ↦ Pr{let y ← X}[y = r]).prod else 0 := by
      intro a
      rw [prEvent_bind_eq_tsum]
      split_ifs with ha
      · subst ha
        have hrest : ∀ as, Pr{let y ← l.mapM fun _ ↦ X}[y = as] * Pr{let y ← (pure (a :: as) : ProbComp _)}[y = a :: rs]
            = if as = rs then Pr{let y ← l.mapM fun _ ↦ X}[y = rs] else 0 := by
          intro as
          rw [RProg.prEvent_pure_eq]
          by_cases has : as = rs
          · subst has; simp
          · simp [has]
        rw [tsum_congr hrest, tsum_ite_eq, prEvent_mapM_const X l rs (by simpa using h)]
      · have hrest : ∀ as, Pr{let y ← l.mapM fun _ ↦ X}[y = as] * Pr{let y ← (pure (a :: as) : ProbComp _)}[y = r :: rs]
            = 0 := by
          intro as
          rw [RProg.prEvent_pure_eq]
          simp [ha]
        rw [tsum_congr hrest, tsum_zero, mul_zero]
    rw [tsum_congr hterm, tsum_ite_eq]


theorem prEvent_coinEs (rs : List E) (h : rs.length = 5) :
    Pr{let y ← runWithRandomPermutation (coinEs 5)}[y = rs] = (rs.map fun r ↦ Pr{let y ← eDist}[y = r]).prod := by
  rw [runWithRandomPermutation_coinEs, prEvent_mapM_const eDist (List.range 5) rs (by simpa using h)]

/-- **Every element of `E` is a possible uniform draw.** -/
theorem prEvent_eDist_ne_zero (r : E) : Pr{let y ← eDist}[y = r] ≠ 0 := by
  refine prEvent_ne_zero_of_mem_support ?_
  simp only [eDist, coinE, coinWord, simulateQ_bind, simulateQ_pure, simulateQ_spec_query, coinsOf,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
  have hw : ∀ w : UInt64, ∃ x ∈ support (liftM (unifSpec.query (2 ^ 64 - 1)) : ProbComp (Fin (2 ^ 64 - 1 + 1))),
      w = UInt64.ofNat ↑x := fun w ↦
    ⟨⟨w.toNat, by simpa using w.toNat_lt⟩, by simp, by simp⟩
  exact ⟨(r.limb 0).lane, hw _, (r.limb 1).lane, hw _, (r.limb 2).lane, hw _, (ofLimbs_limb r).symm⟩

end PcsQuotient.EndToEnd
