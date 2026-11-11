-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here. `card_vec` follows leanerVM `mumbai` (6175f1a0, MIT OR Apache-2.0:
-- `lean_vm/LeanVM/Protocol/Compile/Rom/Encoding.lean`).
import ZK.PcsIdealC

/-!
# Bounding the cost of a program

Tools for `badB` (the tracked queries' local costs along the ideal run): a step averages, an entropy step (state
independent) averages over its distribution, a tracked query costs whether its input is an edge's input plus the
used fraction, and its answer is uniform (`badB_q`). An input that is an injective function of a fresh value of
mass at most `p` lies among `L` edges' inputs with probability at most `L p` (`prEvent_mem_le`).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open FProg

variable {A α β : Type}

/-! ### Counting -/

/-- `UInt64` as `Fin (2^64)`. -/
def u64Equiv : UInt64 ≃ Fin (2 ^ 64) :=
  { toFun := fun w ↦ w.toFin, invFun := fun i ↦ UInt64.ofFin i,
    left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }

theorem card_uint64 : Fintype.card UInt64 = 2 ^ 64 := by
  rw [Fintype.card_congr u64Equiv, Fintype.card_fin]

def vecEquiv (n : ℕ) : Vector UInt64 n ≃ (Fin n → UInt64) where
  toFun v i := v[i]
  invFun f := Vector.ofFn f
  left_inv _ := Vector.ext fun _ _ ↦ Vector.getElem_ofFn _
  right_inv _ := funext fun _ ↦ Vector.getElem_ofFn _

theorem card_vec (n : ℕ) (inst : Fintype (Vector UInt64 n)) :
    @Fintype.card (Vector UInt64 n) inst = 2 ^ (64 * n) := by
  rw [@Fintype.card_congr _ _ inst _ (vecEquiv n), Fintype.card_fun, Fintype.card_fin, card_uint64, ← pow_mul]

set_option exponentiation.threshold 2000 in
theorem card_state : Fintype.card KeccakState = 2 ^ 1600 := card_vec 25 _

/-! ### Averages -/

theorem wavg_le {γ : Type} (X : ProbComp γ) (g : γ → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ o ∈ support X, g o ≤ c) :
    ∑' o, Pr{let y ← X}[y = o] * g o ≤ c := by
  classical
  calc ∑' o, Pr{let y ← X}[y = o] * g o ≤ ∑' o, Pr{let y ← X}[y = o] * c := by
        refine ENNReal.tsum_le_tsum fun o ↦ ?_
        by_cases ho : o ∈ support X
        · gcongr; exact h o ho
        · rw [prEvent_eq_zero_of_not_mem_support _ ho, zero_mul, zero_mul]
    _ = c := by rw [ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul]

/-- **A tracked query, ideally**: its local cost, then a uniform answer. -/
theorem badB_q (x : KeccakState) (k : KeccakState → FProg A α) (s : Edges × A) :
    badB (.q x k) s = εq s x + ∑' y, Pr{let z ← uState}[z = y] * badB (k y) ((x, y) :: s.1, s.2) := by
  rw [badB]
  congr 1
  exact tsum_map uState (fun y ↦ (y, ((x, y) :: s.1, s.2))) fun p ↦ badB (k p.1) p.2

/-- A drawn element's cost is that of the step that draws it. -/
theorem badB_r (k : E → FProg A α) (s : Edges × A) : badB (.r k) s = badB (.step rDraw k) s := by
  simp only [badB]

theorem rDraw_indep : StateIndep (rDraw (A := A)) eDist := fun _ ↦ rfl

theorem badB_step_le {γ : Type} (m : StateT (Edges × A) ProbComp γ) (k : γ → FProg A α) (s : Edges × A) (c : ℝ≥0∞)
    (h : ∀ p ∈ support (m.run s), badB (k p.1) p.2 ≤ c) : badB (.step m k) s ≤ c := by
  rw [badB]
  exact wavg_le _ _ _ h

theorem badB_step_indep {γ : Type} (m : StateT (Edges × A) ProbComp γ) (D : ProbComp γ) (hm : StateIndep m D)
    (k : γ → FProg A α) (s : Edges × A) :
    badB (.step m k) s = ∑' u, Pr{let y ← D}[y = u] * badB (k u) s := by
  rw [badB, hm s]
  exact tsum_map D (fun u ↦ (u, s)) fun p ↦ badB (k p.1) p.2

theorem tsum_add_le {γ : Type} (D : ProbComp γ) (f g : γ → ℝ≥0∞) :
    ∑' u, Pr{let y ← D}[y = u] * (f u + g u) =
      ∑' u, Pr{let y ← D}[y = u] * f u + ∑' u, Pr{let y ← D}[y = u] * g u := by
  rw [← ENNReal.tsum_add]
  exact tsum_congr fun u ↦ mul_add _ _ _

/-! ### Edges' inputs -/

/-- `x` is an edge's input. -/
def inDom (s : Edges × A) (x : KeccakState) : Prop := (forwardLookup s.1 x).isSome

theorem inDom_cons (E : Edges) (a : A) (x y z : KeccakState) :
    inDom ((x, y) :: E, a) z ↔ x = z ∨ inDom (E, a) z := by
  simp only [inDom, forwardLookup]
  split_ifs with h <;> simp [h]

theorem mem_of_inDom {s : Edges × A} {z : KeccakState} (h : inDom s z) : z ∈ s.1.map Prod.fst := by
  obtain ⟨E, a⟩ := s
  induction E with
  | nil => simp [inDom, forwardLookup] at h
  | cons e E ih =>
    obtain ⟨x, y⟩ := e
    rcases (inDom_cons E a x y z).1 h with rfl | h'
    · simp
    · simp [ih h']

/-- The used fraction: `N⁻¹`, `N = 2^1600`. -/
noncomputable def nInv : ℝ≥0∞ := (Fintype.card KeccakState : ℝ≥0∞)⁻¹

theorem εq_le (s : Edges × A) (x : KeccakState) [Decidable (inDom s x)] :
    εq s x ≤ (if inDom s x then 1 else 0) + (s.1.length : ℝ≥0∞) * nInv := by
  rw [εq, nInv]
  by_cases h : inDom s x
  · rw [ite_eq_left h, ite_eq_left (show (forwardLookup s.1 x).isSome = true from h)]
  · rw [ite_eq_right h, ite_eq_right (show ¬ (forwardLookup s.1 x).isSome = true from h)]

/-- **An input among `l`**, for a value of mass at most `p` on which the input depends injectively. -/
theorem prEvent_mem_le {γ : Type} (D : ProbComp γ) (F : γ → KeccakState) (p : ℝ≥0∞)
    (hp : ∀ z, Pr{let u ← D}[F u = z] ≤ p) (l : List KeccakState) :
    Pr{let u ← D}[F u ∈ l] ≤ l.length * p := by
  induction l with
  | nil => rw [(prEvent_eq_zero_iff _ _).2 fun _ _ h ↦ List.not_mem_nil h]; exact zero_le
  | cons a l ih =>
    calc Pr{let u ← D}[F u ∈ a :: l] ≤ Pr{let u ← D}[F u = a] + Pr{let u ← D}[F u ∈ l] :=
          (prEvent_mono _ _ (fun u ↦ F u = a ∨ F u ∈ l) fun u hu ↦ List.mem_cons.1 hu).trans
            (prEvent_or_le _ _ _)
      _ ≤ p + l.length * p := add_le_add (hp a) ih
      _ = (a :: l).length * p := by rw [List.length_cons, Nat.cast_succ]; ring

theorem prEvent_inj_le {γ : Type} (D : ProbComp γ) (F : γ → KeccakState) (hF : Function.Injective F) (p : ℝ≥0∞)
    (hD : ∀ u, Pr{let v ← D}[v = u] ≤ p) (z : KeccakState) : Pr{let u ← D}[F u = z] ≤ p := by
  classical
  by_cases h : ∃ u, F u = z
  · obtain ⟨u, rfl⟩ := h
    exact (prEvent_congr_of_support D _ (· = u) fun v _ ↦ hF.eq_iff).le.trans (hD u)
  · push Not at h
    rw [(prEvent_eq_zero_iff _ _).2 fun v _ ↦ h v]
    exact zero_le

end PcsQuotient.EndToEnd
