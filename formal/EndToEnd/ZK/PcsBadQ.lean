-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here.
import ZK.PcsInj

/-!
# The cost of a tracked query with a fresh input

Every value the phase's inputs are fresh in has mass at most `pmax = 2^-192` (a uniform element of `E`, a uniform
root, a uniform state, the digest of a uniform state). So a tracked query whose input is injective in a value drawn
just before costs at most `δ L = L pmax + L N⁻¹` among `L` edges (`badB_ent`, `badB_chain`).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open PcsQuotient.Transcript
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open FProg

variable {A α : Type}

/-- The mass of a uniform element of `E`: `2^-192`. -/
noncomputable def pmax : ℝ≥0∞ := c64 * (c64 * c64)

theorem c64_eq : c64 = ((2 : ℝ≥0∞) ^ 64)⁻¹ := by
  rw [c64, ← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel Nat.one_le_two_pow, Nat.cast_pow,
    Nat.cast_ofNat]

theorem pmax_eq : pmax = ((2 : ℝ≥0∞) ^ 192)⁻¹ := by
  rw [pmax, c64_eq, ← ENNReal.mul_inv (by simp) (by simp), ← ENNReal.mul_inv (by simp) (by simp), ← pow_add,
    ← pow_add]

theorem nInv_eq : nInv = ((2 : ℝ≥0∞) ^ 1600)⁻¹ := by
  rw [nInv, card_state, Nat.cast_pow, Nat.cast_ofNat]

theorem nInv_le_pmax : nInv ≤ pmax := by
  rw [nInv_eq, pmax_eq]
  exact ENNReal.inv_le_inv.2 (pow_le_pow_right₀ (by norm_num) (by norm_num))

theorem c64_le_one : c64 ≤ 1 := by
  rw [c64_eq]; exact ENNReal.inv_le_one.2 (one_le_pow₀ (by norm_num))

/-- The per-query bound among `L` edges. -/
noncomputable def δq (L : ℕ) : ℝ≥0∞ := L * pmax + L * nInv

/-! ### Masses -/

theorem prEvent_uState_le (y : KeccakState) : Pr{let z ← uState}[z = y] ≤ nInv := (prEvent_uState y).le

theorem prEvent_uState_inj (G : KeccakState → KeccakState) (hG : Function.Injective G) (z : KeccakState) :
    Pr{let y ← uState}[G y = z] ≤ pmax :=
  (prEvent_inj_le _ G hG _ prEvent_uState_le z).trans nInv_le_pmax

/-- The digest-dependent input of a challenge after a challenge: its value determines the digest. -/
theorem prEvent_uState_digest (H : Digest → KeccakState) (hH : Function.Injective H) (z : KeccakState) :
    Pr{let y ← uState}[H (digestOf y) = z] ≤ pmax := by
  classical
  rw [uState_eq_mkDist _]
  by_cases hz : ∃ y, H (digestOf y) = z
  · obtain ⟨y₀, rfl⟩ := hz
    have key : ∀ y, H (digestOf y) = H (digestOf y₀) → laneE (digestOf y) = laneE (digestOf y₀) :=
      fun y h ↦ by rw [hH h]
    calc Pr{let y ← mkDist}[H (digestOf y) = H (digestOf y₀)]
        ≤ Pr{let y ← mkDist}[laneE (digestOf y) = laneE (digestOf y₀)] := prEvent_mono _ _ _ fun y h ↦ key y h
      _ = Pr{let e ← eDist}[e = laneE (digestOf y₀)] := by
          rw [mkDist, prEvent_bind_eq_tsum, prEvent_eq_tsum_ite eDist]
          refine tsum_congr fun e ↦ ?_
          rw [prEvent_bind_eq_tsum]
          simp only [prEvent_pure, laneE_digestOf_mk]
          split_ifs with h
          · simp only [mul_one]
            rw [tsum_prEvent_eq_one, mul_one]
          · simp
      _ = pmax := by rw [prEvent_eDist]; rfl
  · push Not at hz
    rw [(prEvent_eq_zero_iff _ _).2 fun y _ ↦ hz y]
    exact zero_le

/-! ### Tracked queries with fresh inputs -/

theorem tsum_add_const {γ : Type} (D : ProbComp γ) (f : γ → ℝ≥0∞) (c : ℝ≥0∞) :
    ∑' u, Pr{let y ← D}[y = u] * (f u + c) = ∑' u, Pr{let y ← D}[y = u] * f u + c := by
  rw [tsum_add_le, ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul]

theorem tsum_ind {γ : Type} (D : ProbComp γ) (P : γ → Prop) [DecidablePred P] :
    ∑' u, Pr{let y ← D}[y = u] * (if P u then 1 else 0) = Pr{let u ← D}[P u] := by
  rw [prEvent_eq_tsum_ite]
  exact tsum_congr fun u ↦ by split_ifs <;> simp

theorem prEvent_inDom_le {γ : Type} (D : ProbComp γ) (F : γ → KeccakState) (hF : ∀ z, Pr{let u ← D}[F u = z] ≤ pmax)
    (s : Edges × A) : Pr{let u ← D}[inDom s (F u)] ≤ s.1.length * pmax :=
  (prEvent_mono _ _ _ fun u h ↦ mem_of_inDom h).trans ((prEvent_mem_le D F pmax hF _).trans_eq (by simp))

theorem le_δq {L a : ℕ} (h : a ≤ L) : (a : ℝ≥0∞) * pmax + a * nInv ≤ δq L := by
  unfold δq
  gcongr

/-- **A tracked query whose input is injective in a value drawn just before.** -/
theorem badB_ent {γ : Type} (L : ℕ) (m : StateT (Edges × A) ProbComp γ) (D : ProbComp γ) (hm : StateIndep m D)
    (F : γ → KeccakState) (hF : ∀ z, Pr{let u ← D}[F u = z] ≤ pmax) (k : γ → KeccakState → FProg A α)
    (s : Edges × A) (hs : s.1.length ≤ L) (B : ℝ≥0∞)
    (hk : ∀ u, ∑' y, Pr{let z ← uState}[z = y] * badB (k u y) ((F u, y) :: s.1, s.2) ≤ B) :
    badB (.step m fun u ↦ .q (F u) (k u)) s ≤ δq L + B := by
  classical
  rw [badB_step_indep m D hm]
  calc ∑' u, Pr{let y ← D}[y = u] * badB (.q (F u) (k u)) s
      ≤ ∑' u, Pr{let y ← D}[y = u] * ((if inDom s (F u) then 1 else 0) + ((s.1.length : ℝ≥0∞) * nInv + B)) := by
        refine ENNReal.tsum_le_tsum fun u ↦ ?_
        gcongr
        rw [badB_q, ← add_assoc]
        exact add_le_add (εq_le s (F u)) (hk u)
    _ = Pr{let u ← D}[inDom s (F u)] + ((s.1.length : ℝ≥0∞) * nInv + B) := by rw [tsum_add_const, tsum_ind]
    _ ≤ (s.1.length * pmax + s.1.length * nInv) + B := by
        rw [← add_assoc]; gcongr; exact prEvent_inDom_le D F hF s
    _ ≤ δq L + B := by gcongr; exact le_δq hs

/-- **A tracked query whose input is injective in the previous tracked query's answer.** -/
theorem badB_chain (L : ℕ) (x : KeccakState) (G : KeccakState → KeccakState)
    (hG : ∀ z, Pr{let y ← uState}[G y = z] ≤ pmax) (k : KeccakState → KeccakState → FProg A α) (s : Edges × A)
    (hs : s.1.length + 1 ≤ L) (B : ℝ≥0∞)
    (hk : ∀ y, ∑' y', Pr{let z ← uState}[z = y'] * badB (k y y') ((G y, y') :: (x, y) :: s.1, s.2) ≤ B) :
    ∑' y, Pr{let z ← uState}[z = y] * badB (.q (G y) (k y)) ((x, y) :: s.1, s.2) ≤ δq L + B := by
  classical
  calc ∑' y, Pr{let z ← uState}[z = y] * badB (.q (G y) (k y)) ((x, y) :: s.1, s.2)
      ≤ ∑' y, Pr{let z ← uState}[z = y] *
          ((if inDom ((x, y) :: s.1, s.2) (G y) then 1 else 0) + (((s.1.length + 1 : ℕ) : ℝ≥0∞) * nInv + B)) := by
        refine ENNReal.tsum_le_tsum fun y ↦ ?_
        gcongr
        rw [badB_q, ← add_assoc]
        refine add_le_add ((εq_le _ _).trans ?_) (hk y)
        simp
    _ = Pr{let y ← uState}[inDom ((x, y) :: s.1, s.2) (G y)] + (((s.1.length + 1 : ℕ) : ℝ≥0∞) * nInv + B) := by
        rw [tsum_add_const, tsum_ind]
    _ ≤ ((s.1.length + 1 : ℕ) * pmax + (s.1.length + 1 : ℕ) * nInv) + B := by
        rw [← add_assoc]
        gcongr
        calc Pr{let y ← uState}[inDom ((x, y) :: s.1, s.2) (G y)]
            ≤ Pr{let y ← uState}[G y = x] + Pr{let y ← uState}[inDom s (G y)] :=
              (prEvent_mono _ _ (fun y ↦ G y = x ∨ inDom s (G y)) fun y h ↦ by
                rcases (inDom_cons _ _ _ _ _).1 h with h | h
                · exact Or.inl h.symm
                · exact Or.inr h).trans (prEvent_or_le _ _ _)
          _ ≤ pmax + s.1.length * pmax := add_le_add (hG x) (prEvent_inDom_le _ G hG s)
          _ = ((s.1.length + 1 : ℕ) : ℝ≥0∞) * pmax := by push_cast; ring
    _ ≤ δq L + B := by gcongr; exact le_δq hs

/-- The last tracked query of a chain: its answer's continuation bounded. -/
theorem badB_last (x : KeccakState) (k : KeccakState → FProg A α) (s : Edges × A) (B : ℝ≥0∞)
    (hk : ∀ y, badB (k y) ((x, y) :: s.1, s.2) ≤ B) :
    ∑' y, Pr{let z ← uState}[z = y] * badB (k y) ((x, y) :: s.1, s.2) ≤ B :=
  wavg_le _ _ _ fun y _ ↦ hk y

end PcsQuotient.EndToEnd
