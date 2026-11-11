-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- `vRows_ofCantor` follows `formal/QuotientSecurity/Concrete.lean`'s `rowsPoly_eq_vRows` (adapted from leanVM,
-- branch PCS-openings-aggregation, commit 651453c6) and `formal/Compose/Compose/Reduce.lean`'s `matches_params`.
import PcsBridge.Kc3Accepts
import Bridge.Claims.Constants
import Bridge.Claims.Tau

/-!
# The Cantor instance matches the statement's constants

For F1's instance `Kc3.Params.ofCantor B hm σ pins random` on a Cantor basis of `E` whose first `24` vectors are
`beta()`'s words (`hβ`), at `2^22` rows:

* `vCells_ofCantor`: the cells' vanishing polynomial is `w_24` (`digitPoly 24`: monic of degree `2^24`, zero on
  the cells);
* `vRows_ofCantor`: the rows' is the statement's `rows` (a sum of digits with `row_vanishing`'s coefficients,
  zero on the rows' basis vectors: `RowVanishing`);
* `sigmaPoly_eq`: `σ`'s polynomial is the wiring table's when the table carries `σ` on the cells;
* **`matches_ofCantor`**: `Matches`, given the pins' points and the wiring table carrying `σ`.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace PcsBridge.Kc3

open LeanVM.Parameters PcsQuotient PcsQuotient.Domain QuotientSecurity
open _root_.Kc3 (pinCount)

variable {N : ℕ} (B : CantorBasis E N) (hm : 22 + 2 ≤ N) (σ : Equiv.Perm (cantorT B 22 × Fin 4))
  (pins : Fin pinCount ↪ cantorT B 22) (random : Finset (cantorT B 22))

theorem pt_ofCantor (i : cantorT B 22 × Fin 4) :
    (_root_.Kc3.Params.ofCantor B hm σ pins random).pt i = B.point ((cantorCells B hm).symm i) := by
  have h := cantorCells_point B hm ((cantorCells B hm).symm i)
  rw [Equiv.apply_symm_apply] at h
  exact h

/-- `S^k` vanishes on the span of the first `k` vectors of a Cantor basis. -/
theorem sq_iterate_point {m : ℕ} (hm' : m ≤ N) (x : Fin m → Bool) : sq^[m] (B.point x) = 0 := by
  unfold CantorBasis.point
  rw [sq_iterate_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs
  · rw [B.iterate _ _ (by omega), if_neg (by omega)]
  · exact sq_iterate_zero _

/-- **The cells' vanishing polynomial is `w_24`.** -/
theorem vCells_ofCantor (t : E) : (_root_.Kc3.Params.ofCantor B hm σ pins random).vCells.eval t = sq^[24] t := by
  obtain ⟨hmon, hdeg⟩ := digitPoly_monic_natDegree (F := E) 24
  have e := eq_prod_of_monic_of_roots hmon
    (hdeg.trans (_root_.Kc3.ofCantor_nCells B hm σ pins random).symm) (_root_.Kc3.Params.ofCantor B hm σ pins random).pt_injective
    fun i => by
      rw [digitPoly_eval, pt_ofCantor B hm σ pins random i]
      exact sq_iterate_point B hm _
  unfold _root_.Kc3.Params.vCells
  rw [← e, digitPoly_eval]

/-! ## The wiring -/

section Generic0

variable {F : Type*} [Field F] [CharP F 2] [DecidableEq F] {N n : ℕ} (B : CantorBasis F N) (hm : n + 2 ≤ N)
  (σ : Equiv.Perm (cantorT B n × Fin 4)) (pins : Fin pinCount ↪ cantorT B n) (random : Finset (cantorT B n))

theorem ofCantor_sigmaPoly : (_root_.Kc3.Params.ofCantor B hm σ pins random).sigmaPoly =
    Lagrange.interpolate univ (_root_.Kc3.Params.ofCantor B hm σ pins random).pt
      (fun i => (_root_.Kc3.Params.ofCantor B hm σ pins random).pt (σ i)) := rfl

/-- **`σ`'s polynomial is any polynomial of degree below `n` carrying `σ` on the cells.** -/
theorem ofCantor_sigmaPoly_eq (f : F[X]) (hf : f.natDegree < 2 ^ (n + 2))
    (hcar : ∀ i, f.eval ((_root_.Kc3.Params.ofCantor B hm σ pins random).pt i) =
      (_root_.Kc3.Params.ofCantor B hm σ pins random).pt (σ i)) :
    (_root_.Kc3.Params.ofCantor B hm σ pins random).sigmaPoly = f := by
  rw [ofCantor_sigmaPoly]
  refine (Lagrange.eq_interpolate_of_eval_eq _
    (_root_.Kc3.Params.ofCantor B hm σ pins random).pt_injective.injOn ?_ fun i _ => hcar i).symm
  have hlt : f.degree < ((2 ^ (n + 2) : ℕ) : WithBot ℕ) := by
    by_cases h0 : f = 0
    · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
    · rw [degree_eq_natDegree h0]
      exact_mod_cast hf
  convert hlt using 2
  rw [Finset.card_univ]
  exact _root_.Kc3.ofCantor_nCells B hm σ pins random

end Generic0

section Generic

variable {F : Type*} [Field F] [CharP F 2] [DecidableEq F] {N : ℕ} (B : CantorBasis F N) (hm : 22 + 2 ≤ N)
  (σ : Equiv.Perm (cantorT B 22 × Fin 4)) (pins : Fin pinCount ↪ cantorT B 22) (random : Finset (cantorT B 22))

/-- **`σ`'s polynomial is a table's** when the table's polynomial carries `σ` on the cells. -/
theorem sigmaPoly_eq (s₀ : (Fin 24 → Bool) → F)
    (hcar : ∀ i, (tablePoly s₀).eval ((_root_.Kc3.Params.ofCantor B hm σ pins random).pt i) =
      (_root_.Kc3.Params.ofCantor B hm σ pins random).pt (σ i)) :
    (_root_.Kc3.Params.ofCantor B hm σ pins random).sigmaPoly = tablePoly s₀ :=
  ofCantor_sigmaPoly_eq B hm σ pins random _ (natDegree_tablePoly_lt s₀) hcar

end Generic

/-! ## The rows -/

/-- `row_vanishing(24)`'s coefficients in `E`. -/
noncomputable def tauE (k : Fin (22 + 1)) : E := ofK ((rowVanishing 24).getD k 0)

theorem rowsAt_eq (t : E) : rowsAt t = (rowsPoly tauE).eval t := by
  rw [rowsPoly_eval, rowsAt, ← Fin.sum_univ_eq_sum_range
    (fun k => ofK ((rowVanishing 24).getD k 0) * sq^[k] t) 23]
  rfl

theorem tauE_last : tauE (Fin.last 22) = 1 := by
  unfold tauE
  rw [Bridge.Claims.rowVanishing_24_unfold, Fin.val_last,
    List.getD_append_right _ _ _ _ (by simp)]
  simp [Compose.Reduce.ofK_one]

/-- `row_vanishing(24)`'s words. -/
def tauWordsL : List UInt64 :=
  [5246327309480240592, 462416703093199623, 5836061695391999385, 17933131952861334950,
    18372946041939442404, 12828942987611060278, 13588355210333287157, 1205146552516504875,
    981042065287506825, 5923339044450209179, 951408172292342183, 12676167449202766892,
    13719231351162120800, 12661900118541078806, 12449589984762772511, 11682037014426230835,
    1012368888076811759, 18272804218237563919, 5328687504910262779, 18383142605220007825,
    802269026382174146, 1506959928840120550, 1]

/-- `row_vanishing(24)`'s system, in `K`, by kernel evaluation (a copy of `E2ECompleteness.Pcs.tau_system`). -/
theorem tau_systemL : ∀ j < 22 + 2, 2 ≤ j →
    ((List.range (22 + 1)).map fun k ↦
      (if k ≤ j then betaF64 (j - k) else 0) * K.ofLane (tauWordsL.getD k 0)).sum = 0 := by
  decide +kernel

theorem sum_range_eq_listK (f : ℕ → K) :
    ∀ n, ∑ k ∈ Finset.range n, f k = ((List.range n).map f).sum
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_range_eq_listK f n, List.range_succ, List.map_append,
      List.sum_append]
    simp

variable (hβ : ∀ k < 22 + 2, B.β k = ofK (betaAt k))
include hβ hm

/-- The rows' polynomial vanishes on the rows' basis vectors. -/
theorem rowsPoly_tauE_basis (j : Fin (22 + 2)) (hj : 2 ≤ (j : ℕ)) : (rowsPoly tauE).eval (B.β j) = 0 := by
  rw [rowsPoly_eval]
  have e : ∀ k : Fin (22 + 1), tauE k * sq^[(k : ℕ)] (B.β j) =
      ofK ((if (k : ℕ) ≤ j then betaF64 (j - k) else 0) * K.ofLane (tauWordsL.getD k 0)) := by
    intro k
    rw [B.iterate _ _ (by omega), Compose.Reduce.ofK_mul, mul_comm, tauE,
      Bridge.getD_of_words Bridge.Claims.rowVanishing_24_lanes]
    congr 1
    split_ifs
    · rw [hβ _ (by omega), Bridge.betaAt_eq_deployedBasis _ (by omega)]
      rfl
    · rw [Compose.Reduce.ofK_zero]
  rw [Finset.sum_congr rfl fun k _ => e k, ← Compose.Reduce.ofK_sumFin,
    Fin.sum_univ_eq_sum_range (fun k => (if k ≤ (j : ℕ) then betaF64 (j - k) else 0) *
      K.ofLane (tauWordsL.getD k 0)) (22 + 1), sum_range_eq_listK, tau_systemL j j.2 hj,
    Compose.Reduce.ofK_zero]

/-- **The rows' vanishing polynomial is the statement's rows' polynomial.** -/
theorem vRows_ofCantor (t : E) : (_root_.Kc3.Params.ofCantor B hm σ pins random).vRows.eval t = rowsAt t := by
  obtain ⟨hmon, hdeg⟩ := rowsPoly_monic tauE tauE_last
  have e : rowsPoly tauE = (_root_.Kc3.Params.ofCantor B hm σ pins random).vRows := by
    refine eq_prod_of_monic_of_roots hmon (hdeg.trans ((_root_.Kc3.card_cantorT B hm).symm.trans (Fintype.card_coe _).symm))
      Subtype.val_injective fun x => ?_
    obtain ⟨y, -, hy⟩ := Finset.mem_image.mp x.2
    rw [← hy, rowsPoly_eval]
    have hadd : ∀ z : Fin (22 + 2) → Bool, (∀ j : Fin (22 + 2), (j : ℕ) < 2 → z j = false) →
        ∑ k, tauE k * sq^[(k : ℕ)] (B.point z) = 0 := by
      intro z hz
      unfold CantorBasis.point
      simp only [sq_iterate_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : z j = true
      · have h2 : 2 ≤ (j : ℕ) := by
          by_contra h
          rw [hz j (by omega)] at hj
          exact Bool.false_ne_true hj
        simp only [hj, ite_true]
        rw [← rowsPoly_eval]
        exact rowsPoly_tauE_basis B hm hβ j h2
      · simp [hj, sq_iterate_zero]
    refine hadd _ fun j hj => ?_
    obtain ⟨j, hjlt⟩ := j
    interval_cases j <;> rfl
  rw [← e, rowsAt_eq]

/-! ## The match -/

/-- **The Cantor instance matches the statement's constants**, given the pins' points and the wiring table
carrying `σ`. -/
theorem matches_ofCantor (s₀ : (Fin 24 → Bool) → E)
    (hpins : ∀ k : Fin 11, (_root_.Kc3.Params.ofCantor B hm σ pins random).pinPt k = pinE k)
    (hcar : ∀ i, (tablePoly s₀).eval ((_root_.Kc3.Params.ofCantor B hm σ pins random).pt i) =
      (_root_.Kc3.Params.ofCantor B hm σ pins random).pt (σ i)) :
    Matches (_root_.Kc3.Params.ofCantor B hm σ pins random) s₀ where
  theta := hβ 1 (by norm_num)
  card := _root_.Kc3.card_cantorT B hm
  vCells := vCells_ofCantor B hm σ pins random
  vRows := vRows_ofCantor B hm σ pins random hβ
  pins := hpins
  sigma t := by rw [sigmaPoly_eq B hm σ pins random s₀ hcar]

end PcsBridge.Kc3

/-- info: 'PcsBridge.Kc3.vCells_ofCantor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsBridge.Kc3.vCells_ofCantor

/-- info: 'PcsBridge.Kc3.vRows_ofCantor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsBridge.Kc3.vRows_ofCantor

/-- info: 'PcsBridge.Kc3.matches_ofCantor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsBridge.Kc3.matches_ofCantor
