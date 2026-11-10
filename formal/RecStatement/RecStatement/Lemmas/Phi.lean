-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `Φ`'s basis is `crates/leanvm/rec/src/pi2/verifier.rs`'s
-- (`Spec::phi`, its test `the_ports_lagrange_basis`).
import RecStatement.Lemmas.Push

/-!
# The ports' `Φ` by rows

`PI2.md` §1: on a Cantor basis, `w_r(ω_i) = ω_{i >> r}` and `w_m = w_{m−r} ∘ w_r`, and `w_{m−r}' = 1` (its linear
coefficient), so `L_y(z) = w_{m−r}(z)/(z + ω_y)` is `V_{m−r}`'s Lagrange basis at `ω_y` (`lag_eval_omega`), and
`L_y(w_r(X))` (`lagRow`, degree `N − 2^r`) is one on row `y` of `V_m` and zero on the other rows
(`lagRow_eval_omega`), `w_m(t)/(w_r(t) + ω_y)` at `t ∉ V_m` (`lagRow_eval`). The ports' polynomial

`Φ_k = Σ_{ports j of role k} F_j L_{y_j}(w_r)`, `y_j` the row of port `j`'s hole (`phiPoly`),

has degree below `N` (`natDegree_phiPoly_lt`) and takes port `j`'s public fingerprint at its hole
(`phiPoly_eval_port`: no two ports of one role share a row); at `t ∉ V_m` it is the verifier's `Φ_k(t)`, the fraction
of the terms of nonzero value (**`phiAt_eq`**: the ports in no term have zero fingerprints).
-/

set_option linter.unusedSectionVars false

namespace RecStatement

open Finset RecPiop Polynomial QuotientSecurity

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F]

section Lagrange

variable {n : ℕ} (B : CantorBasis F n)

/-- `w_k` vanishes on `V_k`: `s^k(ω_y) = 0` for `y < 2^k ≤ 2^n`. -/
theorem sq_iterate_omega_lt {k y : ℕ} (hk : k ≤ n) (hy : y < 2 ^ k) : sq^[k] (Heap.omega B y) = 0 := by
  rw [Heap.sq_iterate_omega B k (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) hk)),
    Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hy, Heap.omega_zero]

/-- `V_k`'s Lagrange basis at `ω_y`: `w_k/(X − ω_y)`. -/
noncomputable def lagBasis (k y : ℕ) : F[X] := (digitPoly k : F[X]) /ₘ (X - C (Heap.omega B y))

theorem lagBasis_mul {k y : ℕ} (hk : k ≤ n) (hy : y < 2 ^ k) :
    (X - C (Heap.omega B y)) * lagBasis B k y = digitPoly k :=
  (mul_divByMonic_eq_iff_isRoot).mpr (by
    rw [IsRoot.def, digitPoly_eval, sq_iterate_omega_lt B hk hy])

/-- **`V_k`'s Lagrange basis**: one at `ω_y`, zero at the other points of `V_k`. -/
theorem lag_eval_omega {k y y' : ℕ} (hk : k ≤ n) (hy : y < 2 ^ k) (hy' : y' < 2 ^ k) :
    (lagBasis B k y).eval (Heap.omega B y') = if y' = y then 1 else 0 := by
  have hm := lagBasis_mul B hk hy
  split_ifs with h
  · subst h
    have hd := congrArg derivative hm
    rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
      derivative_digitPoly] at hd
    have := congrArg (eval (Heap.omega B y')) hd
    rw [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, eval_one] at this
    exact this
  · have := congrArg (eval (Heap.omega B y')) hm
    rw [eval_mul, eval_sub, eval_X, eval_C, digitPoly_eval, sq_iterate_omega_lt B hk hy'] at this
    have hne : Heap.omega B y' - Heap.omega B y ≠ 0 := fun h0 => h (Heap.omega_injOn B
      (lt_of_lt_of_le hy' (Nat.pow_le_pow_right (by norm_num) hk))
      (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) hk)) (sub_eq_zero.mp h0))
    exact (mul_eq_zero.mp this).resolve_left hne

theorem natDegree_lagBasis {k : ℕ} (y : ℕ) : (lagBasis B k y).natDegree = 2 ^ k - 1 := by
  unfold lagBasis
  rw [natDegree_divByMonic _ (monic_X_sub_C _), (RecPiop.digitPoly_monic k).2, natDegree_X_sub_C]

/-- Off `ω_y`, the basis is `w_k(z)/(z − ω_y)`. -/
theorem lag_eval {k y : ℕ} (hk : k ≤ n) (hy : y < 2 ^ k) {z : F} (hz : z - Heap.omega B y ≠ 0) :
    (lagBasis B k y).eval z = sq^[k] z / (z - Heap.omega B y) := by
  have := congrArg (eval z) (lagBasis_mul B hk hy)
  rw [eval_mul, eval_sub, eval_X, eval_C, digitPoly_eval] at this
  rw [← this]
  field_simp

end Lagrange

section Phi

variable {n : ℕ} (G : RecPiop.Circuit F) (B : CantorBasis F n)

/-- **Row `y`'s basis on `V_m`**: `L_y(w_r(X))`, `L_y` `V_{m−r}`'s Lagrange basis at `ω_y`. -/
noncomputable def lagRow (y : ℕ) : F[X] := (lagBasis B (G.logN - G.logW) y).comp (digitPoly G.logW)

/-- **The ports' `Φ_k`**: `Σ_{ports j of role k} F_j L_{y_j}(w_r)`. -/
noncomputable def phiPoly (pub : ℕ → List F) (γ : F) (k : ℕ) : F[X] :=
  ∑ j ∈ (range G.nP).filter (fun j => G.port j % G.W = k), C (G.pubFp γ pub j) * lagRow G B (G.port j / G.W)

variable {G B}

theorem N_eq_rows (hV : G.Valid) : G.N = 2 ^ (G.logN - G.logW) * G.W := by
  unfold Circuit.N Circuit.W
  rw [← pow_add, Nat.sub_add_cancel hV.logW_lt.le]

theorem row_lt (hV : G.Valid) {i : ℕ} (hi : i < G.N) : i / G.W < 2 ^ (G.logN - G.logW) := by
  rw [Nat.div_lt_iff_lt_mul (show 0 < G.W from Nat.two_pow_pos _), ← N_eq_rows hV]
  exact hi

theorem natDegree_lagRow_lt (hV : G.Valid) (y : ℕ) : (lagRow G B y).natDegree < G.N := by
  unfold lagRow
  refine (natDegree_comp_le).trans_lt ?_
  rw [natDegree_lagBasis, (RecPiop.digitPoly_monic _).2, N_eq_rows hV]
  have h1 := Nat.two_pow_pos (G.logN - G.logW)
  have h2 : 0 < G.W := Nat.two_pow_pos _
  unfold Circuit.W at h2 ⊢
  rw [Nat.sub_mul, one_mul]
  exact Nat.sub_lt (Nat.mul_pos h1 h2) h2

/-- **Row `y`'s basis on `V_m`**: one on row `y`, zero on the other rows. -/
theorem lagRow_eval_omega (hV : G.Valid) (hn : G.logN ≤ n) {y i : ℕ} (hy : y < 2 ^ (G.logN - G.logW))
    (hi : i < G.N) : (lagRow G B y).eval (Heap.omega B i) = if i / G.W = y then 1 else 0 := by
  unfold lagRow
  have hi' : i < 2 ^ n := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hn)
  rw [eval_comp, digitPoly_eval, Heap.sq_iterate_omega B _ hi', Nat.shiftRight_eq_div_pow]
  exact lag_eval_omega B (by omega) hy (row_lt hV hi)

/-- **Row `y`'s basis at `t ∉ V_m`**: `w_m(t)/(w_r(t) + ω_y)`. -/
theorem lagRow_eval (hV : G.Valid) (hn : G.logN ≤ n) {y : ℕ} (hy : y < 2 ^ (G.logN - G.logW)) {t : F}
    (hz : sq^[G.logW] t + Heap.omega B y ≠ 0) :
    (lagRow G B y).eval t = sq^[G.logN] t / (sq^[G.logW] t + Heap.omega B y) := by
  unfold lagRow
  have hz' : sq^[G.logW] t - Heap.omega B y ≠ 0 := by rwa [sub_eq_add_neg, CharTwo.neg_eq]
  rw [eval_comp, digitPoly_eval, lag_eval B (by omega) hy hz', ← Function.iterate_add_apply,
    Nat.sub_add_cancel hV.logW_lt.le, sub_eq_add_neg, CharTwo.neg_eq]

theorem natDegree_phiPoly_lt (hV : G.Valid) (pub : ℕ → List F) (γ : F) (k : ℕ) :
    (phiPoly G B pub γ k).natDegree < G.N := by
  unfold phiPoly
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ fun j _ =>
    (natDegree_C_mul_le _ _).trans (Nat.le_sub_one_of_lt (natDegree_lagRow_lt hV _))) ?_
  have := Circuit.N_pos (G := G)
  omega

/-- **`Φ` at a hole is its port's public fingerprint.** -/
theorem phiPoly_eval_port (hV : G.Valid) (hn : G.logN ≤ n) (pub : ℕ → List F) (γ : F) {j : ℕ}
    (hj : j < G.nP) :
    (phiPoly G B pub γ (G.port j % G.W)).eval (Heap.omega B (G.port j)) = G.pubFp γ pub j := by
  unfold phiPoly
  have hpj := (G.port_lt hV hj).1
  rw [eval_finsetSum, Finset.sum_eq_single j]
  · rw [eval_mul, eval_C, lagRow_eval_omega hV hn (row_lt hV hpj) hpj, ite_eq_left rfl, mul_one]
  · intro j' hj' hne
    obtain ⟨hj'n, hrole⟩ := Finset.mem_filter.mp hj'
    have hpj' := (G.port_lt hV (Finset.mem_range.mp hj'n)).1
    have hrow : ¬ G.port j / G.W = G.port j' / G.W := by
      intro hrow
      apply hne
      refine G.port_inj hV (Finset.mem_range.mp hj'n) hj ?_
      rw [← Nat.div_add_mod (G.port j') G.W, ← Nat.div_add_mod (G.port j) G.W, hrow, hrole]
    rw [eval_mul, eval_C, lagRow_eval_omega hV hn (row_lt hV hpj') hpj, ite_eq_right hrow, mul_zero]
  · intro h
    exact (h (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, rfl⟩)).elim

/-- **`Φ` at `t ∉ V_m`**: `Σ_{ports j of role k} F_j w_m(t)/(w_r(t) + ω_{y_j})`. -/
theorem phiPoly_eval (hV : G.Valid) (hn : G.logN ≤ n) (pub : ℕ → List F) (γ : F) (k : ℕ) {t : F}
    (ht : sq^[G.logN] t ≠ 0) :
    (phiPoly G B pub γ k).eval t = ∑ j ∈ (range G.nP).filter (fun j => G.port j % G.W = k),
      G.pubFp γ pub j * (sq^[G.logN] t / (sq^[G.logW] t + Heap.omega B (G.port j / G.W))) := by
  unfold phiPoly
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hpj := (G.port_lt hV (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)).1
  have hrow := row_lt hV hpj
  rw [eval_mul, eval_C, lagRow_eval hV hn hrow]
  intro h0
  have he : sq^[G.logW] t = Heap.omega B (G.port j / G.W) := CharTwo.add_eq_zero.mp h0
  apply ht
  rw [show G.logN = (G.logN - G.logW) + G.logW by have := hV.logW_lt; omega, Function.iterate_add_apply, he,
    sq_iterate_omega_lt B (by omega) hrow]

end Phi

/-! ## The verifier's `Φ` is `phiPoly`'s -/

section Link

/-- A list's sum by its indices. -/
theorem list_sum_eq_range {α : Type} (f : α → F) (d : α) :
    ∀ L : List α, (L.map f).sum = ∑ J ∈ range L.length, f (L.getD J d)
  | [] => by simp
  | a :: L => by
    rw [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ', list_sum_eq_range f d L]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- The `Φ` terms of a role of the list are its entry's, when the roles are distinct. -/
theorem filter_phiTerms {α : Type} : ∀ (L : List (ℕ × List α)), (L.map (·.1)).Nodup →
    ∀ kt ∈ L, (L.flatMap fun kt ↦ kt.2.map fun yl ↦ (kt.1, yl)).filter (fun x ↦ decide (x.1 = kt.1)) =
      kt.2.map fun yl ↦ (kt.1, yl)
  | [], _, _, h => absurd h List.not_mem_nil
  | kt' :: L, hnd, kt, hkt => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.flatMap_cons, List.filter_append]
    rcases List.mem_cons.mp hkt with rfl | hkt'
    · have h1 : (kt.2.map fun yl ↦ (kt.1, yl)).filter (fun x ↦ decide (x.1 = kt.1)) =
          kt.2.map fun yl ↦ (kt.1, yl) := List.filter_eq_self.mpr fun x hx => by
        obtain ⟨yl, -, rfl⟩ := List.mem_map.mp hx
        simp
      have h2 : (L.flatMap fun kt ↦ kt.2.map fun yl ↦ (kt.1, yl)).filter (fun x ↦ decide (x.1 = kt.1)) = [] :=
        List.filter_eq_nil_iff.mpr fun x hx => by
          obtain ⟨kt'', hkt'', hx'⟩ := List.mem_flatMap.mp hx
          obtain ⟨yl, -, rfl⟩ := List.mem_map.mp hx'
          simp only [decide_eq_true_eq]
          intro he
          exact hnd.1 (he ▸ List.mem_map_of_mem hkt'')
      rw [h1, h2, List.append_nil]
    · have hne : kt'.1 ≠ kt.1 := fun he => hnd.1 (he ▸ List.mem_map_of_mem hkt')
      have h1 : (kt'.2.map fun yl ↦ (kt'.1, yl)).filter (fun x ↦ decide (x.1 = kt.1)) = [] :=
        List.filter_eq_nil_iff.mpr fun x hx => by
          obtain ⟨yl, -, rfl⟩ := List.mem_map.mp hx
          simpa using hne
      rw [h1, List.nil_append, filter_phiTerms L hnd.2 kt hkt']

variable {n : ℕ} {S : CoreSpec F} {G : RecPiop.Circuit F} {B : CantorBasis F n}
  {pairOf : ℕ → Block × ℕ} {portOf : ℕ → ℕ} {pubOf : List F → ℕ → List F}

/-- **The verifier's `Φ_k(t)` is `phiPoly`'s value**, at `t ∉ V_m`. -/
theorem phiAt_eq (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid) (pubs : List F) (γ : F) {t : F}
    (ht : sq^[G.logN] t ≠ 0) (k : ℕ) :
    phiAt S (powersList γ (S.maxGamma + 1)) pubs t k = (phiPoly G B (pubOf pubs) γ k).eval t := by
  set gs := powersList γ (S.maxGamma + 1)
  set len := (phiTerms S).length
  -- the summand over ports
  set f : ℕ → F := fun j ↦ G.pubFp γ (pubOf pubs) j *
    (sq^[G.logN] t / (sq^[G.logW] t + Heap.omega B (G.port j / G.W))) with hf
  have hpoly : (phiPoly G B (pubOf pubs) γ k).eval t =
      ∑ j ∈ (range G.nP).filter (fun j => G.port j % G.W = k), f j := phiPoly_eval hV hS.hn _ γ k ht
  -- the ports of the terms
  have himg : ∀ j ∈ (range G.nP).filter (fun j => G.port j % G.W = k),
      j ∉ ((range len).filter fun J ↦ ((phiTerms S).getD J noPhi).1 = k).image portOf → f j = 0 := by
    intro j hj hnot
    obtain ⟨hjn, hjk⟩ := Finset.mem_filter.mp hj
    have hz : G.pubFp γ (pubOf pubs) j = 0 := hS.zero_ports j (Finset.mem_range.mp hjn) (fun J hJ he => hnot
      (Finset.mem_image.mpr ⟨J, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hJ, by
        rw [hS.phi_role J hJ, he, hjk]⟩, he⟩)) pubs γ
    rw [hf]
    simp only [hz, zero_mul]
  have hsub : ((range len).filter fun J ↦ ((phiTerms S).getD J noPhi).1 = k).image portOf ⊆
      (range G.nP).filter (fun j => G.port j % G.W = k) := by
    intro j hj
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hJl, hJk⟩ := Finset.mem_filter.mp hJ
    have hJl' := Finset.mem_range.mp hJl
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hS.phi_port_lt J hJl'), by rw [← hS.phi_role J hJl', hJk]⟩
  have hreindex : ∑ j ∈ (range G.nP).filter (fun j => G.port j % G.W = k), f j =
      ∑ J ∈ (range len).filter (fun J ↦ ((phiTerms S).getD J noPhi).1 = k), f (portOf J) := by
    rw [← Finset.sum_subset hsub himg, Finset.sum_image fun J hJ J' hJ' he => hS.phi_port_inj J
      (Finset.mem_range.mp (Finset.mem_filter.mp hJ).1) J' (Finset.mem_range.mp (Finset.mem_filter.mp hJ').1) he]
  rw [hpoly, hreindex]
  -- the verifier's side, over the terms
  have hden : ∀ x ∈ phiTerms S, sq^[G.logW] t + Heap.omega B x.2.1 ≠ 0 := fun x hx =>
    phiDen_ne_zero hS hV ht (phiTerm_row_lt hS hV hx)
  have hterm : ∀ J ∈ (range len).filter (fun J ↦ ((phiTerms S).getD J noPhi).1 = k), f (portOf J) =
      sq^[G.logN] t * (((phiTerms S).getD J noPhi).2.2.eval gs (fun c ↦ pubs.getD c 0) /
        (sq^[G.logW] t + Heap.omega B ((phiTerms S).getD J noPhi).2.1)) := by
    intro J hJ
    have hJl := Finset.mem_range.mp (Finset.mem_filter.mp hJ).1
    rw [hf]
    simp only
    rw [hS.phi_value J hJl, hS.phi_row J hJl]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  unfold phiAt
  rw [hS.logN, hS.logRow, hS.omega]
  cases hfind : S.phi.find? (·.1 = k) with
  | none =>
    have hno : (range len).filter (fun J ↦ ((phiTerms S).getD J noPhi).1 = k) = ∅ := by
      refine Finset.filter_false_of_mem fun J hJ he => ?_
      have hmem : (phiTerms S).getD J noPhi ∈ phiTerms S := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Finset.mem_range.mp hJ), Option.getD_some]
        exact List.getElem_mem _
      obtain ⟨kt, hkt, hx⟩ := List.mem_flatMap.mp hmem
      obtain ⟨yl, -, hyl⟩ := List.mem_map.mp hx
      have := List.find?_eq_none.mp hfind kt hkt
      simp only [decide_eq_true_eq] at this
      apply this
      rw [← he, ← hyl]
    rw [hno, Finset.sum_empty, mul_zero]
  | some kt =>
    have hkt := List.mem_of_find?_eq_some hfind
    have hk : kt.1 = k := by simpa using List.find?_some hfind
    have hden' : ∀ yl ∈ kt.2, sq^[G.logW] t + Heap.omega B yl.1 ≠ 0 := fun yl hyl =>
      hden (kt.1, yl) (mem_phiTerms hkt hyl)
    obtain ⟨h2, h1⟩ := phiFrac_spec (Heap.omega B) gs pubs (sq^[G.logW] t) kt.2 hden'
    have hd0 : (phiFrac (Heap.omega B) gs pubs (sq^[G.logW] t) kt.2).2 ≠ 0 := by
      rw [h2]
      exact List.prod_ne_zero fun h0 ↦ by
        obtain ⟨yl, hyl, he⟩ := List.mem_map.mp h0
        exact hden' yl hyl he
    show sq^[G.logN] t * (phiFrac (Heap.omega B) gs pubs (sq^[G.logW] t) kt.2).1 /
      (phiFrac (Heap.omega B) gs pubs (sq^[G.logW] t) kt.2).2 = _
    rw [h1, mul_div_assoc, mul_div_cancel_left₀ _ hd0]
    congr 1
    -- the term list of role `k` is `kt.2`
    have hfl := filter_phiTerms S.phi hS.phi_nodup kt hkt
    have e1 : ((kt.2.map fun yl ↦ (kt.1, yl)).map fun x ↦ x.2.2.eval gs (fun c ↦ pubs.getD c 0) /
        (sq^[G.logW] t + Heap.omega B x.2.1)).sum =
        (kt.2.map fun yl ↦ yl.2.eval gs (fun c ↦ pubs.getD c 0) / (sq^[G.logW] t + Heap.omega B yl.1)).sum := by
      rw [List.map_map]
      rfl
    rw [← e1, ← hfl, sum_filter_map, list_sum_eq_range _ noPhi, Finset.sum_filter]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [hk]
    simp only [phiTerms, decide_eq_true_eq]
    exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

end Link

end RecStatement
