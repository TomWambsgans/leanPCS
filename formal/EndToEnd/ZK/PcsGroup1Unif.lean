-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here.
import ZK.PcsGroup1Map

/-!
# Group 1 is uniform where its random-rows map is onto

The random rows' words are uniform (`prEvent_rowsDist`), and group 1 is a constant plus their image under the
additive map `Lmap` (`group1_eq`). Where `Lmap` is onto `E⁴`, every fiber has the kernel's size, so group 1 is uniform:
**`group1At_of_surj`**.
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open Finset
open scoped ENNReal

namespace PcsQuotient.EndToEnd.Group1

theorem wd_add (r1 r2 : Fin randomWords → K) (i : ℕ) : wd (r1 + r2) i = wd r1 i + wd r2 i := by
  unfold wd; split_ifs <;> simp

theorem wd_smul (a : K) (r : Fin randomWords → K) (i : ℕ) : wd (a • r) i = a * wd r i := by
  unfold wd; split_ifs <;> simp

/-- **`Lsum` as a `K`-linear map of the rows.** -/
noncomputable def LsumL (wt : ℕ → E) : (Fin randomWords → K) →ₗ[K] E where
  toFun := Lsum wt
  map_add' r1 r2 := by
    simp only [Lsum, ← sum_add_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [wd_add, ofK_add]; ring
  map_smul' a r := by
    simp only [Lsum, RingHom.id_apply, wd_smul, ofK_mul]
    rw [Algebra.smul_def, mul_sum, ← ofK_eq]
    refine sum_congr rfl fun k _ ↦ ?_
    ring

theorem LsumL_apply (wt : ℕ → E) (rows : Fin randomWords → K) : LsumL wt rows = Lsum wt rows := rfl

/-- **The four scalars' random part**, as one additive map. -/
noncomputable def Lmap (a b c d : ℕ → E) : (Fin randomWords → K) →+ E × E × E × E :=
  (LsumL a).toAddMonoidHom.prod ((LsumL b).toAddMonoidHom.prod ((LsumL c).toAddMonoidHom.prod
    (LsumL d).toAddMonoidHom))

theorem Lmap_apply (a b c d : ℕ → E) (rows : Fin randomWords → K) :
    Lmap a b c d rows = (Lsum a rows, Lsum b rows, Lsum c rows, Lsum d rows) := rfl

/-! ### The random rows' law -/

/-- The random rows as the coins draw them: `32` uniform words. -/
noncomputable def rowsDist : ProbComp (Fin randomWords → K) :=
  (fun w : List UInt64 ↦ fun r : Fin randomWords ↦ K.ofLane (w.getD r.val 0)) <$>
    (List.range randomWords).mapM fun _ ↦ cwDist

/-- **Each rows vector has mass `c64³²`.** -/
theorem prEvent_rowsDist (f : Fin randomWords → K) : Pr{let x ← rowsDist}[x = f] = c64 ^ 32 := by
  classical
  set ws : List UInt64 := (List.range randomWords).map fun k ↦ (wd f k).lane
  have hws : ws.length = randomWords := by simp [ws]
  rw [rowsDist, prEvent_map]
  rw [prEvent_congr_of_support _ _ (· = ws) fun w hw ↦ ?_]
  · rw [prEvent_mapM_const cwDist (List.range randomWords) ws (by simp [hws])]
    simp [ws, prEvent_cwDist, randomWords, randomRows, Function.comp_def, List.map_const']
    ring
  · have hl : w.length = randomWords := by
      simpa using length_of_mem_mapM cwDist (List.range randomWords) w hw
    constructor
    · intro h
      apply List.ext_getElem (by simp [hl, hws])
      intro i h1 h2
      have hi : i < randomWords := by rw [hl] at h1; exact h1
      have := congrFun h ⟨i, hi⟩
      simp only at this
      simp only [ws, List.getElem_map, List.getElem_range, wd, hi, dite_true, ← this]
      simp [List.getD_eq_getElem?_getD, h1]
    · rintro rfl
      funext k
      simp only [ws, wd]
      simp [List.getD_eq_getElem?_getD, k.isLt]

/-- **The coins' random rows are `rowsDist`.** -/
theorem rows_coinsDist : (fun coins : Coins ↦ coins.rows) <$> coinsDist =ᵈ rowsDist := by
  rw [coinsDist_eq]
  simp only [map_bind, map_pure, withSlack]
  rw [show (38 : ℕ) = 32 + 6 from rfl, List.range_add, List.mapM_append, List.mapM_map, bind_assoc]
  simp only [bind_assoc, pure_bind]
  set rowsOf : List UInt64 → Fin randomWords → K := fun w r ↦ K.ofLane (w.getD r.val 0) with hrowsOf
  have h1 : ((List.range 32).mapM fun _ ↦ cwDist) >>= (fun x ↦
      ((List.range 6).mapM ((fun _ ↦ cwDist) ∘ fun x ↦ 32 + x)) >>= fun l ↦ slDist >>= fun _ ↦
        (pure (mkCoins (x ++ l)).rows : ProbComp _)) =
      ((List.range 32).mapM fun _ ↦ cwDist) >>= (fun x ↦
      ((List.range 6).mapM ((fun _ ↦ cwDist) ∘ fun x ↦ 32 + x)) >>= fun l ↦ slDist >>= fun _ ↦
        (pure (rowsOf x) : ProbComp _)) := by
    refine bind_congr_of_forall_mem_support _ fun x hx ↦ ?_
    have hl : x.length = 32 := by simpa using length_of_mem_mapM cwDist (List.range 32) x hx
    have hr : (fun l ↦ slDist >>= fun _ ↦ (pure (mkCoins (x ++ l)).rows : ProbComp _)) =
        fun _ ↦ slDist >>= fun _ ↦ (pure (rowsOf x) : ProbComp _) := by
      funext l
      congr 1
      funext _
      congr 1
      funext r
      have hr' : r.val < x.length := by rw [hl]; exact r.isLt
      simp only [mkCoins, hrowsOf, List.getD_eq_getElem?_getD, List.getElem?_append_left hr']
    rw [hr]
  rw [h1]
  refine (EvalDistEq.bind_right _ fun x ↦ (evalDistEq_bind_drop _ _).trans (evalDistEq_bind_drop _ _)).trans ?_
  rw [rowsDist, map_eq_bind_pure_comp]
  rfl

/-! ### Uniformity -/

/-- A law of constant mass on a finite type has mass `1 / |T|`. -/
theorem const_mass {T : Type} [Fintype T] (X : ProbComp T) (k : ℝ≥0∞) (hX : ∀ y, Pr{let x ← X}[x = y] = k) :
    k = (Fintype.card T : ℝ≥0∞)⁻¹ := by
  have h1 : k * (Fintype.card T : ℝ≥0∞) = 1 := by
    rw [mul_comm, ← tsum_prEvent_eq_one X, tsum_fintype, Finset.sum_congr rfl fun y _ ↦ hX y, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  exact ENNReal.eq_inv_of_mul_eq_one_left h1

theorem card_E4 : ((Fintype.card (E × E × E × E) : ℕ) : ℝ≥0∞)⁻¹ = κE ^ 4 := by
  have hk : κE = ((2 : ℝ≥0∞) ^ 192)⁻¹ := pmax_eq
  have hE : Fintype.card E = 2 ^ 192 := by convert card_E
  have hc : ((Fintype.card (E × E × E × E) : ℕ) : ℝ≥0∞) = ((2 : ℝ≥0∞) ^ 192) ^ 4 := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, hE]
    push_cast
    ring
  rw [hc, hk, ENNReal.inv_pow]

/-- **Group 1 is uniform where its random-rows map is onto.** -/
theorem group1At_of_surj (stmt : Statement) (cells₀ : Array K) (hc : cells₀.size = 2 ^ 24) (c : Challenges)
    (hz : c.zW.length = 24) (hs : Function.Surjective (Lmap (wW c.zW) (wC c.t) (wVY c.t) (wX c.t))) :
    Group1At stmt cells₀ c := by
  classical
  have hg : (fun coins ↦ group1 stmt cells₀ coins c) = fun coins ↦
      [G0 cells₀ (wW c.zW) + Lsum (wW c.zW) coins.rows, G0 cells₀ (wC c.t) + Lsum (wC c.t) coins.rows,
        G0 cells₀ (wVY c.t) + Lsum (wVY c.t) coins.rows, G0 cells₀ (wX c.t) + Lsum (wX c.t) coins.rows] :=
    funext fun coins ↦ group1_eq stmt cells₀ hc coins c hz
  -- The random part has constant mass, `1 / |E|⁴`.
  have hfib : ∀ y, Pr{let x ← (Lmap (wW c.zW) (wC c.t) (wVY c.t) (wX c.t)) <$> rowsDist}[x = y] =
      c64 ^ 32 * ((univ.filter fun f ↦ Lmap (wW c.zW) (wC c.t) (wVY c.t) (wX c.t) f = 0).card : ℝ≥0∞) := by
    intro y
    rw [prEvent_map, prEvent_eq_tsum_ite, tsum_fintype]
    simp only [prEvent_rowsDist]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm,
      AddMonoidHom.card_fiber_eq_of_mem_range _ (hs y) (hs 0)]
  have hk := const_mass _ _ hfib
  rw [card_E4] at hk
  have hmass : ∀ y, Pr{let x ← rowsDist}[Lmap (wW c.zW) (wC c.t) (wVY c.t) (wX c.t) x = y] = κE ^ 4 :=
    fun y ↦ by rw [← hk, ← hfib y, prEvent_map]
  intro r
  rw [runWithRandomPermutation_sampleCoins_map, hg, prEvent_coinEs_n, prEvent_map]
  have hP : Pr{let x ← coinsDist}[[G0 cells₀ (wW c.zW) + Lsum (wW c.zW) x.rows,
      G0 cells₀ (wC c.t) + Lsum (wC c.t) x.rows, G0 cells₀ (wVY c.t) + Lsum (wVY c.t) x.rows,
      G0 cells₀ (wX c.t) + Lsum (wX c.t) x.rows] = r] =
      Pr{let x ← rowsDist}[[G0 cells₀ (wW c.zW) + Lsum (wW c.zW) x, G0 cells₀ (wC c.t) + Lsum (wC c.t) x,
        G0 cells₀ (wVY c.t) + Lsum (wVY c.t) x, G0 cells₀ (wX c.t) + Lsum (wX c.t) x] = r] := by
    rw [← rows_coinsDist.prEvent_eq, prEvent_map]
  rw [hP]
  split_ifs with h4
  · obtain ⟨a0, a1, a2, a3, rfl⟩ : ∃ a0 a1 a2 a3 : E, r = [a0, a1, a2, a3] := by
      rcases r with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, r⟩⟩⟩⟩⟩
      · simp at h4
      · simp at h4
      · simp at h4
      · simp at h4
      · exact ⟨a0, a1, a2, a3, rfl⟩
      · simp at h4
    rw [← hmass (a0 - G0 cells₀ (wW c.zW), a1 - G0 cells₀ (wC c.t), a2 - G0 cells₀ (wVY c.t),
      a3 - G0 cells₀ (wX c.t))]
    refine prEvent_congr_of_support _ _ _ fun x _ ↦ ?_
    simp only [Lmap_apply, List.cons.injEq, and_true, Prod.ext_iff]
    constructor
    · rintro ⟨e0, e1, e2, e3⟩
      exact ⟨by rw [← e0]; ring, by rw [← e1]; ring, by rw [← e2]; ring, by rw [← e3]; ring⟩
    · rintro ⟨e0, e1, e2, e3⟩
      exact ⟨by rw [e0]; ring, by rw [e1]; ring, by rw [e2]; ring, by rw [e3]; ring⟩
  · refine (prEvent_eq_zero_iff _ _).2 fun x _ hx ↦ h4 ?_
    rw [← hx]
    rfl

end PcsQuotient.EndToEnd.Group1
