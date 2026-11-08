-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The layouts' limbs and the hazard's argument are
-- `formal/UniSound`'s (`Ids/Eval.lean`: `limbs_new_mem`, `y_self`).
import RecGraph.Sim.TablePart
import RecGraph.Sim.Batch

/-!
# The simulation: the relations' shape, the shared lemmas

The pieces of the tail's conditions that the Keccak VM's (`RecGraphKeccak.Sim.ShapeK`, `shapeSpecK`) uses: a column's
limbs are its entries in the layout's column list (`limbs_new_memC`, `layoutOK_newC`), the leaf quotients' degrees
(`leafDegC`), the points' facts (`PointFact`, `relCommitC`), and the hazard's coordinate (`y0_neGenC`).
-/

set_option linter.dupNamespace false

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement RecGraph.Pi1

/-! ## Layouts -/

/-- **A column's limbs are its entries** in the layout's column list, each limb one of three. -/
theorem limbs_new_memC (cols : List (Column × ℕ × Bool)) (col : Column) (b : ℕ × ℕ × ℕ)
    (hb : b ∈ (StackLayout.new cols).limbs col) : b.1 < 3 ∧ ∃ e, (col, b.2.1, e) ∈ cols := by
  unfold StackLayout.new at hb
  dsimp only at hb
  rw [(UniSound.Ids.foldl_place _ (fun _ _ _ _ ↦ rfl) _ #[] 0).1] at hb
  rw [UniSound.Ids.limbs_eq] at hb
  simp only [List.nil_append] at hb
  have hm := UniSound.Ids.limbs_place col ((cols.flatMap fun x ↦ (List.range (if x.2.2 then 3 else 1)).map fun limb ↦
    (x.1, limb, x.2.1)).mergeSort fun a b ↦ decide (b.2.2 ≤ a.2.2)) 0
  have h1 : (col, b.1, b.2.1) ∈ ((cols.flatMap fun x ↦ (List.range (if x.2.2 then 3 else 1)).map fun limb ↦
      (x.1, limb, x.2.1)).mergeSort fun a b ↦ decide (b.2.2 ≤ a.2.2)).filter (fun x ↦ x.1 == col) := by
    rw [← hm]
    exact List.mem_map.mpr ⟨b, hb, rfl⟩
  obtain ⟨h2, -⟩ := List.mem_filter.mp h1
  rw [List.mem_mergeSort] at h2
  obtain ⟨⟨c', v, e⟩, hc, hx⟩ := List.mem_flatMap.mp h2
  obtain ⟨limb, hl, he⟩ := List.mem_map.mp hx
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  refine ⟨?_, e, hc⟩
  rw [List.mem_range] at hl
  split at hl <;> omega

/-- **A layout of columns each listed at one variable count is `LayoutOK`.** -/
theorem layoutOK_newC {cols : List (Column × ℕ × Bool)} (V : Column → ℕ)
    (hV : ∀ col v e, (col, v, e) ∈ cols → v = V col) : LayoutOK (StackLayout.new cols) := by
  intro col b hb
  obtain ⟨h1, e, he⟩ := limbs_new_memC cols col b hb
  refine ⟨h1, ?_⟩
  unfold headVars
  cases hl : (StackLayout.new cols).limbs col with
  | nil => rw [hl] at hb; simp at hb
  | cons b0 rest =>
    obtain ⟨-, e0, he0⟩ := limbs_new_memC cols col b0 (by rw [hl]; exact List.mem_cons_self ..)
    rw [List.headD_cons, hV _ _ _ he, hV _ _ _ he0]

/-- A heap block's leaf quotient's degree, its table's part's degrees from `parts`. -/
def leafDegC (parts : List TablePart) (block : Block) : ℕ :=
  match block.leaves with
  | .unused => 0
  | .memory => degree (2 * (2 ^ block.r - 1)) (2 ^ block.r)
  | .bytecode => degree (2 * (2 ^ block.r - 1)) (2 ^ block.r)
  | .table t => degree (max (parts.getD t default).pullDegree (parts.getD t default).pushDegree *
      (2 ^ block.r - 1) + (2 ^ block.r - Shape.leastRows block.r)) (2 ^ block.r)

/-! ## The terms' facts -/

/-- **A `C1` term's point**: a prefix of the digits, `y` or Flock's point. -/
def PointFact (wE y fp : List E) (tm : Term) : Prop :=
  tm.column.commitment = .c1 → (∃ k, tm.point = wE.take k) ∨ tm.point = y ∨ tm.point = fp

theorem relCommitC {r : Relation} {c : Commitment} (h : ∀ tm ∈ r.terms, tm.column.commitment = c) {tm : Term}
    (htm : tm ∈ r.terms) : r.commitment = c := by
  unfold Relation.commitment
  cases hr : r.terms with
  | nil => rw [hr] at htm; simp at htm
  | cons t0 _ => exact h t0 (by rw [hr]; exact List.mem_cons_self ..)

/-! ## π1-rec3's numbers -/

/-! ## Columns' variables -/

/-! ## The constraint relation's terms -/

/-! ## The relations' facts -/

theorem forall₂_leftOfC {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ {b : β}, b ∈ m → ∃ a ∈ l, R a b
  | _, _, .nil, _, hb => absurd hb List.not_mem_nil
  | _, _, .cons hr hl, _, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self .., hr⟩
    · obtain ⟨a, ha, h⟩ := forall₂_leftOfC hl hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

/-! ## Off the hazard, no `C1` point extends `y(t)` -/

theorem take_getD0C (l : List E) (m : ℕ) (hm : 0 < m) : (l.take m).getD 0 0 = l.getD 0 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hm)
  cases l <;> rfl

/-- **Off `Z_bad`'s roots, `y(t)`'s first coordinate is neither `t` nor `p_0`** (`UniSound.Ids.Eval.y_self`'s
argument), at any shape (at `reference` the kernel would evaluate the functionals). -/
theorem y0_neGenC (S : UniStatement.Shape) {tE p0 : E} (hsz : 0 < S.heights.getD opBlake2s 0)
    (hz : (UniSound.Ids.zBad S p0).eval tE ≠ 0) :
    (coordinatesAt tE (coordinateFunctionals (S.heights.getD opBlake2s 0))).getD 0 0 ≠ tE ∧
      (coordinatesAt tE (coordinateFunctionals (S.heights.getD opBlake2s 0))).getD 0 0 ≠ p0 := by
  have hy0 : (coordinatesAt tE (coordinateFunctionals (S.heights.getD opBlake2s 0))).getD 0 0 =
      (UniSound.Ids.yP (coordinateFunctionals (S.heights.getD opBlake2s 0)) 0).eval tE :=
    UniSound.Ids.Eval.coordinatesAt_getD _ _ _ (by rw [UniSound.Ids.Eval.coordinateFunctionals_size]; exact hsz)
  unfold UniSound.Ids.zBad at hz
  rw [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    ← hy0] at hz
  exact ⟨fun h ↦ hz (by rw [h, CharTwo.add_self_eq_zero, zero_mul]),
    fun h ↦ hz (by rw [h, CharTwo.add_self_eq_zero, mul_zero])⟩

/-! ## `Compose`'s interface: the shapes -/


end RecGraph.Sim
