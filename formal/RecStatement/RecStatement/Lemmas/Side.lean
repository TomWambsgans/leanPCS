-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecStatement.Lemmas.Arith

/-!
# The pushes' sums, as sums

* **The accumulated fractions** (`accStep`): `(a, b) ↦ (a d + b x, b d)` from the first `(x, d)` gives
  `b = Π d_i` and `a/b = Σ x_i/d_i` (`accFold_some`, `accFold_none`; the denominator alone, `accFold_snd`);
  `pushSums` is two of them, over the pulling groups (`(N_g X_g, D_g)`, `X_g = E_g + v_0`) and over the pull-less
  ones (`(N_g X_g, D_g G_d)`, `X_g = (E_g + Δ) G_d + w_m G_n` for its role's `Φ`, `E_g + Δ` and `D_g` for a role of no
  port of nonzero value) (`pushSums_eq`; a one-pair group's `N_g` is `1`).
* **A port role's `Φ` fraction** (`phiFrac_spec`): `G_d = Π (w_r + ω_{y_J})` and `G_n/G_d = Σ F_J/(w_r + ω_{y_J})`.
-/

set_option linter.unusedSectionVars false

namespace RecStatement

open Finset

variable {F : Type} [Field F]

/-! ## Accumulated fractions -/

/-- One step of an accumulated fraction: `(a, b) + x/d = (a d + b x, b d)`, from `(x, d)`. -/
def accStep (acc : Option (F × F)) (xd : F × F) : Option (F × F) :=
  match acc with
  | some (a, b) => some (a * xd.2 + b * xd.1, b * xd.2)
  | none => some (xd.1, xd.2)

theorem accFold_some (xs : List (F × F)) (a b : F) (hb : b ≠ 0) (hd : ∀ xd ∈ xs, xd.2 ≠ 0) :
    ∃ a' b', xs.foldl accStep (some (a, b)) = some (a', b') ∧ b' = b * (xs.map (·.2)).prod ∧
      a' = b' * (a / b + (xs.map fun xd ↦ xd.1 / xd.2).sum) := by
  induction xs generalizing a b with
  | nil => exact ⟨a, b, rfl, by simp, by field_simp; simp⟩
  | cons xd xs ih =>
    have hd0 : xd.2 ≠ 0 := hd xd List.mem_cons_self
    obtain ⟨a', b', h1, h2, h3⟩ := ih (a * xd.2 + b * xd.1) (b * xd.2) (mul_ne_zero hb hd0)
      fun y hy ↦ hd y (List.mem_cons_of_mem _ hy)
    refine ⟨a', b', h1, by rw [h2]; simp [List.prod_cons, mul_assoc], ?_⟩
    rw [h3]
    simp only [List.map_cons, List.sum_cons]
    field_simp
    ring

/-- **An accumulated fraction**: from nothing, over nonzero `d`'s, the product and the sum of the `x/d`. -/
theorem accFold_none (xs : List (F × F)) (h : xs ≠ []) (hd : ∀ xd ∈ xs, xd.2 ≠ 0) :
    ∃ a' b', xs.foldl accStep none = some (a', b') ∧ b' = (xs.map (·.2)).prod ∧
      a' = b' * (xs.map fun xd ↦ xd.1 / xd.2).sum := by
  cases xs with
  | nil => exact absurd rfl h
  | cons xd xs =>
    have hd0 : xd.2 ≠ 0 := hd xd List.mem_cons_self
    obtain ⟨a', b', h1, h2, h3⟩ := accFold_some xs xd.1 xd.2 hd0 fun y hy ↦ hd y (List.mem_cons_of_mem _ hy)
    exact ⟨a', b', h1, by rw [h2]; simp, by rw [h3]; simp [List.map_cons, List.sum_cons]⟩

/-- The accumulated denominator is the product, whatever the numerators. -/
theorem accFold_snd : ∀ (xs : List (F × F)) (acc : Option (F × F)),
    ((xs.foldl accStep acc).map (·.2)).getD 1 = (acc.map (·.2)).getD 1 * (xs.map (·.2)).prod
  | [], acc => by simp
  | xd :: xs, acc => by
    rw [List.foldl_cons, accFold_snd xs]
    cases acc <;> simp [accStep, mul_assoc]

theorem addFrac_eq (acc : Option (F × F)) (x d : F) : addFrac acc x d = accStep acc (x, d) := by
  cases acc with
  | none => rfl
  | some ab => obtain ⟨a, b⟩ := ab; rfl

/-- A pulling group's term `(N_g (E_g + v_0), D_g)`. -/
def intTerm (gs cells : List F) (v0 : F) (gf : GroupF F × (F × F)) : F × F :=
  (gf.2.1 * (gf.1.formula.eval gs (fun c ↦ cells.getD (c ^^^ gf.1.role) 0) + v0), gf.2.2)

/-- A pull-less group's value and denominator before its `N_g`: `((E_g + Δ) G_d + w_m G_n, D_g G_d)` for its role's
`Φ`, `(E_g + Δ, D_g)` for a role of no port of nonzero value. -/
def portVD (gs cells : List F) (delta : F) (wPhi : List (ℕ × F × F)) (gf : GroupF F × (F × F)) : F × F :=
  let e := gf.1.formula.eval gs (fun c ↦ cells.getD (c ^^^ gf.1.role) 0)
  match wPhi.find? (·.1 = gf.1.role) with
  | some (_, n, d) => ((e + delta) * d + n, gf.2.2 * d)
  | none => (e + delta, gf.2.2)

/-- A pull-less group's term `(N_g X_g, D_g G_d)`. -/
def portTerm (gs cells : List F) (delta : F) (wPhi : List (ℕ × F × F)) (gf : GroupF F × (F × F)) : F × F :=
  (gf.2.1 * (portVD gs cells delta wPhi gf).1, (portVD gs cells delta wPhi gf).2)

/-- A one-pair group's fraction is `(1, d)` (`fraction_singleton`). -/
def SingleOne (L : List (GroupF F × (F × F))) : Prop := ∀ gf ∈ L, gf.1.pairs.length = 1 → gf.2.1 = 1

theorem pushStep_eq (gs cells : List F) (v0 delta : F) (wPhi : List (ℕ × F × F)) (ab s : Option (F × F))
    (g : GroupF F) (nd : F × F) (h1 : g.pairs.length = 1 → nd.1 = 1) :
    pushStep gs cells v0 delta wPhi (ab, s) (g, nd) =
      if g.pulls then (accStep ab (intTerm gs cells v0 (g, nd)), s)
      else (ab, accStep s (portTerm gs cells delta wPhi (g, nd))) := by
  by_cases hp : g.pulls
  · by_cases hs : g.pairs.length = 1
    · simp [pushStep, intTerm, hp, hs, h1 hs, addFrac_eq]
    · simp [pushStep, intTerm, hp, hs, addFrac_eq]
  · cases hf : wPhi.find? (·.1 = g.role) with
    | none =>
      by_cases hs : g.pairs.length = 1
      · simp [pushStep, portTerm, portVD, hp, hs, hf, addFrac_eq, h1 hs]
      · simp [pushStep, portTerm, portVD, hp, hs, hf, addFrac_eq]
    | some x =>
      obtain ⟨k, n, d⟩ := x
      by_cases hs : g.pairs.length = 1
      · simp [pushStep, portTerm, portVD, hp, hs, hf, addFrac_eq, h1 hs]
      · simp [pushStep, portTerm, portVD, hp, hs, hf, addFrac_eq]

theorem pushStep_fold (gs cells : List F) (v0 delta : F) (wPhi : List (ℕ × F × F)) :
    ∀ (L : List (GroupF F × (F × F))) (ab s : Option (F × F)), SingleOne L →
      L.foldl (pushStep gs cells v0 delta wPhi) (ab, s) =
        (((L.filter fun gf ↦ gf.1.pulls).map (intTerm gs cells v0)).foldl accStep ab,
          ((L.filter fun gf ↦ !gf.1.pulls).map (portTerm gs cells delta wPhi)).foldl accStep s)
  | [], ab, s, _ => rfl
  | (g, nd) :: L, ab, s, h => by
    have h1 : g.pairs.length = 1 → nd.1 = 1 := h (g, nd) List.mem_cons_self
    have hL : SingleOne L := fun x hx ↦ h x (List.mem_cons_of_mem _ hx)
    rw [List.foldl_cons, pushStep_eq gs cells v0 delta wPhi ab s g nd h1]
    by_cases hp : g.pulls
    · rw [ite_eq_left hp, pushStep_fold gs cells v0 delta wPhi L _ _ hL]
      simp [hp]
    · rw [ite_eq_right hp, pushStep_fold gs cells v0 delta wPhi L _ _ hL]
      simp [hp]

/-- **`pushSums`** is the two accumulated fractions: over the pulling groups, `(N_g (E_g + v_0), D_g)`; over the
pull-less ones, `(N_g X_g, D_g G_d)`. -/
theorem pushSums_eq (S : CoreSpec F) (gs cells : List F) (v0 delta : F) (wPhi : List (ℕ × F × F))
    (fracs : List (F × F)) (h : SingleOne (S.groups.zip fracs)) :
    pushSums S gs cells v0 delta wPhi fracs =
      (((((S.groups.zip fracs).filter fun gf ↦ gf.1.pulls).map (intTerm gs cells v0)).foldl accStep none).map
          (·.1) |>.getD 0,
        ((((S.groups.zip fracs).filter fun gf ↦ gf.1.pulls).map (intTerm gs cells v0)).foldl accStep none).map
          (·.2) |>.getD 1,
        ((((S.groups.zip fracs).filter fun gf ↦ !gf.1.pulls).map (portTerm gs cells delta wPhi)).foldl accStep
          none).map (·.1) |>.getD 0,
        ((((S.groups.zip fracs).filter fun gf ↦ !gf.1.pulls).map (portTerm gs cells delta wPhi)).foldl accStep
          none).map (·.2) |>.getD 1) := by
  unfold pushSums
  rw [pushStep_fold gs cells v0 delta wPhi _ none none h]

/-! ## A port role's `Φ` fraction -/

theorem foldl_phi_snd (ω : ℕ → F) (gs pubs : List F) (wr : F) :
    ∀ (ts : List (ℕ × LinF F)) (nd : F × F),
      (ts.foldl (fun nd yl ↦ (nd.1 * (wr + ω yl.1) + nd.2 * yl.2.eval gs (fun c ↦ pubs.getD c 0),
        nd.2 * (wr + ω yl.1))) nd).2 = nd.2 * (ts.map fun yl ↦ wr + ω yl.1).prod
  | [], nd => by simp
  | yl :: ts, nd => by
    rw [List.foldl_cons, foldl_phi_snd ω gs pubs wr ts]
    simp [mul_assoc]

theorem foldl_phi_fst (ω : ℕ → F) (gs pubs : List F) (wr : F) :
    ∀ (ts : List (ℕ × LinF F)) (nd : F × F), nd.2 ≠ 0 → (∀ yl ∈ ts, wr + ω yl.1 ≠ 0) →
      (ts.foldl (fun nd yl ↦ (nd.1 * (wr + ω yl.1) + nd.2 * yl.2.eval gs (fun c ↦ pubs.getD c 0),
        nd.2 * (wr + ω yl.1))) nd).1 =
        (ts.foldl (fun nd yl ↦ (nd.1 * (wr + ω yl.1) + nd.2 * yl.2.eval gs (fun c ↦ pubs.getD c 0),
          nd.2 * (wr + ω yl.1))) nd).2 *
          (nd.1 / nd.2 + (ts.map fun yl ↦ yl.2.eval gs (fun c ↦ pubs.getD c 0) / (wr + ω yl.1)).sum)
  | [], nd, h0, _ => by
    simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
    field_simp
  | yl :: ts, nd, h0, hy => by
    have hy0 : wr + ω yl.1 ≠ 0 := hy yl List.mem_cons_self
    rw [List.foldl_cons, foldl_phi_fst ω gs pubs wr ts _ (mul_ne_zero h0 hy0)
      fun x hx ↦ hy x (List.mem_cons_of_mem _ hx)]
    simp only [List.map_cons, List.sum_cons]
    field_simp
    ring

/-- **A port role's `Φ` fraction**: its denominator `Π (w_r + ω_{y_J})`, its fraction `Σ F_J/(w_r + ω_{y_J})`,
where no denominator vanishes. -/
theorem phiFrac_spec (ω : ℕ → F) (gs pubs : List F) (wr : F) (ts : List (ℕ × LinF F))
    (hy : ∀ yl ∈ ts, wr + ω yl.1 ≠ 0) :
    (phiFrac ω gs pubs wr ts).2 = (ts.map fun yl ↦ wr + ω yl.1).prod ∧
      (phiFrac ω gs pubs wr ts).1 = (phiFrac ω gs pubs wr ts).2 *
        (ts.map fun yl ↦ yl.2.eval gs (fun c ↦ pubs.getD c 0) / (wr + ω yl.1)).sum := by
  cases ts with
  | nil => exact ⟨rfl, by simp [phiFrac]⟩
  | cons yl ts =>
    obtain ⟨y, l⟩ := yl
    have hy0 : wr + ω y ≠ 0 := hy (y, l) List.mem_cons_self
    refine ⟨?_, ?_⟩
    · simp only [phiFrac]
      rw [foldl_phi_snd]
      simp
    · simp only [phiFrac]
      rw [foldl_phi_fst ω gs pubs wr ts _ hy0 fun x hx ↦ hy x (List.mem_cons_of_mem _ hx)]
      simp only [List.map_cons, List.sum_cons]

end RecStatement
