-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here, after this repository's `formal/EndToEnd/PcsBridge/Claims.lean` (the previous protocol's claims through
-- `Compose.Reduce`, whose fold helpers are copied).
import PcsQuotient.Reduction
import Compose.Reduce
import Field.F192
import Kc3.Cantor
import QuotientSecurity.Tables

/-!
# The deployed reduction's three claims, explicitly

`PcsQuotient.claimsAt` at `2^22` rows (`m = 24` cell variables) computes the witness, wiring and copy claims with
one batched inversion. **`claimsAt_spec`**: when it returns claims, every denominator is nonzero and the claims are,
with `w_k = S^k(t)` (`sq^[k] t`), `ζ = w_24 t`, `d = α + x + β t`, `d' = α + x + β s`:

* the witness claim at `(ρ, z₁, claimPoint 2 22 t)`, value `λ · v / claimScale 2 22 t`;
* the wiring claim at `claimPoint 0 24 t`, value `s / claimScale 0 24 t`;
* the copy claim at `(claimPoint 0 24 t, ζ/(1+ζ), y/(1+y), y²/(1+y²), κ)`, `κ = d d'/(ζ + d d')`, value
  `t (d + d' + μ w_24 g) / ((1+y)(1+y²) claimScale 0 24 t (1+ζ)(ζ + d d'))`, `g = gate / rows + pinned`, `pinned`
  the barycentric `(x + v(t)) / Z_P(t)` (`pinnedV`).
-/

set_option linter.unusedSectionVars false

open Finset

namespace PcsBridge.Kc3

open LeanVM.Parameters PcsQuotient PcsQuotient.Domain QuotientSecurity

/-! ## Folds -/

theorem foldl_congr_mem {α β : Type} (f g : β → α → β) :
    ∀ (l : List α), (∀ x ∈ l, ∀ b, f b x = g b x) → ∀ b, l.foldl f b = l.foldl g b
  | [], _, _ => rfl
  | x :: l, h, b => by
    rw [List.foldl_cons, List.foldl_cons, h x (List.mem_cons_self ..) b]
    exact foldl_congr_mem f g l (fun y hy ↦ h y (List.mem_cons_of_mem _ hy)) _

theorem foldl_add_range {M : Type} [AddCommMonoid M] (g : ℕ → M) (n : ℕ) (a : M) :
    (List.range n).foldl (fun acc e ↦ acc + g e) a = a + ∑ e ∈ range n, g e := by
  rw [List.range_eq_range', Compose.Reduce.foldl_range'_add]
  simp

theorem foldl_mul_range {M : Type} [CommMonoid M] (g : ℕ → M) (n : ℕ) (a : M) :
    (List.range n).foldl (fun acc e ↦ acc * g e) a = a * ∏ e ∈ range n, g e := by
  rw [List.range_eq_range', Compose.Reduce.foldl_range'_mul]
  simp

theorem getD_map_range {α : Type} (f : ℕ → α) {n k : ℕ} (hk : k < n) (d : α) :
    ((List.range n).map f).getD k d = f k := by
  simp [List.getD_eq_getElem?_getD, hk]

/-- The statement's `w` list is `S^k(t)`. -/
theorem digitsOf_eq (t : E) (n : ℕ) : digitsOf t n = (List.range (n + 1)).map fun k ↦ sq^[k] t := by
  unfold digitsOf
  induction n with
  | zero => simp
  | succ n ih =>
    have hlast : ((List.range (n + 1)).map fun k ↦ sq^[k] t).getLastD t = sq^[n] t := by
      rw [List.range_succ, List.map_append, List.map_singleton, List.getLastD_concat]
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, hlast,
      List.range_succ (n := n + 1), List.map_append, List.map_singleton, Function.iterate_succ_apply']
    rfl

/-! ## The constants -/

/-- The pin `p_k` in `E`. -/
noncomputable def pinE (k : ℕ) : E := ofK (point (anchorCell k))

theorem pinPoints_getD {k : ℕ} (hk : k < 11) : pinPoints.getD k 0 = point (anchorCell k) := by
  unfold pinPoints
  rw [getD_map_range _ (by exact hk)]

/-- The rows' polynomial at `t`, as the statement computes it. -/
noncomputable def rowsAt (t : E) : E := ∑ k ∈ range 23, ofK ((rowVanishing 24).getD k 0) * sq^[k] t

/-- The pins' barycentric term `(x + v(t)) / Z_P(t)`, as the statement computes it. -/
noncomputable def pinnedV (stmt : Statement) (t x : E) : E :=
  x * ∏ k ∈ range 11, (t + pinE k)⁻¹ +
    ∑ k ∈ range 11, ofK (pinWeights.getD k 0 * anchorValues stmt.words k) * (t + pinE k)⁻¹

/-- `z₁`, the witness claim's row point. -/
noncomputable def z1Of (t ρ : E) : E :=
  (witnessConic t (sq t) ρ).1 / ((witnessConic t (sq t) ρ).1 + (witnessConic t (sq t) ρ).2)

theorem ey_eq_y : ey = y := Primitives.F192.Y_eq_gen

theorem one_add_ey_ne_zero : (1 : E) + ey ≠ 0 := by
  rw [ey_eq_y]; exact Compose.Reduce.one_add_y_ne_zero

theorem one_add_ey_sq_ne_zero : (1 : E) + ey ^ 2 ≠ 0 := by
  rw [ey_eq_y]; exact Compose.Reduce.one_add_y_sq_ne_zero

theorem extension_eq :
    extension = ((ey / (1 + ey), ey ^ 2 / (1 + ey ^ 2)), ((1 + ey) * (1 + ey ^ 2))⁻¹) := by
  simp only [extension, div_eq_mul_inv, pow_two]

/-! ## The claims -/

/-- **What `claimsAt` returns**, explicitly. -/
structure Spec (stmt : Statement) (α β μ t ρ : E) (v : Fin 3 → E) (next : E) (cl : Claims) : Prop where
  one_add : ∀ k < 24, 1 + sq^[k] t ≠ 0
  zeta : 1 + sq^[24] t * t ≠ 0
  copy : sq^[24] t * t + (α + v 0 + β * t) * (α + v 0 + β * next) ≠ 0
  rows : rowsAt t ≠ 0
  pins : ∀ k < 11, t + pinE k ≠ 0
  conic : (witnessConic t (sq t) ρ).1 + (witnessConic t (sq t) ρ).2 ≠ 0
  wPoint : (fun k : Fin 24 => cl.witness.point.getD k 0) =
    Fin.cons ρ (Fin.cons (z1Of t ρ) (claimPoint 2 22 t))
  wValue : cl.witness.value =
    ((witnessWeights t (sq t) ρ (z1Of t ρ))[0] * v 0 + (witnessWeights t (sq t) ρ (z1Of t ρ))[1] * v 1 +
      (witnessWeights t (sq t) ρ (z1Of t ρ))[2] * v 2) / claimScale 2 22 t
  sPoint : (fun k : Fin 24 => cl.wiring.point.getD k 0) = claimPoint 0 24 t
  sValue : cl.wiring.value = next / claimScale 0 24 t
  cPoint : (fun k : Fin 28 => cl.copy.point.getD k 0) =
    Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (claimPoint 0 24 t)
      (sq^[24] t * t / (1 + sq^[24] t * t))) (ey / (1 + ey))) (ey ^ 2 / (1 + ey ^ 2)))
      ((α + v 0 + β * t) * (α + v 0 + β * next) /
        (sq^[24] t * t + (α + v 0 + β * t) * (α + v 0 + β * next)))
  cValue : cl.copy.value =
    t * ((α + v 0 + β * t) + (α + v 0 + β * next) +
        μ * sq^[24] t * ((v 2 + v 1 + v 0 * v 1) / rowsAt t + pinnedV stmt t (v 0))) /
      ((1 + ey) * (1 + ey ^ 2) * (claimScale 0 24 t * (1 + sq^[24] t * t)) *
        (sq^[24] t * t + (α + v 0 + β * t) * (α + v 0 + β * next)))

/-! ## The denominators' list -/

theorem getD_mem_of_lt {α : Type} (l : List α) (d : α) {k : ℕ} (hk : k < l.length) : l.getD k d ∈ l := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

section Den

variable (A : List E) (a b c : E) (B : List E) (C : E) (hA : A.length = 24) (hB : B.length = 11)
include hA

theorem den_lt {k : ℕ} (hk : k < 24) : (A ++ [a, b, c] ++ B ++ [C]).getD k 1 = A.getD k 1 := by
  simp only [List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_left (by omega)]

theorem den_24 : (A ++ [a, b, c] ++ B ++ [C]).getD 24 1 = a := by
  simp only [List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by omega), hA]
  rfl

theorem den_25 : (A ++ [a, b, c] ++ B ++ [C]).getD 25 1 = b := by
  simp only [List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by omega), hA]
  rfl

theorem den_26 : (A ++ [a, b, c] ++ B ++ [C]).getD 26 1 = c := by
  simp only [List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by omega), hA]
  rfl

include hB

theorem den_pin {k : ℕ} (hk : k < 11) : (A ++ [a, b, c] ++ B ++ [C]).getD (24 + 3 + k) 1 = B.getD k 1 := by
  simp only [List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by omega), hA, show 24 + 3 + k - 24 = 3 + k by omega]
  rw [show [a, b, c] ++ (B ++ [C]) = a :: b :: c :: (B ++ [C]) from rfl]
  rw [show 3 + k = k + 1 + 1 + 1 by omega]
  simp only [List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by omega)]

theorem den_38 : (A ++ [a, b, c] ++ B ++ [C]).getD (24 + 3 + 11) 1 = C := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp [hA, hB])]
  simp [hA, hB]

theorem den_length : (A ++ [a, b, c] ++ B ++ [C]).length = 39 := by simp [hA, hB]

end Den

set_option maxHeartbeats 4000000 in
/-- **The claims `claimsAt` returns at `2^22` rows**, explicitly (`Spec`). -/
theorem claimsAt_spec {stmt : Statement} {α β μ t ρ : E} {v : Fin 3 → E} {next : E} {cl : Claims}
    (h : claimsAt 22 stmt α β μ t ρ (Vector.ofFn v) next = some cl) : Spec stmt α β μ t ρ v next cl := by
  revert h
  unfold claimsAt
  lift_lets
  extract_lets m w wAt x c vy gate tau rows d dNext product z zeta pubWords
  have hm : m = 24 := rfl
  have hw : w = (List.range 25).map fun k => sq^[k] t := digitsOf_eq t 24
  have hwAt : ∀ k < 25, wAt k = sq^[k] t := fun k hk => by simp only [wAt, hw, getD_map_range _ hk]
  have hx : x = v 0 := by simp [x]
  have hc : c = v 1 := by simp [c]
  have hvy : vy = v 2 := by simp [vy]
  have hz : z = sq^[24] t := hwAt 24 (by norm_num)
  have hzeta : zeta = sq^[24] t * t := by rw [show zeta = z * t from rfl, hz]
  have hprod : product = (α + v 0 + β * t) * (α + v 0 + β * next) := by
    simp only [product, d, dNext, hx]
  have hrows : rows = rowsAt t := by
    simp only [rows, tau, hm, rowsAt]
    rw [show 24 - 1 = 23 from rfl, foldl_add_range, zero_add]
    exact sum_congr rfl fun k hk => by rw [hwAt k (by simp at hk; omega)]
  generalize hcon : witnessConic t (wAt 1) ρ = cc
  rcases cc with ⟨cA, cB⟩
  have hcon' : witnessConic t (sq t) ρ = (cA, cB) := by
    rw [← hcon, hwAt 1 (by norm_num)]; rfl
  dsimp (config := { zeta := false }) only
  extract_lets denominators inv u copyInverse rowsInverse pinInverse conicInverse middle wiringScale
    tableScale pinned g kappa copyValue z1 lam opened
  intro h
  split_ifs at h with hany
  cases h
  -- the denominators
  set A : List E := (List.range m).map fun k => 1 + wAt k with hA
  set B : List E := pinPoints.map fun p => t + ofK p with hB
  have hAl : A.length = 24 := by simp [hA, hm]
  have hBl : B.length = 11 := by simp [hB, pinPoints, publicRows, publicWords]
  have hden : denominators = A ++ [1 + zeta, zeta + product, rows] ++ B ++ [cA + cB] := rfl
  have hAk : ∀ k < 24, A.getD k 1 = 1 + sq^[k] t := fun k hk => by
    rw [hA, hm, getD_map_range _ hk, hwAt k (by omega)]
  have hBk : ∀ k < 11, B.getD k 1 = t + pinE k := fun k hk => by
    rw [hB, pinPoints, List.map_map, getD_map_range _ (by exact hk)]
    rfl
  have hnz : ∀ k < 39, denominators.getD k 1 ≠ 0 := by
    intro k hk hk0
    refine hany (List.any_eq_true.mpr ⟨_, getD_mem_of_lt _ 1 (by rw [hden, den_length _ _ _ _ _ _ hAl hBl]; exact hk),
      by simpa using hk0⟩)
  have hinv : ∀ k < 24, inv k = (1 + sq^[k] t)⁻¹ := fun k hk => by
    simp only [inv, hden, den_lt _ _ _ _ _ _ hAl hk, hAk k hk]
  have hinv24 : inv 24 = (1 + sq^[24] t * t)⁻¹ := by
    simp only [inv, hden, den_24 _ _ _ _ _ _ hAl, hzeta]
  have hinv25 : inv 25 = (sq^[24] t * t + (α + v 0 + β * t) * (α + v 0 + β * next))⁻¹ := by
    simp only [inv, hden, den_25 _ _ _ _ _ _ hAl, hzeta, hprod]
  have hinv26 : inv 26 = (rowsAt t)⁻¹ := by
    simp only [inv, hden, den_26 _ _ _ _ _ _ hAl, hrows]
  have hinvP : ∀ k < 11, inv (24 + 3 + k) = (t + pinE k)⁻¹ := fun k hk => by
    simp only [inv, hden, den_pin _ _ _ _ _ _ hAl hBl hk, hBk k hk]
  have hinv38 : inv 38 = (cA + cB)⁻¹ := by
    simp only [inv, hden]
    rw [den_38 _ _ _ _ _ _ hAl hBl]
  have h1 : ∀ k < 24, 1 + sq^[k] t ≠ 0 := fun k hk => by
    have := hnz k (by omega)
    rwa [hden, den_lt _ _ _ _ _ _ hAl hk, hAk k hk] at this
  have h24 : 1 + sq^[24] t * t ≠ 0 := by
    have := hnz 24 (by omega)
    rwa [hden, den_24 _ _ _ _ _ _ hAl, hzeta] at this
  have h25 : sq^[24] t * t + (α + v 0 + β * t) * (α + v 0 + β * next) ≠ 0 := by
    have := hnz 25 (by omega)
    rwa [hden, den_25 _ _ _ _ _ _ hAl, hzeta, hprod] at this
  have h26 : rowsAt t ≠ 0 := by
    have := hnz 26 (by omega)
    rwa [hden, den_26 _ _ _ _ _ _ hAl, hrows] at this
  have hP : ∀ k < 11, t + pinE k ≠ 0 := fun k hk => by
    have := hnz (24 + 3 + k) (by omega)
    rwa [hden, den_pin _ _ _ _ _ _ hAl hBl hk, hBk k hk] at this
  have h38 : cA + cB ≠ 0 := by
    have := hnz 38 (by omega)
    rwa [hden, show (38 : ℕ) = 24 + 3 + 11 from rfl, den_38 _ _ _ _ _ _ hAl hBl] at this
  -- the scales
  have hu : ∀ k < 24, u.getD k 0 = sq^[k] t / (1 + sq^[k] t) := fun k hk => by
    simp only [u, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp [hm]; omega), List.getElem?_map, List.getElem?_range (by rw [hm]; omega)]
    simp only [Option.map_some, Option.getD_some, hwAt k (by omega), hinv k hk, div_eq_mul_inv]
  have hu24 : u.getD 24 0 = sq^[24] t * t / (1 + sq^[24] t * t) := by
    simp only [u, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp [hm])]
    simp [hm, hzeta, hinv24, div_eq_mul_inv]
  have hul : u.length = 25 := by simp [u, hm]
  have hmiddle : middle = (claimScale 2 22 t)⁻¹ := by
    simp only [middle, hm, show 24 - 3 = 21 from rfl]
    have e : ∏ k ∈ range 21, inv (3 + k) = ∏ k ∈ range 21, (1 + sq^[k + 1 + 2] t)⁻¹ :=
      prod_congr rfl fun k hk => by
        rw [hinv (3 + k) (by simp at hk; omega), show k + 1 + 2 = 3 + k by omega]
    rw [Compose.Reduce.foldl_range'_mul, e, hinv 2 (by norm_num), claimScale,
      Fin.prod_univ_eq_prod_range (fun k => 1 + sq^[k + 2] t) 22,
      prod_range_succ' (fun k => 1 + sq^[k + 2] t), mul_inv, prod_inv_distrib, zero_add]
    ring
  have hwire : wiringScale = (claimScale 0 24 t)⁻¹ := by
    simp only [wiringScale, hmiddle, claimScale]
    rw [Fin.prod_univ_eq_prod_range (fun k => 1 + sq^[k + 0] t) 24,
      prod_range_succ' (fun k => 1 + sq^[k + 0] t), prod_range_succ' (fun k => 1 + sq^[k + 1 + 0] t),
      Fin.prod_univ_eq_prod_range (fun k => 1 + sq^[k + 2] t) 22, hinv 0 (by norm_num), hinv 1 (by norm_num)]
    simp only [add_zero, zero_add, mul_inv, add_assoc, Nat.reduceAdd]
    ring
  have hz1 : z1 = z1Of t ρ := by
    simp only [z1, conicInverse, show m + 3 + publicRows = 38 from rfl, hinv38, z1Of, hcon', div_eq_mul_inv]
  have hpinned : pinned = pinnedV stmt t (v 0) := by
    have hstep : ∀ k ∈ List.range 11, ∀ acc : E,
        (if k < publicWords then acc + ofK (pubWords.getD k 0) * ofK (pinWeights.getD k 0) * pinInverse k
          else if anchorValues pubWords k = 0 then acc
          else acc + ofK (pinWeights.getD k 0 * anchorValues pubWords k) * pinInverse k) =
        acc + ofK (pinWeights.getD k 0 * anchorValues stmt.words k) * (t + pinE k)⁻¹ := by
      intro k hk acc
      have hk' : k < 11 := List.mem_range.mp hk
      have hpi : pinInverse k = (t + pinE k)⁻¹ := by
        simp only [pinInverse, hm]
        exact hinvP k hk'
      rw [hpi]
      split_ifs with h8 h0
      · simp only [pubWords, anchorValues, h8, if_true, Compose.Reduce.ofK_mul]
        ring
      · simp only [pubWords] at h0
        rw [h0, mul_zero, Compose.Reduce.ofK_zero, zero_mul, add_zero]
      · rfl
    have hprodP : List.foldl (fun acc k => acc * pinInverse k) 1 (List.range 11) =
        ∏ k ∈ range 11, (t + pinE k)⁻¹ := by
      rw [foldl_mul_range, one_mul]
      exact prod_congr rfl fun k hk => by
        simp only [pinInverse, hm]
        exact hinvP k (List.mem_range.mp (by simpa using hk))
    simp only [pinned, show publicRows = 11 from rfl]
    rw [foldl_congr_mem _ (fun acc k => acc + ofK (pinWeights.getD k 0 * anchorValues stmt.words k) *
      (t + pinE k)⁻¹) _ hstep, foldl_add_range, hprodP, hx]
    rfl
  have hw1 : wAt 1 = QuotientSecurity.sq t := by rw [hwAt 1 (by norm_num)]; rfl
  refine ⟨h1, h24, h25, h26, hP, by rw [hcon']; exact h38, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the witness point
    funext k
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun i => ?_) k) k
    · simp
    · simp [hz1]
    · have hi := i.2
      show ([ρ, z1] ++ List.take (m - 2) (List.drop 2 u)).getD (i + 1 + 1) 0 = _
      rw [show ([ρ, z1] ++ List.take (m - 2) (List.drop 2 u)) = ρ :: z1 :: List.take (m - 2) (List.drop 2 u)
        from rfl]
      simp only [List.getD_cons_succ, Fin.cons_succ]
      rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (by rw [hm]; omega), List.getElem?_drop,
        ← List.getD_eq_getElem?_getD, show 2 + (i : ℕ) = i + 2 by omega, hu _ (by omega)]
      rfl
  · -- the witness value
    simp only [opened, lam, hw1, hz1, hx, hc, hvy, hmiddle, div_eq_mul_inv]
  · -- the wiring point
    funext k
    have hk := k.2
    show (List.take m u).getD k 0 = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (by rw [hm]; omega),
      ← List.getD_eq_getElem?_getD, hu _ hk]
    simp [claimPoint]
  · -- the wiring value
    show next * wiringScale = _
    rw [hwire, div_eq_mul_inv]
  · -- the copy point
    show (fun k : Fin 28 => (copyPoint u kappa).getD k 0) = _
    have hU : (List.map (fun k => wAt k * inv k) (List.range m)).length = 24 := by simp [hm]
    have e : copyPoint u kappa = (((List.map (fun k => wAt k * inv k) (List.range m) ++ [zeta * inv m]) ++
        [ey / (1 + ey)]) ++ [ey ^ 2 / (1 + ey ^ 2)]) ++ [kappa] := by
      simp [copyPoint, extension_eq, u]
    rw [e, Compose.Reduce.getD_snoc_fun _ (by simp [hm]), Compose.Reduce.getD_snoc_fun _ (by simp [hm]),
      Compose.Reduce.getD_snoc_fun _ (by simp [hm]), Compose.Reduce.getD_snoc_fun _ hU]
    have hfun : (fun k : Fin 24 => (List.map (fun k => wAt k * inv k) (List.range m)).getD k 0) =
        claimPoint 0 24 t := by
      funext k
      have hk := k.2
      rw [hm, getD_map_range _ hk, hwAt _ (by omega), hinv _ hk]
      simp [claimPoint, div_eq_mul_inv]
    have hkappa : kappa = (α + v 0 + β * t) * (α + v 0 + β * next) /
        (sq^[24] t * t + (α + v 0 + β * t) * (α + v 0 + β * next)) := by
      simp only [kappa, copyInverse, hm, Nat.reduceAdd, hinv25, hprod, div_eq_mul_inv]
    rw [hfun, hkappa, hm, hzeta, hinv24]
    simp only [div_eq_mul_inv]
  · -- the copy value
    show copyValue = _
    simp only [copyValue, extension_eq, tableScale, hwire, hm, hinv24, copyInverse, Nat.reduceAdd, hinv25,
      g, gate, rowsInverse, hinv26, hpinned, hz, d, dNext, hx, hc, hvy]
    simp only [div_eq_mul_inv, mul_inv]
    ring

end PcsBridge.Kc3
