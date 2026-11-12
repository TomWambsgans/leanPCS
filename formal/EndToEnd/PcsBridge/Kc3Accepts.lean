-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here; `witness_mle'` and `copy_mle` follow `formal/QuotientSecurity/Tables.lean`'s `witness_mle` and
-- `quotient_mle` (adapted from leanVM, branch PCS-openings-aggregation, commit 651453c6) for the deployed layouts.
import PcsBridge.Kc3Claims

/-!
# The claims hold of tables only if F1's verifier accepts their polynomials

The witness table (`24` variables) holds the four row polynomials (`witnessOfTable`), the quotient table (`28`
variables: the coefficient's `24`, then the digit, the two limb bits, the kind) holds `A₀, A₁, B₀, B₁`
(`readTM`: `q = A₀ + ζ A₁`, `x h = B₀ + ζ B₁`, each the limbs on `1, y, y², y³`). **`accepts_of_claims`**: for
F1's parameters `P` that match the statement's constants (`Matches`: `θ = β₁`, `2^22` rows, `Z(t) = w_24(t)`,
`Z_R(t)` the statement's rows' polynomial, the pins `p_k`, `σ`'s polynomial the wiring table's), if `claimsAt`
returns claims and the three tables satisfy them, then `P.Accepts` holds of the tables' polynomials at the
challenges and the proof's values.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace PcsBridge.Kc3

open LeanVM.Parameters PcsQuotient PcsQuotient.Domain QuotientSecurity

/-! ## The witness table -/

/-- The witness table's claim at `(ρ, z₁, …)`, as its polynomials' values at the row. -/
theorem witness_mle' {F : Type*} [Field F] [CharP F 2] {k : ℕ} (c : (Fin (k + 1 + 1) → Bool) → F)
    (t ρ z : F) (ht : ∀ i : Fin k, 1 + sq^[(i : ℕ) + 2] t ≠ 0) :
    mle c (Fin.cons ρ (Fin.cons z (claimPoint 2 k t)))
      = (∑ j, _root_.Kc3.Params.rowWeights ρ z j * ((witnessOfTable c j).comp rowPoly).eval t) / claimScale 2 k t := by
  rw [mle_cons, mle_cons, mle_cons]
  simp only [mle_claimPoint_two _ t ht, Fin.sum_univ_four, _root_.Kc3.Params.rowWeights, witnessOfTable,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

theorem natDegree_witnessOfTable_lt {F : Type*} [Field F] [CharP F 2] {k : ℕ}
    (c : (Fin (k + 1 + 1) → Bool) → F) (j : Fin 4) : (witnessOfTable c j).natDegree < 2 ^ k := by
  fin_cases j <;> exact natDegree_tablePoly_lt _

/-! ## The quotient table -/

/-- One of the sixteen tables the last four coordinates (digit, limb bits, kind) choose from. -/
def subT {F : Type*} {k : ℕ} (c : (Fin (k + 1 + 1 + 1 + 1) → Bool) → F) (d l₀ l₁ κ : Bool) :
    (Fin k → Bool) → F :=
  fun b => c (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc b d) l₀) l₁) κ)

/-- A digit's polynomial of a kind: its four limbs on `1, Y, Y², Y³`. -/
noncomputable def limbPoly {F : Type*} [Field F] [CharP F 2] {k : ℕ} (Y : F) (c : (Fin (k + 1 + 1 + 1 + 1) → Bool) → F)
    (d κ : Bool) : F[X] :=
  tablePoly (subT c d false false κ) + C Y * tablePoly (subT c d true false κ)
    + C (Y ^ 2) * tablePoly (subT c d false true κ) + C (Y ^ 3) * tablePoly (subT c d true true κ)

theorem natDegree_limbPoly_lt {F : Type*} [Field F] [CharP F 2] {k : ℕ} (Y : F) (c : (Fin (k + 1 + 1 + 1 + 1) → Bool) → F)
    (d κ : Bool) : (limbPoly Y c d κ).natDegree < 2 ^ k := by
  have h := fun c' : (Fin k → Bool) → F => natDegree_tablePoly_lt c'
  have hC := fun (a : F) (c' : (Fin k → Bool) → F) =>
    lt_of_le_of_lt (natDegree_C_mul_le a (tablePoly c')) (h c')
  unfold limbPoly
  exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (natDegree_add_le _ _)
    (max_lt (lt_of_le_of_lt (natDegree_add_le _ _) (max_lt (h _) (hC _ _))) (hC _ _))) (hC _ _))

/-- **The quotient table's claim** at `(claimPoint 0 k t, e, y₀, y₁, κ)`, as its four polynomials' values. -/
theorem copy_mle {F : Type*} [Field F] [CharP F 2] {k : ℕ} (c : (Fin (k + 1 + 1 + 1 + 1) → Bool) → F)
    (t e κ Y : F) (hY : 1 + Y ≠ 0) (hY2 : 1 + Y ^ 2 ≠ 0) (ht : ∀ i : Fin k, 1 + sq^[(i : ℕ)] t ≠ 0) :
    mle c (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (claimPoint 0 k t) e) (Y / (1 + Y))) (Y ^ 2 / (1 + Y ^ 2))) κ)
      = ((1 + κ) * ((1 + e) * (limbPoly Y c false false).eval t + e * (limbPoly Y c true false).eval t)
          + κ * ((1 + e) * (limbPoly Y c false true).eval t + e * (limbPoly Y c true true).eval t))
        / ((1 + Y) * (1 + Y ^ 2)) / claimScale 0 k t := by
  have hS := claimScale_ne_zero (first := 0) (m := k) (t := t) (fun i => ht i)
  have hsub : ∀ d l₀ l₁ κ' : Bool,
      mle (fun b => c (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc b d) l₀) l₁) κ')) (claimPoint 0 k t)
        = (tablePoly (subT c d l₀ l₁ κ')).eval t / claimScale 0 k t := fun d l₀ l₁ κ' =>
    mle_claimPoint_zero (subT c d l₀ l₁ κ') t ht
  have h0 : 1 + Y / (1 + Y) = (1 + Y)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [add_mul, one_mul, div_mul_cancel₀ _ hY, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  have h1 : 1 + Y ^ 2 / (1 + Y ^ 2) = (1 + Y ^ 2)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [add_mul, one_mul, div_mul_cancel₀ _ hY2, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  simp only [mle_snoc]
  simp only [hsub, h0, h1]
  simp only [limbPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, div_eq_mul_inv, mul_inv]
  ring

/-- The quotient table's second message. -/
noncomputable def readTM (c : (Fin (24 + 1 + 1 + 1 + 1) → Bool) → E) : _root_.Kc3.Params.TMsg E where
  A₀ := limbPoly (k := 24) ey c false false
  A₁ := limbPoly (k := 24) ey c true false
  B₀ := limbPoly (k := 24) ey c false true
  B₁ := limbPoly (k := 24) ey c true true

theorem readTM_A₀ (c : (Fin (24 + 1 + 1 + 1 + 1) → Bool) → E) :
    (readTM c).A₀ = limbPoly (k := 24) ey c false false := by simp only [readTM]
theorem readTM_A₁ (c : (Fin (24 + 1 + 1 + 1 + 1) → Bool) → E) :
    (readTM c).A₁ = limbPoly (k := 24) ey c true false := by simp only [readTM]
theorem readTM_B₀ (c : (Fin (24 + 1 + 1 + 1 + 1) → Bool) → E) :
    (readTM c).B₀ = limbPoly (k := 24) ey c false true := by simp only [readTM]
theorem readTM_B₁ (c : (Fin (24 + 1 + 1 + 1 + 1) → Bool) → E) :
    (readTM c).B₁ = limbPoly (k := 24) ey c true true := by simp only [readTM]

/-! ## The pins -/

theorem ofK_inv (a : K) : ofK a⁻¹ = (ofK a)⁻¹ := map_inv₀ (algebraMap K E) a

theorem ofK_prod (s : Finset ℕ) (f : ℕ → K) : ofK (∏ i ∈ s, f i) = ∏ i ∈ s, ofK (f i) :=
  map_prod (algebraMap K E) f s

/-- The statement's pin weights, in `E`. -/
theorem ofK_pinWeights {k : ℕ} (hk : k < 11) :
    ofK (pinWeights.getD k 0) = (∏ j ∈ (range 11).erase k, (pinE k + pinE j))⁻¹ := by
  unfold pinWeights
  rw [getD_map_range _ (by exact hk), ofK_inv]
  congr 1
  rw [show publicRows = 11 from rfl,
    foldl_congr_mem _ (fun acc j => acc * (if j = k then 1 else pinPoints.getD k 0 + pinPoints.getD j 0)) _
      (fun j _ acc => by split_ifs <;> simp), foldl_mul_range, one_mul, ofK_prod,
    ← Finset.prod_erase _ (a := k) (by simp)]
  refine prod_congr rfl fun j hj => ?_
  have hjk : j ≠ k := Finset.ne_of_mem_erase hj
  have hj' : j < 11 := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
  rw [if_neg hjk, Compose.Reduce.ofK_add, pinPoints_getD hk, pinPoints_getD hj']
  rfl

/-- **The pins' barycentric term**: `(x + v(t)) / Z_P(t)` is the statement's `pinned`. -/
theorem pinned_eq (P : _root_.Kc3.Params E) (hpins : ∀ k : Fin 11, P.pinPt k = pinE k)
    (stmt : Statement) (t x : E) (ht : ∀ k < 11, t + pinE k ≠ 0) :
    (x + (P.pinPoly (fun k => ofK (anchorValues stmt.words k))).eval t) / P.vPins.eval t =
      pinnedV stmt t x := by
  have hne : ∀ i ∈ (univ : Finset (Fin 11)), t ≠ P.pinPt i := fun i _ h => by
    have := ht i i.2
    rw [h, hpins, CharTwo.add_self_eq_zero] at this
    exact this rfl
  have hZ : P.vPins.eval t = ∏ k ∈ range 11, (t + pinE k) := by
    unfold _root_.Kc3.Params.vPins
    rw [Polynomial.eval_prod, ← Fin.prod_univ_eq_prod_range (fun k => t + pinE k) 11]
    refine prod_congr rfl fun k _ => ?_
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, hpins, CharTwo.sub_eq_add]
  have hZ0 : P.vPins.eval t ≠ 0 := by
    rw [hZ]; exact prod_ne_zero_iff.mpr fun k hk => ht k (mem_range.mp hk)
  unfold _root_.Kc3.Params.pinPoly
  rw [Lagrange.eval_interpolate_not_at_node _ hne]
  have hnodal : (Lagrange.nodal univ P.pinPt).eval t = P.vPins.eval t := rfl
  have hsum : ∑ i : Fin 11, Lagrange.nodalWeight univ P.pinPt i * (t - P.pinPt i)⁻¹ *
      ofK (anchorValues stmt.words i) =
      ∑ k ∈ range 11, ofK (pinWeights.getD k 0 * anchorValues stmt.words k) * (t + pinE k)⁻¹ := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => ofK (pinWeights.getD k 0 * anchorValues stmt.words k) * (t + pinE k)⁻¹) 11]
    refine sum_congr rfl fun i _ => ?_
    have e : ∏ j ∈ univ.erase i, (P.pinPt i - P.pinPt j) = ∏ j ∈ (range 11).erase i, (pinE i + pinE j) := by
      refine Finset.prod_bij (fun j _ => j.val) (fun j hj => ?_) (fun a _ b _ h => Fin.ext h)
        (fun j hj => ⟨⟨j, Finset.mem_range.mp (Finset.mem_of_mem_erase hj)⟩, ?_, rfl⟩)
        (fun j _ => by rw [hpins, hpins, CharTwo.sub_eq_add])
      · exact Finset.mem_erase.mpr ⟨fun h => (Finset.ne_of_mem_erase hj) (Fin.ext h), mem_range.mpr j.2⟩
      · exact Finset.mem_erase.mpr ⟨fun h => (Finset.ne_of_mem_erase hj) (congrArg Fin.val h), mem_univ _⟩
    rw [Compose.Reduce.ofK_mul, ofK_pinWeights i.2, Lagrange.nodalWeight, prod_inv_distrib, e,
      show t - P.pinPt i = t + pinE i by rw [hpins, CharTwo.sub_eq_add]]
    ring
  rw [hnodal, add_div, mul_div_cancel_left₀ _ hZ0, hsum, hZ, div_eq_mul_inv, ← prod_inv_distrib, pinnedV]

/-! ## The match -/

/-- **F1's parameters match the statement's constants**, the wiring table being `s₀`. -/
structure Matches (P : _root_.Kc3.Params E) (s₀ : (Fin 24 → Bool) → E) : Prop where
  theta : P.θ = ofK (betaAt 1)
  card : P.T.card = 2 ^ 22
  vCells : ∀ t, P.vCells.eval t = sq^[24] t
  vRows : ∀ t, P.vRows.eval t = rowsAt t
  pins : ∀ k : Fin 11, P.pinPt k = pinE k
  sigma : ∀ t, P.sigmaPoly.eval t = (tablePoly s₀).eval t

/-- **The claims hold of tables only if F1's verifier accepts their polynomials.** -/
theorem accepts_of_claims (P : _root_.Kc3.Params E) {s₀ : (Fin 24 → Bool) → E} (hM : Matches P s₀)
    {stmt : Statement} {α β μ t ρ : E} {v : Fin 3 → E} {next : E} {cl : Claims}
    (h : claimsAt 22 stmt α β μ t ρ (Vector.ofFn v) next = some cl)
    (cW : (Fin 24 → Bool) → E) (cT : (Fin 28 → Bool) → E)
    (hw : mle cW (fun k => cl.witness.point.getD k 0) = cl.witness.value)
    (hs : mle s₀ (fun k => cl.wiring.point.getD k 0) = cl.wiring.value)
    (hc : mle cT (fun k => cl.copy.point.getD k 0) = cl.copy.value) :
    P.Accepts (fun k => ofK (anchorValues stmt.words k)) (witnessOfTable cW) (readTM cT) α β μ t v next ρ := by
  have S := claimsAt_spec h
  have ht2 : ∀ i : Fin 22, 1 + sq^[(i : ℕ) + 2] t ≠ 0 := fun i => S.one_add _ (by omega)
  have ht0 : ∀ i : Fin 24, 1 + sq^[(i : ℕ)] t ≠ 0 := fun i => S.one_add _ i.2
  rw [S.wPoint, S.wValue, witness_mle' cW t ρ _ ht2, div_left_inj' (claimScale_ne_zero ht2)] at hw
  rw [S.sPoint, S.sValue, wiring_claim s₀ t next (fun i => ht0 i)] at hs
  rw [S.cPoint, S.cValue, copy_mle cT t _ _ ey one_add_ey_ne_zero one_add_ey_sq_ne_zero ht0] at hc
  have hconic : _root_.Kc3.Params.conic P.θ t ρ = witnessConic t (QuotientSecurity.sq t) ρ := by
    rw [hM.theta]
    simp only [witnessConic, _root_.Kc3.Params.conic, QuotientSecurity.sq]
  have hz1 : (_root_.Kc3.Params.conic P.θ t ρ).1 / ((_root_.Kc3.Params.conic P.θ t ρ).1 + (_root_.Kc3.Params.conic P.θ t ρ).2) =
      z1Of t ρ := by rw [hconic, z1Of]
  have hZP : P.vPins.eval t ≠ 0 := by
    have : P.vPins.eval t = ∏ k ∈ range 11, (t + pinE k) := by
      unfold _root_.Kc3.Params.vPins
      rw [Polynomial.eval_prod, ← Fin.prod_univ_eq_prod_range (fun k => t + pinE k) 11]
      refine prod_congr rfl fun k _ => ?_
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, hM.pins, CharTwo.sub_eq_add]
    rw [this]; exact prod_ne_zero_iff.mpr fun k hk => S.pins k (mem_range.mp hk)
  have hpin := pinned_eq P hM.pins stmt t (v 0) S.pins
  unfold _root_.Kc3.Params.Accepts
  dsimp only
  rw [hz1, hconic, hM.vCells, hM.vRows]
  refine ⟨?_, (hM.sigma t).trans hs, S.conic, S.copy, S.rows, hZP, ?_⟩
  · -- the witness claim
    rw [hw, Fin.sum_univ_three, hM.theta]
    simp only [witnessWeights, _root_.Kc3.Params.conicWeights, QuotientSecurity.sq, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  · -- the copy claim
    have hq : (P.qPoly (readTM cT)).eval t =
        (limbPoly ey cT false false).eval t + QuotientSecurity.sq^[24] t * t * (limbPoly ey cT true false).eval t := by
      rw [_root_.Kc3.Params.qPoly, _root_.Kc3.Params.zeta, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_mul, Polynomial.eval_X, hM.vCells, readTM_A₀, readTM_A₁]
    have hxh : (P.xhPoly (readTM cT)).eval t =
        (limbPoly ey cT false true).eval t + QuotientSecurity.sq^[24] t * t * (limbPoly ey cT true true).eval t := by
      rw [_root_.Kc3.Params.xhPoly, _root_.Kc3.Params.zeta, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_mul, Polynomial.eval_X, hM.vCells, readTM_B₀, readTM_B₁]
    rw [hq, hxh, hpin]
    have hZ : 1 + QuotientSecurity.sq^[24] t * t ≠ 0 := S.zeta
    have he : 1 + QuotientSecurity.sq^[24] t * t / (1 + QuotientSecurity.sq^[24] t * t) =
        (1 + QuotientSecurity.sq^[24] t * t)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [add_mul, one_mul, div_mul_cancel₀ _ hZ, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [he] at hc
    have hcs : claimScale 0 24 t ≠ 0 := claimScale_ne_zero (first := 0) (m := 24) (t := t) fun i => ht0 i
    have hYY : (1 + ey) * (1 + ey ^ 2) ≠ 0 := mul_ne_zero one_add_ey_ne_zero one_add_ey_sq_ne_zero
    have hf : (1 + QuotientSecurity.sq^[24] t * t)⁻¹ * (((1 + ey) * (1 + ey ^ 2))⁻¹ * (claimScale 0 24 t)⁻¹)
        ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]
      exact ⟨hZ, ⟨one_add_ey_ne_zero, one_add_ey_sq_ne_zero⟩, hcs⟩
    refine mul_right_cancel₀ hf ?_
    simp only [div_eq_mul_inv, mul_inv, _root_.Kc3.gate] at hc ⊢
    linear_combination hc

end PcsBridge.Kc3

/-- info: 'PcsBridge.Kc3.claimsAt_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsBridge.Kc3.claimsAt_spec

/-- info: 'PcsBridge.Kc3.accepts_of_claims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsBridge.Kc3.accepts_of_claims
