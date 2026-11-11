-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The tables' polynomials are
-- `crates/leanvm/rec/src/pi2/prover.rs`'s, π2v4 (`W` committed in the basis `B`, `Q`'s sixteen slots in the novel basis, the
-- setup's `κ`, `κ + σ` in the basis `B`), each claim a point of the whole stack (the EIP draft's PCS claims,
-- `crates/pcs_claim`); the novel basis and its sums are `formal/UniComplete`'s (`AlgC.novP`) and
-- `formal/QuotientSecurity`'s (`tablePoly`).
import RecCompose.Layers
import UniKeccakComplete.K.AlgCBasis
import UniSound.Ids.Cantor

/-!
# π2's tables' layer

`Pi2Tables D C` (`Layers.lean`) from the stacks: what each candidate stands for, and π2's claims on the candidates as
the model's values. Each claim is the multilinear value of its whole stack at its point (`ClaimOn`, `UniSound.mleStk`;
`mleStk_eq`: the `eqBits` sum), the points padded to the stacks' variables (`W` `m`, `Q` `m + 4`, the setup `m + 1` at
π2's `m = 24`).

* **`W`** (`m` variables, the basis `B`): its stack `T` is the witness's column in the basis `B`; its polynomial is
  `w(x) = Σ_i T_i Π_l (s^l(x) if i_l else 1 + s^l(x))` (`wPoly`, degree below `2^m`), which takes the witness's values on
  `V_m` (`wPoly_eval_pointE`: `s^l(ω_x) = ω_{x >> l}`, so it is `basisValue`). Its **true fold values** at `t` are the
  stack's partial evaluation at the high digits `w_r(t), …, w_{m−1}(t)` (`wFold`); the verifier's cells from them are
  the row's cells `w(t + ω_x)`, `x < 2^r` (`cells_wFold`), and `W`'s claim at `(ρ, ρ², …, w_r(t), …)` is their fold at
  `ρ` (`claim_wFold`).
* **`Q`** (`m + 4` variables: the position, two slot bits `b_0, b_1`, two limb bits; slot `b_0 + 2 b_1 + 4 limb`,
  `PI2.md` §2): the plain sixteen-slot stack, every slot the prover's, each slot a polynomial in the novel basis on `m`
  digits (`slotAt`: its value at the digits `w`). For limbs `l < 3` (an element `Σ_l Y^l` of its limbs' slots,
  `limbCoef`): `H = x h` at `(0, 0)` (`hPoly`), `q`'s digits at `(1, 0)`, `(0, 1)` (`q0Poly`, `q1Poly`; `q = q_0 + Z_V
  q_1`, `qPoly`, below `2N`: `twoDigits_eval`), `G` at `(1, 1)` (`gPoly`); at limb code `3` (`K`, `slotCoef`): `P`
  (`pPoly`), `q_P`'s digits (`qp0Poly`, `qp1Poly`, `qpPoly`), `S` (`sPoly`). A claim at `(u, p₀, p₁, ℓ₀, ℓ₁)`,
  `u_l = w_l/(1 + w_l)`, is `Π_l (1 + w_l)⁻¹` times the slots weighed by `eq((p₀, p₁), b) eq((ℓ₀, ℓ₁), l)` (`claim_Q`):
  the identity's at `(u, z₀, z₁, y₀, y₁)` is `s Π_l (1 + w_l)⁻¹` times the slot bits' combination of `H + Y³ P`,
  `q_0 + Y³ q_{P,0}`, `q_1 + Y³ q_{P,1}`, `G + Y³ S` (`claim_quotient`: `y₀ y₁ = s Y³`), the pushes' at
  `(u, ρ, z'₁, 1, 1)` limb code `3` alone (`claim_pushes`); with `Π_l (1 + w_l)⁻¹ = t/w_m` these are `idEq`, `pushEq`.
* **The setup** (`m + 1` variables): its stack is `κ`'s basis-`B` coefficients, then those of `κ + σ`
  (`setupStack_getD`); its claim at `(w_0(t), …, w_{m−1}(t), β)` is `κ(t) + β σ(t)` (`claim_setup`) for the columns'
  basis-`B` polynomials, which take `κ`, `ω_σ` on `V_m` (`wPoly_bCoefficients`).

**`pi2Tables D C Fa hcol : Pi2Tables D C`**, from the circuit's facts (`Pi2Facts`: `SpecOf`, `2^24` positions, rows
of `16`) and one named input, **`Pi2SetupColumns D C`**: the deployment's setup columns `σ`, `κ` (which the setup's
stack commits) are the compiled circuit's (which the PIOP reads) at every setup (proved from `RecDeployment.Real`'s
`SetupFromCompiler`: `pi2SetupColumns_of_real`, `Real.lean`). `pi2Extraction_of_fs`, `pi2Layers_of_fs`: π2's
extraction and layers with it in place of `Pi2Tables`.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol Finset Polynomial
open scoped ENNReal

/-! ## Products and sums over bits -/

/-- `eqBits` as a product over the point's coordinates. -/
theorem eqBits_foldl (i : ℕ) : ∀ (p : List E) (s : ℕ) (acc : E),
    (p.zipIdx s).foldl (fun w pk ↦ w * if i.testBit pk.2 then pk.1 else 1 + pk.1) acc =
      acc * ∏ k ∈ range p.length, (if i.testBit (s + k) then p.getD k 0 else 1 + p.getD k 0)
  | [], _, acc => by simp
  | q :: p, s, acc => by
    rw [List.zipIdx_cons, List.foldl_cons, eqBits_foldl i p (s + 1), List.length_cons,
      Finset.prod_range_succ' (fun k ↦ if i.testBit (s + k) then (q :: p).getD k 0 else 1 + (q :: p).getD k 0)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [mul_assoc, mul_comm (∏ k ∈ range p.length, _)]
    congr 2
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [show s + 1 + k = s + (k + 1) by ring]

/-- **`eqBits` is a product**: `Π_k (p_k if bit k of i else 1 + p_k)`. -/
theorem eqBits_eq_prod (p : List E) (i : ℕ) :
    PcsQuotient.eqBits p i = ∏ k ∈ range p.length, (if i.testBit k then p.getD k 0 else 1 + p.getD k 0) := by
  unfold PcsQuotient.eqBits
  rw [eqBits_foldl i p 0 1, one_mul]
  simp

/-- Bit `l` of `k + 2^a j`, `k < 2^a`. -/
theorem testBit_add_two_pow_mul {a k : ℕ} (hk : k < 2 ^ a) (j l : ℕ) :
    (k + 2 ^ a * j).testBit l = if l < a then k.testBit l else j.testBit (l - a) := by
  rw [add_comm, Nat.testBit_two_pow_mul_add j hk l]

/-- **A sum over `2^(a+b)` indices, split**: `i = k + 2^a j`. -/
theorem sum_range_two_pow_add {M : Type*} [AddCommMonoid M] (a : ℕ) (f : ℕ → M) : ∀ b : ℕ,
    ∑ i ∈ range (2 ^ (a + b)), f i = ∑ k ∈ range (2 ^ a), ∑ j ∈ range (2 ^ b), f (k + 2 ^ a * j)
  | 0 => by simp
  | b + 1 => by
    rw [show a + (b + 1) = (a + b) + 1 by ring, pow_succ, mul_two, Finset.sum_range_add,
      sum_range_two_pow_add a f b, sum_range_two_pow_add a (fun i ↦ f (2 ^ (a + b) + i)) b, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [pow_succ, mul_two, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1
    rw [pow_add]
    ring

/-- **`eqBits` of a concatenation**: `eq(p ++ q, k + 2^|p| j) = eq(p, k) eq(q, j)`, `k < 2^|p|`. -/
theorem eqBits_append (p q : List E) {k : ℕ} (hk : k < 2 ^ p.length) (j : ℕ) :
    PcsQuotient.eqBits (p ++ q) (k + 2 ^ p.length * j) = PcsQuotient.eqBits p k * PcsQuotient.eqBits q j := by
  rw [eqBits_eq_prod, eqBits_eq_prod, eqBits_eq_prod, List.length_append, Finset.prod_range_add]
  congr 1
  · refine Finset.prod_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.mp hl
    rw [testBit_add_two_pow_mul hk, ite_eq_left hl', List.getD_append _ _ _ _ hl']
  · refine Finset.prod_congr rfl fun l _ ↦ ?_
    have hnl : ¬ p.length + l < p.length := by omega
    have hge : p.length ≤ p.length + l := by omega
    rw [testBit_add_two_pow_mul hk, ite_eq_right hnl, Nat.add_sub_cancel_left, List.getD_append_right _ _ _ _ hge,
      Nat.add_sub_cancel_left]

/-! ## `W`: the basis `B` -/

/-- The weight polynomial of index `i` on `m` digits: `Π_l (s^l if i_l else 1 + s^l)`. -/
noncomputable def eqPolyB (m i : ℕ) : E[X] :=
  ∏ l ∈ range m, if i.testBit l then QuotientSecurity.digitPoly l else 1 + QuotientSecurity.digitPoly l

/-- **A column's polynomial in the basis `B`**: `Σ_i T_i Π_l (s^l if i_l else 1 + s^l)`. -/
noncomputable def wPoly (m : ℕ) (T : ℕ → K) : E[X] := ∑ i ∈ range (2 ^ m), C (ofK (T i)) * eqPolyB m i

theorem eqPolyB_eval (m i : ℕ) (x : E) :
    (eqPolyB m i).eval x =
      ∏ l ∈ range m, if i.testBit l then QuotientSecurity.sq^[l] x else 1 + QuotientSecurity.sq^[l] x := by
  unfold eqPolyB
  rw [eval_prod]
  refine Finset.prod_congr rfl fun l _ ↦ ?_
  split_ifs
  · exact QuotientSecurity.digitPoly_eval l x
  · rw [Polynomial.eval_add, Polynomial.eval_one, QuotientSecurity.digitPoly_eval]

theorem wPoly_eval (m : ℕ) (T : ℕ → K) (x : E) :
    (wPoly m T).eval x = ∑ i ∈ range (2 ^ m), ofK (T i) *
      ∏ l ∈ range m, if i.testBit l then QuotientSecurity.sq^[l] x else 1 + QuotientSecurity.sq^[l] x := by
  unfold wPoly
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, eqPolyB_eval]

theorem sum_two_pow_lt : ∀ m : ℕ, ∑ l ∈ range m, 2 ^ l < 2 ^ m
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ, pow_succ]
    have := sum_two_pow_lt m
    omega

theorem natDegree_eqPolyB_le (m i : ℕ) : (eqPolyB m i).natDegree ≤ ∑ l ∈ range m, 2 ^ l := by
  unfold eqPolyB
  refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun l _ ↦ ?_)
  split_ifs
  · exact QuotientSecurity.natDegree_digitPoly_le l
  · exact (natDegree_add_le _ _).trans (by
      rw [natDegree_one, zero_max]; exact QuotientSecurity.natDegree_digitPoly_le l)

/-- **The column's polynomial has degree below `2^m`.** -/
theorem natDegree_wPoly_lt (m : ℕ) (T : ℕ → K) : (wPoly m T).natDegree < 2 ^ m := by
  unfold wPoly
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ fun i _ ↦ ?_) (sum_two_pow_lt m)
  exact (natDegree_C_mul_le _ _).trans (natDegree_eqPolyB_le m i)

/-- **The column's polynomial takes the basis-`B` values on `V_m`**: `w(ω_x) = basisValue T m x`. -/
theorem wPoly_eval_pointE {m : ℕ} (hm : m ≤ 32) (T : ℕ → K) {x : ℕ} (hx : x < 2 ^ m) :
    (wPoly m T).eval (pi2Omega x) =
      ofK (UniStatement.basisValue (Array.ofFn (n := 2 ^ m) fun i ↦ T i.val) m x) := by
  have hx32 : x < 2 ^ 32 := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hm)
  unfold UniStatement.basisValue
  have hlen : ((List.range m).map fun l ↦ UniStatement.point (x >>> l)).length = m := by simp
  rw [UniSound.Ids.mleK_eq_sum _ _ (by rw [Array.size_ofFn, hlen]), hlen, wPoly_eval, UniSound.Ids.ofK_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [UniSound.Ids.ofK_mul, mul_comm (ofK (UniSound.Ids.cubeEqK _ _ _))]
  congr 1
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp [Finset.mem_range.mp hi]
  · unfold UniSound.Ids.cubeEqK
    rw [UniSound.Ids.ofK_prod]
    refine Finset.prod_congr rfl fun l hl ↦ ?_
    have hpl : ((List.range m).map fun l ↦ UniStatement.point (x >>> l)).getD l 0 = UniStatement.point (x >>> l) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (Finset.mem_range.mp hl)]
      rfl
    rw [hpl, sq_iterate_pi2Omega l hx32, pi2Omega_eq]
    split_ifs
    · rfl
    · rw [UniSound.Ids.ofK_add, UniSound.Ids.ofK_one]
      rfl

/-- **`W`'s true fold values at `t`**: the table's partial evaluation at the high digits `w_r(t), …, w_{m−1}(t)`. -/
noncomputable def wFold (m r : ℕ) (T : ℕ → K) (t : E) (k : ℕ) : E :=
  ∑ j ∈ range (2 ^ (m - r)), ofK (T (k + 2 ^ r * j)) *
    ∏ l ∈ range (m - r), if j.testBit l then QuotientSecurity.sq^[r + l] t else 1 + QuotientSecurity.sq^[r + l] t

/-- **The sibling trick**: the verifier's cells from the true fold values are the row's cells, `w(t + ω_x)`,
`x < 2^r ≤ 2^m`. -/
theorem cells_wFold {m r : ℕ} (hrm : r ≤ m) (T : ℕ → K) (t : E) {x : ℕ} (hx : x < 2 ^ r) (hr32 : r ≤ 32) :
    RecPiop.cellsOf r pi2Omega (wFold m r T t) t x = (wPoly m T).eval (t + pi2Omega x) := by
  have hx32 : x < 2 ^ 32 := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hr32)
  have hdig : ∀ l, QuotientSecurity.sq^[l] (t + pi2Omega x) = QuotientSecurity.sq^[l] t + pi2Omega (x >>> l) :=
    fun l ↦ by rw [QuotientSecurity.sq_iterate_add, sq_iterate_pi2Omega l hx32]
  have hhigh : ∀ l, r ≤ l → pi2Omega (x >>> l) = 0 := fun l hl ↦ by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hl)),
      pi2Omega_zero]
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hrm
  rw [wPoly_eval, sum_range_two_pow_add r _ s]
  unfold RecPiop.cellsOf wFold
  simp only [Nat.add_sub_cancel_left]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' := Finset.mem_range.mp hk
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hA : (∏ l ∈ range r, if (k + 2 ^ r * j).testBit l then QuotientSecurity.sq^[l] (t + pi2Omega x)
      else 1 + QuotientSecurity.sq^[l] (t + pi2Omega x)) =
      ∏ l ∈ range r, if k.testBit l then QuotientSecurity.sq^[l] t + pi2Omega (x >>> l)
        else 1 + (QuotientSecurity.sq^[l] t + pi2Omega (x >>> l)) := by
    refine Finset.prod_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.mp hl
    rw [testBit_add_two_pow_mul hk', ite_eq_left hl', hdig]
  have hB : (∏ l ∈ range s, if (k + 2 ^ r * j).testBit (r + l) then QuotientSecurity.sq^[r + l] (t + pi2Omega x)
      else 1 + QuotientSecurity.sq^[r + l] (t + pi2Omega x)) =
      ∏ l ∈ range s, if j.testBit l then QuotientSecurity.sq^[r + l] t else 1 + QuotientSecurity.sq^[r + l] t := by
    refine Finset.prod_congr rfl fun l _ ↦ ?_
    have hnl : ¬ r + l < r := by omega
    rw [testBit_add_two_pow_mul hk', ite_eq_right hnl, Nat.add_sub_cancel_left, hdig, hhigh (r + l) (by omega), add_zero]
  rw [Finset.prod_range_add, hA, hB]
  ring

/-- `ρ` squared `l` times is `ρ^(2^l)`. -/
theorem sqIter_eq_pow (ρ : E) : ∀ l : ℕ, sqIter ρ l = ρ ^ (2 ^ l)
  | 0 => by simp [sqIter]
  | l + 1 => by
    have ih := sqIter_eq_pow ρ l
    unfold sqIter at ih ⊢
    rw [Function.iterate_succ_apply', ih, pow_succ, pow_mul, pow_two]

/-- **`W`'s claim is the true fold values' fold at `ρ`**: the table's multilinear extension at
`(ρ, ρ², …, ρ^(2^(r−1)), w_r(t), …, w_{m−1}(t))` is `foldAt r (wFold m r T t) ρ`. -/
theorem claim_wFold {m r : ℕ} (hrm : r ≤ m) (T : ℕ → K) (t ρ : E) :
    ∑ i ∈ range (2 ^ m), PcsQuotient.eqBits ((List.range r).map (sqIter ρ) ++
        ((digitsList t (m + 1)).drop r).take (m - r)) i * ofK (T i) =
      RecPiop.foldAt r (wFold m r T t) ρ := by
  have hlr : ((List.range r).map (sqIter ρ)).length = r := by simp
  have hhi : ∀ l < m - r, (((digitsList t (m + 1)).drop r).take (m - r)).getD l 0 =
      QuotientSecurity.sq^[r + l] t := fun l hl ↦ by
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hl, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
    exact digitsList_getD t (by omega)
  have hlenhi : (((digitsList t (m + 1)).drop r).take (m - r)).length = m - r := by
    simp [digitsList]; omega
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hrm
  simp only [Nat.add_sub_cancel_left] at hhi hlenhi ⊢
  rw [sum_range_two_pow_add r _ s]
  unfold RecPiop.foldAt wFold
  simp only [Nat.add_sub_cancel_left]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k < 2 ^ ((List.range r).map (sqIter ρ)).length := by rw [hlr]; exact Finset.mem_range.mp hk
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have e := eqBits_append ((List.range r).map (sqIter ρ)) (((digitsList t (r + s + 1)).drop r).take s) hk' j
  rw [hlr] at e
  rw [e]
  have h1 : PcsQuotient.eqBits ((List.range r).map (sqIter ρ)) k = RecPiop.eqPow r ρ k := by
    rw [eqBits_eq_prod, hlr]
    unfold RecPiop.eqPow
    refine Finset.prod_congr rfl fun l hl ↦ ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (Finset.mem_range.mp hl)]
    simp only [Option.map_some, Option.getD_some, sqIter_eq_pow]
  have h2 : PcsQuotient.eqBits (((digitsList t (r + s + 1)).drop r).take s) j =
      ∏ l ∈ range s, if j.testBit l then QuotientSecurity.sq^[r + l] t else 1 + QuotientSecurity.sq^[r + l] t := by
    rw [eqBits_eq_prod, hlenhi]
    refine Finset.prod_congr rfl fun l hl ↦ ?_
    rw [hhi l (Finset.mem_range.mp hl)]
  rw [h1, h2]
  ring

end RecCompose

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol Finset Polynomial
open scoped ENNReal

end RecCompose

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol Finset Polynomial
open scoped ENNReal

/-! ## The extension's coordinates -/

theorem ext_y0 : extension.1.1 = yE * (1 + yE)⁻¹ := rfl
theorem ext_y1 : extension.1.2 = yE * yE * (1 + yE * yE)⁻¹ := rfl

section Gen

variable {F : Type} [Field F] [CharP F 2]

theorem one_add_mul_inv {x : F} (hx : 1 + x ≠ 0) : 1 + x * (1 + x)⁻¹ = (1 + x)⁻¹ := by
  have h : (1 + x) * (1 + x)⁻¹ = 1 := mul_inv_cancel₀ hx
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (-1 : F) * h + x * (1 + x)⁻¹ * h2

/-- A digit's weight at `u = w/(1 + w)`: `(w if b else 1) (1 + w)⁻¹`. -/
theorem digit_weight {w : F} (hw : 1 + w ≠ 0) (b : Bool) :
    (if b then w / (1 + w) else 1 + w / (1 + w)) = (if b then w else 1) * (1 + w)⁻¹ := by
  cases b
  · simp only [Bool.false_eq_true, ite_false, one_mul, div_eq_mul_inv]
    exact one_add_mul_inv hw
  · simp only [ite_true, div_eq_mul_inv]

theorem limbs_sum_gen (Y : F) (h0 : 1 + Y ≠ 0) (h1 : 1 + Y * Y ≠ 0) (f : ℕ → F) :
    (1 + Y * (1 + Y)⁻¹) * (1 + Y * Y * (1 + Y * Y)⁻¹) * f 0 + Y * (1 + Y)⁻¹ * (1 + Y * Y * (1 + Y * Y)⁻¹) * f 1 +
        (1 + Y * (1 + Y)⁻¹) * (Y * Y * (1 + Y * Y)⁻¹) * f 2 =
      ((1 + Y) * (1 + Y * Y))⁻¹ * (f 0 + Y * f 1 + Y ^ 2 * f 2) := by
  have e1 : 1 + Y * Y * (1 + Y * Y)⁻¹ = (1 + Y * Y)⁻¹ := one_add_mul_inv h1
  rw [one_add_mul_inv h0, e1, mul_inv]
  ring

end Gen

theorem eqBits_pair (p q : E) (l : ℕ) :
    PcsQuotient.eqBits [p, q] l = (if l.testBit 0 then p else 1 + p) * (if l.testBit 1 then q else 1 + q) := by
  rw [eqBits_eq_prod]
  simp [Finset.prod_range_succ]

/-- **The limbs' weights at the extension's point** are the scale times `1, Y, Y²` (limb `3` weighs `y₀ y₁`, read
nowhere): `Σ_{l<4} eq((y₀, y₁), l) f_l = s (f_0 + Y f_1 + Y² f_2)` when `f_3 = 0`. -/
theorem limbs_sum (f : ℕ → E) (h3 : f 3 = 0) :
    ∑ l ∈ range 4, PcsQuotient.eqBits [extension.1.1, extension.1.2] l * f l =
      extension.2 * ∑ l ∈ range 3, yE ^ l * f l := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h3, mul_zero, add_zero]
  rw [eqBits_pair _ _ 0, eqBits_pair _ _ 1, eqBits_pair _ _ 2]
  simp only [show (0 : ℕ).testBit 0 = false from rfl, show (0 : ℕ).testBit 1 = false from rfl,
    show (1 : ℕ).testBit 0 = true from rfl, show (1 : ℕ).testBit 1 = false from rfl,
    show (2 : ℕ).testBit 0 = false from rfl, show (2 : ℕ).testBit 1 = true from rfl, ite_true, ite_false,
    Bool.false_eq_true, pow_zero, pow_one, one_mul]
  rw [ext_y0, ext_y1, ext_scale]
  exact limbs_sum_gen yE one_add_yE_ne_zero one_add_yE_sq_ne_zero f

end RecCompose

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol Finset Polynomial
open scoped ENNReal

/-! ### The weights of `Q`'s claims -/

/-- **The first coordinate of a claim's weight**: `Σ_i eq(x :: p, i) g_i = (1 + x) Σ_j eq(p, j) g_{2j} +
x Σ_j eq(p, j) g_{1 + 2j}`. -/
theorem sum_eqBits_cons (x : E) (p : List E) (g : ℕ → E) :
    ∑ i ∈ range (2 ^ (x :: p).length), PcsQuotient.eqBits (x :: p) i * g i =
      (1 + x) * ∑ j ∈ range (2 ^ p.length), PcsQuotient.eqBits p j * g (2 * j) +
        x * ∑ j ∈ range (2 ^ p.length), PcsQuotient.eqBits p j * g (1 + 2 * j) := by
  have hl : (x :: p).length = 1 + p.length := by simp [Nat.add_comm]
  rw [hl, sum_range_two_pow_add 1 _ p.length]
  have e : ∀ k < 2 ^ ([x] : List E).length, ∀ j,
      PcsQuotient.eqBits (x :: p) (k + 2 ^ 1 * j) = PcsQuotient.eqBits [x] k * PcsQuotient.eqBits p j :=
    fun k hk j ↦ eqBits_append [x] p hk j
  simp only [pow_one, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at e ⊢
  have e0 : ∀ j, PcsQuotient.eqBits (x :: p) (2 * j) = (1 + x) * PcsQuotient.eqBits p j := fun j ↦ by
    have := e 0 (by simp) j
    rw [zero_add] at this
    rw [this, eqBits_eq_prod]
    simp
  have e1 : ∀ j, PcsQuotient.eqBits (x :: p) (1 + 2 * j) = x * PcsQuotient.eqBits p j := fun j ↦ by
    rw [e 1 (by simp) j, eqBits_eq_prod]
    simp
  simp only [e0, e1, Finset.mul_sum, mul_assoc]

/-- `Σ_i eq(1^n, i) g_i = g_{2^n − 1}`. -/
theorem sum_eqBits_ones : ∀ (n : ℕ) (g : ℕ → E),
    ∑ i ∈ range (2 ^ n), PcsQuotient.eqBits (List.replicate n 1) i * g i = g (2 ^ n - 1)
  | 0, f => by simp [eqBits_eq_prod]
  | n + 1, f => by
    have h := sum_eqBits_cons 1 (List.replicate n 1) f
    rw [List.length_cons, List.length_replicate] at h
    rw [List.replicate_succ, h, CharTwo.add_self_eq_zero, zero_mul, zero_add, one_mul,
      sum_eqBits_ones n (fun j ↦ f (1 + 2 * j))]
    congr 1
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [pow_succ]
    omega

/-- `Σ_i eq(0^n, i) g_i = g_0`. -/
theorem sum_eqBits_zeros : ∀ (n : ℕ) (g : ℕ → E),
    ∑ i ∈ range (2 ^ n), PcsQuotient.eqBits (List.replicate n 0) i * g i = g 0
  | 0, f => by simp [eqBits_eq_prod]
  | n + 1, f => by
    have h := sum_eqBits_cons 0 (List.replicate n 0) f
    rw [List.length_cons, List.length_replicate] at h
    rw [List.replicate_succ, h, add_zero, one_mul, zero_mul, add_zero, sum_eqBits_zeros n (fun j ↦ f (2 * j)),
      mul_zero]

end RecCompose

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol Finset Polynomial
open scoped ENNReal

/-! ## `Q`: the novel basis (π2v4: sixteen slots `b_0 + 2 b_1 + 4 limb`) -/

/-- **Slot `j`'s value at the novel monomials `w`**: `Σ_{k<N} T(k + 2^m j) Π_{l : k_l} w_l` (the slot's polynomial in the
novel basis on `m` digits, at the point whose digits are `w`). -/
def slotAt (T : ℕ → K) (m j : ℕ) (w : ℕ → E) : E :=
  ∑ k ∈ range (2 ^ m), ofK (T (k + 2 ^ m * j)) * UniKeccakComplete.AlgC.novX m k w

/-- **An element's coefficient** at `k < N` from slot bits `j` (`j < 4`): its limbs in slots `j, j + 4, j + 8`,
`c_0 + Y c_1 + Y² c_2`. -/
def limbCoef (T : ℕ → K) (m j k : ℕ) : E := ∑ l ∈ range 3, yE ^ l * ofK (T (k + 2 ^ m * (j + 4 * l)))

/-- **A slot's coefficient** at `k < N` (limb code `3`: an element of `K`). -/
def slotCoef (T : ℕ → K) (m j k : ℕ) : E := ofK (T (k + 2 ^ m * j))

/-- Two digits' coefficients on `2N` novel indices: `d₀` below `N`, `d₁` above (`d₀ + Z_V d₁`). -/
def twoDigits (d₀ d₁ : ℕ → E) (m pd : ℕ) : E := if pd < 2 ^ m then d₀ pd else d₁ (pd - 2 ^ m)

/-- **`H = x h`** (slots `0, 4, 8`; degree below `N`). -/
noncomputable def hPoly (T : ℕ → K) (m : ℕ) : E[X] := UniKeccakComplete.AlgC.novP m (limbCoef T m 0)

/-- **`q`'s digit `0`** (slots `1, 5, 9`). -/
noncomputable def q0Poly (T : ℕ → K) (m : ℕ) : E[X] := UniKeccakComplete.AlgC.novP m (limbCoef T m 1)

/-- **`q`'s digit `1`** (slots `2, 6, 10`). -/
noncomputable def q1Poly (T : ℕ → K) (m : ℕ) : E[X] := UniKeccakComplete.AlgC.novP m (limbCoef T m 2)

/-- **`q = q_0 + Z_V q_1`** (degree below `2N`). -/
noncomputable def qPoly (T : ℕ → K) (m : ℕ) : E[X] :=
  UniKeccakComplete.AlgC.novP (m + 1) (twoDigits (limbCoef T m 1) (limbCoef T m 2) m)

/-- **`G`** (slots `3, 7, 11`; the honest prover's zero). -/
noncomputable def gPoly (T : ℕ → K) (m : ℕ) : E[X] := UniKeccakComplete.AlgC.novP m (limbCoef T m 3)

/-- **`P`** (slot `12`). -/
noncomputable def pPoly (T : ℕ → K) (m : ℕ) : E[X] := UniKeccakComplete.AlgC.novP m (slotCoef T m 12)

/-- **`q_P`'s digit `0`** (slot `13`). -/
noncomputable def qp0Poly (T : ℕ → K) (m : ℕ) : E[X] := UniKeccakComplete.AlgC.novP m (slotCoef T m 13)

/-- **`q_P`'s digit `1`** (slot `14`). -/
noncomputable def qp1Poly (T : ℕ → K) (m : ℕ) : E[X] := UniKeccakComplete.AlgC.novP m (slotCoef T m 14)

/-- **`q_P = q_{P,0} + Z_V q_{P,1}`** (degree below `2N`). -/
noncomputable def qpPoly (T : ℕ → K) (m : ℕ) : E[X] :=
  UniKeccakComplete.AlgC.novP (m + 1) (twoDigits (slotCoef T m 13) (slotCoef T m 14) m)

/-- **`S`** (slot `15`; the honest prover's zero). -/
noncomputable def sPoly (T : ℕ → K) (m : ℕ) : E[X] := UniKeccakComplete.AlgC.novP m (slotCoef T m 15)

/-! ### Their values at a point -/

/-- The digits `w_l(x) = s^l(x)`. -/
theorem wP_eval_sq (l : ℕ) (x : E) : (UniComplete.Domain.wP l).eval x = QuotientSecurity.sq^[l] x :=
  UniComplete.Domain.wP_eval x l

/-- **A novel-basis polynomial at a point**: `Σ_k d_k Π_{l : k_l} s^l(x)`. -/
theorem novP_eval_sq (m : ℕ) (d : ℕ → E) (x : E) :
    (UniKeccakComplete.AlgC.novP m d).eval x =
      ∑ k ∈ range (2 ^ m), d k * UniKeccakComplete.AlgC.novX m k (fun l ↦ QuotientSecurity.sq^[l] x) := by
  rw [UniKeccakComplete.AlgC.novP_eval]
  simp only [wP_eval_sq]

/-- **An element's polynomial at a point**: `Σ_{l<3} Y^l` times its limbs' slots there. -/
theorem limb_eval (T : ℕ → K) (m j : ℕ) (x : E) :
    (UniKeccakComplete.AlgC.novP m (limbCoef T m j)).eval x =
      ∑ l ∈ range 3, yE ^ l * slotAt T m (j + 4 * l) (fun l ↦ QuotientSecurity.sq^[l] x) := by
  rw [novP_eval_sq]
  unfold limbCoef slotAt
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  ring

/-- **A slot's polynomial at a point** is the slot there. -/
theorem slot_eval (T : ℕ → K) (m j : ℕ) (x : E) :
    (UniKeccakComplete.AlgC.novP m (slotCoef T m j)).eval x = slotAt T m j (fun l ↦ QuotientSecurity.sq^[l] x) := by
  rw [novP_eval_sq]
  rfl

/-- **Two digits at a point**: `d₀(x) + w_m(x) d₁(x)`. -/
theorem twoDigits_eval (d₀ d₁ : ℕ → E) (m : ℕ) (x : E) :
    (UniKeccakComplete.AlgC.novP (m + 1) (twoDigits d₀ d₁ m)).eval x =
      (UniKeccakComplete.AlgC.novP m d₀).eval x +
        QuotientSecurity.sq^[m] x * (UniKeccakComplete.AlgC.novP m d₁).eval x := by
  rw [UniKeccakComplete.AlgC.novP_succ, Polynomial.eval_add, Polynomial.eval_mul, wP_eval_sq,
    UniKeccakComplete.AlgC.novP_congr m (d' := d₀) fun k hk ↦ by simp only [twoDigits, hk, ↓reduceIte],
    UniKeccakComplete.AlgC.novP_congr m (d := fun k ↦ twoDigits d₀ d₁ m (2 ^ m + k)) (d' := d₁) fun k _ ↦ by
      have h' : ¬ (2 ^ m + k < 2 ^ m) := by omega
      simp only [twoDigits, h', ↓reduceIte, Nat.add_sub_cancel_left]]

/-! ### `Q`'s claims -/


/-- **The limbs' weights at the extension's point**, limb `3` included: `s (f_0 + Y f_1 + Y² f_2) + y₀ y₁ f_3`. -/
theorem limbs_sum4 (f : ℕ → E) :
    ∑ l ∈ range 4, PcsQuotient.eqBits [extension.1.1, extension.1.2] l * f l =
      extension.2 * ∑ l ∈ range 3, yE ^ l * f l + extension.1.1 * extension.1.2 * f 3 := by
  have h := limbs_sum (fun l ↦ if l = 3 then 0 else f l) (by simp)
  have e3 : PcsQuotient.eqBits [extension.1.1, extension.1.2] 3 = extension.1.1 * extension.1.2 := by
    rw [eqBits_pair]; simp [show (3 : ℕ).testBit 0 = true from rfl, show (3 : ℕ).testBit 1 = true from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h ⊢
  simp only [show (0 : ℕ) ≠ 3 by decide, show (1 : ℕ) ≠ 3 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false,
    ite_true, mul_zero, add_zero] at h
  rw [e3, h]

/-- The limbs' weights at `(1, 1)`: limb `3` alone. -/
theorem limbs_sum_ones (f : ℕ → E) : ∑ l ∈ range 4, PcsQuotient.eqBits [1, 1] l * f l = f 3 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, eqBits_pair]
  simp [show (0 : ℕ).testBit 0 = false from rfl, show (0 : ℕ).testBit 1 = false from rfl,
    show (1 : ℕ).testBit 0 = true from rfl, show (1 : ℕ).testBit 1 = false from rfl,
    show (2 : ℕ).testBit 0 = false from rfl, show (2 : ℕ).testBit 1 = true from rfl,
    show (3 : ℕ).testBit 0 = true from rfl, show (3 : ℕ).testBit 1 = true from rfl, CharTwo.add_self_eq_zero]

/-- A point's weight at `u_l = w_l/(1 + w_l)`: the novel monomial times `Π_l (1 + w_l)⁻¹`. -/
theorem eqBits_digits {u : List E} {n : ℕ} (hu : u.length = n) {w : ℕ → E} (hw : ∀ l < n, 1 + w l ≠ 0)
    (huw : ∀ l < n, u.getD l 0 = w l / (1 + w l)) (pd : ℕ) :
    PcsQuotient.eqBits u pd = UniKeccakComplete.AlgC.novX n pd w * ∏ l ∈ range n, (1 + w l)⁻¹ := by
  rw [eqBits_eq_prod, hu, UniKeccakComplete.AlgC.novX, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l hl ↦ ?_
  have hl' := Finset.mem_range.mp hl
  rw [huw l hl', digit_weight (hw l hl')]

/-- **A claim on `Q` at `(u, p₀, p₁, ℓ₀, ℓ₁)`**, `u_l = w_l/(1 + w_l)`: `Π_l (1 + w_l)⁻¹` times the slots at `w`,
weighed by their slot bits `eq((p₀, p₁), b)` and limb bits `eq((ℓ₀, ℓ₁), l)` (slot `b + 4 l`). -/
theorem claim_Q {T : ℕ → K} {m : ℕ} {u : List E} (hu : u.length = m) {w : ℕ → E}
    (hw : ∀ l < m, 1 + w l ≠ 0) (huw : ∀ l < m, u.getD l 0 = w l / (1 + w l)) (p₀ p₁ ℓ₀ ℓ₁ : E) :
    ∑ i ∈ range (2 ^ (m + 4)), PcsQuotient.eqBits (u ++ [p₀, p₁, ℓ₀, ℓ₁]) i * ofK (T i) =
      (∏ l ∈ range m, (1 + w l)⁻¹) * ∑ b ∈ range 4, PcsQuotient.eqBits [p₀, p₁] b *
        ∑ l ∈ range 4, PcsQuotient.eqBits [ℓ₀, ℓ₁] l * slotAt T m (b + 4 * l) w := by
  rw [sum_range_two_pow_add m _ 4]
  have hkey : ∀ k ∈ range (2 ^ m), ∀ s, PcsQuotient.eqBits (u ++ [p₀, p₁, ℓ₀, ℓ₁]) (k + 2 ^ m * s) =
      UniKeccakComplete.AlgC.novX m k w * (∏ l ∈ range m, (1 + w l)⁻¹) * PcsQuotient.eqBits [p₀, p₁, ℓ₀, ℓ₁] s := by
    intro k hk s
    have hk' : k < 2 ^ u.length := by rw [hu]; exact Finset.mem_range.mp hk
    have := eqBits_append u [p₀, p₁, ℓ₀, ℓ₁] hk' s
    rw [hu] at this
    rw [this, eqBits_digits hu hw huw k]
  rw [Finset.sum_congr rfl fun k hk ↦ Finset.sum_congr rfl fun s _ ↦ by rw [hkey k hk s], Finset.sum_comm]
  have hin : ∀ s, ∑ k ∈ range (2 ^ m), UniKeccakComplete.AlgC.novX m k w * (∏ l ∈ range m, (1 + w l)⁻¹) *
      PcsQuotient.eqBits [p₀, p₁, ℓ₀, ℓ₁] s * ofK (T (k + 2 ^ m * s)) =
      PcsQuotient.eqBits [p₀, p₁, ℓ₀, ℓ₁] s * ((∏ l ∈ range m, (1 + w l)⁻¹) * slotAt T m s w) := by
    intro s
    unfold slotAt
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  rw [Finset.sum_congr rfl fun s _ ↦ hin s, show (2 : ℕ) ^ 4 = 2 ^ (2 + 2) from rfl, sum_range_two_pow_add 2 _ 2,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  have hb' : b < 2 ^ ([p₀, p₁] : List E).length := Finset.mem_range.mp hb
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  have h : PcsQuotient.eqBits [p₀, p₁, ℓ₀, ℓ₁] (b + 2 ^ 2 * l) =
      PcsQuotient.eqBits [p₀, p₁] b * PcsQuotient.eqBits [ℓ₀, ℓ₁] l := eqBits_append [p₀, p₁] [ℓ₀, ℓ₁] hb' l
  rw [h, show (2 : ℕ) ^ 2 = 4 from rfl]
  ring

/-- `y₀ y₁ = s Y³`: limb code `3`'s weight at the extension's point. -/
theorem ext_y0y1 : extension.1.1 * extension.1.2 = extension.2 * yCubeE := by
  rw [ext_y0, ext_y1, ext_scale, mul_inv]
  unfold yCubeE
  ring

/-- **The limbs' weights at the extension's point**: `s (f_0 + Y f_1 + Y² f_2 + Y³ f_3)`. -/
theorem limbs_ext (f : ℕ → E) :
    ∑ l ∈ range 4, PcsQuotient.eqBits [extension.1.1, extension.1.2] l * f l =
      extension.2 * (∑ l ∈ range 3, yE ^ l * f l + yCubeE * f 3) := by
  rw [limbs_sum4, ext_y0y1]
  ring

theorem testBit_00 : (0 : ℕ).testBit 0 = false := rfl
theorem testBit_01 : (0 : ℕ).testBit 1 = false := rfl
theorem testBit_10 : (1 : ℕ).testBit 0 = true := rfl
theorem testBit_11 : (1 : ℕ).testBit 1 = false := rfl
theorem testBit_20 : (2 : ℕ).testBit 0 = false := rfl
theorem testBit_21 : (2 : ℕ).testBit 1 = true := rfl
theorem testBit_30 : (3 : ℕ).testBit 0 = true := rfl
theorem testBit_31 : (3 : ℕ).testBit 1 = true := rfl

/-- **`Q`'s identity claim** at `(u, z₀, z₁, y₀, y₁)`: `Π_l (1 + w_l)⁻¹ s` times the slot bits' combination of
`H + Y³ P`, `q_0 + Y³ q_{P,0}`, `q_1 + Y³ q_{P,1}`, `G + Y³ S` (each element `Σ_{l<3} Y^l` its limbs' slots). -/
theorem claim_quotient {T : ℕ → K} {m : ℕ} {u : List E} (hu : u.length = m) {w : ℕ → E}
    (hw : ∀ l < m, 1 + w l ≠ 0) (huw : ∀ l < m, u.getD l 0 = w l / (1 + w l)) (z₀ z₁ : E) :
    ∑ i ∈ range (2 ^ (m + 4)), PcsQuotient.eqBits (u ++ [z₀, z₁, extension.1.1, extension.1.2]) i * ofK (T i) =
      (∏ l ∈ range m, (1 + w l)⁻¹) * extension.2 *
        ((1 + z₀) * (1 + z₁) * (∑ l ∈ range 3, yE ^ l * slotAt T m (0 + 4 * l) w + yCubeE * slotAt T m 12 w) +
          z₀ * (1 + z₁) * (∑ l ∈ range 3, yE ^ l * slotAt T m (1 + 4 * l) w + yCubeE * slotAt T m 13 w) +
          (1 + z₀) * z₁ * (∑ l ∈ range 3, yE ^ l * slotAt T m (2 + 4 * l) w + yCubeE * slotAt T m 14 w) +
          z₀ * z₁ * (∑ l ∈ range 3, yE ^ l * slotAt T m (3 + 4 * l) w + yCubeE * slotAt T m 15 w)) := by
  rw [claim_Q hu hw huw]
  simp only [limbs_ext]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, eqBits_pair, testBit_00, testBit_01,
    testBit_10, testBit_11, testBit_20, testBit_21, testBit_30, testBit_31, ite_true, ite_false, Bool.false_eq_true,
    Nat.reduceAdd, Nat.reduceMul]
  ring

/-- **`Q`'s pushes' claim** at `(u, ρ, z, 1, 1)`: limb code `3` alone, `Π_l (1 + w_l)⁻¹` times the slot bits'
combination of `P`, `q_{P,0}`, `q_{P,1}`, `S`. -/
theorem claim_pushes {T : ℕ → K} {m : ℕ} {u : List E} (hu : u.length = m) {w : ℕ → E}
    (hw : ∀ l < m, 1 + w l ≠ 0) (huw : ∀ l < m, u.getD l 0 = w l / (1 + w l)) (ρ z : E) :
    ∑ i ∈ range (2 ^ (m + 4)), PcsQuotient.eqBits (u ++ [ρ, z, 1, 1]) i * ofK (T i) =
      (∏ l ∈ range m, (1 + w l)⁻¹) *
        ((1 + ρ) * (1 + z) * slotAt T m 12 w + ρ * (1 + z) * slotAt T m 13 w + (1 + ρ) * z * slotAt T m 14 w +
          ρ * z * slotAt T m 15 w) := by
  rw [claim_Q hu hw huw]
  simp only [limbs_sum_ones]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, eqBits_pair, testBit_00, testBit_01,
    testBit_10, testBit_11, testBit_20, testBit_21, testBit_30, testBit_31, ite_true, ite_false, Bool.false_eq_true,
    Nat.reduceAdd, Nat.reduceMul]

end RecCompose


namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol Finset Polynomial
open scoped ENNReal

/-! ## The setup: the basis `B` -/

/-- **The basis-`B` column's polynomial takes the column's values**: `wPoly m (bCoefficients m v)` at `ω_i` is `v_i`
(`m ≤ 28`: UniComplete's `evalB_bCoefficients`, `pEval_colPolyK_pointE`). -/
theorem wPoly_bCoefficients {m : ℕ} (hm : m ≤ 28) (v : Array K) (hv : v.size = 2 ^ m) {i : ℕ} (hi : i < 2 ^ m) :
    (wPoly m fun j ↦ (UniStatement.bCoefficients m v).getD j 0).eval (pi2Omega i) = ofK (v.getD i 0) := by
  rw [← UniKeccakComplete.AlgC.pEval_colPolyK_pointE hm v hv hi, pi2Omega_eq,
    ← UniKeccakComplete.AlgC.evalB_bCoefficients m m v hv le_rfl, wPoly_eval]
  unfold UniComplete.evalB
  have hlen := UniKeccakComplete.AlgC.length_take_digits (UniStatement.pointE i) (le_refl m)
  rw [UniKeccakComplete.AlgC.mle_eq_sum _ _ (by rw [hlen, Array.size_map, UniKeccakComplete.AlgC.bCoefficients_size, hv]), hlen]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [UniKeccakComplete.AlgC.getD_map_ofK]
  congr 1
  refine Finset.prod_congr rfl fun l hl ↦ ?_
  rw [UniKeccakComplete.AlgC.take_digits_getD _ (le_refl m) (Finset.mem_range.mp hl), wP_eval_sq]

end RecCompose

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol Finset Polynomial
open scoped ENNReal

theorem wPoly_congr {m : ℕ} {T T' : ℕ → K} (h : ∀ i < 2 ^ m, T i = T' i) : wPoly m T = wPoly m T' :=
  Finset.sum_congr rfl fun i hi ↦ by rw [h i (Finset.mem_range.mp hi)]

/-- **The setup's claim** at `(w_0(t), …, w_{m−1}(t), β)`: `κ(t) + β σ(t)` for the table's first half and the sum
of its halves. -/
theorem claim_setup (T : ℕ → K) (m : ℕ) (t β : E) :
    ∑ i ∈ range (2 ^ (m + 1)), PcsQuotient.eqBits ((digitsList t (m + 1)).take m ++ [β]) i * ofK (T i) =
      (wPoly m T).eval t + β * (wPoly m fun k ↦ T k + T (k + 2 ^ m)).eval t := by
  have hlen : ((digitsList t (m + 1)).take m).length = m := by simp [digitsList]
  rw [sum_range_two_pow_add m _ 1, wPoly_eval, wPoly_eval, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k < 2 ^ ((digitsList t (m + 1)).take m).length := by rw [hlen]; exact Finset.mem_range.mp hk
  have e : ∀ b, PcsQuotient.eqBits ((digitsList t (m + 1)).take m ++ [β]) (k + 2 ^ m * b) =
      PcsQuotient.eqBits ((digitsList t (m + 1)).take m) k * PcsQuotient.eqBits [β] b := fun b ↦ by
    have := eqBits_append ((digitsList t (m + 1)).take m) [β] hk' b
    rw [hlen] at this
    exact this
  have hw : PcsQuotient.eqBits ((digitsList t (m + 1)).take m) k =
      ∏ l ∈ range m, if k.testBit l then QuotientSecurity.sq^[l] t else 1 + QuotientSecurity.sq^[l] t := by
    rw [eqBits_eq_prod, hlen]
    refine Finset.prod_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.mp hl
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hl', ← List.getD_eq_getElem?_getD,
      digitsList_getD t (by omega)]
  simp only [pow_one, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, e, hw, mul_zero, add_zero, mul_one]
  rw [eqBits_eq_prod, eqBits_eq_prod]
  simp only [List.length_cons, List.length_nil, Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  simp only [List.getD_cons_zero, show (0 : ℕ).testBit 0 = false from rfl, show (1 : ℕ).testBit 0 = true from rfl,
    ite_true, Bool.false_eq_true, ite_false, UniSound.Ids.ofK_add]
  ring

/-- The setup stack's halves: `κ`'s basis-`B` coefficients, then those of `κ + σ`. -/
theorem setupStack_getD (c : Pi2Circuit) {k : ℕ} (hk : k < 2 ^ c.circuit.logN) :
    c.setupStack.getD k 0 = (UniStatement.bCoefficients c.circuit.logN
        (Array.ofFn (n := 2 ^ c.circuit.logN) fun i ↦ c.kappa i.val)).getD k 0 ∧
      c.setupStack.getD (k + 2 ^ c.circuit.logN) 0 = (UniStatement.bCoefficients c.circuit.logN
          (Array.ofFn (n := 2 ^ c.circuit.logN) fun i ↦ c.kappa i.val)).getD k 0 +
        (UniStatement.bCoefficients c.circuit.logN
          (Array.ofFn (n := 2 ^ c.circuit.logN) fun i ↦ UniStatement.point (c.sigma i.val))).getD k 0 := by
  have hs : (UniStatement.bCoefficients c.circuit.logN
      (Array.ofFn (n := 2 ^ c.circuit.logN) fun i ↦ c.kappa i.val)).size = 2 ^ c.circuit.logN := by
    rw [UniKeccakComplete.AlgC.bCoefficients_size, Array.size_ofFn]
  unfold Pi2Circuit.setupStack
  simp only
  constructor
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_left (by rw [hs]; exact hk), ← Array.getD_eq_getD_getElem?]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_right (by rw [hs]; omega), hs, Nat.add_sub_cancel,
      Array.getElem?_ofFn]
    simp [hk]

end RecCompose

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol Finset Polynomial
open scoped ENNReal

/-! ## The tables' layer, assembled -/

section Gen

variable {F : Type} [Field F] [CharP F 2]

theorem prod_inv_ne_zero_gen {n : ℕ} {f : ℕ → F} (h : ∀ l < n, f l ≠ 0) : ∏ l ∈ range n, (f l)⁻¹ ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun l hl ↦ inv_ne_zero (h l (Finset.mem_range.mp hl))

/-- `1 + w_l(t) ≠ 0` below a nonzero digit: `w_{l+1} = w_l (1 + w_l)`. -/
theorem one_add_digit_ne_zero {t : F} {n : ℕ} (h : QuotientSecurity.sq^[n] t ≠ 0) {l : ℕ} (hl : l < n) :
    1 + QuotientSecurity.sq^[l] t ≠ 0 := by
  have := digit_ne_zero_of_le (l := l + 1) (by omega) h
  rw [Function.iterate_succ_apply', sq_eq_mul] at this
  exact right_ne_zero_of_mul this

end Gen

/-- **The deployment's setup columns are the compiled circuit's**, at every setup: `κ` and `σ` of `D.circuitAt roots.pi1`
(which the setup's table commits) are `C.G roots`'s (which the PIOP reads). It follows from `RecDeployment.Real`
(`pi2SetupColumns_of_real`, `Real.lean`): `SetupFromCompiler` says the deployment's `σ`, `κ` are the Lean compiler's on
π1-rec4's graph at every setup commitment, and at π1's reference commitment `Real` pins them by the circuit's digest and
the setup's root (the Rust's; `DigestChecked`, `SetupRootChecked`, evaluated by `rec-real-check`). -/
def Pi2SetupColumns (D : RecDeployment) (C : Pi2Circuits D) : Prop :=
  ∀ (roots : RecSetupRoots) (i : ℕ), i < 2 ^ (C.G roots).logN →
    ofK ((D.circuitAt roots.pi1).kappa i) = (C.G roots).kappa i ∧
      (D.circuitAt roots.pi1).sigma i = (C.G roots).sigma i

section Model

variable {D : RecDeployment} {C : Pi2Circuits D} (Fa : Pi2Facts D C) (roots : RecSetupRoots)

theorem view_logN (Fa : Pi2Facts D C) (roots : RecSetupRoots) : (D.circuitAt roots.pi1).circuit.logN = (C.G roots).logN := (Fa.spec roots).logN

theorem view_logRow (Fa : Pi2Facts D C) (roots : RecSetupRoots) : (D.circuitAt roots.pi1).circuit.logRow = (C.G roots).logW := (Fa.spec roots).logRow

theorem view_logN24 (Fa : Pi2Facts D C) (roots : RecSetupRoots) : (D.circuitAt roots.pi1).circuit.logN = 24 := (view_logN Fa roots).trans (Fa.logN roots)

theorem view_logRow4 (Fa : Pi2Facts D C) (roots : RecSetupRoots) : (D.circuitAt roots.pi1).circuit.logRow = 4 := (view_logRow Fa roots).trans (Fa.logW roots)

theorem pow_view_N (Fa : Pi2Facts D C) (roots : RecSetupRoots) :
    2 ^ (D.circuitAt roots.pi1).circuit.logN = (C.G roots).N := by
  rw [view_logN Fa roots]; rfl

theorem pow_view_N2 (Fa : Pi2Facts D C) (roots : RecSetupRoots) :
    2 ^ ((D.circuitAt roots.pi1).circuit.logN + 1) = 2 * (C.G roots).N := by
  rw [pow_succ, pow_view_N Fa roots]; ring

/-- `W`'s table: the stack's words (its leading `N`, `w`'s basis-`B` coefficients). -/
def wTab (_D : RecDeployment) (_roots : RecSetupRoots) (c : Stk) (i : ℕ) : K := c i

/-- `κ`'s basis-`B` coefficients (the setup table's first half). -/
def kappaB (D : RecDeployment) (roots : RecSetupRoots) : Array K :=
  UniStatement.bCoefficients (D.circuitAt roots.pi1).circuit.logN
    (Array.ofFn (n := 2 ^ (D.circuitAt roots.pi1).circuit.logN) fun i ↦ (D.circuitAt roots.pi1).kappa i.val)

/-- `σ`'s points' basis-`B` coefficients (the setup table's halves' sum). -/
def sigmaB (D : RecDeployment) (roots : RecSetupRoots) : Array K :=
  UniStatement.bCoefficients (D.circuitAt roots.pi1).circuit.logN
    (Array.ofFn (n := 2 ^ (D.circuitAt roots.pi1).circuit.logN) fun i ↦
      UniStatement.point ((D.circuitAt roots.pi1).sigma i.val))

/-- **The setup's polynomials**: `κ`'s and `σ`'s basis-`B` polynomials, which take `C.G roots`'s `κ` and `ω_σ` on
`V_m` (`Pi2SetupColumns`). -/
noncomputable def pi2SetupPolys (hcol : Pi2SetupColumns D C) : RecPiop.SetupPolys (C.G roots) pi2Omega where
  σP := wPoly (D.circuitAt roots.pi1).circuit.logN fun i ↦ (sigmaB D roots).getD i 0
  κP := wPoly (D.circuitAt roots.pi1).circuit.logN fun i ↦ (kappaB D roots).getD i 0
  σ_deg := (natDegree_wPoly_lt _ _).trans_eq (pow_view_N Fa roots)
  κ_deg := (natDegree_wPoly_lt _ _).trans_eq (pow_view_N Fa roots)
  σ_eval i hi := by
    have hi' : i < 2 ^ (D.circuitAt roots.pi1).circuit.logN := by rw [view_logN Fa roots]; exact hi
    unfold sigmaB
    rw [wPoly_bCoefficients (by rw [view_logN24 Fa roots]; norm_num) _ (by rw [Array.size_ofFn]) hi',
      ← (hcol roots i hi).2, pi2Omega_eq]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp [hi', UniStatement.pointE]
  κ_eval i hi := by
    have hi' : i < 2 ^ (D.circuitAt roots.pi1).circuit.logN := by rw [view_logN Fa roots]; exact hi
    unfold kappaB
    rw [wPoly_bCoefficients (by rw [view_logN24 Fa roots]; norm_num) _ (by rw [Array.size_ofFn]) hi',
      ← (hcol roots i hi).1]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp [hi']

/-- **What the candidates stand for** at a setup: `W`'s basis-`B` polynomial and its true fold values, `Q`'s slots
(`H`, `q`, `G`, `P`, `q_P`, `S`) in the novel basis, the setup's polynomials, the ports' `phiPoly`, the identity claim's
`Y³`. -/
noncomputable def pi2Model (hcol : Pi2SetupColumns D C) : RecPiop.Model (C.G roots) pi2Omega Stk where
  setup := pi2SetupPolys Fa roots hcol
  wP c := wPoly (D.circuitAt roots.pi1).circuit.logN (wTab D roots c)
  wP_deg c := (natDegree_wPoly_lt _ _).trans_eq (pow_view_N Fa roots)
  hP c := hPoly c (D.circuitAt roots.pi1).circuit.logN
  hP_deg c := (UniKeccakComplete.AlgC.novP_natDegree_lt _ _).trans_eq (pow_view_N Fa roots)
  qP c := qPoly c (D.circuitAt roots.pi1).circuit.logN
  qP_deg c := (UniKeccakComplete.AlgC.novP_natDegree_lt _ _).trans_eq (pow_view_N2 Fa roots)
  gP c := gPoly c (D.circuitAt roots.pi1).circuit.logN
  gP_deg c := (UniKeccakComplete.AlgC.novP_natDegree_lt _ _).trans_eq (pow_view_N Fa roots)
  pP c := pPoly c (D.circuitAt roots.pi1).circuit.logN
  pP_deg c := (UniKeccakComplete.AlgC.novP_natDegree_lt _ _).trans_eq (pow_view_N Fa roots)
  qPP c := qpPoly c (D.circuitAt roots.pi1).circuit.logN
  qPP_deg c := (UniKeccakComplete.AlgC.novP_natDegree_lt _ _).trans_eq (pow_view_N2 Fa roots)
  sP c := sPoly c (D.circuitAt roots.pi1).circuit.logN
  sP_deg c := (UniKeccakComplete.AlgC.novP_natDegree_lt _ _).trans_eq (pow_view_N Fa roots)
  phi pub γ := phiPoly (C.G roots) UniComplete.Domain.basisE pub γ
  phi_deg pub γ k := natDegree_phiPoly_lt (Fa.valid roots) pub γ k
  phi_eval pub γ j hj := phiPoly_eval_port (Fa.valid roots) (Fa.spec roots).hn pub γ hj
  idC := (Spec.of (D.circuitAt roots.pi1).circuit).core.yCube
  fold c t := wFold (D.circuitAt roots.pi1).circuit.logN (D.circuitAt roots.pi1).circuit.logRow (wTab D roots c) t
  cells_fold c t x hx := by
    have hx' : x < 2 ^ (D.circuitAt roots.pi1).circuit.logRow := by
      rw [view_logRow Fa roots]; exact hx
    have h := cells_wFold (m := (D.circuitAt roots.pi1).circuit.logN)
      (by rw [view_logRow4 Fa roots, view_logN24 Fa roots]; norm_num) (wTab D roots c) t hx'
      (by rw [view_logRow4 Fa roots]; norm_num)
    have e : (C.G roots).logW = (D.circuitAt roots.pi1).circuit.logRow := (view_logRow Fa roots).symm
    exact (congrArg (fun r ↦ RecPiop.cellsOf r pi2Omega (wFold (D.circuitAt roots.pi1).circuit.logN
      (D.circuitAt roots.pi1).circuit.logRow (wTab D roots c) t) t x) e).trans h

end Model

end RecCompose

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol Finset Polynomial
open scoped ENNReal

/-! ### The run's points and values, by definition -/

theorem padded_eq {F : Type} [Field F] {p : List F} {n : ℕ} (h : p.length = n) : padded p n = p := by
  unfold padded
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

section Run

variable {F : Type} [Field F] (S : CoreSpec F) (inp : Inputs F)

theorem run_quotientPoint : (S.run inp).quotientPoint =
    padded ((S.run inp).uList ++ [(S.run inp).z0, (S.run inp).z1, S.y0, S.y1]) (stackVars S.logN).2.1 := rfl
theorem run_pushesPoint : (S.run inp).pushesPoint =
    padded ((S.run inp).uList ++ [inp.ρ, (S.run inp).zp1, 1, 1]) (stackVars S.logN).2.1 := rfl
theorem run_setupPoint : (S.run inp).setupPoint =
    padded ((digitsList inp.t (S.logN + 1)).take S.logN ++ [inp.β]) (stackVars S.logN).2.2 := rfl
theorem run_witnessPoint : (S.run inp).witnessPoint =
    padded ((List.range S.logRow).map (sqIter inp.ρ) ++ ((digitsList inp.t (S.logN + 1)).drop S.logRow).take
      (S.logN - S.logRow)) (stackVars S.logN).1 := rfl
theorem run_uList_length : (S.run inp).uList.length = S.logN := by
  show ((List.range S.logN).map _).length = _
  simp

end Run

theorem spec_core_logN (c : Circuit) : (Spec.of c).core.logN = c.logN := rfl
theorem spec_core_logRow (c : Circuit) : (Spec.of c).core.logRow = c.logRow := rfl
theorem spec_core_y0 (c : Circuit) : (Spec.of c).core.y0 = extension.1.1 := rfl
theorem spec_core_y1 (c : Circuit) : (Spec.of c).core.y1 = extension.1.2 := rfl
theorem spec_core_scale (c : Circuit) : (Spec.of c).core.scale = extension.2 := rfl
theorem spec_core_yCube (c : Circuit) : (Spec.of c).core.yCube = yCubeE := rfl

/-- **A PCS claim's multilinear value as the `eqBits` sum** (characteristic two: `1 + p + 1 = p`), on a point of the
stack's variables. -/
theorem mleStk_eq (c : Stk) {p : List E} {n : ℕ} (hp : p.length = n) :
    UniSound.mleStk c n p = ∑ i ∈ range (2 ^ n), PcsQuotient.eqBits p i * ofK (c i) := by
  unfold UniSound.mleStk
  rw [← Finset.sum_range (fun i ↦ UniSound.cubeEq p n i * ofK (c i))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [eqBits_eq_prod, hp]
  congr 1
  unfold UniSound.cubeEq
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  split_ifs
  · rw [add_comm (1 : E), add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · rw [add_zero]

/-- **π2's tables' layer**: the model `pi2Model` and its link with the claims, from the circuit's facts and the setup's
columns. -/
noncomputable def pi2Tables (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hcol : Pi2SetupColumns D C) : Pi2Tables D C where
  model roots := pi2Model Fa roots hcol
  phi_eq _ _ _ := rfl
  idC_eq _ := rfl
  witness_eval roots c i hi := by
    have hi' : i < 2 ^ (D.circuitAt roots.pi1).circuit.logN := by rw [pow_view_N Fa roots]; exact hi
    exact wPoly_eval_pointE (by rw [view_logN24 Fa roots]; norm_num) (wTab D roots c) hi'
  claims roots cW cQ inp hall hcl := by
    obtain ⟨hW, hQ1, hQ2, hS3⟩ := hcl
    have hS := Fa.spec roots
    have hm := view_logN Fa roots
    have hm24 := view_logN24 Fa roots
    have hr4 := view_logRow4 Fa roots
    set m := (D.circuitAt roots.pi1).circuit.logN with hmdef
    set S := (Spec.of (D.circuitAt roots.pi1).circuit).core with hSdef
    have hSm : S.logN = m := spec_core_logN _
    have hSr : S.logRow = (D.circuitAt roots.pi1).circuit.logRow := spec_core_logRow _
    have hm20 : 20 ≤ m := by omega
    have hqv : (stackVars m).2.1 = m + 4 := by simp only [stackVars, hm20, ite_true]; omega
    -- the digits
    have hT : QuotientSecurity.sq^[(C.G roots).logN] inp.t ≠ 0 :=
      ((all_ne_zero_iff hS (Fa.valid roots) inp).mp hall).1
    rw [← hm] at hT
    have hw : ∀ l < m, 1 + QuotientSecurity.sq^[l] inp.t ≠ 0 := fun l hl ↦ one_add_digit_ne_zero hT hl
    have huw : ∀ l < m, (S.run inp).uList.getD l 0 =
        QuotientSecurity.sq^[l] inp.t / (1 + QuotientSecurity.sq^[l] inp.t) := fun l hl ↦
      run_u hS inp hall (by rw [← hm]; exact hl)
    have hu : (S.run inp).uList.length = m := by rw [run_uList_length, hSm]
    have hscale : inp.t * (QuotientSecurity.sq^[m] inp.t)⁻¹ =
        ∏ l ∈ range m, (1 + QuotientSecurity.sq^[l] inp.t)⁻¹ := digitsScale_eq hT
    have hsc : S.scale = extension.2 := spec_core_scale _
    have hyc : S.yCube = yCubeE := spec_core_yCube _
    have hwm : QuotientSecurity.sq^[(C.G roots).logN] inp.t = QuotientSecurity.sq^[m] inp.t := by rw [hm]
    refine ⟨(q0Poly cQ m).eval inp.t, (q1Poly cQ m).eval inp.t, (qp0Poly cQ m).eval inp.t,
      (qp1Poly cQ m).eval inp.t, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- `q = q_0 + Z_V q_1`
      show (qPoly cQ m).eval inp.t = _
      rw [hwm]
      exact twoDigits_eval _ _ m inp.t
    · -- `q_P = q_{P,0} + Z_V q_{P,1}`
      show (qpPoly cQ m).eval inp.t = _
      rw [hwm]
      exact twoDigits_eval _ _ m inp.t
    · -- `Q`'s identity claim
      unfold ClaimOn at hQ1
      dsimp only at hQ1
      rw [run_quotientPoint, hSm, hqv, padded_eq (by simp [hu]), spec_core_y0, spec_core_y1,
        mleStk_eq _ (by simp [hu]), claim_quotient (T := cQ) hu hw huw] at hQ1
      unfold idEq
      show (S.run inp).quotientValue = S.scale * (inp.t * (QuotientSecurity.sq^[(C.G roots).logN] inp.t)⁻¹) *
        ((1 + (S.run inp).z0) * (1 + (S.run inp).z1) * (hPoly cQ m).eval inp.t +
          (S.run inp).z0 * (1 + (S.run inp).z1) * (q0Poly cQ m).eval inp.t +
          (1 + (S.run inp).z0) * (S.run inp).z1 * (q1Poly cQ m).eval inp.t +
          (S.run inp).z0 * (S.run inp).z1 * (gPoly cQ m).eval inp.t +
          S.yCube * ((1 + (S.run inp).z0) * (1 + (S.run inp).z1) * (pPoly cQ m).eval inp.t +
            (S.run inp).z0 * (1 + (S.run inp).z1) * (qp0Poly cQ m).eval inp.t +
            (1 + (S.run inp).z0) * (S.run inp).z1 * (qp1Poly cQ m).eval inp.t +
            (S.run inp).z0 * (S.run inp).z1 * (sPoly cQ m).eval inp.t))
      rw [hwm, hscale, ← hQ1, hsc, hyc]
      unfold hPoly q0Poly q1Poly gPoly pPoly qp0Poly qp1Poly sPoly
      rw [limb_eval, limb_eval, limb_eval, limb_eval, slot_eval, slot_eval, slot_eval, slot_eval]
      ring
    · -- `Q`'s pushes' claim
      unfold ClaimOn at hQ2
      dsimp only at hQ2
      rw [run_pushesPoint, hSm, hqv, padded_eq (by simp [hu]), mleStk_eq _ (by simp [hu]),
        claim_pushes (T := cQ) hu hw huw] at hQ2
      unfold pushEq
      show (S.run inp).pushesValue = inp.t * (QuotientSecurity.sq^[(C.G roots).logN] inp.t)⁻¹ *
        ((1 + inp.ρ) * (1 + (S.run inp).zp1) * (pPoly cQ m).eval inp.t +
          inp.ρ * (1 + (S.run inp).zp1) * (qp0Poly cQ m).eval inp.t +
          (1 + inp.ρ) * (S.run inp).zp1 * (qp1Poly cQ m).eval inp.t + inp.ρ * (S.run inp).zp1 * (sPoly cQ m).eval inp.t)
      rw [hwm, hscale, ← hQ2]
      unfold pPoly qp0Poly qp1Poly sPoly
      rw [slot_eval, slot_eval, slot_eval, slot_eval]
    · -- the setup's claim
      unfold ClaimOn at hS3
      have hsv : (stackVars m).2.2 = m + 1 := by simp only [stackVars, hm20, ite_true]; omega
      rw [run_setupPoint, hSm, hsv, padded_eq (by simp [digitsList]),
        mleStk_eq _ (by simp [digitsList]), claim_setup] at hS3
      have hT0 : ∀ k < 2 ^ m, (D.circuitAt roots.pi1).setupStack.getD k 0 = (kappaB D roots).getD k 0 :=
        fun k hk ↦ (setupStack_getD _ hk).1
      have hT1 : ∀ k < 2 ^ m, (D.circuitAt roots.pi1).setupStack.getD k 0 +
          (D.circuitAt roots.pi1).setupStack.getD (k + 2 ^ m) 0 = (sigmaB D roots).getD k 0 := fun k hk ↦ by
        rw [hT0 k hk, (setupStack_getD _ hk).2]
        show (kappaB D roots).getD k 0 + ((kappaB D roots).getD k 0 + (sigmaB D roots).getD k 0) = _
        rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      rw [wPoly_congr hT0, wPoly_congr hT1] at hS3
      exact hS3.symm
    · -- `W`'s claim
      unfold ClaimOn at hW
      have hwv : (stackVars m).1 = m := by simp only [stackVars, hm20, ite_true]; omega
      rw [run_witnessPoint, hSm, hSr, hwv, padded_eq (by simp [digitsList]; omega),
        mleStk_eq _ (by simp [digitsList]; omega)] at hW
      rw [claim_wFold (by omega) _ inp.t inp.ρ] at hW
      have e : (C.G roots).logW = (D.circuitAt roots.pi1).circuit.logRow := (view_logRow Fa roots).symm
      refine hW.symm.trans ?_
      exact congrArg (fun r ↦ RecPiop.foldAt r (wFold m (D.circuitAt roots.pi1).circuit.logRow
        (wTab D roots cW) inp.t) inp.ρ) e.symm

end RecCompose

/-- info: 'RecCompose.pi2Tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2Tables

namespace RecCompose

open RecStatement

/-- **π2's extraction without the tables' layer**: from the Fiat–Shamir layer, the circuit's facts and the setup's
columns (`pi2Tables` in place of `Pi2Tables`). -/
theorem pi2Extraction_of_fs {D : RecDeployment} (C : Pi2Circuits D) (Fa : Pi2Facts D C) (hcol : Pi2SetupColumns D C)
    (hfs : Pi2FsLayer D) :
    Pi2Extraction D (fun roots input proof w ↦ (C.G roots).Satisfies
      (Fa.pubOf roots (pi2Scalars D roots input proof)) (RecCircuit.emb w)) pi2Bound :=
  pi2Extraction_of_layers C Fa (pi2Tables D C Fa hcol) hfs

/-- **π2's layers without the tables' layer**: `pi2Layers_of` with `pi2Tables`. -/
noncomputable def pi2Layers_of_fs {D : RecDeployment} (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hcol : Pi2SetupColumns D C) (hfs : Pi2FsLayer D) (hcirc : Pi2CircuitAccepts C Fa) : Pi2Layers D pi2Bound :=
  pi2Layers_of C Fa (pi2Tables D C Fa hcol) hfs hcirc

end RecCompose

/-- info: 'RecCompose.pi2Extraction_of_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2Extraction_of_fs

/-- info: 'RecCompose.cells_wFold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.cells_wFold

/-- info: 'RecCompose.claim_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.claim_quotient
