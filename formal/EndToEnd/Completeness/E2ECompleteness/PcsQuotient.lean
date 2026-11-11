-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `E2ECompleteness/ProverQuotient.lean` (the previous prover's quotient table) to
-- the PCS claims' prover (`E2ECompleteness/PcsDefs.lean`: the coefficient tables of the two
-- quotients, the copy quotient's coset input `q0BOf` with the blinding of `h`), against
-- `formal/Completeness`'s honest prover and its blinded message (`E2ECompleteness/PcsHonest.lean`).
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the fields `K`, `E` and their limbs.
import E2ECompleteness.PcsCells
import E2ECompleteness.PcsHonest

/-!
# The prover's coefficient tables hold the honest polynomials

The PCS claims' prover (`PcsDefs.lean`) computes the two quotients pointwise on the coset
`β₂₆ + span(β₀ … β₂₅)` (`qValuesOf`, `qGateValuesOf`) and takes their coefficients there
(`coefficients 26 (betaAt 26)`); the sum's polynomial on the cells (`hValues`, `coefficients 24 0`).
The copy quotient reads the sum's polynomial on the coset with its blinding (`q0BOf`: the
coefficients of `h₀`, then the blinding words at `2^24 + i`), which is `h₀ + Z_cells · b` there
(`b = blindPoly blind`). Here:

* on the coset, the witness values are F1's witness polynomial (`wValues_coset`), the wiring
  values its `sigmaPoly` (`sigmaValues_coset`), `q0BOf` is `h₀ + Z_cells · b` (`q0B_coset`); so
  `qValuesOf` is the blinded copy quotient `q + d d' b` there (`qValuesB_coset`: exact on the
  cells by `¬ BadAB`, `Z_cells` nonzero on the coset), and `qGateValuesOf` the honest gate quotient
  over `K` (`qGateValues_coset`: exact when the cells satisfy the gates, `hgate`; `Z_rows` nonzero on
  the coset);
* **`hHat_table26`**, **`qHatB_table26`**, **`qGateHat_table26`**: the three coefficient tables
  hold `h₀`, the blinded `q` (`honestB`'s) and the gate quotient over `K`.

The cells must satisfy the gates (`hgate`, the relation's first conjunct): otherwise the gate's
quotient computed on the coset is not the polynomial `gatePoly / vRows` F1's `Params.honest` takes.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM.Parameters PcsQuotient.Domain QuotientSecurity

namespace E2ECompleteness.Pcs

namespace ProverQuotient

open ProverTables

/-! ## Helpers -/

theorem cantorUpTo26 (hK : Constants) : Bridge.Ntt.CantorUpTo 26 :=
  Pcs.Ntt.cantorUpTo_of_isCantorBasis hK.cantor (by unfold basisSize; norm_num)

theorem ofK_inv (a : K) : ofK a⁻¹ = (ofK a)⁻¹ := map_inv₀ (algebraMap K E) a

theorem ofK_eval (p : K[X]) (x : K) : ofK (p.eval x) = (p.map (algebraMap K E)).eval (ofK x) := by
  rw [eval_map]
  exact (eval₂_at_apply (p := p) (algebraMap K E) x).symm

theorem size_ofFn26 {α : Type*} (g : Fin (4 * 2 ^ PcsQuotient.cellVars 22) → α) :
    (Array.ofFn g).size = 2 ^ 26 := by
  rw [Array.size_ofFn]
  unfold PcsQuotient.cellVars
  norm_num

/-- `values` on the coset of an array of `K` given entry by entry. -/
theorem values_ofFn_K (hK : Constants) (g : Fin (4 * 2 ^ PcsQuotient.cellVars 22) → K) (a : ℕ → K)
    (ha : ∀ i, g i = a i.val) {p : ℕ} (hp : p < 2 ^ 26) :
    (values (PcsQuotient.cellVars 22 + 2) (betaAt (PcsQuotient.cellVars 22 + 2)) (Array.ofFn g)).getD
        p 0 = (tablePoly (fun b : Fin 26 → Bool => a (Completeness.idx b))).eval (betaAt 26 + point p) := by
  rw [show PcsQuotient.cellVars 22 + 2 = 26 from rfl,
    Pcs.Ntt.values_getD_tablePoly (cantorUpTo26 hK) (by unfold basisSize; norm_num) _ _
      (size_ofFn26 g) hp]
  have hfun : (fun b : Fin 26 → Bool => (Array.ofFn g).getD (Completeness.idx b) 0) =
      fun b => a (Completeness.idx b) := funext fun b => by
    have hb := Completeness.idx_lt b
    rw [getD_ofFn _ _ (by unfold PcsQuotient.cellVars; omega), ha]
  rw [hfun]

/-- `values` on the coset of an array of `E` given entry by entry. -/
theorem values_ofFn_E (hK : Constants) (g : Fin (4 * 2 ^ PcsQuotient.cellVars 22) → E) (a : ℕ → E)
    (ha : ∀ i, g i = a i.val) {p : ℕ} (hp : p < 2 ^ 26) :
    (values (PcsQuotient.cellVars 22 + 2) (betaAt (PcsQuotient.cellVars 22 + 2)) (Array.ofFn g)).getD
        p 0 =
      (tablePoly (fun b : Fin 26 → Bool => a (Completeness.idx b))).eval (ofK (betaAt 26 + point p)) := by
  rw [show PcsQuotient.cellVars 22 + 2 = 26 from rfl,
    values_getD_tablePoly_E (cantorUpTo26 hK) (by unfold basisSize; norm_num) _ _
      (size_ofFn26 g) hp]
  have hfun : (fun b : Fin 26 → Bool => (Array.ofFn g).getD (Completeness.idx b) 0) =
      fun b => a (Completeness.idx b) := funext fun b => by
    have hb := Completeness.idx_lt b
    rw [getD_ofFn _ _ (by unfold PcsQuotient.cellVars; omega), ha]
  rw [hfun]

/-- A role's polynomial at `t` is the witness polynomial at `t` shifted by the role. -/
theorem cellPoly_eval (P : Params E) (g : Fin 4 → E[X]) (c : Fin 4) (t : E) :
    (Params.cellPoly P g c).eval t = (Instance.witnessPoly g).eval (t + shift P.θ c) := by
  unfold Params.cellPoly Instance.witnessPoly
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [P.rowPoly_eval_shift]

theorem shift_zero (θ : E) : shift θ 0 = 0 := rfl

theorem theta_eq (hK : Constants) : Completeness.deployedInstanceE.params.θ = ofK (point 2) := by
  have h := point_two_pow (n := 1) (by unfold basisSize; norm_num)
  rw [pow_one] at h
  rw [Completeness.Instance'.θ_eq, h, betaAt_eq_deployed hK (by norm_num)]
  rfl

theorem point_one (hK : Constants) : point 1 = 1 := by
  rw [show (1 : ℕ) = 2 ^ 0 from rfl, point_two_pow (by unfold basisSize; norm_num)]
  exact hK.cantor.1

theorem point_three (hK : Constants) : point 3 = 1 + point 2 := by
  rw [show (3 : ℕ) = 1 ^^^ 2 from rfl, point_xor, point_one hK]

/-! ## Limbs -/

theorem limb_mul_algebraMap (x : E) (a : K) (e : Fin 3) :
    (x * algebraMap K E a).limb e = x.limb e * a := by
  show (x * ofK a).limb e = _
  rw [← ofLimbs_limb x, ofK_eq_ofLimbs, mul_limbs]
  fin_cases e <;> simp

theorem limb_sum {ι : Type*} (s : Finset ι) (g : ι → E) (e : Fin 3) :
    (∑ b ∈ s, g b).limb e = ∑ b ∈ s, (g b).limb e := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [limb_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, limb_add, ih]

/-- **A limb of a table's polynomial is the polynomial of the table's limbs** (the novel basis
is over `K`). -/
theorem limb_tablePoly {M : ℕ} (c : (Fin M → Bool) → E) (e : Fin 3) :
    Completeness.limbE.limbPoly (tablePoly c) e = tablePoly (fun b => (c b).limb e) := by
  have hN : ∀ b : Fin M → Bool, (∏ k : Fin M, (if b k then digitPoly (k : ℕ) else 1) : E[X]) =
      (∏ k : Fin M, (if b k then digitPoly (k : ℕ) else 1) : K[X]).map (algebraMap K E) := by
    intro b
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    split_ifs
    · exact (digitPoly_map _ _).symm
    · exact (Polynomial.map_one _).symm
  refine Polynomial.ext fun n => ?_
  rw [Completeness.limbE.coeff_limbPoly]
  have hlimb : (if n ≤ (tablePoly c).natDegree then
      Completeness.limbE.limb ((tablePoly c).coeff n) e else 0) = ((tablePoly c).coeff n).limb e := by
    split_ifs with h
    · rfl
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), limb_zero]
  rw [hlimb]
  unfold tablePoly
  simp only [finsetSum_coeff, coeff_C_mul]
  rw [limb_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hN b, coeff_map, limb_mul_algebraMap]

/-- A table holding the polynomial a `tableSupp` holds is that `tableSupp`. -/
theorem tableSupp_eq {M D : ℕ} (pK : K[X]) (c : (Fin M → Bool) → K) (hc : tablePoly c = pK)
    (hD : D ≤ 2 ^ M) (hdeg : pK.natDegree < D) : Completeness.tableSupp M pK D = c :=
  tablePoly_injective ((Completeness.tableSupp_spec hD (Or.inr hdeg)).trans hc.symm)

/-! ## The quotients' entries, for any blocks

Stated for an abstract array of blocks, so that no unification ever looks into `blocksOf`. -/

/-- Entry `p` of `qGateValuesOf`, given its block. -/
theorem qGateValuesOf_getD (wV : Array K) (blocks : Array (Array E × K × Array K)) {p : ℕ}
    (hp : p < 4 * 2 ^ PcsQuotient.cellVars 22) (W : Array E) (cv : K) (R : Array K)
    (hb : blocks.getD (p / 2 ^ PcsQuotient.region) (#[], 0, #[]) = (W, cv, R)) :
    (qGateValuesOf 22 wV blocks).getD p 0 =
      (wV.getD (p ^^^ 3) 0 + wV.getD p 0 + wV.getD (p ^^^ 2) 0 +
        wV.getD (p ^^^ 1) 0 * wV.getD (p ^^^ 2) 0) * R.getD (p % 4) 0 := by
  unfold qGateValuesOf
  rw [getD_ofFn _ _ hp]
  show (match blocks.getD (p / 2 ^ PcsQuotient.region) (#[], 0, #[]) with
    | (_, _, rowInv) =>
      match (wV.getD p 0, wV.getD (p ^^^ 1) 0, wV.getD (p ^^^ 2) 0, wV.getD (p ^^^ 3) 0) with
      | (x, y, cc, v) => (v + x + cc + y * cc) * rowInv.getD (p % 4) 0) = _
  rw [hb]

/-- Entry `p` of `qValuesOf`, given its block. -/
theorem qValuesOf_getD (wV sV : Array K) (q₀ : Array E) (blocks : Array (Array E × K × Array K))
    (α β : E) {p : ℕ} (hp : p < 4 * 2 ^ PcsQuotient.cellVars 22) (W : Array E) (cv : K)
    (R : Array K) (hb : blocks.getD (p / 2 ^ PcsQuotient.region) (#[], 0, #[]) = (W, cv, R)) :
    (qValuesOf 22 wV sV q₀ blocks α β).getD p 0 =
      ((q₀.getD p 0 + (if p % 2 ^ PcsQuotient.region < W.size then
          W.getD (p % 2 ^ PcsQuotient.region) 0 * ofK (wV.getD p 0) else 0)) *
        (α + ofK (wV.getD p 0) + β * ofK (betaAt (PcsQuotient.cellVars 22 + 2) + point p)) *
        (α + ofK (wV.getD p 0) + β * ofK (sV.getD p 0)) +
        (α + ofK (wV.getD p 0) + β * ofK (betaAt (PcsQuotient.cellVars 22 + 2) + point p)) +
        (α + ofK (wV.getD p 0) + β * ofK (sV.getD p 0))) * ofK cv := by
  unfold qValuesOf
  rw [getD_ofFn _ _ hp]
  show (match blocks.getD (p / 2 ^ PcsQuotient.region) (#[], 0, #[]) with
    | (weights, cellVanishing, _) =>
      ((q₀.getD p 0 + (if p % 2 ^ PcsQuotient.region < weights.size then
          weights.getD (p % 2 ^ PcsQuotient.region) 0 * ofK (wV.getD p 0) else 0)) *
        (α + ofK (wV.getD p 0) + β * ofK (betaAt (PcsQuotient.cellVars 22 + 2) + point p)) *
        (α + ofK (wV.getD p 0) + β * ofK (sV.getD p 0)) +
        (α + ofK (wV.getD p 0) + β * ofK (betaAt (PcsQuotient.cellVars 22 + 2) + point p)) +
        (α + ofK (wV.getD p 0) + β * ofK (sV.getD p 0))) * ofK cellVanishing) = _
  rw [hb]

/-! ## The exact divisions, for any parameters -/

/-- **The copy quotient is exact** when no denominator vanishes at a cell (`¬ BadAB`): the
numerator `d d' h₀ + copies` vanishes on the cells (`Params.honest_consistent`'s computation). -/
theorem q_mul_of (P : Params E) (hE : P.Exact) (g : Fin 4 → E[X]) (α β γ : E)
    (hd : ∀ i, α + P.cells g i + β * P.pt i ≠ 0)
    (hd' : ∀ i, α + P.cells g i + β * P.pt (P.σ i) ≠ 0) :
    P.vCells * (Params.honest P g α β γ).q =
      Params.dPoly P g α β * Params.dNextPoly P g α β * (Params.honest P g α β γ).h₀ +
        Params.copyPoly P g α β γ := by
  have hc0 : P.vCells ≠ 0 := by
    rw [hE.cells]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero _
  refine EuclideanDomain.mul_div_cancel' hc0 ?_
  rw [hE.cells]
  refine prod_X_sub_C_dvd P.pt P.pt_injective _ fun i => ?_
  have e1 := hd i
  have e2 := hd' i
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
    Lagrange.eval_interpolate_at_node _ P.pt_injective.injOn (Finset.mem_univ i), Params.copyPoly]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Params.dPoly_eval_pt,
    Params.dNextPoly_eval_pt, Params.cellPoly_zero_eval_pt]
  unfold Params.sumValue
  generalize α + P.cells g i + β * P.pt i = d at e1 ⊢
  generalize α + P.cells g i + β * P.pt (P.σ i) = d' at e2 ⊢
  have : d * d' * (d⁻¹ + d'⁻¹ + (P.pub γ).eval (P.pt i) * P.cells g i)
      = d + d' + (P.pub γ).eval (P.pt i) * P.cells g i * (d * d') := by
    field_simp
    ring
  rw [this]
  exact CharTwo.add_self_eq_zero _

/-- The copy identity's numerator at a point, for any parameters. -/
theorem numer_eval (P : Params E) (g : Fin 4 → E[X]) (α β γ : E) (h : E[X]) (t : E) :
    (Params.dPoly P g α β * Params.dNextPoly P g α β * h + Params.copyPoly P g α β γ).eval t =
      (α + (Instance.witnessPoly g).eval t + β * t) *
          (α + (Instance.witnessPoly g).eval t + β * P.sigmaPoly.eval t) * h.eval t +
        ((α + (Instance.witnessPoly g).eval t + β * t) +
          (α + (Instance.witnessPoly g).eval t + β * P.sigmaPoly.eval t) +
          (P.pub γ).eval t * (Instance.witnessPoly g).eval t *
            ((α + (Instance.witnessPoly g).eval t + β * t) *
              (α + (Instance.witnessPoly g).eval t + β * P.sigmaPoly.eval t))) := by
  have hc : (Params.cellPoly P g 0).eval t = (Instance.witnessPoly g).eval t := by
    rw [cellPoly_eval, show shift P.θ 0 = 0 from rfl, add_zero]
  simp only [Params.copyPoly, Params.dPoly, Params.dNextPoly, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, hc]

/-- **The gate quotient is exact** when the gate vanishes at the rows. -/
theorem qGate_mul_of (P : Params E) (hE : P.Exact) (g : Fin 4 → E[X]) (α β γ : E)
    (hgate : ∀ x : P.T, (Params.gatePoly P g).eval (x : E) = 0) :
    P.vRows * (Params.honest P g α β γ).qGate = Params.gatePoly P g := by
  have hr0 : P.vRows ≠ 0 := by
    rw [hE.rows]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero _
  refine EuclideanDomain.mul_div_cancel' hr0 ?_
  rw [hE.rows]
  exact prod_X_sub_C_dvd (fun x : P.T => (x : E)) Subtype.val_injective _ hgate

/-- **A table holding `lo` below `2^m` and `hi` from `2^m` on**, zero from `2^(m+1)` on, on any
`N ≥ m + 1` digits, holds `lo`'s polynomial plus `digitPoly m` times `hi`'s (`tablePoly_snoc`). -/
theorem tablePoly_split {F : Type*} [Field F] [CharP F 2] (m N : ℕ) (hN : m + 1 ≤ N) (a : ℕ → F)
    (lo : Array F) (hi : ℕ → F) (hlo : ∀ n, n < 2 ^ m → a n = lo.getD n 0)
    (hhi : ∀ n, n < 2 ^ m → a (n + 2 ^ m) = hi n) (hz : ∀ n, 2 ^ (m + 1) ≤ n → a n = 0) :
    tablePoly (fun b : Fin N → Bool => a (Completeness.idx b)) =
      tablePoly (fun b : Fin m → Bool => lo.getD (Completeness.idx b) 0) +
        digitPoly m * tablePoly (fun b : Fin m → Bool => hi (Completeness.idx b)) := by
  rw [tablePoly_pad (M := m + 1) a hz N hN, tablePoly_snoc]
  refine congrArg₂ (· + ·) (congrArg tablePoly (funext fun b => ?_))
    (congrArg (_ * ·) (congrArg tablePoly (funext fun b => ?_)))
  · rw [Completeness.idx_snoc, if_neg Bool.false_ne_true, add_zero]
    exact hlo _ (Completeness.idx_lt b)
  · rw [Completeness.idx_snoc, if_pos rfl]
    exact hhi _ (Completeness.idx_lt b)

/-- The copy quotient's coset input `q0BOf` by entry: the sum's coefficients, then the blinding. -/
def q0BEntry (hHat : Array E) (blind : Fin 3 → Fin PcsQuotient.hBlind → K) (n : ℕ) : E :=
  if n < 2 ^ PcsQuotient.cellVars 22 then hHat.getD n 0 else blindAt blind (n - 2 ^ PcsQuotient.cellVars 22)

/-- The blinded copy quotient, for any parameters. -/
theorem honestB_q (P : Params E) (g : Params.Witness E) (α β γ : E) (b : E[X]) :
    (honestB P g α β γ b).q =
      (Params.honest P g α β γ).q + Params.dPoly P g α β * Params.dNextPoly P g α β * b := rfl

/-! ## The honest values on the coset -/

section Honest

variable (hK : Constants) (f : (Fin (22 + 2) → Bool) → K) (cells : Array K)
  (hcs : cells.size = 2 ^ 24) (hcells : ∀ b, cells.getD (Completeness.idx b) 0 = f b)
  (sigma : Array ℕ) (hss : sigma.size = 2 ^ 24)
  (hsigma : ∀ b, point (sigma.getD (Completeness.idx b) 0) = deployedBasis.point (deployedSigma b))
  (masks : PcsQuotient.Masks)

include hK hcs hcells in
/-- **The witness values on the coset are F1's witness polynomial.** -/
theorem wValues_coset {p : ℕ} (hp : p < 2 ^ 26) :
    ofK ((wValuesOf 22 (coefficients 24 0 cells) (PcsQuotient.maskEntries masks)).getD p 0) =
      (Instance.witnessPoly (gOf f masks)).eval (ofK (betaAt 26 + point p)) := by
  unfold wValuesOf
  rw [values_ofFn_K hK _
    (Completeness.natTable (Completeness.witnessTable deployedBasis f masks)) ?ha hp]
  · rw [tablePoly_pad (M := 22 + 2 + 1) _ (fun n hn => by
        unfold Completeness.natTable
        rw [if_neg (by omega)]) 26 (by norm_num),
      show (fun b : Fin (22 + 2 + 1) → Bool => Completeness.natTable
          (Completeness.witnessTable deployedBasis f masks) (Completeness.idx b)) =
        Completeness.witnessTable deployedBasis f masks from
        funext (Completeness.natTable_idx _),
      ofK_eval, ← Completeness.tablePoly_map, gOf, Completeness.witnessPoly_witnessOfTable_eval]
  · intro i
    exact witness_table hK f cells hcs hcells masks i.val

include hK hss hsigma in
/-- **The wiring values on the coset are F1's `sigmaPoly`.** -/
theorem sigmaValues_coset {p : ℕ} (hp : p < 2 ^ 26) :
    ofK ((sigmaValuesOf 22 (coefficients 24 0 (sigma.map point))).getD p 0) =
      Completeness.deployedInstanceE.params.sigmaPoly.eval (ofK (betaAt 26 + point p)) := by
  unfold sigmaValuesOf
  rw [values_ofFn_K hK _
    (Completeness.natTable (Completeness.wiringTableK deployedBasis deployedSigma)) ?ha hp]
  · rw [tablePoly_pad (M := 22 + 2) _ (fun n hn => by
        unfold Completeness.natTable
        rw [if_neg (by omega)]) 26 (by norm_num),
      show (fun b : Fin (22 + 2) → Bool => Completeness.natTable
          (Completeness.wiringTableK deployedBasis deployedSigma) (Completeness.idx b)) =
        Completeness.wiringTableK deployedBasis deployedSigma from
        funext (Completeness.natTable_idx _),
      ofK_eval, ← Completeness.tablePoly_map,
      Completeness.sigmaPoly_eq_wiringTableK (algebraMap K E) Completeness.deployedInstanceE
        deployedBasis (fun _ => rfl), Completeness.deployedInstanceE_wiring]
  · intro i
    exact (wiring_table hK sigma hss hsigma).2 i.val

include hK hcells hsigma in
/-- The sum's table on `26` digits holds `h₀`. -/
theorem hHat_table26 (α β γ : E) :
    tablePoly (fun b : Fin 26 → Bool =>
        (coefficients 24 0 (hValues 22 cells sigma α β γ)).getD (Completeness.idx b) 0) =
      (Params.honest Completeness.deployedInstanceE.params (gOf f masks) α β γ).h₀ :=
  (tablePoly_pad (M := 24) (fun n => (coefficients 24 0 (hValues 22 cells sigma α β γ)).getD n 0)
    (fun n hn => getD_of_size_le _ _ (by
      rw [Bridge.Ntt.coefficients_size]
      exact (Array.size_ofFn).trans_le hn)) 26 (by norm_num)).trans
    (hHat_table hK f cells hcells sigma hsigma masks α β γ)

include hK hcells hsigma in
/-- **`q0BOf` is `h₀ + Z_cells · b` on the coset**: the table on `26` digits holds the coefficients
of `h₀` below `2^24` and the blinding words from `2^24` on, so its polynomial is `h₀` plus the
cells' vanishing polynomial `digitPoly 24` times `blindPoly blind` (`tablePoly_snoc`). -/
theorem q0B_coset (α β γ : E) (blind : Fin 3 → Fin PcsQuotient.hBlind → K) {p : ℕ}
    (hp : p < 2 ^ 26) :
    (q0BOf 22 (coefficients 24 0 (hValues 22 cells sigma α β γ)) blind).getD p 0 =
      ((Params.honest Completeness.deployedInstanceE.params (gOf f masks) α β γ).h₀ +
        Completeness.deployedInstanceE.params.vCells * blindPoly blind).eval
          (ofK (betaAt 26 + point p)) := by
  unfold q0BOf
  refine Eq.trans (values_ofFn_E hK _ (q0BEntry (coefficients 24 0 (hValues 22 cells sigma α β γ)) blind)
    (fun _ => rfl) hp) (congrArg (Polynomial.eval _) ?_)
  have hm : PcsQuotient.cellVars 22 = 24 := rfl
  have h1 : tablePoly (fun b : Fin (PcsQuotient.cellVars 22) → Bool =>
      (coefficients 24 0 (hValues 22 cells sigma α β γ)).getD (Completeness.idx b) 0) =
      (Params.honest Completeness.deployedInstanceE.params (gOf f masks) α β γ).h₀ :=
    hHat_table hK f cells hcells sigma hsigma masks α β γ
  have h2 : (digitPoly (PcsQuotient.cellVars 22) : E[X]) = Completeness.deployedInstanceE.params.vCells :=
    (matches_deployed hK).vCells.symm
  have h3 : tablePoly (fun b : Fin (PcsQuotient.cellVars 22) → Bool => blindAt blind (Completeness.idx b)) =
      blindPoly blind := rfl
  refine (tablePoly_split (PcsQuotient.cellVars 22) 26 (by rw [hm]; norm_num)
    (q0BEntry (coefficients 24 0 (hValues 22 cells sigma α β γ)) blind)
    (coefficients 24 0 (hValues 22 cells sigma α β γ)) (blindAt blind)
    (fun n hn => by unfold q0BEntry; rw [if_pos hn])
    (fun n hn => by unfold q0BEntry; rw [if_neg (by omega), Nat.add_sub_cancel])
    (fun n hn => by
      rw [hm] at hn
      unfold q0BEntry blindAt
      rw [hm, if_neg (by omega), dif_neg (by unfold PcsQuotient.hBlind; omega)])).trans ?_
  exact congrArg₂ (· + ·) h1 (congrArg₂ (· * ·) h2 h3)

/-- The gate vanishes at the rows when the cells satisfy the gates. -/
theorem gate_rows (hgate : ∀ y : Fin 22 → Bool, gate (ofK (f (cellBits (y, 0))))
      (ofK (f (cellBits (y, 1)))) (ofK (f (cellBits (y, 2)))) (ofK (f (cellBits (y, 3)))) = 0)
    (x : Completeness.deployedInstanceE.params.T) :
    (Params.gatePoly Completeness.deployedInstanceE.params (gOf f masks)).eval (x : E) = 0 := by
  obtain ⟨y, rfl⟩ := (cantorRows (n := 22) Completeness.deployedInstanceE.basis le24).surjective x
  have hrow : ∀ c : Fin 4, (Params.cellPoly Completeness.deployedInstanceE.params (gOf f masks) c).eval
      ((cantorRows (n := 22) Completeness.deployedInstanceE.basis le24 y :
        Completeness.deployedInstanceE.params.T) : E) = ofK (f (cellBits (y, c))) := by
    intro c
    have he : ((cantorRows (n := 22) Completeness.deployedInstanceE.basis le24 y :
        Completeness.deployedInstanceE.params.T), c) =
        Completeness.deployedInstanceE.cellEquiv (cellBits (y, c)) := by
      show _ = (Equiv.prodCongr _ _) (cellBits.symm (cellBits (y, c)))
      rw [Equiv.symm_apply_apply]
      rfl
    exact (congrArg (Completeness.deployedInstanceE.params.cells (gOf f masks)) he).trans
      (cells_cellEquiv f masks _)
  rw [Params.gatePoly, gate_eval, hrow, hrow, hrow, hrow]
  exact hgate y

theorem qGateK_map (α β γ : E) :
    (Completeness.qGateKOf (Params.honest Completeness.deployedInstanceE.params (gOf f masks) α β γ)).map
        (algebraMap K E) =
      (Params.honest Completeness.deployedInstanceE.params (gOf f masks) α β γ).qGate := by
  have hmem := Completeness.qGate_mem_lifts (algebraMap K E) Completeness.deployedInstanceE
    deployedBasis (fun _ => rfl) (gOf f masks) (Completeness.witnessOfTable_mem_lifts (algebraMap K E)
      Completeness.deployedInstanceE deployedBasis (fun _ => rfl) _) α β γ
  unfold Completeness.qGateKOf
  rw [dif_pos hmem]
  exact Classical.choose_spec ((lifts_iff_set_range _).mp hmem)

include hK hcs hcells in
/-- **The gate's quotient on the coset is the honest one, over `K`.** -/
theorem qGateValues_coset (hgate : ∀ y : Fin 22 → Bool, gate (ofK (f (cellBits (y, 0))))
      (ofK (f (cellBits (y, 1)))) (ofK (f (cellBits (y, 2)))) (ofK (f (cellBits (y, 3)))) = 0)
    (α β γ : E) {p : ℕ} (hp : p < 2 ^ 26) :
    (qGateValuesOf 22 (wValuesOf 22 (coefficients 24 0 cells) (PcsQuotient.maskEntries masks))
        (blocksOf 22 γ)).getD p 0 =
      (Completeness.qGateKOf (Params.honest Completeness.deployedInstanceE.params (gOf f masks)
        α β γ)).eval (betaAt 26 + point p) := by
  apply ofK_injective
  have hv := vRows_coset_ne_zero hK hp
  have hmul := congrArg (fun q => q.eval (ofK (betaAt 26 + point p)))
    (qGate_mul_of Completeness.deployedInstanceE.params Completeness.deployedInstanceE.exact
      (gOf f masks) α β γ (gate_rows f masks hgate))
  simp only [Polynomial.eval_mul] at hmul
  have hq : (Params.honest Completeness.deployedInstanceE.params (gOf f masks) α β γ).qGate.eval
      (ofK (betaAt 26 + point p)) =
      (Params.gatePoly Completeness.deployedInstanceE.params (gOf f masks)).eval
        (ofK (betaAt 26 + point p)) *
        (Completeness.deployedInstanceE.params.vRows.eval (ofK (betaAt 26 + point p)))⁻¹ := by
    rw [← hmul]
    field_simp
  rw [ofK_eval, qGateK_map, hq,
    qGateValuesOf_getD _ _ (show p < 4 * 2 ^ PcsQuotient.cellVars 22 by
      unfold PcsQuotient.cellVars; omega) _ _ _
      (blocksOf_getD γ (hi := p / 2 ^ PcsQuotient.region) (by unfold PcsQuotient.region; omega)),
    rowInv_coset hK hp]
  have key : ∀ a b c d r : K, ofK ((a + b + c + d * c) * r⁻¹) =
      (ofK a + ofK b + ofK c + ofK d * ofK c) * (ofK r)⁻¹ := by
    intro a b c d r
    simp only [Compose.Reduce.ofK_mul, Compose.Reduce.ofK_add, ofK_inv]
  have hx : ∀ j < 4, ofK ((wValuesOf 22 (coefficients 24 0 cells)
      (PcsQuotient.maskEntries masks)).getD (p ^^^ j) 0) =
      (Instance.witnessPoly (gOf f masks)).eval (ofK (betaAt 26 + point p) + ofK (point j)) := by
    intro j hj
    rw [wValues_coset hK f cells hcs hcells masks (Nat.xor_lt_two_pow hp (by omega)), point_xor,
      ← add_assoc, Compose.Reduce.ofK_add]
  have hs0 : shift Completeness.deployedInstanceE.params.θ 0 = 0 := rfl
  have hs1 : shift Completeness.deployedInstanceE.params.θ 1 = ofK (point 1) := by
    rw [point_one hK, Compose.Reduce.ofK_one]
    rfl
  have hs2 : shift Completeness.deployedInstanceE.params.θ 2 = ofK (point 2) := theta_eq hK
  have hs3 : shift Completeness.deployedInstanceE.params.θ 3 = ofK (point 3) := by
    rw [point_three hK, Compose.Reduce.ofK_add, Compose.Reduce.ofK_one, ← theta_eq hK, add_comm]
    rfl
  rw [key, hx 1 (by norm_num), hx 2 (by norm_num), hx 3 (by norm_num),
    wValues_coset hK f cells hcs hcells masks hp, ofK_rowPolyOf hK, Params.gatePoly, gate_eval,
    cellPoly_eval, cellPoly_eval, cellPoly_eval, cellPoly_eval, hs0, hs1, hs2, hs3, add_zero]
  rfl

include hK hcs hcells hss hsigma in
/-- **The copy identity's quotient on the coset is the blinded `q`** (`honestB`'s: `q + d d' b`), at
non-degenerate `α, β`. -/
theorem qValuesB_coset (α β γ : E) (blind : Fin 3 → Fin PcsQuotient.hBlind → K)
    (hab : ¬ Completeness.Reduction.BadAB Completeness.deployedInstanceE (gOf f masks) α β)
    {p : ℕ} (hp : p < 2 ^ 26) :
    (qValuesOf 22 (wValuesOf 22 (coefficients 24 0 cells) (PcsQuotient.maskEntries masks))
        (sigmaValuesOf 22 (coefficients 24 0 (sigma.map point)))
        (q0BOf 22 (coefficients 24 0 (hValues 22 cells sigma α β γ)) blind) (blocksOf 22 γ)
        α β).getD p 0 =
      (honestB Completeness.deployedInstanceE.params (gOf f masks) α β γ (blindPoly blind)).q.eval
        (ofK (betaAt 26 + point p)) := by
  have hd : ∀ i, α + Completeness.deployedInstanceE.params.cells (gOf f masks) i +
      β * Completeness.deployedInstanceE.params.pt i ≠ 0 := fun i h => hab ⟨i, Or.inl h⟩
  have hd' : ∀ i, α + Completeness.deployedInstanceE.params.cells (gOf f masks) i +
      β * Completeness.deployedInstanceE.params.pt (Completeness.deployedInstanceE.params.σ i) ≠ 0 :=
    fun i h => hab ⟨i, Or.inr h⟩
  have hvc := vCells_coset_ne_zero hK hp
  have hmul0 := q_mul_of Completeness.deployedInstanceE.params Completeness.deployedInstanceE.exact
    (gOf f masks) α β γ hd hd'
  have hmulB : Completeness.deployedInstanceE.params.vCells *
      (honestB Completeness.deployedInstanceE.params (gOf f masks) α β γ (blindPoly blind)).q =
      Params.dPoly Completeness.deployedInstanceE.params (gOf f masks) α β *
        Params.dNextPoly Completeness.deployedInstanceE.params (gOf f masks) α β *
        ((Params.honest Completeness.deployedInstanceE.params (gOf f masks) α β γ).h₀ +
          Completeness.deployedInstanceE.params.vCells * blindPoly blind) +
        Params.copyPoly Completeness.deployedInstanceE.params (gOf f masks) α β γ := by
    rw [honestB_q]
    rw [mul_add, hmul0]
    ring
  have hmul := congrArg (fun q => q.eval (ofK (betaAt 26 + point p))) hmulB
  simp only [Polynomial.eval_mul] at hmul
  have hq : (honestB Completeness.deployedInstanceE.params (gOf f masks) α β γ
      (blindPoly blind)).q.eval (ofK (betaAt 26 + point p)) =
      (Params.dPoly Completeness.deployedInstanceE.params (gOf f masks) α β *
        Params.dNextPoly Completeness.deployedInstanceE.params (gOf f masks) α β *
        ((Params.honest Completeness.deployedInstanceE.params (gOf f masks) α β γ).h₀ +
          Completeness.deployedInstanceE.params.vCells * blindPoly blind) +
        Params.copyPoly Completeness.deployedInstanceE.params (gOf f masks) α β γ).eval
          (ofK (betaAt 26 + point p)) *
        (Completeness.deployedInstanceE.params.vCells.eval (ofK (betaAt 26 + point p)))⁻¹ := by
    rw [← hmul]
    field_simp
  rw [hq, qValuesOf_getD _ _ _ _ α β (show p < 4 * 2 ^ PcsQuotient.cellVars 22 by
      unfold PcsQuotient.cellVars; omega) _ _ _
      (blocksOf_getD γ (hi := p / 2 ^ PcsQuotient.region) (by unfold PcsQuotient.region; omega)),
    pub_coset hK γ hp, q0B_coset hK f cells hcells sigma hsigma masks α β γ blind hp,
    show PcsQuotient.cellVars 22 + 2 = 26 from rfl, ofK_inv, ← vCells_coset hK hp,
    wValues_coset hK f cells hcs hcells masks hp, sigmaValues_coset hK sigma hss hsigma hp,
    numer_eval]
  ring

/-! ## The coefficient tables -/

include hK hcs hcells hss hsigma in
/-- **The table `coefficients 26 (betaAt 26) qValues` holds the blinded copy quotient**
(`honestB`'s `q`, of degree below `2^26` by `natDegree_honestB_q_lt`). -/
theorem qHatB_table26 (α β γ : E) (blind : Fin 3 → Fin PcsQuotient.hBlind → K)
    (hab : ¬ Completeness.Reduction.BadAB Completeness.deployedInstanceE (gOf f masks) α β) :
    tablePoly (fun b : Fin 26 → Bool => (coefficients 26 (betaAt 26)
        (qValuesOf 22 (wValuesOf 22 (coefficients 24 0 cells) (PcsQuotient.maskEntries masks))
          (sigmaValuesOf 22 (coefficients 24 0 (sigma.map point)))
          (q0BOf 22 (coefficients 24 0 (hValues 22 cells sigma α β γ)) blind) (blocksOf 22 γ)
          α β)).getD (Completeness.idx b) 0) =
      (honestB Completeness.deployedInstanceE.params (gOf f masks) α β γ (blindPoly blind)).q := by
  have hdeg := natDegree_honestB_q_lt Completeness.deployedInstanceE (gOf f masks)
    (Completeness.natDegree_witnessOfTable_le (algebraMap K E) deployedBasis f masks) α β γ
    (blindPoly blind) (natDegree_blindPoly_lt blind)
  refine coset_ext_E hK (natDegree_tablePoly_lt _) (lt_of_lt_of_le hdeg (by norm_num))
    fun p hp => ?_
  rw [tablePoly_coefficients_E (m := 26) (cantorUpTo26 hK) (by unfold basisSize; norm_num) _ _
    (by unfold qValuesOf; exact size_ofFn26 _) hp]
  exact qValuesB_coset hK f cells hcs hcells sigma hss hsigma masks α β γ blind hab hp

include hK hcs hcells in
/-- **The table `coefficients 26 (betaAt 26) qGateValues` holds the honest gate quotient**, over
`K`. -/
theorem qGateHat_table26 (hgate : ∀ y : Fin 22 → Bool, gate (ofK (f (cellBits (y, 0))))
      (ofK (f (cellBits (y, 1)))) (ofK (f (cellBits (y, 2)))) (ofK (f (cellBits (y, 3)))) = 0)
    (α β γ : E) :
    tablePoly (fun b : Fin 26 → Bool => (coefficients 26 (betaAt 26)
        (qGateValuesOf 22 (wValuesOf 22 (coefficients 24 0 cells) (PcsQuotient.maskEntries masks))
          (blocksOf 22 γ))).getD (Completeness.idx b) 0) =
      Completeness.qGateKOf (Params.honest Completeness.deployedInstanceE.params (gOf f masks)
        α β γ) := by
  have hdeg := (Completeness.honest_degrees Completeness.deployedInstanceE (gOf f masks)
    (Completeness.natDegree_witnessOfTable_le (algebraMap K E) deployedBasis f masks) α β γ).2.2
  rw [← qGateK_map f masks α β γ, natDegree_map_eq_of_injective (algebraMap K E).injective] at hdeg
  refine coset_ext_K hK (natDegree_tablePoly_lt _) (lt_of_le_of_lt hdeg (by norm_num))
    fun p hp => ?_
  rw [Pcs.Ntt.tablePoly_coefficients (m := 26) (cantorUpTo26 hK) (by unfold basisSize; norm_num)
    _ _ (by unfold qGateValuesOf; exact size_ofFn26 _) hp]
  exact qGateValues_coset hK f cells hcs hcells masks hgate α β γ hp


end Honest

end ProverQuotient

end E2ECompleteness.Pcs

/-- info: 'E2ECompleteness.Pcs.ProverQuotient.hHat_table26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.ProverQuotient.hHat_table26

/-- info: 'E2ECompleteness.Pcs.ProverQuotient.qHatB_table26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.ProverQuotient.qHatB_table26

/-- info: 'E2ECompleteness.Pcs.ProverQuotient.qGateHat_table26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.ProverQuotient.qGateHat_table26

/-- info: 'E2ECompleteness.Pcs.ProverQuotient.qGateK_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.ProverQuotient.qGateK_map

/-- info: 'E2ECompleteness.Pcs.ProverQuotient.gate_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.ProverQuotient.gate_rows

/-- info: 'E2ECompleteness.Pcs.ProverQuotient.tablePoly_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.ProverQuotient.tablePoly_split

/-- info: 'E2ECompleteness.Pcs.ProverQuotient.q0B_coset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.ProverQuotient.q0B_coset

/-- info: 'E2ECompleteness.Pcs.ProverQuotient.qValuesB_coset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.ProverQuotient.qValuesB_coset

/-- info: 'E2ECompleteness.Pcs.ProverQuotient.ofK_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.ProverQuotient.ofK_eval

/-- info: 'E2ECompleteness.Pcs.ProverQuotient.limb_tablePoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.ProverQuotient.limb_tablePoly
