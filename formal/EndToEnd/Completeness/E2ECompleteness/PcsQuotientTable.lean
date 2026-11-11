-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New for the PCS claims: the quotient table assembled from the honest prover's three parts is the blinded
-- honest second message. Builds on `E2ECompleteness/PcsTable.lean` (`quotientsOfTable_assemble`) and
-- `E2ECompleteness/PcsQuotient.lean` (the coefficient tables hold the honest polynomials), against
-- `formal/Completeness`'s honest prover (`QuotientSecurity`, adapted from leanVM, branch
-- PCS-openings-aggregation, commit 651453c6). Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM,
-- branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the fields `K`, `E` and their limbs.
import E2ECompleteness.PcsQuotient
import E2ECompleteness.PcsTable

/-!
# The honest quotient table is the blinded honest second message

The prover commits `H`, `Q`, `G` (`hTableOf`, `qTableOf`, `gTableOf`); F1 reads one quotient table,
`PcsBridge.assemble` of the three. **`quotientsOfTable_honest`**: the second message that table holds
(`quotientsOfTable y`) is `honestB` with the blinding `blindPoly blind`, at non-degenerate `α, β` for cells
satisfying the gates. By `quotientsOfTable_assemble`:

* `H`'s low half holds, limb by limb, `h`'s coefficients (`hTable_low`), so its limb sum is the 24-digit
  table of `hHat` (`limbSum_of`), the honest `h₀` (`hHat_table`); its high half holds the blinding
  (`hTable_high`), so its limb sum is `blindPoly blind`;
* `Q` holds, limb by limb, `q`'s coefficients (`qTable_getD`, `qTable_at`), the blinded copy quotient
  (`qHatB_table26`);
* `G` holds the gate quotient's first `2^25` coefficients (`gTable_at`); the gate quotient over `K` is
  of degree below `2^25`, so the upper half of its 26-digit table vanishes (`eq_of_monic_add`,
  `digitPoly 25` monic of degree `2^25`) and the lower half holds it (`gTable_poly`).

Everything about the parts is stated for abstract arrays (`quotientsOfTable_of_arrays`), so that no
unification looks into the prover's computations.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM.Parameters QuotientSecurity PcsQuotient PcsQuotient.Domain

namespace E2ECompleteness.Pcs

/-! ## Limbs -/

theorem limbOf_lt (x : E) (e : ℕ) (he : e < 3) : limbOf x e = x.limb ⟨e, he⟩ := by
  unfold limbOf LeanVM.Prover.limbAt
  interval_cases e <;> rfl

theorem ofLimbs_limb_fin (F : Fin 3 → K) (l : Fin 3) : (E.ofLimbs (F 0) (F 1) (F 2)).limb l = F l := by
  fin_cases l <;> rfl

/-- **The limb sum of a table holding the limbs of `c`**, limb `limbN e₀ e₁`, zero for limb `3`. -/
theorem limbSum_of {M : ℕ} (T : Bool → Bool → (Fin M → Bool) → K) (c : (Fin M → Bool) → E)
    (hT : ∀ e₀ e₁ b, T e₀ e₁ b =
      if h : limbN e₀ e₁ < 3 then (c b).limb ⟨limbN e₀ e₁, h⟩ else 0) :
    limbSum (fun e₀ e₁ b ↦ ofK (T e₀ e₁ b)) = tablePoly c := by
  have h0 : (fun b ↦ ofK (T false false b)) = fun b ↦ ofK ((c b).limb 0) :=
    funext fun b ↦ by rw [hT, dif_pos (by decide)]; rfl
  have h1 : (fun b ↦ ofK (T true false b)) = fun b ↦ ofK ((c b).limb 1) :=
    funext fun b ↦ by rw [hT, dif_pos (by decide)]; rfl
  have h2 : (fun b ↦ ofK (T false true b)) = fun b ↦ ofK ((c b).limb 2) :=
    funext fun b ↦ by rw [hT, dif_pos (by decide)]; rfl
  have h3 : (fun b ↦ ofK (T true true b)) = fun _ ↦ (0 : E) :=
    funext fun b ↦ by rw [hT, dif_neg (by decide)]; exact map_zero (algebraMap K E)
  show tablePoly (fun b ↦ ofK (T false false b)) + C y * tablePoly (fun b ↦ ofK (T true false b)) +
      C (y ^ 2) * tablePoly (fun b ↦ ofK (T false true b)) +
      C (y ^ 3) * tablePoly (fun b ↦ ofK (T true true b)) = _
  rw [h0, h1, h2, h3]
  exact tablePoly_limbs c

/-! ## The three parts by their bits -/

section Parts

variable (hHat : Array E) (blind : Fin 3 → Fin hBlind → K) (qHat : Array E) (qGateHat : Array K)

/-- `H`'s low half: limb `limbN e₀ e₁` of `h`'s coefficients. -/
theorem hTable_low (b : Fin 24 → Bool) (e₀ e₁ : Bool) :
    (hTableOf 22 hHat blind).getD
        (Completeness.idx (Fin.snoc (Fin.snoc (Fin.snoc b false) e₀) e₁ : Fin (24 + 1 + 1 + 1) → Bool)) 0 =
      if h : limbN e₀ e₁ < 3 then (hHat.getD (Completeness.idx b) 0).limb ⟨limbN e₀ e₁, h⟩ else 0 := by
  have hb : Completeness.idx b < 2 ^ cellVars 22 := Completeness.idx_lt b
  have hj : Completeness.idx b < 2 * 2 ^ cellVars 22 := by omega
  rw [idx_hbits, if_neg Bool.false_ne_true, add_zero]
  refine (hTable_getD hHat blind (limbN e₀ e₁) (Completeness.idx b) (limbN_lt e₀ e₁) hj).trans ?_
  rw [if_pos hb]
  by_cases he : limbN e₀ e₁ < 3
  · rw [if_neg (show ¬ 3 ≤ limbN e₀ e₁ by omega), dif_pos he, limbOf_lt _ _ he]
  · rw [if_pos (show 3 ≤ limbN e₀ e₁ by omega), dif_neg he]

/-- `H`'s high half: limb `limbN e₀ e₁` of the blinding. -/
theorem hTable_high (b : Fin 24 → Bool) (e₀ e₁ : Bool) :
    (hTableOf 22 hHat blind).getD
        (Completeness.idx (Fin.snoc (Fin.snoc (Fin.snoc b true) e₀) e₁ : Fin (24 + 1 + 1 + 1) → Bool)) 0 =
      if h : limbN e₀ e₁ < 3 then (blindAt blind (Completeness.idx b)).limb ⟨limbN e₀ e₁, h⟩
      else 0 := by
  have hb : Completeness.idx b < 2 ^ cellVars 22 := Completeness.idx_lt b
  have hj : Completeness.idx b + 2 ^ cellVars 22 < 2 * 2 ^ cellVars 22 := by omega
  rw [idx_hbits, if_pos rfl]
  refine (hTable_getD hHat blind (limbN e₀ e₁) (Completeness.idx b + 2 ^ cellVars 22) (limbN_lt e₀ e₁)
    hj).trans ?_
  rw [if_neg (show ¬ Completeness.idx b + 2 ^ cellVars 22 < 2 ^ cellVars 22 by omega)]
  simp only [Nat.add_sub_cancel]
  by_cases he : limbN e₀ e₁ < 3
  · rw [if_neg (show ¬ 3 ≤ limbN e₀ e₁ by omega), dif_pos he]
    unfold blindAt
    by_cases hi : Completeness.idx b < hBlind
    · rw [dif_pos ⟨hi, he⟩, dif_pos hi]
      exact (ofLimbs_limb_fin (fun l ↦ blind l ⟨Completeness.idx b, hi⟩) ⟨limbN e₀ e₁, he⟩).symm
    · rw [dif_neg (fun h ↦ hi h.1), dif_neg hi, limb_zero]
  · rw [if_pos (show 3 ≤ limbN e₀ e₁ by omega), dif_neg he]

/-- `Q` by limb and coefficient (`N = 2^24` cells). -/
theorem qTable_getD (e j : ℕ) (he : e < 4) (hj : j < 4 * 2 ^ cellVars 22) :
    (qTableOf 22 qHat).getD (e * (4 * 2 ^ cellVars 22) + j) 0 =
      if e < 3 then limbOf (qHat.getD j 0) e else 0 := by
  have hlt : e * (4 * 2 ^ cellVars 22) + j < 16 * 2 ^ cellVars 22 := by
    have : e * (4 * 2 ^ cellVars 22) ≤ 3 * (4 * 2 ^ cellVars 22) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hpos : 0 < 4 * 2 ^ cellVars 22 := by positivity
  have h1 : (e * (4 * 2 ^ cellVars 22) + j) / (4 * 2 ^ cellVars 22) = e := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hj, zero_add]
  have h2 : (e * (4 * 2 ^ cellVars 22) + j) % (4 * 2 ^ cellVars 22) = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  unfold qTableOf
  rw [getD_ofFn₂ _ _ hlt]
  dsimp only
  rw [h1, h2]

/-- The index of `(low, e₀, e₁)`, `low` on `26` digits. -/
theorem idx_qbits (low : Fin (24 + 1 + 1) → Bool) (e₀ e₁ : Bool) :
    Completeness.idx (Fin.snoc (Fin.snoc low e₀) e₁ : Fin (24 + 1 + 1 + 1 + 1) → Bool) =
      limbN e₀ e₁ * (4 * 2 ^ 24) + Completeness.idx low := by
  rw [Completeness.idx_snoc, Completeness.idx_snoc]
  unfold limbN
  cases e₀ <;> cases e₁ <;> simp <;> ring

/-- `Q`: limb `limbN e₀ e₁` of `q`'s coefficients. -/
theorem qTable_at (b : Fin (24 + 1 + 1) → Bool) (e₀ e₁ : Bool) :
    (qTableOf 22 qHat).getD
        (Completeness.idx (Fin.snoc (Fin.snoc b e₀) e₁ : Fin (24 + 1 + 1 + 1 + 1) → Bool)) 0 =
      if h : limbN e₀ e₁ < 3 then (qHat.getD (Completeness.idx b) 0).limb ⟨limbN e₀ e₁, h⟩ else 0 := by
  have hb : Completeness.idx b < 4 * 2 ^ cellVars 22 := by
    have := Completeness.idx_lt b
    show Completeness.idx b < 4 * 2 ^ 24
    norm_num at this ⊢
    omega
  rw [idx_qbits]
  refine (qTable_getD qHat (limbN e₀ e₁) (Completeness.idx b) (limbN_lt e₀ e₁) hb).trans ?_
  by_cases he : limbN e₀ e₁ < 3
  · rw [if_pos he, dif_pos he, limbOf_lt _ _ he]
  · rw [if_neg he, dif_neg he]

/-- `G`: the gate quotient's coefficients below `2^25`. -/
theorem gTable_at (b : Fin (24 + 1) → Bool) :
    (gTableOf 22 qGateHat).getD (Completeness.idx b) 0 = qGateHat.getD (Completeness.idx b) 0 := by
  have hb : Completeness.idx b < 2 * 2 ^ cellVars 22 := by
    have := Completeness.idx_lt b
    show Completeness.idx b < 2 * 2 ^ 24
    norm_num at this ⊢
    omega
  unfold gTableOf
  exact getD_ofFn₂ _ _ hb 0

/-- A polynomial `s = p + D r` with `D` monic of degree `N` and `p`, `s` below `N` is `p`. -/
theorem eq_of_monic_add {F : Type*} [Field F] (p r s D : F[X]) (N : ℕ) (hD : D.Monic)
    (hDN : D.natDegree = N) (hp : p.natDegree < N) (hs : s.natDegree < N) (h : s = p + D * r) :
    p = s := by
  by_cases hr : r = 0
  · rw [h, hr, mul_zero, add_zero]
  · exfalso
    have h1 : D * r = s - p := by rw [h]; ring
    have h2 : (D * r).natDegree = N + r.natDegree := by rw [hD.natDegree_mul' hr, hDN]
    have h3 : (s - p).natDegree < N := lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hs hp)
    rw [← h1, h2] at h3
    omega

/-- **The lower half of a table holding a polynomial of degree below `2^m`** holds it too. -/
theorem lowHalf_eq {F : Type*} [Field F] [CharP F 2] {m : ℕ} (c : (Fin (m + 1) → Bool) → F) (p : F[X])
    (hc : tablePoly c = p) (hdeg : p.natDegree < 2 ^ m) :
    tablePoly (fun b : Fin m → Bool ↦ c (Fin.snoc b false)) = p :=
  eq_of_monic_add _ _ _ _ (2 ^ m) (digitPoly_monic_natDegree m).1 (digitPoly_monic_natDegree m).2
    (natDegree_tablePoly_lt _) hdeg (hc.symm.trans (tablePoly_snoc c))

/-- **`G`'s polynomial**: the 26-digit table of the gate quotient's coefficients holds `qGK`, of degree
below `2^25`, so the 25-digit `G` holds `qGK`, read in `E`. -/
theorem gTable_poly (qGK : K[X])
    (hq : tablePoly (fun b : Fin 26 → Bool ↦ qGateHat.getD (Completeness.idx b) 0) = qGK)
    (hdeg : qGK.natDegree < 2 ^ 25) :
    tablePoly (fun b : Fin (24 + 1) → Bool ↦ ofK ((gTableOf 22 qGateHat).getD (Completeness.idx b) 0)) =
      qGK.map (algebraMap K E) := by
  have hlo : tablePoly (fun b : Fin (24 + 1) → Bool ↦
      qGateHat.getD (Completeness.idx (Fin.snoc b false : Fin (24 + 1 + 1) → Bool)) 0) = qGK :=
    lowHalf_eq (m := 24 + 1) (fun b ↦ qGateHat.getD (Completeness.idx b) 0) qGK hq hdeg
  rw [← hlo, ← Completeness.tablePoly_map (algebraMap K E)]
  refine congrArg tablePoly (funext fun b ↦ ?_)
  rw [gTable_at, Completeness.idx_snoc, if_neg Bool.false_ne_true, add_zero]
  rfl

end Parts

/-! ## The assembled table -/

theorem honestB_hHigh {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] (P : Params F)
    (g : Params.Witness F) (α β γ : F) (b : F[X]) : (honestB P g α β γ b).hHigh = b := rfl

theorem honestB_junk {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] (P : Params F)
    (g : Params.Witness F) (α β γ : F) (b : F[X]) : (honestB P g α β γ b).junk = 0 := rfl

/-- **The quotient table of three abstract coefficient arrays**: `h`'s coefficients hold `R.h₀`, the blinding
`R.hHigh`, `q`'s `R.q`, the gate quotient's (26 digits) a `qGK` below `2^25` that reads `R.qGate` in `E`. -/
theorem quotientsOfTable_of_arrays (R : Params.Quotients E) (hHat qHat : Array E) (qGateHat : Array K)
    (blind : Fin 3 → Fin hBlind → K) (qGK : K[X])
    (hh : tablePoly (fun b : Fin 24 → Bool ↦ hHat.getD (Completeness.idx b) 0) = R.h₀)
    (hb : blindPoly blind = R.hHigh)
    (hq : tablePoly (fun b : Fin 26 → Bool ↦ qHat.getD (Completeness.idx b) 0) = R.q)
    (hg : tablePoly (fun b : Fin 26 → Bool ↦ qGateHat.getD (Completeness.idx b) 0) = qGK)
    (hdeg : qGK.natDegree < 2 ^ 25) (hgm : qGK.map (algebraMap K E) = R.qGate) (hj : R.junk = 0) :
    quotientsOfTable y (PcsBridge.assemble (m := 24)
        (fun b ↦ ofK ((hTableOf 22 hHat blind).getD (Completeness.idx b) 0))
        (fun b ↦ ofK ((qTableOf 22 qHat).getD (Completeness.idx b) 0))
        (fun b ↦ ofK ((gTableOf 22 qGateHat).getD (Completeness.idx b) 0))) = R := by
  refine quotientsOfTable_assemble _ _ _ R ?_ ?_ ?_ ?_ hj
  · exact (limbSum_of _ (fun b ↦ hHat.getD (Completeness.idx b) 0)
      (fun e₀ e₁ b ↦ hTable_low hHat blind b e₀ e₁)).trans hh
  · exact (limbSum_of _ (fun b ↦ blindAt blind (Completeness.idx b))
      (fun e₀ e₁ b ↦ hTable_high hHat blind b e₀ e₁)).trans hb
  · exact (limbSum_of _ (fun b ↦ qHat.getD (Completeness.idx b) 0)
      (fun e₀ e₁ b ↦ qTable_at qHat b e₀ e₁)).trans hq
  · exact (gTable_poly qGateHat qGK hg hdeg).trans hgm

/-- **The honest quotient table is the blinded honest second message**: the table `PcsBridge.assemble` of
the honest prover's three parts `H`, `Q`, `G` holds `honestB` with the blinding `blindPoly blind`, at
non-degenerate `α, β` (`¬ BadAB`), for cells satisfying the gates (`hgate`). -/
theorem quotientsOfTable_honest (hK : Constants) (f : (Fin (22 + 2) → Bool) → K) (cells : Array K)
    (hcs : cells.size = 2 ^ 24) (hcells : ∀ b, cells.getD (Completeness.idx b) 0 = f b)
    (sigma : Array ℕ) (hss : sigma.size = 2 ^ 24)
    (hsigma : ∀ b, point (sigma.getD (Completeness.idx b) 0) = deployedBasis.point (deployedSigma b))
    (masks : PcsQuotient.Masks) (blind : Fin 3 → Fin PcsQuotient.hBlind → K)
    (hgate : ∀ y : Fin 22 → Bool, gate (ofK (f (cellBits (y, 0))))
      (ofK (f (cellBits (y, 1)))) (ofK (f (cellBits (y, 2)))) (ofK (f (cellBits (y, 3)))) = 0)
    (α β γ : E)
    (hab : ¬ Completeness.Reduction.BadAB Completeness.deployedInstanceE
      (ProverQuotient.gOf f masks) α β) :
    quotientsOfTable y (PcsBridge.assemble (m := 24)
        (fun b ↦ ofK ((hTableOf 22 (coefficients 24 0 (hValues 22 cells sigma α β γ)) blind).getD
          (Completeness.idx b) 0))
        (fun b ↦ ofK ((qTableOf 22 (coefficients 26 (betaAt 26) (qValuesOf 22 (wValuesOf 22
          (coefficients 24 0 cells) (PcsQuotient.maskEntries masks))
          (sigmaValuesOf 22 (coefficients 24 0 (sigma.map point)))
          (q0BOf 22 (coefficients 24 0 (hValues 22 cells sigma α β γ)) blind) (blocksOf 22 γ) α β))).getD
          (Completeness.idx b) 0))
        (fun b ↦ ofK ((gTableOf 22 (coefficients 26 (betaAt 26) (qGateValuesOf 22 (wValuesOf 22
          (coefficients 24 0 cells) (PcsQuotient.maskEntries masks)) (blocksOf 22 γ)))).getD
          (Completeness.idx b) 0))) =
      honestB Completeness.deployedInstanceE.params (ProverQuotient.gOf f masks) α β γ
        (blindPoly blind) := by
  have hdeg := (Completeness.honest_degrees Completeness.deployedInstanceE (ProverQuotient.gOf f masks)
    (Completeness.natDegree_witnessOfTable_le (algebraMap K E) deployedBasis f masks) α β γ).2.2
  rw [← ProverQuotient.qGateK_map f masks α β γ,
    natDegree_map_eq_of_injective (algebraMap K E).injective] at hdeg
  have h1 := ProverQuotient.hHat_table hK f cells hcells sigma hsigma masks α β γ
  have h2 := ProverQuotient.qHatB_table26 hK f cells hcs hcells sigma hss hsigma masks α β γ blind hab
  have h3 := ProverQuotient.qGateHat_table26 hK f cells hcs hcells masks hgate α β γ
  have h4 := ProverQuotient.qGateK_map f masks α β γ
  have h5 : (Completeness.qGateKOf (Params.honest Completeness.deployedInstanceE.params
      (ProverQuotient.gOf f masks) α β γ)).natDegree < 2 ^ 25 := lt_of_le_of_lt hdeg (by norm_num)
  exact quotientsOfTable_of_arrays _ _ _ _ blind _ h1 (honestB_hHigh _ _ _ _ _ _).symm h2 h3 h5 h4
    (honestB_junk _ _ _ _ _ _)

end E2ECompleteness.Pcs

/-- info: 'E2ECompleteness.Pcs.quotientsOfTable_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.quotientsOfTable_honest
