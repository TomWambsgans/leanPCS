-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The polynomials are `formal/RecPiop`'s (`Identity.lean`:
-- `pushPolyV`, `tPoly`, `holePoly`, `formulaPoly`, `cellPoly`, `Role.value_eval`; `Indicator.lean`: `ind`).
import RecCompose.Pi2HonestCopy

/-!
# π2's honest prover: `q` and `q_P` on the extension coset are the honest ones (π2v3)

The prover computes `q` and `q_P` pointwise on the coset `β_{m+1} + V_{m+1}` (`qValues`, `qpValues`) and interpolates
them there (`qNovel`, `qpNovel`). Here, at a circuit valid on `2^m` positions (`m + 1 < 28`):

* **the pairs** as a list (`pairsList`): `G.pairs`' elements once each (`sum_pairs`, `sum_pairs_filter`);
* **the indicators**: the prover's `indFrom` from a pair's data is `RecPiop.Circuit.ind` at a point off `V_m`
  (`ind_eval_eq`: `Z_V = Π_{j ∉ p} · Π_{j ∈ p}`);
* **the coset values**: `onCoset` is the novel polynomial at the coset's points (`onCoset_getD`); the prover's `P_v`,
  `T` and holes' indicator are `pushPolyV`'s, `tPoly`'s and `holePoly`'s values there (`pvAtCoset_eq`, `tAtCoset_eq`,
  `holeAtCoset_eq`), so its `q` values are the identity without `q` over `Z_V` (`qValues_eq`) and its `q_P` values
  `(P + P_v)/Z_V` (`qpValues_eq`);
* **`qNovel`'s polynomial is the honest `q`** (`novP_qNovel`: both of degree below `2N`, agreeing on the coset's `2N`
  points), and **`qpNovel`'s is the honest `q_P`** (`novP_qpNovel`: its values are in `K` at a circuit over `K`,
  `qpValues_mem`, so their limb `0`'s transform is theirs).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters Finset Polynomial

variable {G : RecPiop.Circuit E}

/-! ## The pairs as a list -/

theorem mem_pairsList {q : RecPiop.Block × ℕ} : q ∈ pairsList G ↔ q ∈ G.pairs := by
  rcases q with ⟨b, k⟩
  unfold pairsList RecPiop.Circuit.pairs
  simp [List.mem_product, and_assoc]

theorem pairsList_nodup : (pairsList G).Nodup :=
  ((List.nodup_dedup _).product List.nodup_range).filter _

theorem pairs_eq_toFinset : G.pairs = (pairsList G).toFinset :=
  Finset.ext fun q ↦ by rw [List.mem_toFinset, mem_pairsList]

theorem sum_pairs (f : RecPiop.Block × ℕ → E) : ∑ q ∈ G.pairs, f q = ((pairsList G).map f).sum := by
  rw [pairs_eq_toFinset, List.sum_toFinset _ pairsList_nodup]

theorem sum_pairs_filter (P : RecPiop.Block × ℕ → Bool) (f : RecPiop.Block × ℕ → E) :
    ∑ q ∈ G.pairs.filter (fun q ↦ P q = true), f q = (((pairsList G).filter P).map f).sum := by
  have : G.pairs.filter (fun q ↦ P q = true) = ((pairsList G).filter P).toFinset := Finset.ext fun q ↦ by
    rw [List.mem_toFinset, List.mem_filter, Finset.mem_filter, mem_pairsList]
  rw [this, List.sum_toFinset _ (pairsList_nodup.filter _)]

/-! ## The indicators -/

theorem iterate_sq_eq (m : ℕ) (x : E) : (fun y : E ↦ y * y + y)^[m] x = QuotientSecurity.sq^[m] x := rfl

theorem prod_filter_range (N : ℕ) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → E) :
    (((List.range N).filter fun j ↦ decide (P j)).map f).prod = ∏ j ∈ (range N).filter P, f j := by
  rw [← List.prod_toFinset _ (List.nodup_range.filter _), List.toFinset_filter, List.toFinset_range]
  simp

/-- **The prover's indicator is the polynomial's**, at a point off `V_m`. -/
theorem ind_eval_eq (hn : G.logN ≤ 32) (q : RecPiop.Block × ℕ) {x : E} (hx : ∀ j < G.N, x ≠ pi2Omega j) :
    (G.ind pi2Omega q).eval x =
      indFrom G.logN (∏ j ∈ G.compl q, (UniStatement.pointE (G.pairBase q) + UniStatement.pointE j))
        ((List.range G.N).filter fun j ↦ decide (G.InPair q j)) x := by
  have hz : zvAt G.logN x = ∏ j ∈ range G.N, (x + pi2Omega j) := by
    unfold zvAt
    rw [iterate_sq_eq, ← RecPiop.Circuit.zV_eval_eq G UniComplete.Domain.basisE hn x]
    unfold RecPiop.Circuit.zV
    rw [Polynomial.eval_prod]
    simp
  have hsplit := Finset.prod_filter_not_mul_prod_filter (range G.N) (G.InPair q) (fun j ↦ x + pi2Omega j)
  have hpos : (((List.range G.N).filter fun j ↦ decide (G.InPair q j)).map fun j ↦ x + UniStatement.pointE j).prod =
      ∏ j ∈ (range G.N).filter (G.InPair q), (x + pi2Omega j) := by
    rw [prod_filter_range]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [pi2Omega_eq]
  have hne : ∏ j ∈ (range G.N).filter (G.InPair q), (x + pi2Omega j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj ↦ fun h ↦
      hx j (mem_range.mp (mem_filter.mp hj).1) (CharTwo.add_eq_zero.mp h)
  have hc : ∏ j ∈ G.compl q, (UniStatement.pointE (G.pairBase q) + UniStatement.pointE j) =
      ∏ j ∈ G.compl q, (pi2Omega (G.pairBase q) + pi2Omega j) :=
    Finset.prod_congr rfl fun j _ ↦ by rw [pi2Omega_eq, pi2Omega_eq]
  unfold indFrom RecPiop.Circuit.ind
  rw [hz, hpos, hc, ← hsplit, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  unfold RecPiop.Circuit.compl
  field_simp

/-! ## The coset values -/

theorem size_wNov (w : ℕ → K) : (UniComplete.novelOfValuesK G.logN (wValues G w)).size = 2 ^ G.logN := by
  simp [UniComplete.novelOfValuesK, Bridge.Ntt.coefficients_size, wValues, RecPiop.Circuit.N]

theorem size_sigmaNov : (UniComplete.novelOfValuesE G.logN (sigmaValues G)).size = 2 ^ G.logN := by
  simp [ UniComplete.novelOfValuesE, Bridge.Ntt.coefficients_size, sigmaValues, RecPiop.Circuit.N]

theorem size_kappaNov : (UniComplete.novelOfValuesE G.logN (kappaValues G)).size = 2 ^ G.logN := by
  simp [ UniComplete.novelOfValuesE, Bridge.Ntt.coefficients_size, kappaValues, RecPiop.Circuit.N]

theorem size_hNovel (w : ℕ → K) (α β : E) : (hNovel G w α β).size = 2 ^ G.logN := by
  simp [hNovel, UniComplete.novelOfValuesE, Bridge.Ntt.coefficients_size, size_hValues]

theorem size_pColumn (w : ℕ → K) : (pColumn G w).size = 2 ^ G.logN := by
  simp [pColumn, RecPiop.Circuit.N]

theorem size_pNovel (w : ℕ → K) : (pNovel G w).size = 2 ^ G.logN := by
  simp [pNovel, Bridge.Ntt.coefficients_size, size_pColumn]

theorem size_pNovelE (w : ℕ → K) : ((pNovel G w).map ofK).size = 2 ^ G.logN := by
  rw [Array.size_map, size_pNovel]

/-- **`onCoset` is the novel polynomial at the coset's points.** -/
theorem onCoset_getD {m : ℕ} (hm : m + 1 ≤ 28) (c : Array E) (hc : c.size = 2 ^ m) {p : ℕ}
    (hp : p < 2 ^ (m + 1)) :
    (onCoset m c).getD p 0 = (UniKeccakComplete.AlgC.novP m fun j ↦ c.getD j 0).eval (cosetPoint m p) := by
  unfold onCoset
  rw [values_getD_novP hm _ _ Array.size_ofFn hp]
  unfold cosetPoint
  congr 1
  have hle : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [UniKeccakComplete.AlgC.novP_of_zero_above (b := m) (m + 1) _ (by omega) fun k hk1 hk2 ↦ by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp only [hk2, dite_true, Option.getD_some]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    rfl]
  refine UniKeccakComplete.AlgC.novP_congr m fun k hk ↦ ?_
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [show k < 2 ^ (m + 1) by omega, dite_true, Option.getD_some]

theorem cosetPoint_ne' {m p : ℕ} (hm : m + 1 < 28) (hp : p < 2 ^ (m + 1)) :
    ∀ j < 2 ^ m, cosetPoint m p ≠ pi2Omega j := fun _ hj ↦ cosetPoint_ne hm hp hj

/-- **A pair's formula at a coset point is its polynomial's value.** -/
theorem formulaAtCoset_eq (hV : G.Valid) (hm : G.logN + 1 < 28) (wP : E[X]) (wD : Array E) (γ : E) {p : ℕ}
    (hp : p < 2 ^ (G.logN + 1))
    (hw : ∀ p' < 2 ^ (G.logN + 1), wD.getD p' 0 = wP.eval (cosetPoint G.logN p'))
    {q : RecPiop.Block × ℕ} (hq' : q ∈ G.pairs) (c0 : E) (l : List ℕ) :
    formulaAtCoset G (q, c0, l) wD γ p = (G.formulaPoly pi2Omega wP γ q).eval (cosetPoint G.logN p) := by
  have hW : G.W ≤ 2 ^ (G.logN + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by have := hV.logW_lt; omega)
  unfold formulaAtCoset RecPiop.Circuit.formulaPoly
  rw [RecPiop.Role.value_eval, hw p hp]
  refine RecPiop.Role.value_congr _ γ (fun _ ↦ rfl) fun c hc ↦ ?_
  have hc' := RecPiop.Circuit.regionRole_reads_lt hV hq' hc
  have hk : q.2 < G.W := (RecPiop.Circuit.mem_pairs.mp hq').2.1
  have hkc : q.2 ^^^ c < G.W := Nat.xor_lt_two_pow hk hc'
  unfold RecPiop.cellPoly
  have hkc' : q.2 ^^^ c < 2 ^ (G.logN + 1) := lt_of_lt_of_le hkc hW
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, ← cosetPoint_xor hm hp hkc',
    hw (p ^^^ (q.2 ^^^ c)) (xor_lt_pow hp hkc')]

theorem intPairs_eq : G.intPairs = G.pairs.filter fun q ↦ (!(G.regionRole q.1 q.2).isPort) = true :=
  Finset.filter_congr fun q _ ↦ by simp

theorem portPairs_eq : G.portPairs = G.pairs.filter fun q ↦ (G.regionRole q.1 q.2).isPort = true := rfl

/-- **The prover's `P_v` at a coset point is `pushPolyV`'s value.** -/
theorem pvAtCoset_eq (hV : G.Valid) (hm : G.logN + 1 < 28) (wP : E[X]) (wD : Array E) (γ : E) {p : ℕ}
    (hp : p < 2 ^ (G.logN + 1))
    (hw : ∀ p' < 2 ^ (G.logN + 1), wD.getD p' 0 = wP.eval (cosetPoint G.logN p')) :
    pvAtCoset G (pairData G) G.logN wD γ p = (G.pushPolyV pi2Omega wP γ).eval (cosetPoint G.logN p) := by
  have hn : G.logN ≤ 32 := by omega
  unfold pvAtCoset RecPiop.Circuit.pushPolyV pairData
  rw [Polynomial.eval_add, Polynomial.eval_finsetSum, intPairs_eq,
    sum_pairs_filter (fun q ↦ !(G.regionRole q.1 q.2).isPort), hw p hp]
  simp only [List.filter_map, List.map_map, Function.comp_def]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun q hq ↦ ?_)
  have hq' := mem_pairsList.mp (List.mem_filter.mp hq).1
  rw [Polynomial.eval_mul, Polynomial.eval_add, ind_eval_eq hn q (cosetPoint_ne' hm hp),
    formulaAtCoset_eq hV hm wP wD γ hp hw hq']

/-- **The prover's `T` at a coset point is `tPoly`'s value**, for `phi` taking `Φ`'s values there. -/
theorem tAtCoset_eq (hV : G.Valid) (hm : G.logN + 1 < 28) (wP : E[X]) (wD : Array E) (γ : E) (phi : E → ℕ → E)
    (Φ : ℕ → E[X]) {p : ℕ} (hp : p < 2 ^ (G.logN + 1))
    (hw : ∀ p' < 2 ^ (G.logN + 1), wD.getD p' 0 = wP.eval (cosetPoint G.logN p'))
    (hphi : ∀ k, phi (cosetPoint G.logN p) k = (Φ k).eval (cosetPoint G.logN p)) :
    tAtCoset G (pairData G) G.logN wD γ phi p = (G.tPoly pi2Omega Φ wP γ).eval (cosetPoint G.logN p) := by
  have hn : G.logN ≤ 32 := by omega
  unfold tAtCoset RecPiop.Circuit.tPoly pairData
  rw [Polynomial.eval_finsetSum, portPairs_eq, sum_pairs_filter (fun q ↦ (G.regionRole q.1 q.2).isPort)]
  simp only [List.filter_map, List.map_map, Function.comp_def]
  refine congrArg List.sum (List.map_congr_left fun q hq ↦ ?_)
  have hq' := mem_pairsList.mp (List.mem_filter.mp hq).1
  rw [Polynomial.eval_mul, Polynomial.eval_add, ind_eval_eq hn q (cosetPoint_ne' hm hp),
    formulaAtCoset_eq hV hm wP wD γ hp hw hq', hphi]

/-- **The prover's holes' indicator at a coset point is the polynomial's.** -/
theorem holeAtCoset_eq (hm : G.logN + 1 < 28) {p : ℕ} (hp : p < 2 ^ (G.logN + 1)) :
    holeAtCoset G (pairData G) G.logN p = (G.holePoly pi2Omega).eval (cosetPoint G.logN p) := by
  have hn : G.logN ≤ 32 := by omega
  unfold holeAtCoset RecPiop.Circuit.holePoly pairData
  rw [Polynomial.eval_finsetSum, portPairs_eq, sum_pairs_filter (fun q ↦ (G.regionRole q.1 q.2).isPort)]
  simp only [List.filter_map, List.map_map, Function.comp_def]
  refine congrArg List.sum (List.map_congr_left fun q _ ↦ ?_)
  rw [ind_eval_eq hn q (cosetPoint_ne' hm hp)]

/-- **The honest polynomials**: `w`'s, `h`'s and `P`'s of their novel coefficients. -/
structure HonestPolys (G : RecPiop.Circuit E) (w : ℕ → K) (α β : E) (S : RecPiop.SetupPolys G pi2Omega)
    (wP hP pP : E[X]) : Prop where
  wE : wP = UniKeccakComplete.AlgC.novP G.logN fun j ↦ (UniComplete.novelOfValuesK G.logN (wValues G w)).getD j 0
  σE : S.σP = UniKeccakComplete.AlgC.novP G.logN fun j ↦ (UniComplete.novelOfValuesE G.logN (sigmaValues G)).getD j 0
  κE : S.κP = UniKeccakComplete.AlgC.novP G.logN fun j ↦ (UniComplete.novelOfValuesE G.logN (kappaValues G)).getD j 0
  hE : hP = UniKeccakComplete.AlgC.novP G.logN fun j ↦ (hNovel G w α β).getD j 0
  pE : pP = UniKeccakComplete.AlgC.novP G.logN fun j ↦ ((pNovel G w).map ofK).getD j 0

theorem HonestPolys.wD {w : ℕ → K} {α β : E} {S : RecPiop.SetupPolys G pi2Omega} {wP hP pP : E[X]}
    (hH : HonestPolys G w α β S wP hP pP) (hm : G.logN + 1 < 28) :
    ∀ p' < 2 ^ (G.logN + 1), (onCoset G.logN (UniComplete.novelOfValuesK G.logN (wValues G w))).getD p' 0 =
      wP.eval (cosetPoint G.logN p') :=
  fun p' hp' ↦ by rw [onCoset_getD (by omega) _ (size_wNov w) hp', hH.wE]

theorem HonestPolys.pD {w : ℕ → K} {α β : E} {S : RecPiop.SetupPolys G pi2Omega} {wP hP pP : E[X]}
    (hH : HonestPolys G w α β S wP hP pP) (hm : G.logN + 1 < 28) {p : ℕ} (hp : p < 2 ^ (G.logN + 1)) :
    (onCoset G.logN ((pNovel G w).map ofK)).getD p 0 = pP.eval (cosetPoint G.logN p) := by
  rw [onCoset_getD (by omega) _ (size_pNovelE w) hp, hH.pE]

/-- **The prover's `q` values are the identity without `q` over `Z_V`**, at the polynomials of its novel
coefficients. -/
theorem qValues_eq (hV : G.Valid) (hm : G.logN + 1 < 28) (w : ℕ → K) (α β γ : E) (phi : E → ℕ → E)
    (Φ : ℕ → E[X]) (S : RecPiop.SetupPolys G pi2Omega) (wP hP pP : E[X]) (hH : HonestPolys G w α β S wP hP pP)
    {p : ℕ} (hp : p < 2 ^ (G.logN + 1))
    (hphi : ∀ k, phi (cosetPoint G.logN p) k = (Φ k).eval (cosetPoint G.logN p)) :
    (qValues G w α β γ phi).getD p 0 =
      (numPoly S Φ wP hP pP α β γ).eval (cosetPoint G.logN p) * (zvAt G.logN (cosetPoint G.logN p))⁻¹ := by
  have hm' : G.logN + 1 ≤ 28 := by omega
  have hσD : (onCoset G.logN (UniComplete.novelOfValuesE G.logN (sigmaValues G))).getD p 0 =
      S.σP.eval (cosetPoint G.logN p) := by
    rw [onCoset_getD hm' _ size_sigmaNov hp, hH.σE]
  have hκD : (onCoset G.logN (UniComplete.novelOfValuesE G.logN (kappaValues G))).getD p 0 =
      S.κP.eval (cosetPoint G.logN p) := by
    rw [onCoset_getD hm' _ size_kappaNov hp, hH.κE]
  have hhD : (onCoset G.logN (hNovel G w α β)).getD p 0 = hP.eval (cosetPoint G.logN p) := by
    rw [onCoset_getD hm' _ (size_hNovel w α β) hp, hH.hE]
  unfold qValues
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hp, dite_true, Option.getD_some]
  rw [hH.wD hm p hp, hσD, hhD, hκD, hH.pD hm hp, holeAtCoset_eq hm hp,
    tAtCoset_eq hV hm wP _ γ phi Φ hp (hH.wD hm) hphi]
  unfold numPoly RecPiop.Circuit.idPoly RecPiop.Circuit.dPushP RecPiop.dPullP
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
    zero_mul, add_zero]

/-- **The prover's `q_P` values are `(P + P_v)/Z_V`.** -/
theorem qpValues_eq (hV : G.Valid) (hm : G.logN + 1 < 28) (w : ℕ → K) (α β γ : E)
    (S : RecPiop.SetupPolys G pi2Omega) (wP hP pP : E[X]) (hH : HonestPolys G w α β S wP hP pP)
    {p : ℕ} (hp : p < 2 ^ (G.logN + 1)) :
    (qpValues G w γ).getD p 0 =
      (pP + G.pushPolyV pi2Omega wP γ).eval (cosetPoint G.logN p) * (zvAt G.logN (cosetPoint G.logN p))⁻¹ := by
  unfold qpValues
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hp, dite_true, Option.getD_some]
  rw [hH.pD hm hp, pvAtCoset_eq hV hm wP _ γ hp (hH.wD hm), Polynomial.eval_add]

/-! ## `q`'s and `q_P`'s novel coefficients -/

theorem size_qValues (w : ℕ → K) (α β γ : E) (phi : E → ℕ → E) :
    (qValues G w α β γ phi).size = 2 ^ (G.logN + 1) := by
  simp [qValues]

theorem size_qpValues (w : ℕ → K) (γ : E) : (qpValues G w γ).size = 2 ^ (G.logN + 1) := by
  simp [qpValues]

theorem zV_coset_ne (hm : G.logN + 1 < 28) {p : ℕ} (hp : p < 2 ^ (G.logN + 1)) :
    (G.zV pi2Omega).eval (cosetPoint G.logN p) ≠ 0 := by
  unfold RecPiop.Circuit.zV
  rw [Polynomial.eval_prod]
  exact Finset.prod_ne_zero_iff.mpr fun j hj ↦ by
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    exact fun h ↦ cosetPoint_ne hm hp (mem_range.mp hj) (CharTwo.add_eq_zero.mp h)

theorem zvAt_coset (hm : G.logN + 1 < 28) (p : ℕ) :
    zvAt G.logN (cosetPoint G.logN p) = (G.zV pi2Omega).eval (cosetPoint G.logN p) := by
  unfold zvAt
  rw [iterate_sq_eq, RecPiop.Circuit.zV_eval_eq G UniComplete.Domain.basisE (by omega)]

/-- **A polynomial `Z_V` divides is its quotient's `Z_V` multiple, at a coset point** (`q`'s values recover it). -/
theorem coset_div_eval (hm : G.logN + 1 < 28) {n : E[X]} (hn : n = G.zV pi2Omega * (n /ₘ G.zV pi2Omega)) {p : ℕ}
    (hp : p < 2 ^ (G.logN + 1)) :
    n.eval (cosetPoint G.logN p) * (zvAt G.logN (cosetPoint G.logN p))⁻¹ =
      (n /ₘ G.zV pi2Omega).eval (cosetPoint G.logN p) := by
  have hzne := zV_coset_ne hm hp
  rw [zvAt_coset hm]
  conv_lhs => rw [hn]
  rw [Polynomial.eval_mul]
  field_simp

/-- **`qNovel`'s polynomial is the honest `q`** `numPoly /ₘ Z_V`, for a witness, the non-holes' denominators nonzero,
`phi` taking `Φ`'s values on the coset. -/
theorem novP_qNovel (hV : G.Valid) (hm : G.logN + 1 < 28) (w : ℕ → K) (α β γ : E) (phi : E → ℕ → E)
    {pub : ℕ → List E} (Φ : ℕ → E[X]) (hΦdeg : ∀ k, (Φ k).natDegree < G.N)
    (hΦ : ∀ j < G.nP, (Φ (G.port j % G.W)).eval (pi2Omega (G.port j)) = G.pubFp γ pub j)
    (hphi : ∀ p < 2 ^ (G.logN + 1), ∀ k, phi (cosetPoint G.logN p) k = (Φ k).eval (cosetPoint G.logN p))
    (S : RecPiop.SetupPolys G pi2Omega) (wP hP pP qPP : E[X]) (hH : HonestPolys G w α β S wP hP pP)
    (hdef : G.defPoly pi2Omega wP pP qPP γ = 0) (hw : G.Satisfies pub (RecCircuit.emb w))
    (hwv : ∀ j < G.N, wP.eval (pi2Omega j) = RecCircuit.emb w j)
    (hhv : ∀ i < G.N, hP.eval (pi2Omega i) = (hValues G w α β).getD i 0)
    (hpull : ∀ i < G.N, ¬ G.IsHole i → RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i ≠ 0)
    (hpush : ∀ i < G.N, ¬ G.IsHole i → G.dPushV pi2Omega (RecCircuit.emb w) α β i ≠ 0) :
    (UniKeccakComplete.AlgC.novP (G.logN + 1) fun j ↦ (qNovel G w α β γ phi).getD j 0) =
      numPoly S Φ wP hP pP α β γ /ₘ G.zV pi2Omega := by
  have hn : G.logN ≤ 32 := by omega
  have hnum := num_eq_zV_mul hn fun i hi ↦
    numPoly_eval_omega hV hn S w hwv α β γ hΦ hdef hw hhv hpull hpush hi
  have hwdeg : wP.natDegree < G.N := by rw [hH.wE]; exact UniKeccakComplete.AlgC.novP_natDegree_lt _ _
  have hhdeg : hP.natDegree < G.N := by rw [hH.hE]; exact UniKeccakComplete.AlgC.novP_natDegree_lt _ _
  have hpdeg : pP.natDegree < G.N := by rw [hH.pE]; exact UniKeccakComplete.AlgC.novP_natDegree_lt _ _
  refine poly_eq_of_eval_eq (n := 2 ^ (G.logN + 1)) (UniKeccakComplete.AlgC.novP_natDegree_lt _ _) ?_
    (cosetPoint G.logN) (fun a ha b hb h ↦ cosetPoint_inj hm ha hb h) fun p hp ↦ ?_
  · have := natDegree_qHonest_lt hV S hΦdeg hwdeg hhdeg hpdeg α β γ
    calc _ < 2 * G.N := this
      _ = 2 ^ (G.logN + 1) := by unfold RecPiop.Circuit.N; ring
  · have hc : (UniKeccakComplete.AlgC.novP (G.logN + 1) fun j ↦ (qNovel G w α β γ phi).getD j 0).eval
          (cosetPoint G.logN p) = (qValues G w α β γ phi).getD p 0 :=
      novP_coefficients_eval (k := G.logN + 1) (by omega) (cosetOffset G.logN) (qValues G w α β γ phi)
        (size_qValues w α β γ phi) hp
    rw [hc, qValues_eq hV hm w α β γ phi Φ S wP hP pP hH hp (hphi p hp), coset_div_eval hm hnum hp]

/-! ### `q_P` is in `K` -/

theorem zvAt_mem {m : ℕ} {x : E} (hx : x ∈ subK) : zvAt m x ∈ subK := by
  unfold zvAt
  induction m with
  | zero => exact hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact add_mem (mul_mem ih ih) ih

theorem cosetPoint_mem (m p : ℕ) : cosetPoint m p ∈ subK := ofK_mem_subK _

theorem pointE_mem (i : ℕ) : UniStatement.pointE i ∈ subK := ofK_mem_subK _

theorem onCoset_mem {m : ℕ} (c : Array E) (hcs : c.size = 2 ^ m) (hc : ∀ j < 2 ^ m, c.getD j 0 ∈ subK) (p : ℕ) :
    (onCoset m c).getD p 0 ∈ subK := by
  by_cases hp : p < 2 ^ (m + 1)
  · unfold onCoset
    refine values_mem_subK _ _ Array.size_ofFn (fun i hi ↦ ?_) hp
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp only [hi, dite_true, Option.getD_some]
    by_cases hj : i < 2 ^ m
    · exact hc i hj
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      exact zero_mem _
  · have hs : (onCoset m c).size = 2 ^ (m + 1) := by
      unfold onCoset
      rw [Bridge.Ntt.values_size, Array.size_ofFn]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    exact zero_mem _

theorem wD_mem (w : ℕ → K) (p : ℕ) :
    (onCoset G.logN (UniComplete.novelOfValuesK G.logN (wValues G w))).getD p 0 ∈ subK :=
  onCoset_mem _ (size_wNov w) (fun j _ ↦ by
    unfold UniComplete.novelOfValuesK
    rw [UniKeccakComplete.AlgC.getD_map_ofK]
    exact ofK_mem_subK _) p

theorem indFrom_mem (m : ℕ) {c : E} (hc : c ∈ subK) (pos : List ℕ) {x : E} (hx : x ∈ subK) :
    indFrom m c pos x ∈ subK := by
  unfold indFrom
  refine mul_mem (zvAt_mem hx) (inv_mem (mul_mem hc (list_prod_mem fun y hy ↦ ?_)))
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
  exact add_mem hx (pointE_mem j)

theorem mem_pairData {d : (RecPiop.Block × ℕ) × E × List ℕ} (hd : d ∈ pairData G) : d.2.1 ∈ subK := by
  unfold pairData at hd
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp hd
  show (∏ j ∈ G.compl q, (UniStatement.pointE (G.pairBase q) + UniStatement.pointE j)) ∈ subK
  exact prod_mem fun j _ ↦ add_mem (pointE_mem _) (pointE_mem _)

/-- **`P_v` at a coset point is in `K`**, at a circuit over `K`. -/
theorem pvAtCoset_mem (hK : KCircuit G) (w : ℕ → K) (γ : E) (p : ℕ) :
    pvAtCoset G (pairData G) G.logN (onCoset G.logN (UniComplete.novelOfValuesK G.logN (wValues G w))) γ p ∈ subK := by
  unfold pvAtCoset
  refine add_mem (wD_mem w p) (list_sum_mem_subK fun x hx ↦ ?_)
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hd1, hd2⟩ := List.mem_filter.mp hd
  refine mul_mem (indFrom_mem _ (mem_pairData hd1) _ (cosetPoint_mem _ _)) (add_mem ?_ (wD_mem w p))
  unfold formulaAtCoset
  exact hK.value _ _ γ _ _ (by simpa using hd2) (wD_mem w p) fun _ ↦ wD_mem w _

/-- **`q_P`'s values on the coset are in `K`**, at a circuit over `K`. -/
theorem qpValues_mem (hK : KCircuit G) (w : ℕ → K) (γ : E) {p : ℕ} (hp : p < 2 ^ (G.logN + 1)) :
    (qpValues G w γ).getD p 0 ∈ subK := by
  unfold qpValues
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hp, dite_true, Option.getD_some]
  refine mul_mem (add_mem (onCoset_mem _ (size_pNovelE w) (fun j _ ↦ ?_) p) (pvAtCoset_mem hK w γ p))
    (inv_mem (zvAt_mem (cosetPoint_mem _ _)))
  rw [UniKeccakComplete.AlgC.getD_map_ofK]
  exact ofK_mem_subK _

/-- **`qpNovel`'s polynomial is the honest `q_P`** `(P + P_v) /ₘ Z_V`, at a circuit over `K`, `P` taking `P_v + κ`. -/
theorem novP_qpNovel (hK : KCircuit G) (hV : G.Valid) (hm : G.logN + 1 < 28) (w : ℕ → K) (α β γ : E)
    (S : RecPiop.SetupPolys G pi2Omega) (wP hP pP : E[X]) (hH : HonestPolys G w α β S wP hP pP)
    (hwv : ∀ j < G.N, wP.eval (pi2Omega j) = RecCircuit.emb w j)
    (hpv : ∀ i < G.N, pP.eval (pi2Omega i) = pvValue G w i) :
    (UniKeccakComplete.AlgC.novP (G.logN + 1) fun j ↦ ofK ((qpNovel G w γ).getD j 0)) =
      qpHonest wP pP γ (G := G) := by
  have hn : G.logN ≤ 32 := by omega
  have hwdeg : wP.natDegree < G.N := by rw [hH.wE]; exact UniKeccakComplete.AlgC.novP_natDegree_lt _ _
  have hpdeg : pP.natDegree < G.N := by rw [hH.pE]; exact UniKeccakComplete.AlgC.novP_natDegree_lt _ _
  have hA : ((qpValues G w γ).map fun x ↦ x.limb 0).map ofK = qpValues G w γ := by
    refine Array.ext (by simp) fun i h1 h2 ↦ ?_
    simp only [Array.getElem_map]
    have hi : i < 2 ^ (G.logN + 1) := by rw [← size_qpValues w γ]; exact h2
    have := qpValues_mem hK w γ hi
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2, Option.getD_some] at this
    exact limb_zero_of_mem this
  have hq : (UniKeccakComplete.AlgC.novP (G.logN + 1) fun j ↦ ofK ((qpNovel G w γ).getD j 0)) =
      UniKeccakComplete.AlgC.novP (G.logN + 1) fun j ↦
        (PcsQuotient.Domain.coefficients (G.logN + 1) (cosetOffset G.logN) (qpValues G w γ)).getD j 0 := by
    refine UniKeccakComplete.AlgC.novP_congr _ fun j hj ↦ ?_
    unfold qpNovel
    rw [coefficients_map_ofK _ _ (by rw [Array.size_map, size_qpValues]) hj, hA]
  have hnum := num_eq_zV_mul hn fun i hi ↦ defNum_eval_omega hV hn w hwv γ hpv hi
  rw [hq]
  refine poly_eq_of_eval_eq (n := 2 ^ (G.logN + 1)) (UniKeccakComplete.AlgC.novP_natDegree_lt _ _) ?_
    (cosetPoint G.logN) (fun a ha b hb h ↦ cosetPoint_inj hm ha hb h) fun p hp ↦ ?_
  · have := natDegree_qpHonest_lt hV hwdeg hpdeg γ (G := G)
    calc _ < 2 * G.N := this
      _ = 2 ^ (G.logN + 1) := by unfold RecPiop.Circuit.N; ring
  · have hc : (UniKeccakComplete.AlgC.novP (G.logN + 1) fun j ↦
          (PcsQuotient.Domain.coefficients (G.logN + 1) (cosetOffset G.logN) (qpValues G w γ)).getD j 0).eval
          (cosetPoint G.logN p) = (qpValues G w γ).getD p 0 :=
      novP_coefficients_eval (k := G.logN + 1) (by omega) (cosetOffset G.logN) (qpValues G w γ)
        (size_qpValues w γ) hp
    rw [hc, qpValues_eq hV hm w α β γ S wP hP pP hH hp, coset_div_eval hm hnum hp]
    rfl

end RecCompose

/-- info: 'RecCompose.novP_qNovel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.novP_qNovel

/-- info: 'RecCompose.novP_qpNovel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.novP_qpNovel
