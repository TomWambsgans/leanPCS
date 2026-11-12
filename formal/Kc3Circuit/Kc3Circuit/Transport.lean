-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Kc3Circuit.Honest
import Kc3.Cantor

/-!
# The deployed circuit as `Kc3` data, on a Cantor basis

`Kc3.Params.ofCantor B hm σ pins random` (`formal/Kc3/Cantor.lean`) takes the cells as `cantorT B 22 × Fin 4`, a
row the point `B(4 r)` (`QuotientSecurity.cantorRows`), its cells `B(4 r + c)`. The Statement's circuit numbers its
cells `4 r + c`. `idxE`: the cells by their bits, the bits as a number (`finFunctionFinEquiv`); `idx_eq`: cell
`(t, c)` is number `c + 4 · rowIdx t`.

* `deployedSigma`: the circuit's σ (`(membership 22).sigma`) on the cells, a permutation (`sigC` maps the cells
  `< 4 · 2^22` to themselves injectively); `deployedPins`: anchor rows `0 … 10`; `deployedRandom`: the last `16` rows;
  `deployedParams B hm`, the instance;
* **`poleCondition_deployed`**: its pole condition, from `Kc3Closed.pole_idx`;
* **`relation_of_sat_deployed`**: cells satisfying `Kc3.Params.Sat` at the instance, for the statement's pinned values
  (`stmtOf s k = ofK (anchorValues s.words k)`), spell a secret of `s`: the input rows' `V` cells read `= 1`.
-/

set_option linter.unusedSectionVars false

namespace Kc3Deployed

open PcsQuotient Kc3Closed Kc3Wiring LeanVM.Parameters QuotientSecurity Finset

attribute [local irreducible] PcsQuotient.membershipBuilder Kc3Circuit.membershipBuild PcsQuotient.membership

/-! ## Bits as numbers -/

/-- Bits as a number below `2^m`, little-endian. -/
def bitsNum {m : ℕ} : (Fin m → Bool) ≃ Fin (2 ^ m) :=
  (Equiv.piCongrRight fun _ => finTwoEquiv.symm).trans finFunctionFinEquiv

theorem finTwo_val (b : Bool) : ((finTwoEquiv.symm b : Fin 2) : ℕ) = if b then 1 else 0 := by
  cases b <;> rfl

theorem bitsNum_val {m : ℕ} (x : Fin m → Bool) :
    (bitsNum x : ℕ) = ∑ i : Fin m, (if x i then 1 else 0) * 2 ^ (i : ℕ) := by
  unfold bitsNum
  rw [Equiv.trans_apply, finFunctionFinEquiv_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← finTwo_val]
  rfl

theorem bitsNum_cons {m : ℕ} (b : Bool) (x : Fin m → Bool) :
    (bitsNum (Fin.cons b x : Fin (m + 1) → Bool) : ℕ) = (if b then 1 else 0) + 2 * (bitsNum x : ℕ) := by
  rw [bitsNum_val, bitsNum_val, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

variable {F : Type*} [Field F] [CharP F 2] [DecidableEq F] {N : ℕ} (B : CantorBasis F N) (hm : 22 + 2 ≤ N)

/-- The number of a row of the instance. -/
noncomputable def rowIdx (t : cantorT B 22) : ℕ := bitsNum ((cantorRows B hm).symm t)

theorem rowIdx_lt (t : cantorT B 22) : rowIdx B hm t < 2 ^ 22 := (bitsNum _).isLt

/-- The cells by their numbers. -/
noncomputable def idxE : cantorT B 22 × Fin 4 ≃ Fin (2 ^ (22 + 2)) := (cantorCells B hm).symm.trans bitsNum

theorem roleBits_num (c : Fin 4) : (if roleBit0 c then 1 else 0) + 2 * (if roleBit1 c then 1 else 0) = c.val := by
  fin_cases c <;> rfl

/-- **Cell `(t, c)` is number `c + 4 · rowIdx t`.** -/
theorem idx_eq (i : cantorT B 22 × Fin 4) : (idxE B hm i : ℕ) = i.2.val + 4 * rowIdx B hm i.1 := by
  obtain ⟨t, c⟩ := i
  unfold idxE cantorCells rowIdx
  simp only [Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Equiv.refl_symm, Equiv.refl_apply, Equiv.symm_symm, Prod.map]
  show (bitsNum (cellBits ((cantorRows B hm).symm t, c)) : ℕ) = _
  unfold cellBits
  simp only [Equiv.coe_fn_mk]
  rw [bitsNum_cons, bitsNum_cons, ← roleBits_num c]
  ring

theorem idx_lt (i : cantorT B 22 × Fin 4) : (idxE B hm i : ℕ) < 4 * 2 ^ 22 :=
  lt_of_lt_of_eq (idxE B hm i).isLt (by norm_num)

theorem idx_mod (i : cantorT B 22 × Fin 4) : (idxE B hm i : ℕ) % 4 = i.2.val := by
  rw [idx_eq]; have := i.2.isLt; omega

theorem idx_div (i : cantorT B 22 × Fin 4) : (idxE B hm i : ℕ) / 4 = rowIdx B hm i.1 := by
  rw [idx_eq]; have := i.2.isLt; omega

/-- The cell of a number below `4 · 2^22`. -/
noncomputable def cellOf (c : ℕ) (hc : c < 4 * 2 ^ 22) : cantorT B 22 × Fin 4 :=
  (idxE B hm).symm ⟨c, by norm_num at hc ⊢; omega⟩

theorem idx_cellOf (c : ℕ) (hc : c < 4 * 2 ^ 22) : (idxE B hm (cellOf B hm c hc) : ℕ) = c := by
  unfold cellOf; rw [Equiv.apply_symm_apply]

/-- The row of a number below `2^22`. -/
noncomputable def rowOf (r : ℕ) (hr : r < 2 ^ 22) : cantorT B 22 := (cellOf B hm (4 * r) (by omega)).1

theorem rowIdx_rowOf (r : ℕ) (hr : r < 2 ^ 22) : rowIdx B hm (rowOf B hm r hr) = r := by
  unfold rowOf
  rw [← idx_div, idx_cellOf]; omega

theorem rowIdx_injective : Function.Injective (rowIdx B hm) := by
  intro t t' h
  have h' : idxE B hm (t, 0) = idxE B hm (t', 0) := Fin.ext (by rw [idx_eq, idx_eq, h])
  exact (Prod.mk.inj ((idxE B hm).injective h')).1

theorem cell_ext {i j : cantorT B 22 × Fin 4} (h : (idxE B hm i : ℕ) = (idxE B hm j : ℕ)) : i = j :=
  (idxE B hm).injective (Fin.ext h)

/-! ## σ, the pins, the random rows -/

theorem sigC_injOn {c d : ℕ} (hc : c < 4 * 2 ^ 22) (hd : d < 4 * 2 ^ 22) (h : sigC c = sigC d) : c = d := by
  have hsz := rows_size
  rw [sigC_eq] at h
  exact sigma_inj _ _ cell_slots_lt (by rw [hsz]; exact hc) (by rw [hsz]; exact hd) h

/-- σ on the cells' numbers, a function of `Fin (4 · 2^22)`. -/
noncomputable def sigFin (c : Fin (2 ^ (22 + 2))) : Fin (2 ^ (22 + 2)) :=
  ⟨sigC c, by have := Kc3Closed.sigC_lt c (by have := c.isLt; norm_num at this ⊢; omega); norm_num at this ⊢; omega⟩

theorem sigFin_injective : Function.Injective sigFin := by
  intro c d h
  have h' : sigC c = sigC d := congrArg Fin.val h
  exact Fin.ext (sigC_injOn (by have := c.isLt; norm_num at this ⊢; omega)
    (by have := d.isLt; norm_num at this ⊢; omega) h')

/-- **The deployed wiring on the instance's cells.** -/
noncomputable def deployedSigma : Equiv.Perm (cantorT B 22 × Fin 4) :=
  (idxE B hm).symm.permCongr (Equiv.ofBijective sigFin sigFin_injective.bijective_of_finite)

theorem idx_sigma (i : cantorT B 22 × Fin 4) :
    (idxE B hm (deployedSigma B hm i) : ℕ) = sigC (idxE B hm i) := by
  unfold deployedSigma
  simp [Equiv.permCongr_apply, sigFin]

set_option maxHeartbeats 50000

theorem iter_zero' (f : ℕ → ℕ) (x : ℕ) : PcsCircuit.iter f 0 x = x := rfl

theorem iter_succ' (f : ℕ → ℕ) (k x : ℕ) : PcsCircuit.iter f (k + 1) x = PcsCircuit.iter f k (f x) := rfl

theorem idx_sigma_pow (i : cantorT B 22 × Fin 4) :
    ∀ k : ℕ, (idxE B hm ((deployedSigma B hm ^ k) i) : ℕ) = PcsCircuit.iter sigC k (idxE B hm i) := by
  intro k
  induction k generalizing i with
  | zero =>
    have e : (deployedSigma B hm ^ 0) i = i := by rw [pow_zero, Equiv.Perm.one_apply]
    rw [e, iter_zero']
  | succ k ih =>
    have e : (deployedSigma B hm ^ (k + 1)) i = (deployedSigma B hm ^ k) (deployedSigma B hm i) := by
      rw [pow_succ, Equiv.Perm.mul_apply]
    rw [e, ih, iter_succ', idx_sigma]

/-- The anchor rows `0 … 10`, the pins. -/
noncomputable def deployedPins : Fin Kc3.pinCount ↪ cantorT B 22 where
  toFun k := rowOf B hm k.val (by have := k.isLt; unfold Kc3.pinCount at this; omega)
  inj' := by
    intro a b h
    have := congrArg (rowIdx B hm) h
    simp only [rowIdx_rowOf] at this
    exact Fin.ext this

/-- The random rows: the last `16`. -/
noncomputable def deployedRandom : Finset (cantorT B 22) := univ.filter fun t => 2 ^ 22 - 16 ≤ rowIdx B hm t

/-- **The deployed instance**. -/
noncomputable def deployedParams : Kc3.Params F :=
  Kc3.Params.ofCantor B hm (deployedSigma B hm) (deployedPins B hm) (deployedRandom B hm)

theorem deployedParams_σ : (deployedParams B hm).σ = deployedSigma B hm := rfl

theorem errorCell_iff (i : cantorT B 22 × Fin 4) :
    (deployedParams B hm).ErrorCell i ↔ ErrIdx (idxE B hm i) := by
  have hpin : (∃ k, i = (deployedParams B hm).pinCell k) ↔ i.2.val = 2 ∧ rowIdx B hm i.1 < 11 := by
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨rfl, ?_⟩
      show rowIdx B hm (rowOf B hm k.val (by have := k.isLt; unfold Kc3.pinCount at this; omega)) < 11
      rw [rowIdx_rowOf]; exact k.isLt
    · rintro ⟨h2, h11⟩
      refine ⟨⟨rowIdx B hm i.1, h11⟩, ?_⟩
      apply Prod.ext
      · apply rowIdx_injective B hm
        show rowIdx B hm i.1 = rowIdx B hm (rowOf B hm (rowIdx B hm i.1) (by omega))
        rw [rowIdx_rowOf]
      · exact Fin.ext h2
  have hrand : i.1 ∈ (deployedParams B hm).random ↔ 2 ^ 22 - 16 ≤ rowIdx B hm i.1 := by
    show i.1 ∈ deployedRandom B hm ↔ _
    simp [deployedRandom]
  have h0 : i.2 = 0 ↔ i.2.val = 0 := Fin.ext_iff
  show (i.2 = 0 ∨ (∃ k, i = (deployedParams B hm).pinCell k) ∨ i.1 ∈ (deployedParams B hm).random) ↔ _
  rw [h0, hpin, hrand]
  unfold ErrIdx
  rw [idx_mod, idx_div]

/-- **The pole condition of the deployed instance**, proved (`Kc3Closed.pole_idx`). -/
theorem poleCondition_deployed : (deployedParams B hm).PoleCondition := by
  intro i hi
  have hne : sigC (idxE B hm i) ≠ (idxE B hm i : ℕ) := by
    intro h
    apply hi
    apply cell_ext B hm
    rw [deployedParams_σ]
    exact (idx_sigma B hm i).trans h
  obtain ⟨k, hk⟩ := Kc3Closed.pole_idx (idxE B hm i : ℕ) (idx_lt B hm i) hne
  refine ⟨k, fun h => hk ?_⟩
  rw [deployedParams_σ] at h
  have e := idx_sigma_pow B hm i k
  rw [← e]
  exact (errorCell_iff B hm _).mp h


/-! ## The relation -/

/-- The values of the cells' numbers, from values of the instance's cells. -/
noncomputable def wIdx (w : cantorT B 22 × Fin 4 → E) (c : ℕ) : E :=
  if hc : c < 4 * 2 ^ 22 then w (cellOf B hm c hc) else 0

theorem wIdx_idx (w : cantorT B 22 × Fin 4 → E) (i : cantorT B 22 × Fin 4) :
    wIdx B hm w (idxE B hm i) = w i := by
  unfold wIdx
  rw [dif_pos (idx_lt B hm i)]
  congr 1
  apply cell_ext B hm
  rw [idx_cellOf]

theorem cell_of_row (r : ℕ) (hr : r < 2 ^ 22) (c : Fin 4) :
    (idxE B hm (rowOf B hm r hr, c) : ℕ) = 4 * r + c := by
  rw [idx_eq, rowIdx_rowOf]; ring

/-- The statement's pinned values: its eight words, then `0`, `1`, `3`. -/
def stmtOf (s : Statement) : Kc3.Params.Stmt E := fun k => ofK (anchorValues s.words k.val)

theorem wIdx_row (w : cantorT B 22 × Fin 4 → E) (r : ℕ) (hr : r < 2 ^ 22) (c : Fin 4) :
    wIdx B hm w (4 * r + c) = w (rowOf B hm r hr, c) := by
  rw [← cell_of_row B hm r hr c, wIdx_idx]

end Kc3Deployed

namespace Kc3Deployed

open PcsQuotient Kc3Closed LeanVM.Parameters QuotientSecurity

attribute [local irreducible] PcsQuotient.membershipBuilder Kc3Circuit.membershipBuild PcsQuotient.membership

variable {N : ℕ} (B : CantorBasis E N) (hm : 22 + 2 ≤ N)

/-- The input bits read off cells: input row `r`'s `V` cell `= 1`. -/
noncomputable def inputBits (w : cantorT B 22 × Fin 4 → E) : List Bool :=
  (membership 22).inputs.toList.map fun r => decide (wIdx B hm w (4 * r + 3) = 1)

theorem gatesIdx_of_sat {s : Statement} {w : cantorT B 22 × Fin 4 → E}
    (h : (deployedParams B hm).Sat (stmtOf s) w) : GatesIdx (wIdx B hm w) := by
  intro r hr
  have e0 : wIdx B hm w (4 * r) = w (rowOf B hm r hr, 0) := wIdx_row B hm w r hr 0
  have e1 : wIdx B hm w (4 * r + 1) = w (rowOf B hm r hr, 1) := wIdx_row B hm w r hr 1
  have e2 : wIdx B hm w (4 * r + 2) = w (rowOf B hm r hr, 2) := wIdx_row B hm w r hr 2
  have e3 : wIdx B hm w (4 * r + 3) = w (rowOf B hm r hr, 3) := wIdx_row B hm w r hr 3
  rw [e0, e1, e2, e3]
  exact h.1 (rowOf B hm r hr)

theorem copiesIdx_of_sat {s : Statement} {w : cantorT B 22 × Fin 4 → E}
    (h : (deployedParams B hm).Sat (stmtOf s) w) : CopiesIdx (wIdx B hm w) := by
  intro c hc
  obtain ⟨i, rfl⟩ : ∃ i, (idxE B hm i : ℕ) = c := ⟨_, idx_cellOf B hm c hc⟩
  rw [← idx_sigma, wIdx_idx, wIdx_idx]
  exact h.2.1 i

theorem pinsIdx_of_sat {s : Statement} {w : cantorT B 22 × Fin 4 → E}
    (h : (deployedParams B hm).Sat (stmtOf s) w) : PinsIdx s (wIdx B hm w) := by
  intro k hk
  have e : wIdx B hm w (4 * k + 2) = w (rowOf B hm k (by omega), 2) := wIdx_row B hm w k (by omega) 2
  rw [e]
  exact h.2.2 ⟨k, hk⟩

/-- **Cells satisfying the deployed instance spell a secret**: for the statement's pinned values, the input rows'
`V` cells, read `= 1`, are a secret of `s`. -/
theorem relation_of_sat_deployed (s : Statement) (w : cantorT B 22 × Fin 4 → E)
    (h : (deployedParams B hm).Sat (stmtOf s) w) : Relation s (secretOfInputs (inputBits B hm w)) :=
  relation_of_sat (gatesIdx_of_sat B hm h) (copiesIdx_of_sat B hm h) (pinsIdx_of_sat B hm h)

/-- The honest prover's cells on the instance: the Statement's prover's cells (`randomizeCells` of the circuit's
cells for the secret's inputs) at each cell's number, in `E`. -/
noncomputable def honestCells (w : Secret) (rows : Fin randomWords → K) : cantorT B 22 × Fin 4 → E :=
  fun i => ofK ((randomizeCells (membership 22) ((membership 22).cells (membershipInputs w)) rows).getD (idxE B hm i) 0)

theorem honestCells_eq (w : Secret) (rows : Fin randomWords → K) (i : cantorT B 22 × Fin 4) :
    honestCells B hm w rows i = wH w rows (idxE B hm i) := rfl

/-- **The honest cells satisfy the deployed instance**, for the statement the secret proves and every random
words. -/
theorem sat_honest (w : Secret) (rows : Fin randomWords → K) :
    (deployedParams B hm).Sat (stmtOf w.statement) (honestCells B hm w rows) := by
  have hg := gates_honest w rows
  have hc := copies_honest w rows
  have hp := pins_honest w rows
  refine ⟨fun (x : cantorT B 22) => ?_, fun (i : cantorT B 22 × Fin 4) => ?_, fun k => ?_⟩
  · have v1 : ((1 : Fin 4) : ℕ) = 1 := rfl
    have v2 : ((2 : Fin 4) : ℕ) = 2 := rfl
    have v3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    have e0 : (idxE B hm (x, 0) : ℕ) = 4 * rowIdx B hm x := by rw [idx_eq, Fin.val_zero]; ring
    have e1 : (idxE B hm (x, 1) : ℕ) = 4 * rowIdx B hm x + 1 := by rw [idx_eq, v1]; ring
    have e2 : (idxE B hm (x, 2) : ℕ) = 4 * rowIdx B hm x + 2 := by rw [idx_eq, v2]; ring
    have e3 : (idxE B hm (x, 3) : ℕ) = 4 * rowIdx B hm x + 3 := by rw [idx_eq, v3]; ring
    have h := hg _ (rowIdx_lt B hm x)
    rw [← e1, ← e2, ← e3, ← e0] at h
    exact h
  · show wH w rows (idxE B hm (deployedSigma B hm i)) = wH w rows (idxE B hm i)
    have h := hc _ (idx_lt B hm i)
    rw [← idx_sigma] at h
    exact h
  · have hk : k.val < 2 ^ 22 := by have := k.isLt; unfold Kc3.pinCount at this; omega
    have e : (idxE B hm (rowOf B hm k.val hk, 2) : ℕ) = 4 * k.val + 2 := by
      rw [cell_of_row]; rfl
    have h := hp k.val k.isLt
    rw [← e] at h
    exact h

/-- **Completeness of the circuit**: for a secret of the statement `s`, the honest cells satisfy the deployed
instance at `s`'s pinned values. -/
theorem sat_honest_of_relation {s : Statement} {w : Secret} (h : Relation s w) (rows : Fin randomWords → K) :
    (deployedParams B hm).Sat (stmtOf s) (honestCells B hm w rows) := by
  rw [← show w.statement = s from h]
  exact sat_honest B hm w rows

end Kc3Deployed
