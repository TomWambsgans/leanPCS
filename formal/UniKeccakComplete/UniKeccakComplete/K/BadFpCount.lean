-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The reference shape's constants are
-- `formal/UniKeccakSound`'s (`IdsNum/Deployed.lean`, `keccakRef_eq`).
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/Core.lean` (`badFpCard_reference`) and
-- `Mapping.lean` (`fpOf_eq`, `capBound`).
import UniKeccakComplete.K.ProbHyp
import UniKeccakSound.IdsNum.Deployed

/-!
# The bad bus challenges at the reference Keccak shape: `BadFpCard`

`BadFp tr α β`: some divided tuple's fingerprint `β + Σ_s eq(α)_s τ_s` vanishes. For each `α` it pins `β` to one
value per divided tuple (`fpOf_eq'`), so the bad `β` are at most the divided tuples, and those are at most
`capBoundK shape = Σ_t pulls_t · 2^(h_t) + 2^lm + 2^lb` (every table full, `dividedTuples_length_le_cap`: a table's
active rows are among its `2^h_t` positions; no row-count hypothesis needed).

**`badFpCard_keccakRef`**: at `keccakRefShape` (heights `15 16 15 16 14 15`, memory `2^20`, bytecode `2^18`) the cap
is `capBoundK keccakRefShape = 3,227,648 < 2^22` (`capBoundK_keccakRef`; the pulls are `[5, 5, 3, 5, 5, 28]`,
`pullsK_eq`), so `BadFpCard D (2 ^ 28 - 1)` (and even `BadFpCard D (2 ^ 22 - 1)`, `badFpCard_keccakRef_22`). With the
reference's row counts (`[24260, 36229, 24626, 35812, 15509, 17712]`) the exact count is
`dividedBound_keccakRef = 2,439,584`.
-/

namespace UniKeccakComplete.BadFp

open UniComplete

open UniStatement UniKeccak UniKeccakSound LeanVM.Parameters LeanVM.Protocol

/-- A fingerprint is its challenge plus its weighted sum (`Mapping.fpOf_eq`). -/
theorem fpOf_eq' (weights : Array E) (beta : E) (tau : List E) :
    fpOf weights beta tau = beta + fpOf weights 0 tau := by
  have key : ∀ (l : List ℕ) (a : E), l.foldl (fun acc s ↦ acc + weights.getD s 0 * tau.getD s 0) a =
      a + l.foldl (fun acc s ↦ acc + weights.getD s 0 * tau.getD s 0) 0 := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons x l ih =>
      intro a
      simp only [List.foldl_cons]
      rw [ih (a + _), ih (0 + _)]
      ring
  simp only [fpOf]
  exact key _ beta

/-- The pulls of each table of the Keccak VM. -/
def pullsK (t : ℕ) : ℕ := (tablesKeccak.getD t default).flushes.pull.length

theorem pullsK_eq : (List.range 6).map pullsK = [5, 5, 3, 5, 5, 28] := by decide +kernel

/-- **The divided tuples' cap of a shape**: every table full. -/
def capBoundK (shape : UniStatement.Shape) : ℕ :=
  ((List.range 6).map fun t ↦ pullsK t * 2 ^ shape.heights.getD t 0).sum + 2 ^ shape.logMemory +
    2 ^ shape.logBytecode

/-- **The divided tuples' count from the row counts**: `Σ_t pulls_t · rows_t + 2^lm + 2^lb`. -/
def dividedBoundK (shape : UniStatement.Shape) (rows : List ℕ) : ℕ :=
  ((List.range 6).map fun t ↦ pullsK t * rows.getD t 0).sum + 2 ^ shape.logMemory + 2 ^ shape.logBytecode

/-- **At most `capBoundK` divided tuples**, for every trace (a table's active rows are among its `2^h_t`). -/
theorem dividedTuples_length_le_cap (tr : Trace) : (dividedTuples tr).length ≤ capBoundK tr.shape := by
  have hlen : (dividedTuples tr).length =
      ((List.range 6).map fun t ↦ pullsK t * (activeRows tr t).length).sum +
        2 ^ tr.shape.logMemory + 2 ^ tr.shape.logBytecode := by
    simp only [dividedTuples, List.length_append, List.length_flatMap, List.length_map, List.length_range,
      List.map_const', List.sum_replicate, smul_eq_mul, pullsK]
  rw [hlen, capBoundK]
  have hs : ((List.range 6).map fun t ↦ pullsK t * (activeRows tr t).length).sum ≤
      ((List.range 6).map fun t ↦ pullsK t * 2 ^ tr.shape.heights.getD t 0).sum := by
    refine List.sum_le_sum fun t _ ↦ Nat.mul_le_mul_left _ ?_
    unfold activeRows
    exact (List.length_filter_le _ _).trans (by rw [List.length_range]; rfl)
  omega

/-- **The reference shape's cap**: `3,227,648 < 2^22`. -/
theorem capBoundK_keccakRef : capBoundK keccakRefShape = 3227648 := by
  rw [UniKeccakSound.IdsNum.keccakRef_eq]
  decide +kernel

/-- The reference's exact count, at its row counts. -/
theorem dividedBound_keccakRef :
    dividedBoundK keccakRefShape [24260, 36229, 24626, 35812, 15509, 17712] = 2439584 := by
  rw [UniKeccakSound.IdsNum.keccakRef_eq]
  decide +kernel

/-- **At most `capBoundK` bad `β` for each `α`**, at every deployment. -/
theorem badFpCard_cap (D : KDeployment) : Prob.BadFpCard D (capBoundK D.shape) := by
  classical
  intro input rows q _ _ alphas
  refine ⟨((dividedTuples (honestTrace D input rows q)).map fun tau ↦ -fpOf (eqKernel alphas) 0 tau).toFinset,
    ?_, ?_⟩
  · calc _ ≤ ((dividedTuples (honestTrace D input rows q)).map fun tau ↦ -fpOf (eqKernel alphas) 0 tau).length :=
          List.toFinset_card_le _
      _ = (dividedTuples (honestTrace D input rows q)).length := List.length_map _
      _ ≤ capBoundK (honestTrace D input rows q).shape := dividedTuples_length_le_cap _
      _ = capBoundK D.shape := rfl
  · rintro b ⟨tau, htau, h0⟩
    rw [fpOf_eq'] at h0
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨tau, htau, neg_eq_of_add_eq_zero_left h0⟩

/-- `BadFpCard` is monotone in its bound. -/
theorem badFpCard_mono {D : KDeployment} {a b : ℕ} (h : Prob.BadFpCard D a) (hab : a ≤ b) : Prob.BadFpCard D b :=
  fun input rows q hfit hrel alphas ↦
    let ⟨T, hT, hmem⟩ := h input rows q hfit hrel alphas
    ⟨T, hT.trans hab, hmem⟩

/-- **At most `2^22 − 1` bad `β` for each `α`** at the reference Keccak shape. -/
theorem badFpCard_keccakRef_22 (D : KDeployment) (hD : D.shape = keccakRefShape) :
    Prob.BadFpCard D (2 ^ 22 - 1) :=
  badFpCard_mono (badFpCard_cap D) (by rw [hD, capBoundK_keccakRef]; norm_num)

/-- **At most `2^28 − 1` bad `β` for each `α`** at the reference Keccak shape (the premise's bound). -/
theorem badFpCard_keccakRef (D : KDeployment) (hD : D.shape = keccakRefShape) : Prob.BadFpCard D (2 ^ 28 - 1) :=
  badFpCard_mono (badFpCard_keccakRef_22 D hD) (by norm_num)

end UniKeccakComplete.BadFp

/-- info: 'UniKeccakComplete.BadFp.badFpCard_keccakRef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.BadFp.badFpCard_keccakRef
