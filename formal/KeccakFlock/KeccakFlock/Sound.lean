-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import KeccakFlock.Block

/-!
# Soundness of the Keccak-f block

`step_of_holds`: every block of a column satisfying `BlockR1CS.BatchHolds r1cs cpos (bitTable c)` holds
`keccakF1600` of its input port words (`inSlot l`, word `4l + 2`) at its output port words (`outSlot l`, word `4l`):
the `step_of_holds` field of `KeccakVm.KeccakFlockSpec`.

The block the predicate reads is Boolean (`batchBlock_bitTable`: position `z + 64 w` is bit `z` of the block's word
`w`), so each row's two sums are parities of bits (`sum_ofBool`) and each position holds the AND of its row's two
parities (`holds_rows`). Round by round (`state_of_rows`, as `RecCircuit.d16_state` does for π2's D16v relations):
* the bits `b[i][z]` a round's forms sum are `πρθ` of the state before it (`parity_bForm`);
* the product rows give `t_j[x + 5y] = ¬b[x+1] ∧ b[x+2]`;
* the lin-id rows give the next state `b ⊕ t ⊕ ι`, which is `KeccakBits.round` (`RecCircuit.round_apply`);
so the output port holds the state after 24 rounds, `KeccakBits.keccakF` of the input port, which is leanerVM's
`keccakF1600` bit by bit (`PcsCircuit.keccakF_bits`).
-/

namespace KeccakFlock

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol Lv42.Protocol PcsCircuit PcsCircuit.Builder CompPoly
open ProductCircuit (ofBool ofBool_and ofBool_injective)

/-! ## Parities -/

/-- The parity of the bits `β` at the positions of `L`. -/
def parity (β : Pos → Bool) (L : List Pos) : Bool := L.foldr (fun p b ↦ β p ^^ b) false

theorem parity_nil (β : Pos → Bool) : parity β [] = false := rfl

theorem parity_cons (β : Pos → Bool) (p : Pos) (L : List Pos) : parity β (p :: L) = (β p ^^ parity β L) := rfl

theorem parity_append (β : Pos → Bool) (L₁ L₂ : List Pos) :
    parity β (L₁ ++ L₂) = (parity β L₁ ^^ parity β L₂) := by
  induction L₁ with
  | nil => simp [parity]
  | cons p L ih => rw [List.cons_append, parity_cons, parity_cons, ih, Bool.xor_assoc]

/-- In characteristic two, a sum of bits is the bit of their parity. -/
theorem sum_ofBool (β : Pos → Bool) (L : List Pos) :
    (L.map fun p ↦ ofBool E (β p)).sum = ofBool E (parity β L) := by
  induction L with
  | nil => simp [parity, ofBool]
  | cons p L ih =>
    rw [List.map_cons, List.sum_cons, ih, parity_cons]
    cases β p <;> cases parity β L <;> simp [ofBool, CharTwo.add_self_eq_zero]

/-- **A Boolean block satisfying the R1CS** holds at every position the AND of its row's two parities. -/
theorem holds_rows {z : CMlPolynomialEval E m} {β : Pos → Bool} (hz : ∀ p : Pos, z[p] = ofBool E (β p))
    (h : r1cs.Holds z) (k : Pos) : β k = (parity β (row k).1 && parity β (row k).2) := by
  have e : ∀ L : List Pos, (L.map fun p ↦ z[p]).sum = ofBool E (parity β L) := fun L ↦ by
    rw [← sum_ofBool]
    exact congrArg List.sum (List.map_congr_left fun p _ ↦ hz p)
  have hk := h k
  rw [BlockR1CS.rows_fst, BlockR1CS.rows_snd] at hk
  change (∑ j, if xorMem (row k).1 j then z[j] else 0) * (∑ j, if xorMem (row k).2 j then z[j] else 0) = z[k]
    at hk
  rw [sum_ite_xorMem, sum_ite_xorMem, e, e, hz, ← ofBool_and] at hk
  exact (ofBool_injective hk).symm

/-! ## The rows at the layout's words -/

theorem stWord_lt {j l : ℕ} (hj : j ≤ 24) (hl : l < 25) : stWord j l < 2048 := by
  unfold stWord portWord aWord
  split_ifs <;> omega

theorem tWord_lt {j l : ℕ} (hj : j < 24) (hl : l < 25) : tWord j l < 2048 := by
  unfold tWord; omega

/-- The row of `t_j[l]`: the product `(1 + b[x+1], b[x+2])`. -/
theorem rowW_t {j l z : ℕ} (hj : j < 24) (hl : l < 25) :
    rowW (tWord j l) z =
      (cpos :: bForm j ((l % 5 + 1) % 5 + 5 * (l / 5)) z, bForm j ((l % 5 + 2) % 5 + 5 * (l / 5)) z) := by
  unfold rowW tWord
  rw [ite_eq_right (by omega), ite_eq_left (by omega), show (64 * (j + 2) + l) / 64 - 2 = j by omega,
    show (64 * (j + 2) + l) % 64 = l by omega]
  unfold roundRow
  rw [ite_eq_left hl]

/-- The row of lane `l` of the state after round `j`: the lin-id `(b[l] + t_j[l] + RC_j, 1)`, in a materialised
state word (`j < 23`) or in the output port's `X` word (`j = 23`). -/
theorem rowW_st {j l z : ℕ} (hj : j < 24) (hl : l < 25) :
    rowW (stWord (j + 1) l) z = (linForm j l z, [cpos]) := by
  unfold stWord
  rw [ite_eq_right (by omega)]
  by_cases h23 : j + 1 = 24
  · rw [ite_eq_left h23]
    unfold rowW portWord
    rw [ite_eq_left (by omega), show (4 * l + 0) / 4 = l by omega, show (4 * l + 0) % 4 = 0 by omega]
    unfold portRow
    rw [ite_eq_right (by decide), ite_eq_left hl, ite_eq_left rfl, show j = 23 by omega]
  · rw [ite_eq_right h23]
    unfold rowW aWord
    rw [ite_eq_right (by omega), ite_eq_left (by omega), show (64 * (j + 1 - 1 + 2) + 32 + l) / 64 - 2 = j by omega,
      show (64 * (j + 1 - 1 + 2) + 32 + l) % 64 = 32 + l by omega]
    unfold roundRow
    rw [ite_eq_right (by omega), ite_eq_left (by omega), show 32 + l - 32 = l by omega]

/-! ## The rounds -/

/-- **The bits `b[i][z]` sums are `πρθ` of the state before the round.** -/
theorem parity_bForm {β : Pos → Bool} {j : ℕ} {s : Bits}
    (hS : ∀ l < 25, ∀ z < 64, β (pos (stWord j l) z) = s l z) {i : ℕ} (z : ℕ) (hi : i < 25) :
    parity β (bForm j i z) = KeccakBits.rhoPi (KeccakBits.theta s) i z := by
  have hp : piInv i < 25 := piInv_lt i hi
  obtain ⟨zp, hzp, e⟩ : ∃ zp, zp < 64 ∧ (z + 64 - rho (piInv i)) % 64 = zp := ⟨_, Nat.mod_lt _ (by decide), rfl⟩
  have hzr : (zp + 63) % 64 < 64 := Nat.mod_lt _ (by decide)
  simp only [bForm, parity_cons, parity_nil, KeccakBits.rhoPi, KeccakBits.theta, KeccakBits.thetaD,
    RecCircuit.thetaC_eq, e]
  rw [hS _ hp _ hzp, hS ((piInv i % 5 + 4) % 5) (by omega) _ hzp, hS ((piInv i % 5 + 4) % 5 + 5) (by omega) _ hzp,
    hS ((piInv i % 5 + 4) % 5 + 10) (by omega) _ hzp, hS ((piInv i % 5 + 4) % 5 + 15) (by omega) _ hzp,
    hS ((piInv i % 5 + 4) % 5 + 20) (by omega) _ hzp, hS ((piInv i % 5 + 1) % 5) (by omega) _ hzr,
    hS ((piInv i % 5 + 1) % 5 + 5) (by omega) _ hzr, hS ((piInv i % 5 + 1) % 5 + 10) (by omega) _ hzr,
    hS ((piInv i % 5 + 1) % 5 + 15) (by omega) _ hzr, hS ((piInv i % 5 + 1) % 5 + 20) (by omega) _ hzr]
  simp only [Bool.xor_false, Bool.xor_assoc]

/-- **The rows, round by round**: the state words before round `j` hold the state after `j` rounds of Keccak-f from
the input port. -/
theorem state_of_rows {β : Pos → Bool} (hc : β cpos = true)
    (hrow : ∀ k, β k = (parity β (row k).1 && parity β (row k).2)) :
    ∀ j ≤ 24, ∀ l < 25, ∀ z < 64,
      β (pos (stWord j l) z) = RecCircuit.stAfter (fun l z ↦ β (pos (stWord 0 l) z)) j l z := by
  intro j
  induction j with
  | zero => intro _ l _ z _; rfl
  | succ j ih =>
    intro hj l hl z hz
    have hS := ih (by omega)
    obtain ⟨x, y, hx, hy, rfl⟩ : ∃ x y, x < 5 ∧ y < 5 ∧ l = x + 5 * y :=
      ⟨l % 5, l / 5, Nat.mod_lt _ (by decide), by omega, by omega⟩
    have e1 : (x + 5 * y) % 5 = x := by omega
    have e2 : (x + 5 * y) / 5 = y := by omega
    have ht : β (pos (tWord j (x + 5 * y)) z) =
        (!KeccakBits.rhoPi (KeccakBits.theta (RecCircuit.stAfter (fun l z ↦ β (pos (stWord 0 l) z)) j))
            ((x + 1) % 5 + 5 * y) z &&
          KeccakBits.rhoPi (KeccakBits.theta (RecCircuit.stAfter (fun l z ↦ β (pos (stWord 0 l) z)) j))
            ((x + 2) % 5 + 5 * y) z) := by
      rw [hrow, row_pos (tWord_lt (by omega) hl) hz, rowW_t (by omega) hl, parity_cons, hc, e1, e2,
        parity_bForm hS z (by omega), parity_bForm hS z (by omega), Bool.true_xor]
    rw [hrow, row_pos (stWord_lt hj hl) hz, rowW_st (by omega) hl, RecCircuit.stAfter_succ _ _ (by omega),
      RecCircuit.round_apply _ _ x y z hx]
    simp only [linForm, parity_append, parity_cons, parity_nil, hc, Bool.xor_false, Bool.and_true]
    rw [parity_bForm hS z hl, ht, rcBit]
    generalize (keccakRC.getD j 0).toBitVec.getLsbD z = r
    have hrc : ∀ (P : Prop) [Decidable P] (r : Bool),
        parity β (if P ∧ r = true then [cpos] else []) = (decide P && r) := by
      intro P _ r
      by_cases hP : P <;> cases r <;> simp [hP, parity_cons, parity_nil, hc]
    rw [hrc, Bool.xor_assoc]

/-! ## The block a column's batch holds -/

/-- Bit `p mod 64` of the block's word `p / 64`. -/
def blockBit {κ : ℕ} (c : Column (KeccakVm.kWords + κ)) (t : Fin (2 ^ κ)) (p : Pos) : Bool :=
  (KeccakVm.kBlockCell c t ⟨p.val / 64, by
    have h : p.val < 131072 := p.isLt
    show p.val / 64 < 2048
    omega⟩).toBitVec.getLsbD (p.val % 64)

theorem blockBit_pos {κ : ℕ} (c : Column (KeccakVm.kWords + κ)) (t : Fin (2 ^ κ)) {w z : ℕ} (hw : w < 2048)
    (hz : z < 64) :
    blockBit c t (pos w z) =
      (KeccakVm.kBlockCell c t ⟨w, by rw [two_pow_kWords]; exact hw⟩).toBitVec.getLsbD z := by
  have hv := pos_val hw hz
  have h1 : (pos w z).val / 64 = w := by rw [hv]; omega
  have h2 : (pos w z).val % 64 = z := by rw [hv]; omega
  simp only [blockBit, h1, h2]

private theorem cubeSplit_symm {k n : ℕ} (j : Fin (2 ^ (k + n))) :
    (cubeSplit k n).symm j =
      (⟨j.val % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩,
        ⟨j.val / 2 ^ k, Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact j.isLt)⟩) := by
  rw [Equiv.symm_apply_eq, cubeSplit_apply]
  ext
  simp only [cubeIndex_val]
  exact (Nat.mod_add_div _ _).symm

/-- **The block the predicate reads** at batch index `t` holds bit `z` of word `w` of block `t` at `z + 64 w`. -/
theorem batchBlock_bitTable {κ : ℕ} (c : Column (KeccakVm.kWords + κ)) (t : Fin (2 ^ κ)) (p : Pos) :
    (BlockR1CS.batchBlock (s := Lv42.Parameters.Flock.kSkip) (m := KeccakVm.kWords) (bitTable c) t)[p] =
      ofBool E (blockBit c t p) := by
  simp only [BlockR1CS.batchBlock, bitTable, cubeSplit_symm, Vector.getElem_ofFn, cellBit, blockBit,
    KeccakVm.kBlockCell, ofBool, Vector.get_eq_getElem, Fin.getElem_fin]
  rfl

theorem lane_eq_getElem (a : KeccakState) {l : ℕ} (hl : l < 25) : Keccak.lane a l = a[l] := by
  simp [Keccak.lane, Array.getD_eq_getD_getElem?, hl]

/-- **Soundness**: every block of a column satisfying the predicate holds Keccak-f[1600] of its input port at its
output port. -/
theorem step_of_holds {κ : ℕ} (c : Column (KeccakVm.kWords + κ))
    (h : BlockR1CS.BatchHolds r1cs cpos (bitTable c)) (t : Fin (2 ^ κ)) :
    KeccakVm.kBlockState c t outSlot = keccakF1600 (KeccakVm.kBlockState c t inSlot) := by
  obtain ⟨hz, h1⟩ := h t
  have hzb := batchBlock_bitTable c t
  have hc : blockBit c t cpos = true := by
    rw [hzb] at h1
    exact ofBool_injective (h1.trans (by simp [ofBool]))
  have hst := state_of_rows hc (holds_rows hzb hz) 24 le_rfl
  have hin : BitsEq (laneBits (KeccakVm.kBlockState c t inSlot))
      (fun l z ↦ blockBit c t (pos (stWord 0 l) z)) := by
    intro l hl z hz
    simp only [laneBits, lane_eq_getElem _ hl, KeccakVm.kBlockState, Vector.getElem_ofFn]
    rw [blockBit_pos c t (stWord_lt (by omega) hl) hz]
    rfl
  apply Vector.ext
  intro l hl
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  have hk := (keccakF_bits _ l hl z hz).trans (RecCircuit.keccakF_congr hin l hl z hz)
  rw [← RecCircuit.stAfter_24, ← hst l hl z hz, laneBits, lane_eq_getElem _ hl,
    blockBit_pos c t (stWord_lt le_rfl hl) hz] at hk
  rw [hk]
  simp only [KeccakVm.kBlockState, Vector.getElem_ofFn]
  rfl

end KeccakFlock
