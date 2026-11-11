-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `E2ECompleteness/ProverCircuit.lean` (the previous prover's cells and wiring, `circuitMatch`)
-- to the PCS claims' prover (`formal/Statement/PcsQuotient/Prover.lean`: `randomizeCells`, the random rows
-- filled), with `secretOf` from `E2ECompleteness/End.lean` and `cellOf_idx`, `pcsCircuit_sigma_size` from
-- `Bridge/Setup.lean`. Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`,
-- commit 6175f1a0, MIT OR Apache-2.0): the field `K`.
import E2ECompleteness.PcsStaging
import E2ECompleteness.PcsConstants
import Bridge.Circuit
import Bridge.Circuit.Outputs
import Completeness

/-!
# The Statement's cells and wiring are F0b's (the PCS claims)

The Statement's prover fills the circuit's `16` random rows (`randomizeCells`, `Prover.lean`; the cells
`cellsR`, `PcsDefs.lean`): the `X` and `V` cells of the `k`-th random row (`Circuit.randomRows`, row
`2^22 − 1 − k`, `Bridge.Circuit.membership_randomRows`) take `coins.rows k`. Everything goes through
`Bridge/Circuit`'s equalities (which never evaluate the `2^22`-row circuit):

* **the cells before** (`cells_getD`): `Bridge.Circuit.membership_cells` gives the Statement's cells as
  F0b's cell bits (`cellBitC`) of `PcsCircuit.Circuit.outputs` on the input bits of `secretTr w`, which is
  `(secretOf w).toPcs` (`secretTr_eq`); a cell bit is the bit of what the cell carries, every source a
  constant or a row of the circuit (`Bridge.Circuit.membership_slots`), on which `Circuit.outputs` is
  `deployedAssign` (`deployedAssign_eq_outputs`);
* **the random rows** (`randomize_getD`): the fold of `randomizeCells` over rows `N − 1 − k`, `k < n`,
  sets cells `4r` and `4r + 3` of each to its value and keeps the others;
* **the cells** (**`cellsR_getD`**): the cells with the random rows filled are F0b's
  `deployed.cellsRandomized` of the honest assignment, with `rndOf coins` on the random rows (F0b's
  `isRandom` holds exactly of the last `16`, `Completeness.deployed_isRandom_iff`), which
  `Completeness.honest_relation_deployed_random` shows satisfy the relation; `cellsR_size`;
* **the wiring** (`sigma_point`): the Statement's σ is F0b's (`Bridge.Circuit.membership_sigma`),
  `deployedSigma` moves cell `n` to cell `σ[n]` (`deployedSigma_cellOf`), and the Statement's point of
  `p < 2^24` is the deployed basis's point of `p`'s bits (`point_eq_deployed`); `sigma_size`,
  `wiringTable_eq`.
-/

open LeanVM.Parameters
open QuotientSecurity

set_option autoImplicit false

namespace E2ECompleteness.Pcs

-- The circuits are closed terms of `2^22` rows: nothing below may unfold them.
attribute [local irreducible] PcsQuotient.membership PcsCircuit.membership
  PcsQuotient.membershipBuilder PcsCircuit.membershipBuild

/-! ## The secret -/

/-- The Statement's secret as `formal/Completeness`'s (`Fin 32 → UInt8` bytes, `Fin 32` paths). -/
def secretOf (w : PcsQuotient.Secret) : Completeness.Secret where
  x i := w.x[i]
  siblings i j := (w.siblings.get ⟨i, by simp [PcsQuotient.depth]⟩)[j]
  directions i := w.directions.get ⟨i, by simp [PcsQuotient.depth]⟩

theorem ofFn_getElem_vector {α : Type} {n : ℕ} (v : Vector α n) :
    List.ofFn (fun i : Fin n => v[i]) = v.toList := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp

/-- **The two readings of a Statement secret as F0b's agree**: `Bridge`'s `secretTr` and
`formal/Completeness`'s `Secret.toPcs` of `secretOf`. -/
theorem secretTr_eq (w : PcsQuotient.Secret) : Bridge.Circuit.secretTr w = (secretOf w).toPcs := by
  obtain ⟨x, sib, dir⟩ := w
  have hx : x.toList = List.ofFn (secretOf ⟨x, sib, dir⟩).x := (ofFn_getElem_vector x).symm
  have hs : sib.toList.map Vector.toList =
      List.ofFn fun i : Fin 32 => List.ofFn ((secretOf ⟨x, sib, dir⟩).siblings i) := by
    apply List.ext_getElem (by rw [List.length_map, List.length_ofFn]; exact Vector.length_toList)
    intro k h1 h2
    simp only [List.getElem_map, Vector.getElem_toList, List.getElem_ofFn]
    rw [← ofFn_getElem_vector]
    rfl
  have hd : dir.toList = List.ofFn (secretOf ⟨x, sib, dir⟩).directions := by
    apply List.ext_getElem (by rw [List.length_ofFn]; exact Vector.length_toList)
    intro k h1 h2
    simp only [Vector.getElem_toList, List.getElem_ofFn]
    rfl
  show PcsCircuit.Secret.mk _ _ _ = PcsCircuit.Secret.mk _ _ _
  rw [hx, hs, hd]
  rfl

/-! ## The cells before the random rows -/

theorem cellOf_idx (x : Fin (22 + 2) → Bool) : QuotientSecurity.cellOf (Completeness.idx x) = x :=
  funext fun k ↦ Completeness.testBit_idx x k

/-- **A cell bit is the bit of what the cell carries**, for every circuit and outputs. -/
theorem cellBitC_eq_carried (c : PcsCircuit.Circuit) (v : Array Bool) (i : ℕ) :
    Bridge.Circuit.cellBitC c v i = PcsCircuit.readBit v (PcsCircuit.carried c.rows i) := by
  unfold Bridge.Circuit.cellBitC PcsCircuit.carried
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h | h | h | h <;>
    simp [h, PcsCircuit.readBit]

theorem two_pow_24 : (2 : ℕ) ^ (22 + 2) = 16777216 := by norm_num

theorem two_pow_22 : (2 : ℕ) ^ 22 = 4194304 := by norm_num

/-- What a cell of `membership` carries is a constant or a row of the circuit. -/
theorem slot_carried_lt {n : ℕ} (hn : n < 2 ^ (22 + 2)) :
    PcsCircuit.slot (PcsCircuit.carried PcsCircuit.membership.rows n) < 2 ^ 22 + 2 := by
  have hr : n / 4 < 2 ^ 22 := by rw [two_pow_24] at hn; rw [two_pow_22]; omega
  obtain ⟨hx, hy, hc⟩ := Bridge.Circuit.membership_slots (n / 4) hr
  unfold PcsCircuit.carried
  split_ifs
  · exact hx
  · exact hy
  · exact hc
  · show 2 + n / 4 < 2 ^ 22 + 2
    omega

theorem readBit_row (v : Array Bool) (r : ℕ) : PcsCircuit.readBit v (.row r) = v.getD r false :=
  rfl

theorem read_row (f : ℕ → Bool) (r : ℕ) : PcsCircuit.read f (.row r) = f r := rfl

theorem bitF_eq (x : Bool) : (bitF x : LeanVM.Parameters.K) = if x then 1 else 0 := rfl

/-- **On a constant or a row of the circuit, `Circuit.outputs` reads what `deployedAssign` reads.** -/
theorem readBit_eq (s : PcsCircuit.Secret) (src : PcsCircuit.Src)
    (h : PcsCircuit.slot src < 2 ^ 22 + 2) :
    PcsCircuit.readBit (PcsCircuit.Circuit.outputs PcsCircuit.membership s.inputs) src =
      PcsCircuit.read (natVal (deployedAssign s)) src := by
  cases src with
  | zero => rfl
  | one => rfl
  | row r =>
    have hr : r < 2 ^ 22 := by simp only [PcsCircuit.slot] at h; omega
    rw [readBit_row, read_row, natVal, dite_eq_left hr, deployedAssign_eq_outputs]

/-- The Statement's membership circuit has `2^22` rows. -/
theorem rows_size : (PcsQuotient.membership 22).rows.size = 2 ^ 22 := by
  have h := congrArg Array.size Bridge.Circuit.membership_rows
  rw [Array.size_map, PcsCircuit.membership_rows_size] at h
  exact h

/-- **The Statement's cells of a witness, before the random rows, are `formal/Completeness`'s honest
cells.** -/
theorem cells_getD (w : PcsQuotient.Secret) (b : Fin (22 + 2) → Bool) :
    (cellsOf w).getD (Completeness.idx b) 0 =
      Completeness.cellBitsK Completeness.deployedMembership (secretOf w) b := by
  have hcells : cellsOf w =
      PcsQuotient.Circuit.cells (PcsQuotient.membership 22) (PcsQuotient.membershipInputs w) := rfl
  have hn : Completeness.idx b < 2 ^ (22 + 2) := Completeness.idx_lt b
  have hlt : Completeness.idx b < 4 * (PcsQuotient.membership 22).rows.size := by
    rw [rows_size]
    rw [two_pow_24] at hn
    rw [two_pow_22]
    omega
  rw [hcells, Bridge.Circuit.membership_cells, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
    dite_eq_left hlt, Option.getD_some, secretTr_eq]
  show _ = bitF ((deployed.cellSrc b).bval (deployedAssign (secretOf w).toPcs))
  conv_rhs => rw [← cellOf_idx b]
  rw [deployed_cellSrc_cellOf hn, bval_ofSrc, cellBitC_eq_carried,
    readBit_eq _ _ (slot_carried_lt hn), bitF_eq]

/-- The cells before the random rows have `2^24` entries. -/
theorem cellsOf_size (w : PcsQuotient.Secret) : (cellsOf w).size = 4 * 2 ^ 22 := by
  have hcells : cellsOf w =
      PcsQuotient.Circuit.cells (PcsQuotient.membership 22) (PcsQuotient.membershipInputs w) := rfl
  rw [hcells, PcsQuotient.Circuit.cells, Array.size_ofFn, rows_size]

/-! ## The random rows -/

/-- The value `randomizeCells` writes into the `k`-th random row. -/
def rowValue (rows : Fin PcsQuotient.randomRows → K) (k : ℕ) : K :=
  if h : k < PcsQuotient.randomRows then rows ⟨k, h⟩ else 0

/-- One step of `randomizeCells`: the `X` and `V` cells of row `p.1` take the `p.2`-th value. -/
def rStep (rows : Fin PcsQuotient.randomRows → K) (cs : Array K) (p : ℕ × ℕ) : Array K :=
  (cs.setIfInBounds (4 * p.1) (rowValue rows p.2)).setIfInBounds (4 * p.1 + 3) (rowValue rows p.2)

theorem randomizeCells_eq (c : PcsQuotient.Circuit) (cells : Array K)
    (rows : Fin PcsQuotient.randomRows → K) :
    PcsQuotient.randomizeCells c cells rows = c.randomRows.zipIdx.foldl (rStep rows) cells := rfl

theorem rStep_size (rows : Fin PcsQuotient.randomRows → K) (cs : Array K) (p : ℕ × ℕ) :
    (rStep rows cs p).size = cs.size := by
  simp [rStep]

theorem getD_setIfInBounds (cs : Array K) (a : ℕ) (v : K) {i : ℕ} (hi : i < cs.size) :
    (cs.setIfInBounds a v).getD i 0 = if a = i then v else cs.getD i 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getD_eq_getD_getElem?]
  split_ifs with h1 h2
  · rfl
  · subst h1; exact absurd hi h2
  · rfl

theorem rStep_getD (rows : Fin PcsQuotient.randomRows → K) (cs : Array K) (p : ℕ × ℕ) {i : ℕ}
    (hi : i < cs.size) :
    (rStep rows cs p).getD i 0 =
      if 4 * p.1 + 3 = i then rowValue rows p.2
      else if 4 * p.1 = i then rowValue rows p.2 else cs.getD i 0 := by
  unfold rStep
  rw [getD_setIfInBounds _ _ _ (by rw [Array.size_setIfInBounds]; exact hi),
    getD_setIfInBounds _ _ _ hi]

theorem foldl_rStep_size (rows : Fin PcsQuotient.randomRows → K) :
    ∀ (l : List (ℕ × ℕ)) (cs : Array K), (l.foldl (rStep rows) cs).size = cs.size
  | [], _ => rfl
  | p :: l, cs => by rw [List.foldl_cons, foldl_rStep_size rows l, rStep_size]

/-- **The fold of `randomizeCells` over rows `N − 1 − k`, `k < n`**: cell `i` of row `N − 1 − k` with
`k < n` and role `X` or `V` holds the `k`-th value; every other cell is kept. -/
theorem randomize_getD (rows : Fin PcsQuotient.randomRows → K) (N : ℕ) (cs : Array K)
    (hs : cs.size = 4 * N) :
    ∀ n, n ≤ N → ∀ i, i < 4 * N →
      (((List.range n).map fun k ↦ (N - 1 - k, k)).foldl (rStep rows) cs).getD i 0 =
        if N - 1 - i / 4 < n ∧ (i % 4 = 0 ∨ i % 4 = 3) then rowValue rows (N - 1 - i / 4)
        else cs.getD i 0
  | 0, _, i, _ => by simp
  | n + 1, hn, i, hi => by
    have ih := randomize_getD rows N cs hs n (by omega) i hi
    rw [List.range_succ, List.map_append, List.foldl_append, List.map_singleton, List.foldl_cons,
      List.foldl_nil]
    have hsz : (((List.range n).map fun k ↦ (N - 1 - k, k)).foldl (rStep rows) cs).size = 4 * N := by
      rw [foldl_rStep_size, hs]
    rw [rStep_getD _ _ _ (by rw [hsz]; exact hi), ih]
    dsimp only
    by_cases h3 : 4 * (N - 1 - n) + 3 = i
    · rw [if_pos h3, if_pos (by omega), show N - 1 - i / 4 = n by omega]
    · rw [if_neg h3]
      by_cases h0 : 4 * (N - 1 - n) = i
      · rw [if_pos h0, if_pos (by omega), show N - 1 - i / 4 = n by omega]
      · rw [if_neg h0]
        by_cases hc : N - 1 - i / 4 < n ∧ (i % 4 = 0 ∨ i % 4 = 3)
        · rw [if_pos hc, if_pos (by omega)]
        · rw [if_neg hc, if_neg (by omega)]

/-- The random rows' list with its indices: row `N − 1 − k` is the `k`-th. -/
theorem zipIdx_rows (N : ℕ) :
    ((List.range PcsQuotient.randomRows).map fun k ↦ N - 1 - k).zipIdx =
      (List.range PcsQuotient.randomRows).map fun k ↦ (N - 1 - k, k) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp [List.getElem_zipIdx]

/-- **The cells with the random rows filled, entry by entry** (any cells of `2^24` entries). -/
theorem cellsR_getD_nat (cells₀ : Array K) (hs : cells₀.size = 4 * 2 ^ 22)
    (coins : PcsQuotient.Coins) {i : ℕ} (hi : i < 4 * 2 ^ 22) :
    (cellsR (PcsQuotient.membership PcsQuotient.logRows) cells₀ coins).getD i 0 =
      if 2 ^ 22 - 1 - i / 4 < 16 ∧ (i % 4 = 0 ∨ i % 4 = 3) then
        rowValue coins.rows (2 ^ 22 - 1 - i / 4)
      else cells₀.getD i 0 := by
  show (PcsQuotient.randomizeCells (PcsQuotient.membership 22) cells₀ coins.rows).getD i 0 = _
  rw [randomizeCells_eq, Bridge.Circuit.membership_randomRows, zipIdx_rows]
  exact randomize_getD coins.rows (2 ^ 22) cells₀ hs 16 (by norm_num) i hi

/-- **The cells with the random rows filled have `2^24` entries.** -/
theorem cellsR_size (w : PcsQuotient.Secret) (coins : PcsQuotient.Coins) :
    (cellsR (PcsQuotient.membership PcsQuotient.logRows) (cellsOf w) coins).size = 2 ^ 24 := by
  show (PcsQuotient.randomizeCells (PcsQuotient.membership 22) (cellsOf w) coins.rows).size = _
  rw [randomizeCells_eq, foldl_rStep_size, cellsOf_size]
  norm_num

/-- **The random rows' values as F0b's rows**: row `r` is the `(2^22 − 1 − r)`-th random row. -/
def rndOf (coins : PcsQuotient.Coins) : Fin (2 ^ 22) → K := fun r ↦
  if h : 2 ^ 22 - 1 - r.val < 16 then coins.rows ⟨2 ^ 22 - 1 - r.val, h⟩ else 0

/-- **The Statement's cells of a witness, the random rows filled, are F0b's randomized honest cells**:
`deployed.cellsRandomized` of the honest assignment with `rndOf coins` on the random rows (the cells
`Completeness.honest_relation_deployed_random` shows satisfy the relation). -/
theorem cellsR_getD (w : PcsQuotient.Secret) (coins : PcsQuotient.Coins) (b : Fin (22 + 2) → Bool) :
    (cellsR (PcsQuotient.membership PcsQuotient.logRows) (cellsOf w) coins).getD
        (Completeness.idx b) 0 =
      deployed.cellsRandomized (deployedAssign (secretOf w).toPcs) (rndOf coins) b := by
  have hn : Completeness.idx b < 4 * 2 ^ 22 := by
    have := Completeness.idx_lt b
    rw [two_pow_24] at this
    rw [two_pow_22]
    omega
  set i := Completeness.idx b with hi
  have hr : i / 4 < 2 ^ 22 := by omega
  have hk : i % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hb : rowCell ⟨i / 4, hr⟩ ⟨i % 4, hk⟩ = b := by
    rw [rowCell_eq_cellOf]
    show cellOf (4 * (i / 4) + i % 4) = b
    rw [Nat.div_add_mod, hi, cellOf_idx]
  obtain ⟨hrow, hrole⟩ := cellRow_rowCell ⟨i / 4, hr⟩ ⟨i % 4, hk⟩
  rw [hb] at hrow hrole
  rw [cellsR_getD_nat _ (cellsOf_size w) coins hn]
  unfold ChiCircuit.cellsRandomized
  rw [hrow, hrole]
  have hrand : deployed.isRandom ⟨i / 4, hr⟩ ↔ 2 ^ 22 - 1 - i / 4 < 16 := by
    rw [Completeness.deployed_isRandom_iff]
    simp only [PcsCircuit.randomRows]
    omega
  have hrole' : ((⟨i % 4, hk⟩ : Fin 4) = 0 ∨ (⟨i % 4, hk⟩ : Fin 4) = 3) ↔
      (i % 4 = 0 ∨ i % 4 = 3) := by
    simp only [Fin.ext_iff, Fin.val_zero]
    rfl
  by_cases hc : 2 ^ 22 - 1 - i / 4 < 16 ∧ (i % 4 = 0 ∨ i % 4 = 3)
  · rw [if_pos hc, if_pos ⟨hrand.mpr hc.1, hrole'.mpr hc.2⟩]
    unfold rowValue rndOf
    rw [dif_pos hc.1, dif_pos (show 2 ^ 22 - 1 - i / 4 < PcsQuotient.randomRows from hc.1)]
  · rw [if_neg hc, if_neg (fun h ↦ hc ⟨hrand.mp h.1, hrole'.mp h.2⟩), hi, cells_getD]
    rfl

/-- **The same in `E`** (the field of `Completeness.honest_relation_deployed_random`): the cells with the
random rows filled, embedded, are `deployed.cellsRandomized` with the embedded random values. -/
theorem cellsR_getD_E (w : PcsQuotient.Secret) (coins : PcsQuotient.Coins) (b : Fin (22 + 2) → Bool) :
    algebraMap K E ((cellsR (PcsQuotient.membership PcsQuotient.logRows) (cellsOf w) coins).getD
        (Completeness.idx b) 0) =
      deployed.cellsRandomized (deployedAssign (secretOf w).toPcs)
        (fun r ↦ algebraMap K E (rndOf coins r)) b := by
  rw [cellsR_getD]
  unfold ChiCircuit.cellsRandomized ChiCircuit.cellsOfBits bitF
  split_ifs <;> simp

/-! ## The wiring -/

/-- The statement's first `24` basis vectors are a Cantor basis (they are `deployedBasis`'s). -/
theorem cantorUpTo24 : Bridge.Ntt.CantorUpTo 24 :=
  ⟨by rw [betaAt_eq_deployedBasis 0 (by norm_num)]; exact deployedBasis.zero,
    fun k hk => by
      rw [betaAt_eq_deployedBasis (k + 1) hk, betaAt_eq_deployedBasis k (by omega)]
      exact deployedBasis.succ k hk⟩

/-- **The Statement's point of `p < 2^24` is the deployed basis's point of `p`'s bits.** -/
theorem point_eq_deployed {p : ℕ} (hp : p < 2 ^ (22 + 2)) :
    PcsQuotient.Domain.point p = deployedBasis.point (cellOf p) := by
  rw [Ntt.point_eq_cantor cantorUpTo24 (by decide) hp]
  unfold CantorBasis.point
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (Bridge.Ntt.cantorOf cantorUpTo24).β j = PcsQuotient.Domain.betaAt j from rfl,
    betaAt_eq_deployedBasis j j.isLt]
  rfl

/-- **The Statement's wiring's points are the deployed σ's.** -/
theorem sigma_point (b : Fin (22 + 2) → Bool) :
    PcsQuotient.Domain.point
        ((PcsQuotient.membership PcsQuotient.logRows).sigma.getD (Completeness.idx b) 0) =
      deployedBasis.point (deployedSigma b) := by
  have hσ : (PcsQuotient.membership PcsQuotient.logRows).sigma = PcsCircuit.membership.sigma :=
    Bridge.Circuit.membership_sigma
  have hn : Completeness.idx b < 2 ^ (22 + 2) := Completeness.idx_lt b
  have hm : PcsCircuit.membership.sigma.getD (Completeness.idx b) 0 < 2 ^ (22 + 2) := by
    have h := PcsCircuit.membership_sigma_lt (Completeness.idx b) (by rw [four_mul_rows]; exact hn)
    rwa [four_mul_rows] at h
  rw [hσ, point_eq_deployed hm, ← deployedSigma_cellOf hn, cellOf_idx]

/-- F0b's `σ` has `4 · 2^22 = 2^24` entries (`wiring_inv`'s invariant). -/
theorem pcsCircuit_sigma_size : PcsCircuit.membership.sigma.size = 2 ^ 24 := by
  obtain ⟨st, hst, hinv⟩ :=
    PcsCircuit.wiring_inv PcsCircuit.membership.rows PcsCircuit.membership_hsrc
  rw [PcsCircuit.membership_sigma, ← hst, hinv.sigma_size, PcsCircuit.membership_rows_size]
  rfl

/-- **The Statement's σ has `2^24` entries.** -/
theorem sigma_size : (PcsQuotient.membership PcsQuotient.logRows).sigma.size = 2 ^ 24 := by
  have hσ : (PcsQuotient.membership PcsQuotient.logRows).sigma = PcsCircuit.membership.sigma :=
    Bridge.Circuit.membership_sigma
  rw [hσ]
  exact pcsCircuit_sigma_size

/-- **The wiring table** is the coefficients of the σ-points (`m = 24` variables). -/
theorem wiringTable_eq : (PcsQuotient.membership PcsQuotient.logRows).wiringTable =
    PcsQuotient.Domain.coefficients 24 0
      ((PcsQuotient.membership PcsQuotient.logRows).sigma.map PcsQuotient.Domain.point) := by
  rw [PcsQuotient.Circuit.wiringTable, membership_logRows]

end E2ECompleteness.Pcs

/-- info: 'E2ECompleteness.Pcs.cellsR_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.cellsR_getD

/-- info: 'E2ECompleteness.Pcs.cellsR_getD_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.cellsR_getD_E

/-- info: 'E2ECompleteness.Pcs.cellsR_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.cellsR_size

/-- info: 'E2ECompleteness.Pcs.sigma_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.sigma_point

/-- info: 'E2ECompleteness.Pcs.sigma_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.sigma_size

/-- info: 'E2ECompleteness.Pcs.wiringTable_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.wiringTable_eq
