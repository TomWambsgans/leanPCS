-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Kc3Circuit.Pole
import Kc3.Protocol

/-!
# Cells that satisfy the copies and the pins, read through the rows

For values `w` of the cells (`c ↦ w c`, cell `4 r + role`) that σ keeps (`CopiesIdx`) and that hold the pinned values
(`PinsIdx`): a reading cell holds the value of what it reads (`read_cell`): `0`, `1`, `3`, or row `r'`'s `V` cell; so a
row whose gate holds (`GatesIdx`) has the gate's output on what it reads in its `V` cell (`out_eq`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 40000

namespace Kc3Closed

open PcsQuotient Kc3Bridge Kc3Wiring LeanVM.Parameters

attribute [local irreducible] PcsQuotient.membershipBuilder Kc3Circuit.membershipBuild PcsQuotient.membership

/-- The gates hold on every row (`Kc3.gate`: `V + Y + C + X·C = 0`). -/
def GatesIdx (w : ℕ → E) : Prop :=
  ∀ r < 2 ^ 22, Kc3.gate (w (4 * r)) (w (4 * r + 1)) (w (4 * r + 2)) (w (4 * r + 3)) = 0

/-- σ keeps the values: every copy holds. -/
def CopiesIdx (w : ℕ → E) : Prop := ∀ c < 4 * 2 ^ 22, w (sigC c) = w c

/-- The pinned cells hold the statement's words and the constants. -/
def PinsIdx (s : Statement) (w : ℕ → E) : Prop := ∀ k < 11, w (4 * k + 2) = ofK (anchorValues s.words k)

/-- The pinned constants: anchors `8`, `9`, `10` hold `0`, `1`, `3` in their `C` cells. -/
def PinsC (w : ℕ → E) : Prop := w (4 * 8 + 2) = 0 ∧ w (4 * 9 + 2) = 1 ∧ w (4 * 10 + 2) = ofK three

theorem sigC_lt (c : ℕ) (hc : c < 4 * 2 ^ 22) : sigC c < 4 * 2 ^ 22 := by
  have hc' : c < 4 * (membership 22).rows.size := by rw [rows_size]; exact hc
  have := sigma_lt _ _ cell_slots_lt hc'
  rw [← sigC_eq, rows_size] at this
  exact this

theorem iter_lt (c : ℕ) (hc : c < 4 * 2 ^ 22) : ∀ k, PcsCircuit.iter sigC k c < 4 * 2 ^ 22 := by
  intro k
  induction k generalizing c with
  | zero => exact hc
  | succ k ih => exact ih _ (sigC_lt c hc)

theorem copies_iter {w : ℕ → E} (hc : CopiesIdx w) (c : ℕ) (hcl : c < 4 * 2 ^ 22) :
    ∀ k, w (PcsCircuit.iter sigC k c) = w c := by
  intro k
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    show w (PcsCircuit.iter sigC k (sigC c)) = w c
    rw [ih _ (sigC_lt c hcl), hc c hcl]

/-- **Two cells of a slot hold one value.** -/
theorem copies_slot {w : ℕ → E} (hc : CopiesIdx w) {c d a : ℕ} (hcl : c < 4 * 2 ^ 22) (hdl : d < 4 * 2 ^ 22)
    (h1 : slotOfCell (membership 22).rows c = some a) (h2 : slotOfCell (membership 22).rows d = some a) :
    w c = w d := by
  have hsz := rows_size
  obtain ⟨k, hk⟩ := slot_reach _ _ cell_slots_lt (by rw [hsz]; exact hcl) (by rw [hsz]; exact hdl) h1 h2
  rw [← sigC_eq] at hk
  rw [← hk, copies_iter hc c hcl k]

/-- The value a source holds: `0`, `1`, `3`, or row `r`'s `V` cell (a free cell's: none, `0`). -/
def valE (w : ℕ → E) : Src → E
  | .zero => 0
  | .one => 1
  | .three => ofK three
  | .row r => w (4 * r + 3)
  | .free => 0

/-- The anchors of the constants read them as `C`. -/
theorem anchor_c (k : ℕ) (hk : 8 ≤ k) (hk' : k < 11) :
    slotOfCell (membership 22).rows (4 * k + 2) = some (k - 8) := by
  unfold slotOfCell
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show (4 * k + 2) / 4 = k by omega,
    rows_getD k (by omega), closedRow_anchor (by omega)]
  unfold anchorRow sources
  have e : ((List.range 8).map (fun J ↦ Src.row (qr.2.rows.size + 63 * J + 62)) ++ [Src.zero, Src.one, Src.three]).getD
      k .zero = [Src.zero, Src.one, Src.three].getD (k - 8) .zero := by
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp
  rw [e]
  interval_cases k <;> rfl

theorem anchorValues_const (s : Statement) :
    anchorValues s.words 8 = 0 ∧ anchorValues s.words 9 = 1 ∧ anchorValues s.words 10 = three := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [anchorValues, publicWords]

theorem pinsC_of {s : Statement} {w : ℕ → E} (hp : PinsIdx s w) : PinsC w := by
  have hv := anchorValues_const s
  refine ⟨?_, ?_, ?_⟩
  · rw [hp 8 (by norm_num), hv.1]; exact map_zero (algebraMap K E)
  · rw [hp 9 (by norm_num), hv.2.1]; exact map_one (algebraMap K E)
  · rw [hp 10 (by norm_num), hv.2.2]

/-- The cell whose value a source's slot holds: row `r`'s `V` cell, the `C` cell of anchor `8`, `9` or `10`. -/
def headCell : Src → ℕ
  | .zero => 34
  | .one => 38
  | .three => 42
  | .row r => 4 * r + 3
  | .free => 0

/-- **A reading cell holds what it reads.** -/
theorem read_cell {w : ℕ → E} (hc : CopiesIdx w) (hp : PinsC w) {c : ℕ} (hcl : c < 4 * 2 ^ 22)
    {src : Src} (hsrc : slotOfCell (membership 22).rows c = kSlot src) (hfree : src ≠ .free)
    (hrow : ∀ r', src = .row r' → r' < 2 ^ 22) : w c = valE w src := by
  cases src with
  | free => exact absurd rfl hfree
  | zero =>
    rw [copies_slot hc hcl (by norm_num) hsrc (anchor_c 8 (by norm_num) (by norm_num))]
    exact hp.1
  | one =>
    rw [copies_slot hc hcl (by norm_num) hsrc (anchor_c 9 (by norm_num) (by norm_num))]
    exact hp.2.1
  | three =>
    rw [copies_slot hc hcl (by norm_num) hsrc (anchor_c 10 (by norm_num) (by norm_num))]
    exact hp.2.2
  | row r' =>
    have := hrow r' rfl
    exact copies_slot hc hcl (by omega) hsrc (slotOfCell_out r')

theorem slot_x (r : ℕ) (hr : r < 2 ^ 22) :
    slotOfCell (membership 22).rows (4 * r) = kSlot (closedRow r).x := by
  unfold slotOfCell; rw [if_pos (by omega), show 4 * r / 4 = r by omega, rows_getD r hr]

theorem slot_y (r : ℕ) (hr : r < 2 ^ 22) :
    slotOfCell (membership 22).rows (4 * r + 1) = kSlot (closedRow r).y := by
  unfold slotOfCell; rw [if_neg (by omega), if_pos (by omega), show (4 * r + 1) / 4 = r by omega, rows_getD r hr]

theorem slot_c (r : ℕ) (hr : r < 2 ^ 22) :
    slotOfCell (membership 22).rows (4 * r + 2) = kSlot (closedRow r).c := by
  unfold slotOfCell
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show (4 * r + 2) / 4 = r by omega, rows_getD r hr]

theorem rowBelow_lt {s : Src} (h : RowBelow (qr.2.rows.size + 504) s) : ∀ r', s = .row r' → r' < 2 ^ 22 := by
  intro r' hr
  exact lt_of_lt_of_le (h r' hr) (le_trans size_lt_random (Nat.sub_le _ _))

/-- **A row's `V` cell holds the gate's output on what it reads**, its three sources not free. -/
theorem out_eq {w : ℕ → E} (hg : GatesIdx w) (hc : CopiesIdx w) (hp : PinsC w) (r : ℕ)
    (hr : r < 2 ^ 22) (hx : (closedRow r).x ≠ .free) (hy : (closedRow r).y ≠ .free) (hcf : (closedRow r).c ≠ .free) :
    w (4 * r + 3) = valE w (closedRow r).y + valE w (closedRow r).c + valE w (closedRow r).x * valE w (closedRow r).c := by
  have hb := closedRow_reads r
  have e0 := read_cell hc hp (by omega) (slot_x r hr) hx (rowBelow_lt hb.1)
  have e1 := read_cell hc hp (by omega) (slot_y r hr) hy (rowBelow_lt hb.2.1)
  have e2 := read_cell hc hp (by omega) (slot_c r hr) hcf (rowBelow_lt hb.2.2)
  have h := hg r hr
  unfold Kc3.gate at h
  rw [e0, e1, e2] at h
  have h' : w (4 * r + 3) = -(valE w (closedRow r).y + valE w (closedRow r).c +
      valE w (closedRow r).x * valE w (closedRow r).c) := by
    rw [← sub_eq_zero, sub_neg_eq_add, ← h]; ring
  rw [h', CharTwo.neg_eq]

end Kc3Closed
