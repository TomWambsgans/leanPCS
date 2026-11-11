-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Kc3Circuit.Cells
import Kc3Circuit.Words

/-!
# Cells satisfying the relation spell a secret of the statement

For values `w` of the cells of `PcsQuotient.membership 22` whose gates (`GatesIdx`), copies (`CopiesIdx`) and pins
(`PinsIdx s`) hold:

1. every built row's `V` cell holds a bit, the gate's output on bits of what it reads (`built_bit`; an input row
   reads its own output, so `v² = v`): the bits `vOf w` satisfy `Kc3Circuit`'s rows (`sat_vOf`), and so the wires of
   `y` and of the root hold the bits of `Secret.y` and `Secret.root` of the secret the input bits spell
   (`builder_facts`);
2. the packing rows hold Horner's rule on those wires (`pack_acc`), so the anchors' pins say that the packed words,
   the numbers the wires spell, are the statement's words (`word_bits`), bit for bit the bytes of `y` and of the root;
3. hence **`relation_of_sat`**: the secret the input rows' `V` cells spell (as `PcsQuotient.inputBitsOfStack` reads
   them, `= 1`) satisfies `PcsQuotient.Relation s`.
-/

set_option linter.unusedSectionVars false

namespace Kc3Closed

open PcsQuotient Kc3Bridge Kc3Wiring Kc3Words LeanVM.Parameters

attribute [local irreducible] PcsQuotient.membershipBuilder Kc3Circuit.membershipBuild PcsQuotient.membership

variable {w : ℕ → E} {s : Statement}

/-- The bits the `V` cells hold (`= 1`). -/
def vOf (w : ℕ → E) (r : ℕ) : Bool := decide (w (4 * r + 3) = 1)

/-- A bit cell. -/
def IsBit (a : E) : Prop := a = 0 ∨ a = 1

theorem valE_bit {src : Src} (h : src = .zero ∨ src = .one ∨ ∃ r', src = .row r' ∧ IsBit (w (4 * r' + 3))) :
    valE w src = bE (Kc3Circuit.read (vOf w) (srcTr src)) := by
  rcases h with rfl | rfl | ⟨r', rfl, hb⟩
  · simp [valE, bE, srcTr, Kc3Circuit.read]
  · simp [valE, bE, srcTr, Kc3Circuit.read]
  · simp only [valE, srcTr, Kc3Circuit.read, vOf]
    exact bE_bit _ hb

theorem srcs_not_free {src : Src} (h : src = .zero ∨ src = .one ∨ ∃ r', src = .row r' ∧ 11 ≤ r' ∧ r' < r) :
    src ≠ .free := by
  rcases h with rfl | rfl | ⟨r', rfl, -⟩ <;> simp

theorem S_lt_random : qr.2.rows.size ≤ 2 ^ 22 - 16 := le_trans (Nat.le_add_right _ _) size_lt_random

/-- **A built row's `V` cell holds a bit**, the gate's output on bits of what it reads. -/
theorem built_bit (hg : GatesIdx w) (hc : CopiesIdx w) (hp : PinsIdx s w) :
    ∀ r, 11 ≤ r → r < qr.2.rows.size → IsBit (w (4 * r + 3)) ∧
      vOf w r = Kc3Circuit.Row.eval (vOf w) ((bTr qr.2).rows.getD r .idle) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro h1 h2
  have hS := S_lt_random
  have hcr := closedRow_built (r := r) (by omega) (by omega) h2
  have hr : r < 2 ^ 22 := by omega
  rw [bTr_rows_getD]
  rcases builder_row r h1 h2 with ⟨-, hrow⟩ | ⟨-, hs⟩
  · -- an input row: `V = V + V + V V`
    rw [hrow] at hcr ⊢
    have ho := out_eq hg hc hp r hr (by rw [hcr]; simp) (by rw [hcr]; simp) (by rw [hcr]; simp)
    simp only [hcr, valE] at ho
    have hb := bit_of_input (w (4 * r + 3)) (by linear_combination (-1 : E) * ho + w (4 * r + 3) * two_eq_zero)
    refine ⟨hb, ?_⟩
    simp only [rowTr, srcTr, Kc3Circuit.Row.eval, Kc3Circuit.read, Kc3Circuit.gateBits]
    cases vOf w r <;> rfl
  · have hb : ∀ src ∈ [(qr.2.rows.getD r idle).x, (qr.2.rows.getD r idle).y, (qr.2.rows.getD r idle).c],
        valE w src = bE (Kc3Circuit.read (vOf w) (srcTr src)) := by
      intro src hsrc
      refine valE_bit ?_
      rcases hs src hsrc with h | h | ⟨r', rfl, h1', h2'⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨r', rfl, (ih r' h2' h1' (by omega)).1⟩)
    have m0 : (qr.2.rows.getD r idle).x ∈ [(qr.2.rows.getD r idle).x, (qr.2.rows.getD r idle).y,
      (qr.2.rows.getD r idle).c] := List.mem_cons_self ..
    have m1 : (qr.2.rows.getD r idle).y ∈ [(qr.2.rows.getD r idle).x, (qr.2.rows.getD r idle).y,
      (qr.2.rows.getD r idle).c] := List.mem_cons_of_mem _ (List.mem_cons_self ..)
    have m2 : (qr.2.rows.getD r idle).c ∈ [(qr.2.rows.getD r idle).x, (qr.2.rows.getD r idle).y,
      (qr.2.rows.getD r idle).c] := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have ho := out_eq hg hc hp r hr (by rw [hcr]; exact srcs_not_free (hs _ m0))
      (by rw [hcr]; exact srcs_not_free (hs _ m1)) (by rw [hcr]; exact srcs_not_free (hs _ m2))
    rw [hcr, hb _ m0, hb _ m1, hb _ m2, gate_bE] at ho
    refine ⟨by rw [ho]; unfold IsBit bE; split <;> simp, ?_⟩
    simp only [vOf, ho, decide_bE, rowTr, Kc3Circuit.Row.eval]
    rfl

/-- **The bits of the `V` cells satisfy the built rows.** -/
theorem sat_vOf (hg : GatesIdx w) (hc : CopiesIdx w) (hp : PinsIdx s w) : Kc3Circuit.Sat (vOf w) (bTr qr.2) :=
  fun r h1 h2 => (built_bit hg hc hp r h1 (by rw [bTr_size] at h2; exact h2)).2

/-! ## The wires and the packing rows -/

theorem valE_three : valE w .three = ofK three := rfl

theorem valE_row (r : ℕ) : valE w (.row r) = w (4 * r + 3) := rfl

/-- Bit `j` of public word `J`, the bit its wire holds. -/
def bJ (w : ℕ → E) (J j : ℕ) : Bool := Kc3Circuit.read (vOf w) (srcTr ((pw.getD J []).getD j .zero))

theorem valE_wire (hg : GatesIdx w) (hc : CopiesIdx w) (hp : PinsIdx s w) (J j : ℕ) (hJ : J < 8) (hj : j < 64) :
    valE w ((pw.getD J []).getD j .zero) = bE (bJ w J j) := by
  unfold bJ
  refine valE_bit ?_
  rw [pw_getD J j hJ hj]
  have h := wire_cases _ (wire_index_lt J j hj)
  have key : ∀ src : Src, (src = .zero ∨ src = .one ∨ ∃ r', src = .row r' ∧ 11 ≤ r' ∧ r' < qr.2.rows.size) →
      src = .zero ∨ src = .one ∨ ∃ r', src = .row r' ∧ IsBit (w (4 * r' + 3)) := by
    intro src hs
    rcases hs with h | h | ⟨r', rfl, h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨r', rfl, (built_bit hg hc hp r' h1 h2).1⟩)
  split
  · exact key _ (h _ (List.mem_cons_self ..))
  · exact key _ (h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem src_not_free_wire (J j : ℕ) (hJ : J < 8) (hj : j < 64) : (pw.getD J []).getD j .zero ≠ .free := by
  rw [pw_getD J j hJ hj]
  have h := wire_cases _ (wire_index_lt J j hj)
  split
  · exact srcs_not_free (r := qr.2.rows.size) (h _ (List.mem_cons_self ..))
  · exact srcs_not_free (r := qr.2.rows.size) (h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

/-- Packing row `i` of word `J`. -/
theorem closedRow_packing (J i : ℕ) (hJ : J < 8) (hi : i < 63) :
    closedRow (qr.2.rows.size + 63 * J + i) = ⟨.three, (pw.getD J []).getD (62 - i) .zero,
      if i = 0 then (pw.getD J []).getD 63 .zero else .row (qr.2.rows.size + 63 * J + i - 1)⟩ := by
  have h11 := S_ge
  have hS := size_lt_random
  rw [closedRow_pack (by omega) (by omega) (by omega),
    show qr.2.rows.size + 63 * J + i - qr.2.rows.size = 63 * J + i by omega,
    packAll_getD pw _ J i pw_length (by rw [pw_len]; exact hJ) hi]

/-- **The packing rows compute Horner's rule** on the word's bits, from bit `63` down. -/
theorem pack_acc (hg : GatesIdx w) (hc : CopiesIdx w) (hp : PinsIdx s w) (J : ℕ) (hJ : J < 8) :
    ∀ i < 63, w (4 * (qr.2.rows.size + 63 * J + i) + 3) =
      ∑ t ∈ Finset.range (i + 2), bE (bJ w J (62 - i + t)) * X2 ^ t := by
  have hS := size_lt_random
  intro i
  induction i with
  | zero =>
    intro _
    have hcr := closedRow_packing J 0 hJ (by norm_num)
    simp only [if_true, Nat.sub_zero, Nat.add_zero] at hcr
    simp only [Nat.add_zero, Nat.sub_zero]
    have ho := out_eq hg hc hp (qr.2.rows.size + 63 * J) (by omega) (by rw [hcr]; simp)
      (by rw [hcr]; exact src_not_free_wire J _ hJ (by norm_num))
      (by rw [hcr]; exact src_not_free_wire J _ hJ (by norm_num))
    rw [hcr] at ho
    dsimp only at ho
    rw [valE_three] at ho
    rw [ho, valE_wire hg hc hp J 62 hJ (by norm_num), valE_wire hg hc hp J 63 hJ (by norm_num),
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    rw [← one_add_three]
    ring
  | succ i ih =>
    intro hi
    have hcr := closedRow_packing J (i + 1) hJ hi
    simp only [Nat.add_one_ne_zero, if_false] at hcr
    have ho := out_eq hg hc hp (qr.2.rows.size + 63 * J + (i + 1)) (by omega) (by rw [hcr]; simp)
      (by rw [hcr]; exact src_not_free_wire J _ hJ (by omega)) (by rw [hcr]; simp)
    rw [hcr] at ho
    dsimp only at ho
    rw [valE_three, valE_row] at ho
    rw [ho, valE_wire hg hc hp J (62 - (i + 1)) hJ (by omega), show qr.2.rows.size + 63 * J + (i + 1) - 1 =
      qr.2.rows.size + 63 * J + i by omega, ih (by omega)]
    have hR : ∑ t ∈ Finset.range (i + 1 + 2), bE (bJ w J (62 - (i + 1) + t)) * X2 ^ t =
        bE (bJ w J (62 - (i + 1))) + X2 * ∑ t ∈ Finset.range (i + 2), bE (bJ w J (62 - i + t)) * X2 ^ t := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      have e : ∀ t ∈ Finset.range (i + 2), bE (bJ w J (62 - (i + 1) + (t + 1))) * X2 ^ (t + 1) =
          X2 * (bE (bJ w J (62 - i + t)) * X2 ^ t) := fun t _ => by
        rw [show 62 - (i + 1) + (t + 1) = 62 - i + t by omega, pow_succ]; ring
      rw [Finset.sum_congr rfl e, pow_zero, mul_one, add_comm]
      simp only [Nat.add_zero]
    rw [hR, ← one_add_three]
    ring

end Kc3Closed
