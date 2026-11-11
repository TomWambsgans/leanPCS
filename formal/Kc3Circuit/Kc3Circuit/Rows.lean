-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Kc3Circuit.Closed

/-!
# The closed circuit's rows

`closedRow r`: row `r` of `PcsQuotient.membership 22`, an anchor, a random row, a built row or a packing row (or
idle); the circuit's fields (`membership_fields`); the built rows and the wires, read back from `builder_facts`.
-/

set_option linter.unusedSectionVars false

namespace Kc3Closed

open PcsQuotient Kc3Bridge

attribute [local irreducible] PcsQuotient.membershipBuilder Kc3Circuit.membershipBuild

/-! ## The closed circuit -/

/-- The public words' wires (`public_words`). -/
def pw : List (List Src) := publicWordWires qr.1.1 qr.1.2

theorem pw_length : ∀ bits ∈ pw, bits.length = 64 := by
  intro bits h
  unfold pw publicWordWires at h
  simp only [List.mem_map, List.mem_range] at h
  obtain ⟨J, _, rfl⟩ := h
  simp [wordBits]

theorem pw_len : pw.length = 8 := by simp [pw, publicWordWires, publicWords]

/-- The anchors' sources: the packed words, then the constants `0`, `1`, `3`. -/
def sources : List Src := (List.range 8).map (fun J ↦ Src.row (qr.2.rows.size + 63 * J + 62)) ++ [.zero, .one, .three]

/-- Anchor `k`: `(0, 0, s_k)`, or `(0, c, c)` for the constants one and three. -/
def anchorRow (k : ℕ) : Row :=
  ⟨.zero, if sources.getD k .zero = .one ∨ sources.getD k .zero = .three then sources.getD k .zero else .zero,
    sources.getD k .zero⟩

/-- **Row `r` of the closed circuit**, by its kind. -/
def closedRow (r : ℕ) : Row :=
  if r < 11 then anchorRow r
  else if 2 ^ 22 - 16 ≤ r then (RandomShape.of (2 ^ 22 - 1 - r)).row
  else if r < qr.2.rows.size then qr.2.rows.getD r idle
  else (packAll pw qr.2.rows.size).getD (r - qr.2.rows.size) idle

theorem membership_eq : membership 22 = finish 22 pw qr.2 := by
  rw [pw, qr_def]
  rfl

theorem run_pw : qrun (pw.mapM packWord) qr.2 =
    ((List.range 8).map (fun J ↦ .row (qr.2.rows.size + 63 * J + 62)),
      ⟨qr.2.rows ++ (packAll pw qr.2.rows.size).toArray, qr.2.inputs⟩) := by
  rw [run_packWords pw qr.2 pw_length, pw_len]

/-- `finish`'s rows, for general arguments. -/
theorem finish_rows_getD (logRows : ℕ) (pub : List (List Src)) (b : Builder) (r : ℕ) (hr : r < 2 ^ logRows) :
    (finish logRows pub b).rows.getD r idle =
      if r < 11 then
        (let c : Src := ((qrun (pub.mapM packWord) b).1 ++ [Src.zero, Src.one, Src.three]).getD r Src.zero
         (⟨.zero, (if c = .one ∨ c = .three then c else .zero), c⟩ : Row))
      else if 2 ^ logRows - 16 ≤ r then (RandomShape.of (2 ^ logRows - 1 - r)).row
      else (qrun (pub.mapM packWord) b).2.rows.getD r idle := by
  simp only [finish, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hr, dite_true, Option.getD_some]
  rfl

theorem finish_sigma (logRows : ℕ) (pub : List (List Src)) (b : Builder) :
    (finish logRows pub b).sigma = wiring logRows (finish logRows pub b).rows := rfl

theorem finish_inputs (logRows : ℕ) (pub : List (List Src)) (b : Builder) :
    (finish logRows pub b).inputs = (qrun (pub.mapM packWord) b).2.inputs := rfl

theorem finish_rows_size (logRows : ℕ) (pub : List (List Src)) (b : Builder) :
    (finish logRows pub b).rows.size = 2 ^ logRows := by simp [finish]

theorem append_getD_rows (a : Array Row) (l : List Row) (r : ℕ) :
    (a ++ l.toArray).getD r idle = if r < a.size then a.getD r idle else l.getD (r - a.size) idle := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append, List.getD_eq_getElem?_getD]
  split <;> simp

/-- **Row `r` of the closed circuit.** -/
theorem rows_getD (r : ℕ) (hr : r < 2 ^ 22) : (membership 22).rows.getD r idle = closedRow r := by
  rw [membership_eq, finish_rows_getD 22 pw qr.2 r hr, run_pw]
  unfold closedRow anchorRow sources
  by_cases h11 : r < 11
  · rw [if_pos h11, if_pos h11]
  · rw [if_neg h11, if_neg h11]
    by_cases hR : 2 ^ 22 - 16 ≤ r
    · rw [if_pos hR, if_pos hR]
    · rw [if_neg hR, if_neg hR]
      exact append_getD_rows _ _ _

theorem rows_size : (membership 22).rows.size = 2 ^ 22 := by
  rw [membership_eq, finish_rows_size]

theorem sigma_eq : (membership 22).sigma = wiring 22 (membership 22).rows := by
  rw [membership_eq, finish_sigma]

theorem inputs_eq : (membership 22).inputs = qr.2.inputs := by
  rw [membership_eq, finish_inputs, run_pw]

/-! ## The builder's rows, read back -/

theorem S_ge : 11 ≤ qr.2.rows.size := by rw [← bTr_size]; exact builder_facts.1.size

theorem S_le : qr.2.rows.size ≤ 4002123 := by
  rw [← bTr_size]; exact builder_facts.2.1.trans (le_of_eq Kc3Circuit.buildRows_eq)

theorem srcTr_eq_row {s : Src} {r : ℕ} (h : srcTr s = .row r) : s = .row r := by
  cases s <;> simp_all [srcTr]

/-- What a source a row may read (`Kc3Circuit.Below`) is: zero, one, or a row from `11` on before `r`. -/
theorem below_cases {r : ℕ} {s : Src} (h : Kc3Circuit.Below r (srcTr s)) :
    s = .zero ∨ s = .one ∨ ∃ r', s = .row r' ∧ 11 ≤ r' ∧ r' < r := by
  cases s with
  | zero => exact Or.inl rfl
  | one => exact Or.inr (Or.inl rfl)
  | three => exact h.elim
  | free => exact h.elim
  | row r' => exact Or.inr (Or.inr ⟨r', rfl, h⟩)

/-- **A built row**: an input reads its own output three times; another row reads zero, one or earlier rows from
`11` on. -/
theorem builder_row (r : ℕ) (h1 : 11 ≤ r) (h2 : r < qr.2.rows.size) :
    (r ∈ qr.2.inputs ∧ qr.2.rows.getD r idle = ⟨.row r, .row r, .row r⟩) ∨
      (r ∉ qr.2.inputs ∧ ∀ s ∈ [(qr.2.rows.getD r idle).x, (qr.2.rows.getD r idle).y, (qr.2.rows.getD r idle).c],
        s = .zero ∨ s = .one ∨ ∃ r', s = .row r' ∧ 11 ≤ r' ∧ r' < r) := by
  have hwf := builder_facts.1
  have h2' : r < (bTr qr.2).rows.size := by rw [bTr_size]; exact h2
  by_cases hin : r ∈ qr.2.inputs
  · refine Or.inl ⟨hin, ?_⟩
    have := hwf.input_row r hin
    rw [bTr_rows_getD] at this
    rcases hrow : qr.2.rows.getD r idle with ⟨x, y, c⟩
    rw [hrow] at this
    simp only [rowTr, Kc3Circuit.Row.mk.injEq] at this
    rw [srcTr_eq_row this.1, srcTr_eq_row this.2.1, srcTr_eq_row this.2.2]
  · refine Or.inr ⟨hin, ?_⟩
    have := hwf.order r h1 h2' hin
    rw [bTr_rows_getD] at this
    simp only [rowTr] at this
    intro s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact below_cases this.1
    · exact below_cases this.2.1
    · exact below_cases this.2.2

/-- **A wire of `y` or of the root**: zero, one, or a built row from `11` on. -/
theorem wire_cases (k : ℕ) (hk : k < 256) :
    (∀ s ∈ [qr.1.1.getD k .zero, qr.1.2.getD k .zero], s = .zero ∨ s = .one ∨ ∃ r', s = .row r' ∧ 11 ≤ r' ∧ r' < qr.2.rows.size) := by
  intro s hs
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
  have hv := builder_facts.2.2.2.1 k hk
  rw [← bTr_size]
  rcases hs with rfl | rfl
  · exact below_cases hv.1
  · exact below_cases hv.2

end Kc3Closed
