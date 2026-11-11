-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Kc3Circuit.Rows

/-!
# The pole condition of the deployed circuit, by its structure

`Circuit::errors_have_their_own_poles` (`circuit.rs`, `docs/membership/PROTOCOL.md`, "The pole lemma"): every cycle of
the wiring but a lone cell's holds a cell that is neither a row's first cell, nor a pinned one, nor a cell of a random
row. Here it is **proved** of `PcsQuotient.membership 22` from the structure of its rows and of `finish`'s wiring
(nothing evaluates the circuit):

* every row reads only rows below `S + 504` (`S` the built rows, then `504` packing rows), so never a random row
  (`closedRow_reads`);
* σ is the cyclic successor in each slot's list of cells and fixes a free cell (`Kc3Wiring`), so a cell `c` with
  `σ c ≠ c` is on its slot's cycle, which holds: for the slot of the constant `0`, `1` or `3`, the `Y` cell of anchor
  `8`, `9` or `10` (`(0, 0, 0)`, `(0, 1, 1)`, `(0, 3, 3)`); for the slot of a row `r'`, its `V` cell `4 r' + 3`, and
  `r'` is read by some cell, so it is no random row (`pole_idx`).
-/

set_option linter.unusedSectionVars false

namespace Kc3Closed

open PcsQuotient Kc3Bridge Kc3Wiring

attribute [local irreducible] PcsQuotient.membershipBuilder Kc3Circuit.membershipBuild PcsQuotient.membership

/-- A source reads no row at or above `B`. -/
def RowBelow (B : ℕ) (s : Src) : Prop := ∀ r', s = .row r' → r' < B

theorem rowBelow_const {B : ℕ} {s : Src} (h : s = .zero ∨ s = .one ∨ s = .three ∨ s = .free) : RowBelow B s := by
  intro r' hr; rcases h with rfl | rfl | rfl | rfl <;> cases hr

theorem rowBelow_of_cases {B : ℕ} {s : Src} (h : s = .zero ∨ s = .one ∨ ∃ r', s = .row r' ∧ 11 ≤ r' ∧ r' < B) :
    RowBelow B s := by
  rcases h with rfl | rfl | ⟨r', rfl, -, h⟩
  · exact rowBelow_const (Or.inl rfl)
  · exact rowBelow_const (Or.inr (Or.inl rfl))
  · intro r'' hr; cases hr; exact h

theorem RowBelow.mono {B B' : ℕ} {s : Src} (h : RowBelow B s) (hB : B ≤ B') : RowBelow B' s :=
  fun r' hr => lt_of_lt_of_le (h r' hr) hB

/-- The public words' wires, bit by bit (`public_words`). -/
theorem pw_getD (J j : ℕ) (hJ : J < 8) (hj : j < 64) :
    (pw.getD J []).getD j .zero =
      (if J < 4 then qr.1.1 else qr.1.2).getD (8 * (8 * (J % 4) + 7 - j / 8) + j % 8) .zero := by
  unfold pw publicWordWires
  have hJ' : J < publicWords := hJ
  have hj' : j < wordBits := hj
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ', Option.map_some,
    Option.getD_some, List.getElem?_range hj']

theorem wire_index_lt (J j : ℕ) (hj : j < 64) : 8 * (8 * (J % 4) + 7 - j / 8) + j % 8 < 256 := by
  have : J % 4 < 4 := Nat.mod_lt _ (by decide)
  omega

/-- A public word's bit wire reads zero, one, or a built row. -/
theorem pw_rowBelow (J j : ℕ) (hJ : J < 8) (hj : j < 64) : RowBelow qr.2.rows.size ((pw.getD J []).getD j .zero) := by
  rw [pw_getD J j hJ hj]
  have h := wire_cases _ (wire_index_lt J j hj)
  split
  · exact rowBelow_of_cases (h _ (List.mem_cons_self ..))
  · exact rowBelow_of_cases (h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem length_packAll_pw : (packAll pw qr.2.rows.size).length = 504 := by
  rw [length_packAll pw _ pw_length, pw_len]

theorem closedRow_anchor {r : ℕ} (h : r < 11) : closedRow r = anchorRow r := by
  unfold closedRow; rw [if_pos h]

theorem closedRow_random {r : ℕ} (h1 : ¬ r < 11) (h2 : 2 ^ 22 - 16 ≤ r) :
    closedRow r = (RandomShape.of (2 ^ 22 - 1 - r)).row := by
  unfold closedRow; rw [if_neg h1, if_pos h2]

theorem closedRow_built {r : ℕ} (h1 : ¬ r < 11) (h2 : ¬ 2 ^ 22 - 16 ≤ r) (h3 : r < qr.2.rows.size) :
    closedRow r = qr.2.rows.getD r idle := by
  unfold closedRow; rw [if_neg h1, if_neg h2, if_pos h3]

theorem closedRow_pack {r : ℕ} (h1 : ¬ r < 11) (h2 : ¬ 2 ^ 22 - 16 ≤ r) (h3 : ¬ r < qr.2.rows.size) :
    closedRow r = (packAll pw qr.2.rows.size).getD (r - qr.2.rows.size) idle := by
  unfold closedRow; rw [if_neg h1, if_neg h2, if_neg h3]

/-- **Every row of the closed circuit reads rows below `S + 504` only.** -/
theorem closedRow_reads (r : ℕ) :
    RowBelow (qr.2.rows.size + 504) (closedRow r).x ∧ RowBelow (qr.2.rows.size + 504) (closedRow r).y ∧
      RowBelow (qr.2.rows.size + 504) (closedRow r).c := by
  have hsrc : ∀ k, RowBelow (qr.2.rows.size + 504) (sources.getD k .zero) := by
    intro k r' hr
    unfold sources at hr
    rw [List.getD_eq_getElem?_getD] at hr
    by_cases hk : k < 8
    · rw [List.getElem?_append_left (by simpa using hk)] at hr
      simp only [List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.getD_some] at hr
      cases hr; omega
    · rw [List.getElem?_append_right (by simpa using hk)] at hr
      simp only [List.length_map, List.length_range] at hr
      rcases h : k - 8 with _ | _ | _ | m <;> simp [h] at hr
  by_cases h1 : r < 11
  · rw [closedRow_anchor h1]
    unfold anchorRow
    refine ⟨rowBelow_const (Or.inl rfl), ?_, hsrc r⟩
    split
    · exact hsrc r
    · exact rowBelow_const (Or.inl rfl)
  by_cases h2 : 2 ^ 22 - 16 ≤ r
  · rw [closedRow_random h1 h2]
    unfold RandomShape.row
    split <;> exact ⟨rowBelow_const (by simp), rowBelow_const (by simp), rowBelow_const (by simp)⟩
  by_cases h3 : r < qr.2.rows.size
  · rw [closedRow_built h1 h2 h3]
    rcases builder_row r (by omega) h3 with ⟨-, hrow⟩ | ⟨-, hs⟩
    · rw [hrow]
      exact ⟨fun r' h => by injection h with h; omega, fun r' h => by injection h with h; omega,
        fun r' h => by injection h with h; omega⟩
    · exact ⟨(rowBelow_of_cases (hs _ (List.mem_cons_self ..))).mono (by omega),
        (rowBelow_of_cases (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))).mono (by omega), (rowBelow_of_cases (hs _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))).mono (by omega)⟩
  · rw [closedRow_pack h1 h2 h3]
    by_cases hp : r - qr.2.rows.size < 504
    · have hJ : (r - qr.2.rows.size) / 63 < pw.length := by rw [pw_len]; omega
      have he : r - qr.2.rows.size = 63 * ((r - qr.2.rows.size) / 63) + (r - qr.2.rows.size) % 63 := by omega
      rw [he, packAll_getD pw _ _ _ pw_length hJ (Nat.mod_lt _ (by decide))]
      refine ⟨rowBelow_const (by simp), ?_, ?_⟩
      · exact (pw_rowBelow _ _ (by rw [← pw_len]; exact hJ) (by omega)).mono (by omega)
      · split
        · exact (pw_rowBelow _ _ (by rw [← pw_len]; exact hJ) (by omega)).mono (by omega)
        · intro r' h; injection h with h; omega
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [length_packAll_pw]; omega)]
      exact ⟨rowBelow_const (by simp [idle]), rowBelow_const (by simp [idle]), rowBelow_const (by simp [idle])⟩

/-- The built and packing rows end below the random rows. -/
theorem size_lt_random : qr.2.rows.size + 504 ≤ 2 ^ 22 - 16 := by
  have := S_le; norm_num; omega

/-! ## σ on the cells -/

theorem rows_getD' (r : ℕ) (hr : r < (membership 22).rows.size) :
    (membership 22).rows.getD r idle = closedRow r := rows_getD r (by rw [rows_size] at hr; exact hr)

/-- The slots the rows read are below the rows' number plus three. -/
theorem slots_lt : ∀ r < (membership 22).rows.size, ∀ a,
    (kSlot ((membership 22).rows.getD r idle).x = some a ∨ kSlot ((membership 22).rows.getD r idle).y = some a ∨
      kSlot ((membership 22).rows.getD r idle).c = some a) → a < (membership 22).rows.size + 3 := by
  intro r hr a ha
  rw [rows_getD' r hr] at ha
  have hb := closedRow_reads r
  have hsz := size_lt_random
  rw [rows_size]
  have key : ∀ s : Src, RowBelow (qr.2.rows.size + 504) s → kSlot s = some a → a < 2 ^ 22 + 3 := by
    intro s hs h
    cases s with
    | zero => cases h; omega
    | one => cases h; omega
    | three => cases h; omega
    | free => cases h
    | row r' => cases h; have := hs r' rfl; omega
  rcases ha with h | h | h
  · exact key _ hb.1 h
  · exact key _ hb.2.1 h
  · exact key _ hb.2.2 h

/-- The cells' slots are below the rows' number plus three. -/
theorem cell_slots_lt : ∀ c < 4 * (membership 22).rows.size, ∀ a,
    slotOfCell (membership 22).rows c = some a → a < (membership 22).rows.size + 3 := by
  intro c hc a h
  unfold slotOfCell at h
  have hr : c / 4 < (membership 22).rows.size := by omega
  by_cases h0 : c % 4 = 0
  · rw [if_pos h0] at h; exact slots_lt _ hr a (Or.inl h)
  rw [if_neg h0] at h
  by_cases h1 : c % 4 = 1
  · rw [if_pos h1] at h; exact slots_lt _ hr a (Or.inr (Or.inl h))
  rw [if_neg h1] at h
  by_cases h2 : c % 4 = 2
  · rw [if_pos h2] at h; exact slots_lt _ hr a (Or.inr (Or.inr h))
  rw [if_neg h2] at h
  cases h; omega

/-- The circuit's σ as a function (irreducible: unfolding it would evaluate the circuit). -/
irreducible_def sigC (c : ℕ) : ℕ := (membership 22).sigma.getD c 0

/-- **The circuit's σ is the joins'.** -/
theorem sigC_eq : sigC = sig ((joins (membership 22).rows (membership 22).rows.size).foldl
    (fun st p => PcsCircuit.join st p.1 p.2) (joins₀ (membership 22).rows.size)) := by
  funext c
  rw [sigC_def, sigma_eq, wiring_eq_joins 22 _ rows_size slots_lt, sig]

/-- A cell an error can sit on: a row's first cell, a pinned cell, a cell of a random row. -/
def ErrIdx (d : ℕ) : Prop := d % 4 = 0 ∨ (d % 4 = 2 ∧ d / 4 < 11) ∨ 2 ^ 22 - 16 ≤ d / 4

theorem slotOfCell_out (r : ℕ) : slotOfCell (membership 22).rows (4 * r + 3) = some (3 + r) := by
  unfold slotOfCell
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show (4 * r + 3) / 4 = r by omega]

/-- A reading cell's slot is a row's only if it reads that row. -/
theorem slot_read_row {c r' : ℕ} (hc : c < 4 * 2 ^ 22) (h3 : c % 4 ≠ 3)
    (h : slotOfCell (membership 22).rows c = some (3 + r')) : r' < qr.2.rows.size + 504 := by
  unfold slotOfCell at h
  have hr : c / 4 < 2 ^ 22 := by omega
  rw [rows_getD _ hr] at h
  have hb := closedRow_reads (c / 4)
  have key : ∀ s : Src, RowBelow (qr.2.rows.size + 504) s → kSlot s = some (3 + r') → r' < qr.2.rows.size + 504 := by
    intro s hs h
    cases s with
    | zero => simp only [kSlot, Option.some.injEq] at h; omega
    | one => simp only [kSlot, Option.some.injEq] at h; omega
    | three => simp only [kSlot, Option.some.injEq] at h; omega
    | free => simp [kSlot] at h
    | row r'' =>
      simp only [kSlot, Option.some.injEq] at h
      have e : r'' = r' := by omega
      subst e
      exact hs r'' rfl
  by_cases h0 : c % 4 = 0
  · rw [if_pos h0] at h; exact key _ hb.1 h
  rw [if_neg h0] at h
  by_cases h1 : c % 4 = 1
  · rw [if_pos h1] at h; exact key _ hb.2.1 h
  rw [if_neg h1] at h
  by_cases h2 : c % 4 = 2
  · rw [if_pos h2] at h; exact key _ hb.2.2 h
  omega

theorem anchor_y (k : ℕ) (hk : 8 ≤ k) (hk' : k < 11) :
    slotOfCell (membership 22).rows (4 * k + 1) = some (k - 8) := by
  unfold slotOfCell
  rw [if_neg (by omega), if_pos (by omega), show (4 * k + 1) / 4 = k by omega, rows_getD k (by omega)]
  unfold closedRow anchorRow sources
  rw [if_pos (by omega)]
  have e : ((List.range 8).map (fun J ↦ Src.row (qr.2.rows.size + 63 * J + 62)) ++ [Src.zero, Src.one, Src.three]).getD
      k .zero = [Src.zero, Src.one, Src.three].getD (k - 8) .zero := by
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp
  rw [e]
  interval_cases k <;> rfl

/-- **The pole condition**, on the cells' indices: a cell that σ moves reaches a cell that is no error cell. -/
theorem pole_idx (c : ℕ) (hc : c < 4 * 2 ^ 22) (hσ : sigC c ≠ c) :
    ∃ k, ¬ ErrIdx (PcsCircuit.iter sigC k c) := by
  have hsz := rows_size
  have hs := cell_slots_lt
  have hc' : c < 4 * (membership 22).rows.size := by rw [hsz]; exact hc
  rcases hslot : slotOfCell (membership 22).rows c with _ | a
  · have h := sigma_free _ _ hs hc' hslot
    rw [← sigC_eq] at h
    exact absurd h hσ
  have ha := hs c hc' a hslot
  rw [hsz] at ha
  -- the witness of the slot
  have reach : ∀ d, d < 4 * 2 ^ 22 → slotOfCell (membership 22).rows d = some a → ¬ ErrIdx d →
      ∃ k, ¬ ErrIdx (PcsCircuit.iter sigC k c) := by
    intro d hd hds hne
    obtain ⟨k, hk⟩ := slot_reach _ _ hs hc' (by rw [hsz]; exact hd) hslot hds
    rw [← sigC_eq] at hk
    exact ⟨k, by rw [hk]; exact hne⟩
  by_cases ha3 : a < 3
  · refine reach (4 * (a + 8) + 1) (by omega) ?_ (by unfold ErrIdx; omega)
    rw [anchor_y (a + 8) (by omega) (by omega)]
    congr 1
  · obtain ⟨r', rfl⟩ : ∃ r', a = 3 + r' := ⟨a - 3, by omega⟩
    have hr' : r' < qr.2.rows.size + 504 := by
      by_cases h3 : c % 4 = 3
      · -- `c` is the `V` cell of `r'`; σ moves it to another cell of the slot, a reading one.
        have hcv : c = 4 * r' + 3 := by
          have := slotOfCell_out (c / 4)
          rw [show 4 * (c / 4) + 3 = c by omega, hslot] at this
          simp only [Option.some.injEq] at this
          omega
        obtain ⟨hlt, hsl⟩ := sigma_slot _ _ hs hc' hslot
        rw [← sigC_eq] at hlt hsl
        rw [hsz] at hlt
        refine slot_read_row hlt (fun h => hσ ?_) hsl
        have := slotOfCell_out (sigC c / 4)
        rw [show 4 * (sigC c / 4) + 3 = sigC c by omega, hsl] at this
        simp only [Option.some.injEq] at this
        omega
      · exact slot_read_row hc h3 hslot
    have := size_lt_random
    refine reach (4 * r' + 3) (by omega) (slotOfCell_out r') (by unfold ErrIdx; omega)

end Kc3Closed
