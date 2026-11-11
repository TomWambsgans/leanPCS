-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Kc3Circuit.BridgeBuild
import Kc3Circuit.Secret
import Kc3Circuit.Wiring
import Mathlib.Tactic.IrreducibleDef

/-!
# The closed circuit `PcsQuotient.membership 22`

The Statement's circuit is `finish` of its builder's run (`formal/Statement/PcsQuotient/Circuit.lean`). Here, for
general arguments (nothing evaluates the `2^22`-row run):

* `builder_facts`: the builder's run (`qr`: the wires of `y` and of the root, the builder) is `Kc3Circuit`'s, read
  by `bTr` (`Kc3Bridge.sim_membershipBuilder`), so what `Kc3Circuit.spec_membershipBuild` proves of its rows holds of
  the Statement's: well-formed, at most `4,002,123` rows, `8480` inputs, the wires valid, and the wires hold the
  bits of `y` and of the root under every valuation satisfying the rows whose input bits are a secret's;
* the packing rows (`run_packWords`): word `J`'s `63` rows `(3, bit_{62 − i}, acc)` from `start + 63 J`, the word
  the last of them;
* `rows_getD`: row `r` of the closed circuit, an anchor (`r < 11`), a random row (the last `16`), a built row, a
  packing row, or idle.
-/

set_option linter.unusedSectionVars false

namespace Kc3Closed

open PcsQuotient Kc3Bridge

-- The membership rows are a closed term of millions of rows: never unfold a run of them.
attribute [local irreducible] PcsQuotient.membershipBuilder Kc3Circuit.membershipBuild

/-! ## The builder's run -/

/-- The Statement's builder run of the membership rows from the anchor rows; irreducible, so that neither the
elaborator nor the kernel ever unfolds the run of millions of rows to compare two terms. -/
irreducible_def qr : (List Src × List Src) × Builder := qrun membershipBuilder Builder.new

theorem getD_toArray_map' (l : List Src) (k : ℕ) :
    (l.map srcTr).toArray.getD k .zero = srcTr (l.getD k .zero) := getD_toArray_map l k

/-- What `Kc3Circuit.spec_membershipBuild` proves of a builder run, read through `bTr` (for a general run). -/
theorem facts_of (q : (List Src × List Src) × Builder) (y root : Array Kc3Circuit.Src) (bf : Kc3Circuit.Builder)
    (h2 : bTr q.2 = bf) (hy : y = (q.1.1.map srcTr).toArray) (hr : root = (q.1.2.map srcTr).toArray)
    (hwf : Kc3Circuit.WF bf) (hsize : bf.rows.size ≤ Kc3Circuit.buildRows)
    (hin : bf.inputs.size = 256 + 257 * PcsCircuit.depth)
    (hval : ∀ k < 256, Kc3Circuit.Valid bf (y.getD k .zero) ∧ Kc3Circuit.Valid bf (root.getD k .zero))
    (hsem : ∀ s : PcsCircuit.Secret, s.WellFormed → ∀ v, Kc3Circuit.Sat v bf → Kc3Circuit.SecretInputs s v bf.inputs →
      ∀ k < 256, Kc3Circuit.read v (y.getD k .zero) = PcsCircuit.bitOf s.y k ∧
        Kc3Circuit.read v (root.getD k .zero) = PcsCircuit.bitOf s.root k) :
    Kc3Circuit.WF (bTr q.2) ∧ (bTr q.2).rows.size ≤ Kc3Circuit.buildRows ∧
      q.2.inputs.size = 256 + 257 * PcsCircuit.depth ∧
      (∀ k < 256, Kc3Circuit.Valid (bTr q.2) (srcTr (q.1.1.getD k .zero)) ∧
        Kc3Circuit.Valid (bTr q.2) (srcTr (q.1.2.getD k .zero))) ∧
      ∀ s : PcsCircuit.Secret, s.WellFormed → ∀ v, Kc3Circuit.Sat v (bTr q.2) →
        Kc3Circuit.SecretInputs s v q.2.inputs → ∀ k < 256,
          Kc3Circuit.read v (srcTr (q.1.1.getD k .zero)) = PcsCircuit.bitOf s.y k ∧
            Kc3Circuit.read v (srcTr (q.1.2.getD k .zero)) = PcsCircuit.bitOf s.root k := by
  subst h2 hy hr
  refine ⟨hwf, hsize, by rw [← hin, bTr_inputs], fun k hk => ?_, fun s hs v hv hsi k hk => ?_⟩
  · rw [← getD_toArray_map', ← getD_toArray_map']
    exact hval k hk
  · rw [← getD_toArray_map', ← getD_toArray_map']
    exact hsem s hs v hv (by rw [bTr_inputs]; exact hsi) k hk

/-- **What the builder's rows compute**, through `Kc3Circuit`'s (stated on `qr`'s projections: the kernel
must never be asked to unfold a run). -/
theorem builder_facts : Kc3Circuit.WF (bTr qr.2) ∧ (bTr qr.2).rows.size ≤ Kc3Circuit.buildRows ∧
      qr.2.inputs.size = 256 + 257 * PcsCircuit.depth ∧
      (∀ k < 256, Kc3Circuit.Valid (bTr qr.2) (srcTr (qr.1.1.getD k .zero)) ∧
        Kc3Circuit.Valid (bTr qr.2) (srcTr (qr.1.2.getD k .zero))) ∧
      ∀ s : PcsCircuit.Secret, s.WellFormed → ∀ v, Kc3Circuit.Sat v (bTr qr.2) →
        Kc3Circuit.SecretInputs s v qr.2.inputs → ∀ k < 256,
          Kc3Circuit.read v (srcTr (qr.1.1.getD k .zero)) = PcsCircuit.bitOf s.y k ∧
            Kc3Circuit.read v (srcTr (qr.1.2.getD k .zero)) = PcsCircuit.bitOf s.root k := by
  obtain ⟨y, root, bf, he, hwf, hsize, hin, hval, hsem⟩ := Kc3Circuit.spec_membershipBuild
  have hs := sim_membershipBuilder Builder.new
  rw [bTr_new, ← qr_def] at hs
  have he' : Kc3Circuit.runBuild Kc3Circuit.membershipBuild Kc3Circuit.Builder.new = ((y, root), bf) := he
  rw [he'] at hs
  have h2 : bTr qr.2 = bf := hs.2.symm
  have h3 : y = (qr.1.1.map srcTr).toArray := hs.1.1
  have h4 : root = (qr.1.2.map srcTr).toArray := hs.1.2
  exact facts_of qr y root bf h2 h3 h4 hwf hsize hin hval hsem
theorem bTr_rows_getD (b : Builder) (r : ℕ) : (bTr b).rows.getD r .idle = rowTr (b.rows.getD r idle) := by
  simp only [bTr_rows, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases b.rows[r]? <;> rfl

theorem bTr_size (b : Builder) : (bTr b).rows.size = b.rows.size := by simp

/-! ## The packing rows -/

/-- The rows a fold of packing rows from `acc` appends at `base`. -/
def packRows : List Src → Src → ℕ → List Row
  | [], _, _ => []
  | bit :: l, acc, base => ⟨.three, bit, acc⟩ :: packRows l (.row base) (base + 1)

/-- The source a fold of packing rows from `acc` returns. -/
def packEnd : List Src → Src → ℕ → Src
  | [], acc, _ => acc
  | _ :: l, _, base => packEnd l (.row base) (base + 1)

theorem run_foldl_row : ∀ (l : List Src) (acc : Src) (b : Builder),
    qrun (l.foldlM (fun acc bit ↦ Build.row .three bit acc) acc) b =
      (packEnd l acc b.rows.size, ⟨b.rows ++ (packRows l acc b.rows.size).toArray, b.inputs⟩)
  | [], acc, b => by simp [qrun_pure, packEnd, packRows]
  | bit :: l, acc, b => by
    rw [List.foldlM_cons, qrun_bind]
    have hrow : qrun (Build.row .three bit acc) b =
        (.row b.rows.size, ⟨b.rows.push ⟨.three, bit, acc⟩, b.inputs⟩) := rfl
    rw [hrow]
    simp only
    rw [run_foldl_row l]
    simp only [Array.size_push, packEnd, packRows]
    refine Prod.ext rfl ?_
    simp only
    congr 1
    rw [Array.push_eq_append, Array.append_assoc]
    congr 1
    apply Array.toList_inj.mp
    simp

theorem length_packRows : ∀ (l : List Src) (acc : Src) (base : ℕ), (packRows l acc base).length = l.length
  | [], _, _ => rfl
  | _ :: l, _, base => by simp [packRows, length_packRows l]

theorem packRows_getD : ∀ (l : List Src) (acc : Src) (base i : ℕ), i < l.length →
    (packRows l acc base).getD i idle =
      ⟨.three, l.getD i .zero, if i = 0 then acc else .row (base + i - 1)⟩
  | [], _, _, i, h => by simp at h
  | bit :: l, acc, base, 0, _ => by simp [packRows]
  | bit :: l, acc, base, i + 1, h => by
    simp only [packRows, List.getD_cons_succ, List.length_cons] at h ⊢
    rw [packRows_getD l _ (base + 1) i (by omega)]
    by_cases hi : i = 0
    · subst hi; simp
    · first | (simp [hi]; done) | (simp [hi]; omega)

theorem packEnd_cons : ∀ (l : List Src) (acc : Src) (base : ℕ), l ≠ [] →
    packEnd l acc base = .row (base + l.length - 1)
  | [], _, _, h => absurd rfl h
  | [_], _, base, _ => by simp [packEnd]
  | _ :: b :: l, _, base, _ => by
    have ih := packEnd_cons (b :: l) (.row base) (base + 1) (by simp)
    simp only [packEnd] at ih ⊢
    rw [ih]
    simp; omega

/-- The bit packing row `i < 63` of a word reads: bit `62 − i`. -/
theorem reverse_take_getD (bits : List Src) (h : bits.length = 64) (i : ℕ) (hi : i < 63) :
    ((bits.take 63).reverse).getD i .zero = bits.getD (62 - i) .zero := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_reverse (by simp [h]; omega)]
  simp only [List.length_take, h, show min 63 64 = 63 from rfl]
  rw [List.getElem?_take]
  simp [show 63 - 1 - i < 63 by omega, show 63 - 1 - i = 62 - i by omega]

/-- **One word's packing rows.** -/
theorem run_packWord (bits : List Src) (h : bits.length = 64) (b : Builder) :
    qrun (packWord bits) b = (.row (b.rows.size + 62),
      ⟨b.rows ++ (packRows ((bits.take 63).reverse) (bits.getD 63 .zero) b.rows.size).toArray, b.inputs⟩) := by
  unfold packWord
  rw [show wordBits - 1 = 63 from rfl, run_foldl_row]
  rw [packEnd_cons _ _ _ (by intro he; have := congrArg List.length he; simp [h] at this)]
  simp [h]

/-- The rows of words `ws` packed from `base`, word after word. -/
def packAll : List (List Src) → ℕ → List Row
  | [], _ => []
  | bits :: ws, base => packRows ((bits.take 63).reverse) (bits.getD 63 .zero) base ++ packAll ws (base + 63)

theorem run_packWords : ∀ (ws : List (List Src)) (b : Builder), (∀ bits ∈ ws, bits.length = 64) →
    qrun (ws.mapM packWord) b =
      ((List.range ws.length).map (fun J ↦ .row (b.rows.size + 63 * J + 62)),
        ⟨b.rows ++ (packAll ws b.rows.size).toArray, b.inputs⟩)
  | [], b, _ => by simp [qrun_pure, packAll]
  | bits :: ws, b, h => by
    rw [List.mapM_cons, qrun_bind, run_packWord bits (h bits (by simp)) b]
    simp only
    rw [qrun_bind, run_packWords ws _ fun x hx => h x (List.mem_cons_of_mem _ hx), qrun_pure]
    simp only [Array.size_append, List.size_toArray, length_packRows, List.length_reverse, List.length_take,
      h bits (by simp), show min 63 64 = 63 from rfl, packAll, Array.append_assoc, List.append_toArray]
    refine Prod.ext ?_ rfl
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    refine List.map_congr_left fun J _ => ?_
    simp only [Function.comp]
    congr 1
    omega

theorem length_packAll : ∀ (ws : List (List Src)) (base : ℕ), (∀ bits ∈ ws, bits.length = 64) →
    (packAll ws base).length = 63 * ws.length
  | [], _, _ => rfl
  | bits :: ws, base, h => by
    simp only [packAll, List.length_append, length_packRows, List.length_reverse, List.length_take,
      h bits (by simp), length_packAll ws _ fun x hx => h x (List.mem_cons_of_mem _ hx), List.length_cons]
    omega

/-- **Packing row `63 J + i` of the words**: `(3, bit_{62 − i}, acc)` of word `J`, `acc` its bit `63` for `i = 0`,
the row before otherwise. -/
theorem packAll_getD : ∀ (ws : List (List Src)) (base J i : ℕ), (∀ bits ∈ ws, bits.length = 64) →
    J < ws.length → i < 63 →
    (packAll ws base).getD (63 * J + i) idle =
      ⟨.three, (ws.getD J []).getD (62 - i) .zero,
        if i = 0 then (ws.getD J []).getD 63 .zero else .row (base + 63 * J + i - 1)⟩
  | [], _, _, _, _, hJ, _ => by simp at hJ
  | bits :: ws, base, 0, i, h, _, hi => by
    have hl := h bits (by simp)
    simp only [packAll, Nat.mul_zero, Nat.zero_add, List.getD_cons_zero]
    rw [List.getD_append _ _ _ _ (by simp [length_packRows, hl]; omega),
      packRows_getD _ _ _ _ (by simp [hl]; omega), reverse_take_getD bits hl i hi]
    simp
  | bits :: ws, base, J + 1, i, h, hJ, hi => by
    have hl := h bits (by simp)
    simp only [packAll, List.getD_cons_succ]
    rw [List.getD_append_right _ _ _ _ (by simp [length_packRows, hl]; omega)]
    simp only [length_packRows, List.length_reverse, List.length_take, hl, show min 63 64 = 63 from rfl]
    rw [show 63 * (J + 1) + i - 63 = 63 * J + i by omega,
      packAll_getD ws (base + 63) J i (fun x hx => h x (List.mem_cons_of_mem _ hx)) (by simpa using hJ) hi]
    congr 2
    by_cases h0 : i = 0
    · subst h0; simp <;> omega
    · congr 1; omega

end Kc3Closed
