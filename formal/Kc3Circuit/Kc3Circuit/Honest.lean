-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Kc3Circuit.Sound
import Kc3Circuit.Folds
import Kc3Circuit.Inputs
import PcsQuotient.Prover

/-!
# The honest cells satisfy the circuit

The Statement's prover's cells (`randomizeCells (membership 22) ((membership 22).cells (membershipInputs w))
coins.rows`) hold the gates, the copies and the pins of the statement `w.statement`.
-/

set_option linter.unusedSectionVars false

namespace Kc3Closed

open PcsQuotient Kc3Bridge Kc3Wiring Kc3Words LeanVM.Parameters Kc3Fold

attribute [local irreducible] PcsQuotient.membershipBuilder Kc3Circuit.membershipBuild PcsQuotient.membership

/-! ## The loops as folds -/

/-- A row's output bit from the outputs so far. -/
def gBits (c : Circuit) (r : ℕ) (v : Array Bool) : Bool :=
  gateBits (readSrc v (c.rows.getD r idle).x) (readSrc v (c.rows.getD r idle).y) (readSrc v (c.rows.getD r idle).c)

/-- A row's output over `K` from the outputs so far. -/
def gK (c : Circuit) (r : ℕ) (v : Array K) : K :=
  gateK (readK v (c.rows.getD r idle).x) (readK v (c.rows.getD r idle).y) (readK v (c.rows.getD r idle).c)

/-- The inputs set. -/
def inputsSet (c : Circuit) (ins : List Bool) : Array Bool :=
  (c.inputs.toList.zip ins).foldl (fun v p => v.set! p.1 p.2) (Array.replicate c.rows.size false)

theorem outputs_fold (c : Circuit) (ins : List Bool) :
    c.outputs ins = (List.range' publicRows (c.rows.size - publicRows) ++ List.range publicRows).foldl
      (fun v r => v.set! r (gBits c r v)) (inputsSet c ins) := by
  unfold Circuit.outputs inputsSet gBits
  simp only [List.forIn_pure_yield_eq_foldl, Id.run_bind, Id.run_pure]

theorem outputsK_fold (c : Circuit) (ins : List Bool) :
    c.outputsK ins = (List.range' c.packing.1 c.packing.2 ++ List.range publicRows).foldl
      (fun v r => v.set! r (gK c r v)) ((c.outputs ins).map fun b => if b then 1 else 0) := by
  unfold Circuit.outputsK gK
  simp only [List.forIn_pure_yield_eq_foldl, Id.run_bind, Id.run_pure]

theorem readSrc_congr {v v' : Array Bool} {s : Src} (h : ∀ r', s = .row r' → v.getD r' false = v'.getD r' false) :
    readSrc v s = readSrc v' s := by
  cases s with
  | row r' => exact h r' rfl
  | _ => rfl

theorem readK_congr {v v' : Array K} {s : Src} (h : ∀ r', s = .row r' → v.getD r' 0 = v'.getD r' 0) :
    readK v s = readK v' s := by
  cases s with
  | row r' => exact h r' rfl
  | _ => rfl

/-! ## The order of the rows -/

/-- Row `r` of the deployed circuit reads row `r'`. -/
def Reads (r r' : ℕ) : Prop :=
  ((membership 22).rows.getD r idle).x = .row r' ∨ ((membership 22).rows.getD r idle).y = .row r' ∨
    ((membership 22).rows.getD r idle).c = .row r'

theorem gBits_loc (r : ℕ) (v v' : Array Bool) (h : ∀ r', Reads r r' → v.getD r' false = v'.getD r' false) :
    gBits (membership 22) r v = gBits (membership 22) r v' := by
  unfold gBits
  rw [readSrc_congr fun r' e => h r' (Or.inl e), readSrc_congr fun r' e => h r' (Or.inr (Or.inl e)),
    readSrc_congr fun r' e => h r' (Or.inr (Or.inr e))]

theorem gK_loc (r : ℕ) (v v' : Array K) (h : ∀ r', Reads r r' → v.getD r' 0 = v'.getD r' 0) :
    gK (membership 22) r v = gK (membership 22) r v' := by
  unfold gK
  rw [readK_congr fun r' e => h r' (Or.inl e), readK_congr fun r' e => h r' (Or.inr (Or.inl e)),
    readK_congr fun r' e => h r' (Or.inr (Or.inr e))]

/-- What a row may read for the honest computation's order: a row from `11` on, before it unless it is an
anchor. -/
def OkSrc (r : ℕ) (s : Src) : Prop := ∀ r', s = .row r' → 11 ≤ r' ∧ (r < 11 ∨ r' < r)

theorem okSrc_const {r : ℕ} {s : Src} (h : s = .zero ∨ s = .one ∨ s = .three ∨ s = .free) : OkSrc r s := by
  intro r' hr; rcases h with rfl | rfl | rfl | rfl <;> cases hr

theorem okSrc_cases {r : ℕ} {s : Src} (h : s = .zero ∨ s = .one ∨ ∃ r', s = .row r' ∧ 11 ≤ r' ∧ r' < r) :
    OkSrc r s := by
  rcases h with rfl | rfl | ⟨r', rfl, h1, h2⟩
  · exact okSrc_const (Or.inl rfl)
  · exact okSrc_const (Or.inr (Or.inl rfl))
  · intro r'' e; injection e with e; subst e; exact ⟨h1, Or.inr h2⟩

theorem pw_ok (J j : ℕ) (hJ : J < 8) (hj : j < 64) :
    ∀ r', (pw.getD J []).getD j .zero = .row r' → 11 ≤ r' ∧ r' < qr.2.rows.size := by
  intro r' e
  rw [pw_getD J j hJ hj] at e
  have h := wire_cases _ (wire_index_lt J j hj)
  split at e
  · rcases h _ (List.mem_cons_self ..) with h | h | ⟨r'', h, h1, h2⟩
    · rw [h] at e; cases e
    · rw [h] at e; cases e
    · rw [h] at e; injection e with e; subst e; exact ⟨h1, h2⟩
  · rcases h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) with h | h | ⟨r'', h, h1, h2⟩
    · rw [h] at e; cases e
    · rw [h] at e; cases e
    · rw [h] at e; injection e with e; subst e; exact ⟨h1, h2⟩

/-- **The order of the rows**: an input row reads itself; every other row reads rows from `11` on, before it
unless it is an anchor. -/
theorem closedRow_order (r : ℕ) :
    (11 ≤ r ∧ r < qr.2.rows.size ∧ r ∈ qr.2.inputs ∧ closedRow r = ⟨.row r, .row r, .row r⟩) ∨
      (OkSrc r (closedRow r).x ∧ OkSrc r (closedRow r).y ∧ OkSrc r (closedRow r).c) := by
  have h11 := S_ge
  have hsrc : ∀ k, k < 11 → OkSrc k (sources.getD k .zero) := by
    intro k hk r' hr
    refine ⟨?_, Or.inl hk⟩
    unfold sources at hr
    rw [List.getD_eq_getElem?_getD] at hr
    by_cases hk8 : k < 8
    · rw [List.getElem?_append_left (by simpa using hk8)] at hr
      simp only [List.getElem?_map, List.getElem?_range hk8, Option.map_some, Option.getD_some] at hr
      cases hr; omega
    · rw [List.getElem?_append_right (by simpa using hk8)] at hr
      simp only [List.length_map, List.length_range] at hr
      rcases h : k - 8 with _ | _ | _ | m <;> simp [h] at hr
  by_cases h1 : r < 11
  · right
    rw [closedRow_anchor h1]
    unfold anchorRow
    refine ⟨okSrc_const (Or.inl rfl), ?_, hsrc r h1⟩
    split
    · exact hsrc r h1
    · exact okSrc_const (Or.inl rfl)
  by_cases h2 : 2 ^ 22 - 16 ≤ r
  · right
    rw [closedRow_random h1 h2]
    unfold RandomShape.row
    split <;> exact ⟨okSrc_const (by simp), okSrc_const (by simp), okSrc_const (by simp)⟩
  by_cases h3 : r < qr.2.rows.size
  · rw [closedRow_built h1 h2 h3]
    rcases builder_row r (by omega) h3 with ⟨hin, hrow⟩ | ⟨-, hs⟩
    · exact Or.inl ⟨by omega, h3, hin, hrow⟩
    · exact Or.inr ⟨okSrc_cases (hs _ (List.mem_cons_self ..)),
        okSrc_cases (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
        okSrc_cases (hs _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))⟩
  · right
    rw [closedRow_pack h1 h2 h3]
    by_cases hp : r - qr.2.rows.size < 504
    · have hJ : (r - qr.2.rows.size) / 63 < pw.length := by rw [pw_len]; omega
      have he : r - qr.2.rows.size = 63 * ((r - qr.2.rows.size) / 63) + (r - qr.2.rows.size) % 63 := by omega
      rw [he, packAll_getD pw _ _ _ pw_length hJ (Nat.mod_lt _ (by decide))]
      refine ⟨okSrc_const (by simp), ?_, ?_⟩
      · intro r' e
        have := pw_ok _ _ (by rw [← pw_len]; exact hJ) (by omega) r' e
        exact ⟨this.1, Or.inr (by omega)⟩
      · split
        · intro r' e
          have := pw_ok _ _ (by rw [← pw_len]; exact hJ) (by omega) r' e
          exact ⟨this.1, Or.inr (by omega)⟩
        · intro r' e; injection e with e; subst e; exact ⟨by omega, Or.inr (by omega)⟩
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [length_packAll_pw]; omega)]
      exact ⟨okSrc_const (by simp [idle]), okSrc_const (by simp [idle]), okSrc_const (by simp [idle])⟩

theorem no_reads {a b : ℕ} (ha : a < 2 ^ 22) (hab : (11 ≤ a ∧ a < b) ∨ b < 11) (hne : a ≠ b) : ¬ Reads a b := by
  unfold Reads
  rw [rows_getD a ha]
  rcases closedRow_order a with ⟨-, -, -, hrow⟩ | ⟨hx, hy, hc⟩
  · rw [hrow]
    rintro (e | e | e) <;> (injection e with e; exact hne e)
  · rintro (e | e | e)
    · have := hx b e; omega
    · have := hy b e; omega
    · have := hc b e; omega

theorem reads_self {a : ℕ} (ha : a < 2 ^ 22) (h : Reads a a) :
    11 ≤ a ∧ a < qr.2.rows.size ∧ a ∈ qr.2.inputs ∧ closedRow a = ⟨.row a, .row a, .row a⟩ := by
  unfold Reads at h
  rw [rows_getD a ha] at h
  rcases closedRow_order a with h' | ⟨hx, hy, hc⟩
  · exact h'
  · exfalso
    rcases h with e | e | e
    · have := hx a e; omega
    · have := hy a e; omega
    · have := hc a e; omega

/-- The loops' lists: no row reads one set after it. -/
theorem order_pairwise (lo n : ℕ) (hlo : 11 ≤ lo) (hn : lo + n ≤ 2 ^ 22) :
    (List.range' lo n ++ List.range 11).Pairwise (fun a b => a ≠ b ∧ ¬ Reads a b) := by
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · refine (List.pairwise_lt_range' (s := lo) (n := n)).imp_of_mem fun {a b} ha hb hab => ?_
    simp only [List.mem_range'_1] at ha hb
    exact ⟨by omega, no_reads (by omega) (Or.inl ⟨by omega, hab⟩) (by omega)⟩
  · refine (List.pairwise_lt_range (n := 11)).imp_of_mem fun {a b} ha hb hab => ?_
    simp only [List.mem_range] at ha hb
    exact ⟨by omega, no_reads (by omega) (Or.inr hb) (by omega)⟩
  · intro a ha b hb
    simp only [List.mem_range'_1, List.mem_range] at ha hb
    exact ⟨by omega, no_reads (by omega) (Or.inr hb) (by omega)⟩

/-! ## The honest outputs -/

theorem inputsSet_size (ins : List Bool) : (inputsSet (membership 22) ins).size = 2 ^ 22 := by
  unfold inputsSet; rw [size_foldl_setPairs, Array.size_replicate, rows_size]

/-- **The outputs' bits**: every row holds its gate's output on what it reads; an input row its input. -/
theorem bits_facts (ins : List Bool) :
    (∀ r < 2 ^ 22, ((membership 22).outputs ins).getD r false = gBits (membership 22) r ((membership 22).outputs ins)) ∧
      (∀ r < 2 ^ 22, Reads r r → ((membership 22).outputs ins).getD r false = (inputsSet (membership 22) ins).getD r false) ∧
      ((membership 22).outputs ins).size = 2 ^ 22 := by
  have hL : List.range' publicRows ((membership 22).rows.size - publicRows) ++ List.range publicRows =
      List.range' 11 (2 ^ 22 - 11) ++ List.range 11 := by rw [rows_size]; rfl
  have hmem : ∀ r < 2 ^ 22, r ∈ List.range' 11 (2 ^ 22 - 11) ++ List.range 11 := by
    intro r hr
    simp only [List.mem_append, List.mem_range'_1, List.mem_range]
    omega
  have hsz := inputsSet_size ins
  have key := foldl_set (gBits (membership 22)) false Reads gBits_loc (List.range' 11 (2 ^ 22 - 11) ++ List.range 11)
    (inputsSet (membership 22) ins) (order_pairwise 11 _ le_rfl (by omega))
    (fun r hr => by rw [hsz]; simp only [List.mem_append, List.mem_range'_1, List.mem_range] at hr; omega)
    (fun r hr hd v => by
      have hr' : r < 2 ^ 22 := by simp only [List.mem_append, List.mem_range'_1, List.mem_range] at hr; omega
      obtain ⟨-, -, -, hrow⟩ := reads_self hr' hd
      unfold gBits
      rw [rows_getD r hr', hrow]
      simp only [readSrc, gateBits]
      cases v.getD r false <;> rfl)
  rw [outputs_fold, hL]
  refine ⟨fun r hr => (key r (hmem r hr)).1, fun r hr hd => (key r (hmem r hr)).2 hd, ?_⟩
  exact (size_foldl_set _ _ _).trans hsz

theorem inputs_lt (r : ℕ) (h : r ∈ qr.2.inputs) : 11 ≤ r ∧ r < qr.2.rows.size := by
  have := builder_facts.1.input_range r (by rw [bTr_inputs]; exact h)
  rw [bTr_size] at this
  exact this

/-- **The inputs set**: input row `k` holds input bit `k`. -/
theorem inputsSet_input (ins : List Bool) (hl : ins.length = 8480) (k : ℕ) (hk : k < 8480) :
    (inputsSet (membership 22) ins).getD (qr.2.inputs.getD k 0) false = ins.getD k false := by
  have hsz := inputs_size
  have hk' : k < (qr.2.inputs.toList.zip ins).length := by simp [hsz, hl, hk]
  unfold inputsSet
  rw [inputs_eq]
  have hfst : ((qr.2.inputs.toList.zip ins)[k]'hk').1 = qr.2.inputs.getD k 0 := by
    simp [List.getElem_zip, Array.getD_eq_getD_getElem?, hsz, hk]
  have hsnd : ((qr.2.inputs.toList.zip ins)[k]'hk').2 = ins.getD k false := by
    simp [List.getElem_zip, List.getD_eq_getElem?_getD, hl, hk]
  rw [← hfst, ← hsnd]
  refine foldl_setPairs false _ _ ?_ _ (List.getElem_mem hk') ?_
  · rw [List.map_fst_zip (by simp [hsz, hl])]
    exact (by simpa using builder_facts.1.sorted : qr.2.inputs.toList.Pairwise (· < ·)).imp ne_of_lt
  · rw [hfst, Array.size_replicate, rows_size]
    have hm : qr.2.inputs.getD k 0 ∈ qr.2.inputs := by
      simp [Array.getD_eq_getD_getElem?, hsz, hk]
    have := inputs_lt _ hm
    have := size_lt_random
    omega

theorem finish_packing (logRows : ℕ) (pub : List (List Src)) (b : Builder) :
    (finish logRows pub b).packing = (b.rows.size, (qrun (pub.mapM packWord) b).2.rows.size - b.rows.size) := rfl

theorem packing_eq : (membership 22).packing = (qr.2.rows.size, 504) := by
  rw [membership_eq, finish_packing, run_pw]
  simp [length_packAll_pw]

/-- A bit in `K`. -/
def bK (b : Bool) : K := if b then 1 else 0

theorem getD_map_bK (a : Array Bool) (r : ℕ) : (a.map fun b => if b then (1 : K) else 0).getD r 0 = bK (a.getD r false) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[r]? <;> rfl

/-- **The outputs over `K`**: the packing rows and the anchors hold their gates' outputs over `K` on what they
read; every other row its bit. -/
theorem K_facts (ins : List Bool) :
    (∀ r, (qr.2.rows.size ≤ r ∧ r < qr.2.rows.size + 504 ∨ r < 11) →
        ((membership 22).outputsK ins).getD r 0 = gK (membership 22) r ((membership 22).outputsK ins)) ∧
      (∀ r, ¬ (qr.2.rows.size ≤ r ∧ r < qr.2.rows.size + 504 ∨ r < 11) →
        ((membership 22).outputsK ins).getD r 0 = bK (((membership 22).outputs ins).getD r false)) := by
  have h11 := S_ge
  have hS := size_lt_random
  have hsz := (bits_facts ins).2.2
  have hsz' : (((membership 22).outputs ins).map fun b => if b then (1 : K) else 0).size = 2 ^ 22 := by
    rw [Array.size_map, hsz]
  have key := foldl_set (gK (membership 22)) 0 Reads gK_loc (List.range' qr.2.rows.size 504 ++ List.range 11)
    (((membership 22).outputs ins).map fun b => if b then (1 : K) else 0)
    (order_pairwise _ _ h11 (by omega))
    (fun r hr => by rw [hsz']; simp only [List.mem_append, List.mem_range'_1, List.mem_range] at hr; omega)
    (fun r hr hd => by
      have hr' : r < 2 ^ 22 := by simp only [List.mem_append, List.mem_range'_1, List.mem_range] at hr; omega
      have := reads_self hr' hd
      simp only [List.mem_append, List.mem_range'_1, List.mem_range] at hr
      omega)
  rw [outputsK_fold, packing_eq]
  refine ⟨fun r hr => (key r ?_).1, fun r hr => ?_⟩
  · simp only [List.mem_append, List.mem_range'_1, List.mem_range]; omega
  · rw [foldl_set_out _ _ _ _ r (by simp only [publicRows, publicWords, List.mem_append, List.mem_range'_1, List.mem_range]; omega),
      getD_map_bK]

/-! ## The cells -/

theorem cells_getD (c : Circuit) (ins : List Bool) (r j : ℕ) (hr : r < c.rows.size) (hj : j < 4) :
    (c.cells ins).getD (4 * r + j) 0 =
      if j = 0 then readK (c.outputsK ins) (c.rows.getD r idle).x
      else if j = 1 then readK (c.outputsK ins) (c.rows.getD r idle).y
      else if j = 2 then readK (c.outputsK ins) (c.rows.getD r idle).c
      else (c.outputsK ins).getD r 0 := by
  have h1 : (4 * r + j) / 4 = r := by omega
  have h2 : (4 * r + j) % 4 = j := by omega
  unfold Circuit.cells
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, show 4 * r + j < 4 * c.rows.size by omega,
    dif_pos, Option.getD_some, h1, h2]
  interval_cases j <;> rfl

/-- The `j`-th cell of the `k`-th random row (from the last) for the random words. -/
def shapeVal (rows : Fin randomWords → K) (k j : ℕ) : K :=
  let word (i : ℕ) : K := if h : i < randomWords then rows ⟨i, h⟩ else 0
  let t := (RandomShape.of k).cells (word (2 * k)) (word (2 * k + 1))
  if j = 0 then t.1 else if j = 1 then t.2.1 else if j = 2 then t.2.2.1 else t.2.2.2

/-- Four cells of row `r` set. -/
theorem set4_getD (cs : Array K) (r i : ℕ) (x y c v : K) :
    ((((cs.setIfInBounds (4 * r) x).setIfInBounds (4 * r + 1) y).setIfInBounds (4 * r + 2) c).setIfInBounds
      (4 * r + 3) v).getD i 0 =
      if i / 4 = r ∧ i < cs.size then (if i % 4 = 0 then x else if i % 4 = 1 then y else if i % 4 = 2 then c else v)
      else cs.getD i 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.size_setIfInBounds]
  by_cases h : i / 4 = r
  · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 4 ∧ i = 4 * r + j := ⟨i % 4, by omega, by omega⟩
    have hd : (4 * r + j) / 4 = r := by omega
    have hm : (4 * r + j) % 4 = j := by omega
    simp only [hd, hm, true_and]
    by_cases hs : 4 * r + j < cs.size
    · interval_cases j <;> (try simp only [Nat.add_zero] at hs ⊢) <;> simp [hs]
    · rw [Array.getElem?_eq_none (by omega)]
      interval_cases j <;> (try simp only [Nat.add_zero] at hs ⊢) <;> simp [hs]
  · have h0 : 4 * r ≠ i := by omega
    have h1 : 4 * r + 1 ≠ i := by omega
    have h2 : 4 * r + 2 ≠ i := by omega
    have h3 : 4 * r + 3 ≠ i := by omega
    simp [h, h0, h1, h2, h3]

theorem randomRows_zipIdx (c : Circuit) :
    c.randomRows.zipIdx = (List.range 16).map fun k => (c.rows.size - 1 - k, k) := by
  apply List.ext_getElem (by simp [Circuit.randomRows, PcsQuotient.randomRows])
  intro n h1 h2
  simp [Circuit.randomRows, List.getElem_zipIdx, PcsQuotient.randomRows]

theorem foldl_rows (F : Array K → ℕ × ℕ → Array K) (rows : Fin randomWords → K) (n i : ℕ)
    (hF : ∀ cs (p : ℕ × ℕ), (F cs p).size = cs.size ∧ ∀ i, (F cs p).getD i 0 =
      if i / 4 = p.1 ∧ i < cs.size then shapeVal rows p.2 (i % 4) else cs.getD i 0) :
    ∀ (m : ℕ) (B : Array K), m ≤ n → i < B.size → i / 4 < n →
      (((List.range m).map fun k => (n - 1 - k, k)).foldl F B).getD i 0 =
        if n - m ≤ i / 4 then shapeVal rows (n - 1 - i / 4) (i % 4) else B.getD i 0 := by
  intro m
  induction m with
  | zero => intro B _ _ hn; rw [if_neg (by omega)]; rfl
  | succ m ih =>
    intro B hm hi hn
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    have hsz : ∀ (l : List (ℕ × ℕ)) (B : Array K), (l.foldl F B).size = B.size := by
      intro l
      induction l with
      | nil => intro B; rfl
      | cons p l ihl => intro B; rw [List.foldl_cons, ihl, (hF B p).1]
    rw [(hF _ _).2 i, hsz, ih B (by omega) hi hn]
    by_cases h1 : i / 4 = n - 1 - m
    · rw [if_pos ⟨h1, hi⟩, if_pos (by omega), show n - 1 - i / 4 = m by omega]
    · rw [if_neg (fun h => h1 h.1)]
      by_cases h2 : n - m ≤ i / 4
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

/-- **The random rows filled**: a random row's cells are its shape's; the others are left. -/
theorem randomize_getD (c : Circuit) (A : Array K) (rows : Fin randomWords → K) (i : ℕ)
    (hi : i < A.size) (hn : i / 4 < c.rows.size) (h16 : 16 ≤ c.rows.size) :
    (randomizeCells c A rows).getD i 0 =
      if c.rows.size - 16 ≤ i / 4 then shapeVal rows (c.rows.size - 1 - i / 4) (i % 4) else A.getD i 0 := by
  unfold randomizeCells
  rw [randomRows_zipIdx]
  apply foldl_rows _ rows c.rows.size i ?_ 16 A h16 hi hn
  intro cs p
  obtain ⟨r, k⟩ := p
  simp only
  refine ⟨by simp, fun i => ?_⟩
  rw [set4_getD]
  simp only [shapeVal]

theorem gateBits_K (a b c : Bool) : bK (gateBits a b c) = gateK (bK a) (bK b) (bK c) := by
  cases a <;> cases b <;> cases c <;> decide

/-! ## The honest cells -/

attribute [local irreducible] Circuit.outputs Circuit.outputsK

theorem readSrc_row (v : Array Bool) (r : ℕ) : readSrc v (.row r) = v.getD r false := rfl

theorem readK_row (v : Array K) (r : ℕ) : readK v (.row r) = v.getD r 0 := rfl

theorem readSrc_zero (v : Array Bool) : readSrc v .zero = false := rfl

theorem readSrc_one (v : Array Bool) : readSrc v .one = true := rfl

theorem readK_zero (v : Array K) : readK v .zero = 0 := rfl

theorem readK_one (v : Array K) : readK v .one = 1 := rfl

theorem gateBits_K_idle (v : Array Bool) (u : Array K) :
    bK (gateBits (readSrc v idle.x) (readSrc v idle.y) (readSrc v idle.c)) =
      gateK (readK u idle.x) (readK u idle.y) (readK u idle.c) := by
  rw [show idle = ⟨.zero, .zero, .zero⟩ from rfl]
  simp only [readSrc_zero, readK_zero, gateBits_K]
  decide

/-- The prover's cells (`Prover.lean`): the circuit's cells for the secret's inputs, the random rows filled. -/
def hArr (w : Secret) (rows : Fin randomWords → K) : Array K :=
  randomizeCells (membership 22) ((membership 22).cells (membershipInputs w)) rows

/-- The prover's cells in `E`, by number. -/
noncomputable def wH (w : Secret) (rows : Fin randomWords → K) (c : ℕ) : E := ofK ((hArr w rows).getD c 0)

theorem cells_size (ins : List Bool) : ((membership 22).cells ins).size = 4 * 2 ^ 22 := by
  unfold Circuit.cells; rw [Array.size_ofFn, rows_size]

theorem hArr_row (w : Secret) (rows : Fin randomWords → K) (r j : ℕ) (hr : r < 2 ^ 22 - 16) (hj : j < 4) :
    (hArr w rows).getD (4 * r + j) 0 =
      if j = 0 then readK ((membership 22).outputsK (membershipInputs w)) (closedRow r).x
      else if j = 1 then readK ((membership 22).outputsK (membershipInputs w)) (closedRow r).y
      else if j = 2 then readK ((membership 22).outputsK (membershipInputs w)) (closedRow r).c
      else ((membership 22).outputsK (membershipInputs w)).getD r 0 := by
  unfold hArr
  rw [randomize_getD _ _ _ _ (by rw [cells_size]; omega) (by rw [rows_size]; omega) (by rw [rows_size]; norm_num),
    rows_size, if_neg (by omega), cells_getD _ _ r j (by rw [rows_size]; omega) hj, rows_getD r (by omega)]

theorem hArr_random (w : Secret) (rows : Fin randomWords → K) (r j : ℕ) (hr1 : 2 ^ 22 - 16 ≤ r) (hr2 : r < 2 ^ 22)
    (hj : j < 4) : (hArr w rows).getD (4 * r + j) 0 = shapeVal rows (2 ^ 22 - 1 - r) j := by
  unfold hArr
  rw [randomize_getD _ _ _ _ (by rw [cells_size]; omega) (by rw [rows_size]; omega) (by rw [rows_size]; norm_num),
    rows_size, if_pos (by omega), show (4 * r + j) / 4 = r by omega, show (4 * r + j) % 4 = j by omega]

theorem ofK_add (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

theorem ofK_mul (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b

theorem ofK_zero : ofK (0 : K) = 0 := map_zero (algebraMap K E)

theorem ofK_one : ofK (1 : K) = 1 := map_one (algebraMap K E)

theorem gate_ofK (X Y C : K) : Kc3.gate (ofK X) (ofK Y) (ofK C) (ofK (gateK X Y C)) = 0 := by
  unfold Kc3.gate gateK
  rw [ofK_add, ofK_add, ofK_mul]
  linear_combination (ofK Y + ofK C + ofK X * ofK C) * two_eq_zero

theorem gate_cells (s : RandomShape) (a b : K) :
    Kc3.gate (ofK (s.cells a b).1) (ofK (s.cells a b).2.1) (ofK (s.cells a b).2.2.1) (ofK (s.cells a b).2.2.2) = 0 := by
  cases s <;> simp only [RandomShape.cells, ofK_add, ofK_zero, ofK_one, Kc3.gate]
  · linear_combination (ofK a + ofK b) * two_eq_zero
  · linear_combination (ofK a) * two_eq_zero
  · linear_combination (ofK a + ofK b) * two_eq_zero

theorem gate_shape (rows : Fin randomWords → K) (k : ℕ) :
    Kc3.gate (ofK (shapeVal rows k 0)) (ofK (shapeVal rows k 1)) (ofK (shapeVal rows k 2)) (ofK (shapeVal rows k 3)) = 0 :=
  gate_cells _ _ _

/-- A source of a built row, read over `K`, is its bit. -/
theorem readK_bit (ins : List Bool) {s : Src} {B : ℕ} (hB : B ≤ qr.2.rows.size)
    (hs : s = .zero ∨ s = .one ∨ ∃ r', s = .row r' ∧ 11 ≤ r' ∧ r' < B) :
    readK ((membership 22).outputsK ins) s = bK (readSrc ((membership 22).outputs ins) s) := by
  rcases hs with rfl | rfl | ⟨r', rfl, h1, h2⟩
  · rw [readK_zero, readSrc_zero]; decide
  · rw [readK_one, readSrc_one]; decide
  · rw [readK_row, readSrc_row, (K_facts ins).2 r' (by omega)]

/-- **Every row but the random ones holds its gate's output over `K`.** -/
theorem outK_gate (ins : List Bool) (r : ℕ) (hr : r < 2 ^ 22 - 16) :
    ((membership 22).outputsK ins).getD r 0 = gateK (readK ((membership 22).outputsK ins) (closedRow r).x)
      (readK ((membership 22).outputsK ins) (closedRow r).y) (readK ((membership 22).outputsK ins) (closedRow r).c) := by
  have hS := size_lt_random
  have h11 := S_ge
  by_cases hL : qr.2.rows.size ≤ r ∧ r < qr.2.rows.size + 504 ∨ r < 11
  · rw [(K_facts ins).1 r hL]; unfold gK; rw [rows_getD r (by omega)]
  · rw [(K_facts ins).2 r hL, (bits_facts ins).1 r (by omega)]
    unfold gBits
    rw [rows_getD r (by omega), gateBits_K]
    by_cases h3 : r < qr.2.rows.size
    · rw [closedRow_built (by omega) (by omega) h3]
      rcases builder_row r (by omega) h3 with ⟨-, hrow⟩ | ⟨-, hs⟩
      · rw [hrow]
        have e := readK_bit ins (s := .row r) le_rfl (Or.inr (Or.inr ⟨r, rfl, by omega, h3⟩))
        rw [e]
      · rw [readK_bit ins h3.le (hs _ (List.mem_cons_self ..)),
          readK_bit ins h3.le (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
          readK_bit ins h3.le (hs _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))]
    · rw [closedRow_pack (by omega) (by omega) h3, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [length_packAll_pw]; omega), Option.getD_none, ← gateBits_K]
      exact gateBits_K_idle _ _

/-- **The honest cells hold every gate.** -/
theorem gates_honest (w : Secret) (rows : Fin randomWords → K) : GatesIdx (wH w rows) := by
  intro r hr
  unfold wH
  by_cases hR : 2 ^ 22 - 16 ≤ r
  · have e : ∀ j < 4, (hArr w rows).getD (4 * r + j) 0 = shapeVal rows (2 ^ 22 - 1 - r) j :=
      fun j hj => hArr_random w rows r j hR hr hj
    have e0 := e 0 (by norm_num)
    simp only [Nat.add_zero] at e0
    rw [e0, e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num)]
    exact gate_shape _ _
  · have e : ∀ j < 4, (hArr w rows).getD (4 * r + j) 0 = _ := fun j hj => hArr_row w rows r j (by omega) hj
    have e0 := e 0 (by norm_num)
    simp only [Nat.add_zero] at e0
    rw [e0, e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num)]
    simp only [ite_true, show (1 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num,
      show (3 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 1 by norm_num, show (3 : ℕ) ≠ 2 by norm_num, ite_false]
    rw [outK_gate _ r (by omega)]
    exact gate_ofK _ _ _

/-! ## The copies -/

/-- The value of a slot: `0`, `1`, `3`, or row `r`'s `V` cell. -/
noncomputable def valS (w : Secret) (rows : Fin randomWords → K) (a : ℕ) : E :=
  if a = 0 then 0 else if a = 1 then 1 else if a = 2 then ofK three else wH w rows (4 * (a - 3) + 3)

theorem valS_zero (w : Secret) (rows : Fin randomWords → K) : valS w rows 0 = 0 := by
  unfold valS; rw [if_pos rfl]

theorem valS_one (w : Secret) (rows : Fin randomWords → K) : valS w rows 1 = 1 := by
  unfold valS; rw [if_neg (by norm_num), if_pos rfl]

theorem valS_two (w : Secret) (rows : Fin randomWords → K) : valS w rows 2 = ofK three := by
  unfold valS; rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

theorem valS_row (w : Secret) (rows : Fin randomWords → K) (r : ℕ) : valS w rows (3 + r) = wH w rows (4 * r + 3) := by
  unfold valS; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show 3 + r - 3 = r by omega]

theorem hArr_out (w : Secret) (rows : Fin randomWords → K) (r : ℕ) (hr : r < 2 ^ 22 - 16) :
    (hArr w rows).getD (4 * r + 3) 0 = ((membership 22).outputsK (membershipInputs w)).getD r 0 := by
  rw [hArr_row w rows r 3 hr (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]

/-- A non-random row's reading cell holds its slot's value. -/
theorem read_val (w : Secret) (rows : Fin randomWords → K) {s : Src} {a : ℕ} (hs : kSlot s = some a)
    (hrow : ∀ r', s = .row r' → r' < 2 ^ 22 - 16) :
    ofK (readK ((membership 22).outputsK (membershipInputs w)) s) = valS w rows a := by
  cases s with
  | zero => obtain rfl := Option.some.inj hs; rw [readK_zero, ofK_zero, valS_zero]
  | one => obtain rfl := Option.some.inj hs; rw [readK_one, ofK_one, valS_one]
  | three => obtain rfl := Option.some.inj hs; rw [valS_two]; rfl
  | free => cases hs
  | row r' =>
    obtain rfl := Option.some.inj hs
    have hr := hrow r' rfl
    rw [valS_row]
    unfold wH
    rw [hArr_out w rows r' hr, readK_row]

/-- A random row's non-free cell holds its slot's value. -/
theorem rand_val (w : Secret) (rows : Fin randomWords → K) (k j : ℕ) (hj : j < 3) {a : ℕ}
    (hs : kSlot (if j = 0 then (RandomShape.of k).row.x else if j = 1 then (RandomShape.of k).row.y
      else (RandomShape.of k).row.c) = some a) :
    ofK (shapeVal rows k j) = valS w rows a := by
  unfold shapeVal
  generalize RandomShape.of k = sh at hs ⊢
  cases sh <;> interval_cases j <;> simp only [RandomShape.row, RandomShape.cells, kSlot] at hs ⊢ <;>
    cases hs <;> simp [valS, ofK_zero, ofK_one]

theorem slot_cell (r j : ℕ) (hr : r < 2 ^ 22) (hj : j < 3) :
    slotOfCell (membership 22).rows (4 * r + j) =
      kSlot (if j = 0 then (closedRow r).x else if j = 1 then (closedRow r).y else (closedRow r).c) := by
  interval_cases j
  · exact slot_x r hr
  · exact slot_y r hr
  · exact slot_c r hr

/-- **A cell of a slot holds the slot's value.** -/
theorem slot_val (w : Secret) (rows : Fin randomWords → K) {c a : ℕ} (hc : c < 4 * 2 ^ 22)
    (h : slotOfCell (membership 22).rows c = some a) : wH w rows c = valS w rows a := by
  obtain ⟨r, j, hj, rfl⟩ : ∃ r j, j < 4 ∧ c = 4 * r + j := ⟨c / 4, c % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  have hr : r < 2 ^ 22 := by omega
  by_cases h3 : j = 3
  · subst h3
    rw [slotOfCell_out] at h
    obtain rfl := Option.some.inj h
    rw [valS_row]
  rw [slot_cell r j hr (by omega)] at h
  by_cases hR : 2 ^ 22 - 16 ≤ r
  · unfold wH
    rw [hArr_random w rows r j hR hr hj]
    rw [closedRow_random (by omega) hR] at h
    exact rand_val w rows _ j (by omega) h
  · unfold wH
    rw [hArr_row w rows r j (by omega) hj]
    have hb := closedRow_reads r
    have hS := size_lt_random
    interval_cases j
    · exact read_val w rows h fun r' e => by have := hb.1 r' e; omega
    · exact read_val w rows h fun r' e => by have := hb.2.1 r' e; omega
    · exact read_val w rows h fun r' e => by have := hb.2.2 r' e; omega
    · exact absurd rfl h3

/-- **The honest cells hold every copy.** -/
theorem copies_honest (w : Secret) (rows : Fin randomWords → K) : CopiesIdx (wH w rows) := by
  intro c hc
  have hsz := rows_size
  have hc' : c < 4 * (membership 22).rows.size := by rw [hsz]; exact hc
  rcases hsl : slotOfCell (membership 22).rows c with _ | a
  · rw [sigC_eq, sigma_free _ _ cell_slots_lt hc' hsl]
  · obtain ⟨hlt, hsl'⟩ := sigma_slot _ _ cell_slots_lt hc' hsl
    rw [← sigC_eq] at hlt hsl'
    rw [slot_val w rows (by rw [hsz] at hlt; exact hlt) hsl', slot_val w rows hc hsl]

/-- **The honest cells hold the constants' pins.** -/
theorem pinsC_honest (w : Secret) (rows : Fin randomWords → K) : PinsC (wH w rows) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [slot_val w rows (by norm_num) (anchor_c 8 (by norm_num) (by norm_num)), show 8 - 8 = 0 from rfl, valS_zero]
  · rw [slot_val w rows (by norm_num) (anchor_c 9 (by norm_num) (by norm_num)), show 9 - 8 = 1 from rfl, valS_one]
  · rw [slot_val w rows (by norm_num) (anchor_c 10 (by norm_num) (by norm_num)), show 10 - 8 = 2 from rfl, valS_two]

end Kc3Closed
