-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from this repository's `formal/EndToEnd/Bridge/Circuit/Wiring.lean` and `formal/Circuit/Circuit/Wiring.lean`
-- (commit `f96a7938`'s circuit) to the deployed circuit's wiring: the slots `0`, `1`, `3` and rows, a free cell
-- joining none.
import Kc3Circuit.BridgeSim
import Circuit.Wiring

/-!
# The wiring σ of the deployed circuit

The Statement's `wiring` (`formal/Statement/PcsQuotient/Circuit.lean`, `finish`): every row's `V` cell joins its row's
slot, then every row's `X`, `Y`, `C` cell the slot of what it reads (`0`, `1`, `3`, or a row), a free cell none.
`wiring_eq_joins`: it is the fold of `PcsCircuit.join` over that list of joins (`joins`), so `formal/Circuit`'s
`JoinInv` describes it (`joins_inv`): **on the cells, σ is the cyclic successor in its slot's list of cells, and fixes
a free cell** (`sigma_lt`, `sigma_inj`, `sigma_slot`, `sigma_free`, `slot_reach`).
-/

namespace Kc3Wiring

open PcsCircuit (Joins join JoinInv cellsOf OneSlot Cyclic iter)

/-! ## The statement's wiring as folds -/

/-- `finish`'s `slot`: `0`, `1`, `3` at `0`, `1`, `2`, row `r` at `3 + r`, a free cell none. -/
def kSlot : PcsQuotient.Src → Option ℕ
  | .zero => some 0
  | .one => some 1
  | .three => some 2
  | .row r => some (3 + r)
  | .free => none

/-- One join of the statement's `finish`: `cell` joins the cycle of slot `at_`, the sentinel `none` for a slot
without a cell. -/
def qJoin (none : ℕ) (s : Array ℕ × Array ℕ × Array ℕ) (at_ cell : ℕ) : Array ℕ × Array ℕ × Array ℕ :=
  if s.1[at_]! = none then
    (s.1.set! at_ cell, s.2.1.set! at_ cell, s.2.2.set! cell (s.1.set! at_ cell)[at_]!)
  else (s.1, s.2.1.set! at_ cell, (s.2.2.set! s.2.1[at_]! cell).set! cell s.1[at_]!)

/-- A join to an optional slot: none for a free cell. -/
def qJoinO (none : ℕ) (s : Array ℕ × Array ℕ × Array ℕ) (o : Option ℕ) (cell : ℕ) :
    Array ℕ × Array ℕ × Array ℕ :=
  match o with
  | Option.none => s
  | some at_ => qJoin none s at_ cell

/-- The statement's wiring, its loops as folds. -/
def wiringFoldQ (logRows : ℕ) (rows : Array PcsQuotient.Row) : Array ℕ × Array ℕ × Array ℕ :=
  let n := 2 ^ logRows
  let st₀ := (Array.replicate (n + 3) (4 * n), Array.replicate (n + 3) (4 * n), Array.range (4 * n))
  let st₁ := (List.range n).foldl (fun st r => qJoin (4 * n) st (3 + r) (4 * r + 3)) st₀
  (List.range n).foldl (fun st r =>
    let row := rows.getD r PcsQuotient.idle
    qJoinO (4 * n) (qJoinO (4 * n) (qJoinO (4 * n) st (kSlot row.x) (4 * r)) (kSlot row.y) (4 * r + 1))
      (kSlot row.c) (4 * r + 2)) st₁

theorem forIn_id_yield {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β))
    (g : β → α → β) (h : ∀ a b, f a b = pure (.yield (g b a))) :
    forIn l init f = pure (l.foldl g init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => rw [List.forIn_cons, h, pure_bind, List.foldl_cons]; exact ih _

theorem forIn_range_id {β : Type} (n : ℕ) (init : β) (f : ℕ → β → Id (ForInStep β)) :
    forIn [:n] init f = forIn (List.range n) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp [Std.Legacy.Range.size, List.range_eq_range']

theorem ite_pure_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

theorem wiring_eq_fold (logRows : ℕ) (rows : Array PcsQuotient.Row) :
    PcsQuotient.wiring logRows rows = (wiringFoldQ logRows rows).2.2 := by
  unfold PcsQuotient.wiring wiringFoldQ
  simp only [forIn_range_id]
  rw [forIn_id_yield (g := fun st r => qJoin (4 * 2 ^ logRows) st (3 + r) (4 * r + 3))]
  · simp only [pure_bind]
    rw [forIn_id_yield (g := fun st r =>
      qJoinO (4 * 2 ^ logRows) (qJoinO (4 * 2 ^ logRows) (qJoinO (4 * 2 ^ logRows) st
        (kSlot (rows.getD r PcsQuotient.idle).x) (4 * r)) (kSlot (rows.getD r PcsQuotient.idle).y)
        (4 * r + 1)) (kSlot (rows.getD r PcsQuotient.idle).c) (4 * r + 2))]
    · rfl
    · intro r s
      rw [forIn_id_yield (g := fun st (a : ℕ × PcsQuotient.Src) =>
        qJoinO (4 * 2 ^ logRows) st (kSlot a.2) (4 * r + a.1))]
      · simp only [List.foldl_cons, List.foldl_nil, pure_bind, Nat.add_zero, Prod.mk.eta]
      · intro a st
        obtain ⟨k, src⟩ := a
        cases src <;> simp only [ite_pure_yield, qJoinO, qJoin, kSlot] <;> rfl
  · intro r s
    simp only [ite_pure_yield, qJoin]

/-! ## The two states, related -/

theorem getElem!_eq_getD (a : Array ℕ) (i : ℕ) : a[i]! = a.getD i 0 := by
  simp only [Array.getD_eq_getD_getElem?, getElem!_def]
  cases a[i]? <;> rfl

/-- The statement's state (numbers, the sentinel `4n`) and `formal/Circuit`'s (`Option`s), `n + 3` slots. -/
structure JRel (n : ℕ) (s : Array ℕ × Array ℕ × Array ℕ) (st : Joins) : Prop where
  sigma : s.2.2 = st.sigma
  fsize : s.1.size = n + 3
  lsize : s.2.1.size = n + 3
  pfsize : st.first.size = n + 3
  plsize : st.last.size = n + 3
  none_ : ∀ i < n + 3, st.first.getD i none = none → s.1.getD i 0 = 4 * n
  some_ : ∀ i < n + 3, ∀ f, st.first.getD i none = some f →
    s.1.getD i 0 = f ∧ f < 4 * n ∧ ∃ l, st.last.getD i none = some l ∧ s.2.1.getD i 0 = l

theorem jRel_join {n : ℕ} {s : Array ℕ × Array ℕ × Array ℕ} {st : Joins}
    (h : JRel n s st) {at_ cell : ℕ} (ha : at_ < n + 3) (hc : cell < 4 * n) :
    JRel n (qJoin (4 * n) s at_ cell) (join st at_ cell) := by
  obtain ⟨first, last, sigma⟩ := st
  obtain ⟨f₁, l₁, σ₁⟩ := s
  unfold qJoin join
  simp only [getElem!_eq_getD]
  rcases hf : first.getD at_ none with _ | f
  · have h1 := h.none_ at_ ha hf
    simp only [h1, if_true]
    have hfs : at_ < f₁.size := by rw [h.fsize]; exact ha
    rw [PcsCircuit.getD_set!_eq _ _ _ hfs]
    refine ⟨by have := h.sigma; simp only at this ⊢; rw [this], by simp [PcsCircuit.size_set!, h.fsize],
      by simp [PcsCircuit.size_set!, h.lsize], by simp [PcsCircuit.size_set!, h.pfsize],
      by simp [PcsCircuit.size_set!, h.plsize], ?_, ?_⟩
    · intro i hi hn
      by_cases hia : at_ = i
      · subst hia
        rw [PcsCircuit.getD_set!_eq _ _ _ (by rw [h.pfsize]; exact ha)] at hn
        cases hn
      · rw [PcsCircuit.getD_set!_ne _ _ _ hia] at hn
        rw [PcsCircuit.getD_set!_ne _ _ _ hia]
        exact h.none_ i hi hn
    · intro i hi f hs
      by_cases hia : at_ = i
      · subst hia
        rw [PcsCircuit.getD_set!_eq _ _ _ (by rw [h.pfsize]; exact ha)] at hs
        cases hs
        refine ⟨PcsCircuit.getD_set!_eq _ _ _ hfs, hc, cell, ?_, ?_⟩
        · exact PcsCircuit.getD_set!_eq _ _ _ (by rw [h.plsize]; exact ha)
        · exact PcsCircuit.getD_set!_eq _ _ _ (by rw [h.lsize]; exact ha)
      · rw [PcsCircuit.getD_set!_ne _ _ _ hia] at hs
        obtain ⟨e1, e2, l, e3, e4⟩ := h.some_ i hi f hs
        exact ⟨by rw [PcsCircuit.getD_set!_ne _ _ _ hia]; exact e1, e2, l,
          by rw [PcsCircuit.getD_set!_ne _ _ _ hia]; exact e3,
          by rw [PcsCircuit.getD_set!_ne _ _ _ hia]; exact e4⟩
  · obtain ⟨e1, e2, l, e3, e4⟩ := h.some_ at_ ha f hf
    have hne : f ≠ 4 * n := by omega
    simp only [e1, hne, if_false, e4, e3, Option.getD_some]
    refine ⟨by have := h.sigma; simp only at this ⊢; rw [this], h.fsize, by simp [PcsCircuit.size_set!, h.lsize],
      h.pfsize, by simp [PcsCircuit.size_set!, h.plsize], ?_, ?_⟩
    · intro i hi hn
      exact h.none_ i hi hn
    · intro i hi f' hs
      obtain ⟨g1, g2, l', g3, g4⟩ := h.some_ i hi f' hs
      by_cases hia : at_ = i
      · subst hia
        exact ⟨g1, g2, cell, PcsCircuit.getD_set!_eq _ _ _ (by rw [h.plsize]; exact ha),
          PcsCircuit.getD_set!_eq _ _ _ (by rw [h.lsize]; exact ha)⟩
      · exact ⟨g1, g2, l', by rw [PcsCircuit.getD_set!_ne _ _ _ hia]; exact g3,
          by rw [PcsCircuit.getD_set!_ne _ _ _ hia]; exact g4⟩

theorem jRel_init (n : ℕ) :
    JRel n (Array.replicate (n + 3) (4 * n), Array.replicate (n + 3) (4 * n), Array.range (4 * n))
      ⟨Array.replicate (n + 3) none, Array.replicate (n + 3) none, Array.range (4 * n)⟩ := by
  refine ⟨rfl, by simp, by simp, by simp, by simp, fun i hi _ => ?_, fun i hi f hs => ?_⟩
  · simp [Array.getD_eq_getD_getElem?, hi]
  · simp [Array.getD_eq_getD_getElem?, hi] at hs

/-! ## The joins -/

/-- The joins of the `V` cells: row `r`'s output cell `4 r + 3` to slot `3 + r`. -/
def outJoins (n : ℕ) : List (ℕ × ℕ) := (List.range n).map fun r => (3 + r, 4 * r + 3)

/-- The joins of row `r`'s reading cells: its `X`, `Y`, `C` cells to the slots of what they read, a free cell
none. -/
def rowJoins (row : PcsQuotient.Row) (r : ℕ) : List (ℕ × ℕ) :=
  [(kSlot row.x, 4 * r), (kSlot row.y, 4 * r + 1), (kSlot row.c, 4 * r + 2)].filterMap
    fun p => p.1.map fun a => (a, p.2)

/-- The joins of the reading cells. -/
def readJoins (rows : Array PcsQuotient.Row) (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun r => rowJoins (rows.getD r PcsQuotient.idle) r

/-- The joins, in `finish`'s order. -/
def joins (rows : Array PcsQuotient.Row) (n : ℕ) : List (ℕ × ℕ) := outJoins n ++ readJoins rows n

/-- The initial state of `formal/Circuit`'s joins on `n` rows. -/
def joins₀ (n : ℕ) : Joins := ⟨Array.replicate (n + 3) none, Array.replicate (n + 3) none, Array.range (4 * n)⟩

theorem qJoinO_rel {n : ℕ} {s : Array ℕ × Array ℕ × Array ℕ} {st : Joins} (h : JRel n s st) (o : Option ℕ)
    (cell : ℕ) (ho : ∀ a, o = some a → a < n + 3) (hc : cell < 4 * n) :
    JRel n (qJoinO (4 * n) s o cell) ((((o, cell) : Option ℕ × ℕ) :: []).filterMap
      (fun p => p.1.map fun a => (a, p.2)) |>.foldl (fun st p => join st p.1 p.2) st) := by
  cases o with
  | none => exact h
  | some a => exact jRel_join h (ho a rfl) hc

/-- **The statement's σ is the fold of the joins**, on `2^logRows` rows whose sources read slots below `n + 3`. -/
theorem wiring_eq_joins (logRows : ℕ) (rows : Array PcsQuotient.Row) (hn : rows.size = 2 ^ logRows)
    (hs : ∀ r < rows.size, ∀ a, (kSlot (rows.getD r PcsQuotient.idle).x = some a ∨
      kSlot (rows.getD r PcsQuotient.idle).y = some a ∨ kSlot (rows.getD r PcsQuotient.idle).c = some a) →
      a < rows.size + 3) :
    PcsQuotient.wiring logRows rows =
      ((joins rows rows.size).foldl (fun st p => join st p.1 p.2) (joins₀ rows.size)).sigma := by
  rw [wiring_eq_fold]
  unfold wiringFoldQ joins outJoins readJoins joins₀
  rw [List.foldl_append, List.foldl_map, List.foldl_flatMap]
  simp only [hn]
  rw [hn] at hs
  generalize 2 ^ logRows = n at hs ⊢
  have h1 : ∀ (l : List ℕ) (s : Array ℕ × Array ℕ × Array ℕ) (st : Joins),
      (∀ r ∈ l, r < n) → JRel n s st →
      JRel n (l.foldl (fun st r => qJoin (4 * n) st (3 + r) (4 * r + 3)) s)
        (l.foldl (fun st r => join st (3 + r) (4 * r + 3)) st) := by
    intro l
    induction l with
    | nil => intro s st _ h; exact h
    | cons r l ih =>
      intro s st hl h
      have hr := hl r (List.mem_cons_self ..)
      exact ih _ _ (fun r' h' => hl r' (List.mem_cons_of_mem _ h')) (jRel_join h (by omega) (by omega))
  have h2 : ∀ (l : List ℕ) (s : Array ℕ × Array ℕ × Array ℕ) (st : Joins),
      (∀ r ∈ l, r < n) → JRel n s st →
      JRel n (l.foldl (fun st r =>
          qJoinO (4 * n) (qJoinO (4 * n) (qJoinO (4 * n) st (kSlot (rows.getD r PcsQuotient.idle).x)
            (4 * r)) (kSlot (rows.getD r PcsQuotient.idle).y) (4 * r + 1))
            (kSlot (rows.getD r PcsQuotient.idle).c) (4 * r + 2)) s)
        (l.foldl (fun st r => (rowJoins (rows.getD r PcsQuotient.idle) r).foldl
          (fun st p => join st p.1 p.2) st) st) := by
    intro l
    induction l with
    | nil => intro s st _ h; exact h
    | cons r l ih =>
      intro s st hl h
      have hr := hl r (List.mem_cons_self ..)
      refine ih _ _ (fun r' h' => hl r' (List.mem_cons_of_mem _ h')) ?_
      have hx := fun a ha => hs r hr a (Or.inl ha)
      have hy := fun a ha => hs r hr a (Or.inr (Or.inl ha))
      have hc := fun a ha => hs r hr a (Or.inr (Or.inr ha))
      have e : rowJoins (rows.getD r PcsQuotient.idle) r =
          ([(kSlot (rows.getD r PcsQuotient.idle).x, 4 * r)].filterMap fun p => p.1.map fun a => (a, p.2)) ++
          ([(kSlot (rows.getD r PcsQuotient.idle).y, 4 * r + 1)].filterMap fun p => p.1.map fun a => (a, p.2)) ++
          ([(kSlot (rows.getD r PcsQuotient.idle).c, 4 * r + 2)].filterMap fun p => p.1.map fun a => (a, p.2)) := by
        unfold rowJoins
        simp only [List.filterMap_cons, List.filterMap_nil]
        cases kSlot (rows.getD r PcsQuotient.idle).x <;> cases kSlot (rows.getD r PcsQuotient.idle).y <;>
          cases kSlot (rows.getD r PcsQuotient.idle).c <;> rfl
      beta_reduce
      rw [e, List.foldl_append, List.foldl_append]
      exact qJoinO_rel (qJoinO_rel (qJoinO_rel h _ _ hx (by omega)) _ _ hy (by omega)) _ _ hc (by omega)
  exact (h2 _ _ _ (fun r h => List.mem_range.mp h)
    (h1 _ _ _ (fun r h => List.mem_range.mp h) (jRel_init n))).sigma

/-! ## The joins' invariant -/

/-- The slot cell `c` joins: its row's for a `V` cell, what it reads otherwise (none for a free cell). -/
def slotOfCell (rows : Array PcsQuotient.Row) (c : ℕ) : Option ℕ :=
  if c % 4 = 0 then kSlot (rows.getD (c / 4) PcsQuotient.idle).x
  else if c % 4 = 1 then kSlot (rows.getD (c / 4) PcsQuotient.idle).y
  else if c % 4 = 2 then kSlot (rows.getD (c / 4) PcsQuotient.idle).c
  else some (3 + c / 4)

theorem mem_rowJoins {row : PcsQuotient.Row} {r a c : ℕ} :
    (a, c) ∈ rowJoins row r ↔
      (c = 4 * r ∧ kSlot row.x = some a) ∨ (c = 4 * r + 1 ∧ kSlot row.y = some a) ∨
        (c = 4 * r + 2 ∧ kSlot row.c = some a) := by
  unfold rowJoins
  simp only [List.mem_filterMap, List.mem_cons, List.mem_nil_iff, or_false, Option.map_eq_some_iff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨p, hp, a', ha', rfl, rfl⟩
    rcases hp with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, ha'⟩
    · exact Or.inr (Or.inl ⟨rfl, ha'⟩)
    · exact Or.inr (Or.inr ⟨rfl, ha'⟩)
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨_, Or.inl rfl, a, h, rfl, rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), a, h, rfl, rfl⟩
    · exact ⟨_, Or.inr (Or.inr rfl), a, h, rfl, rfl⟩

/-- **A join of `c` is to the slot of `c`.** -/
theorem mem_joins_iff (rows : Array PcsQuotient.Row) (n a c : ℕ) :
    (a, c) ∈ joins rows n ↔ c < 4 * n ∧ slotOfCell rows c = some a := by
  unfold joins outJoins readJoins slotOfCell
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap, Prod.mk.injEq, mem_rowJoins]
  constructor
  · rintro (⟨r, hr, rfl, rfl⟩ | ⟨r, hr, (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)⟩)
    · refine ⟨by omega, ?_⟩
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show (4 * r + 3) / 4 = r by omega]
    · refine ⟨by omega, ?_⟩
      rw [if_pos (by omega), show 4 * r / 4 = r by omega, h]
    · refine ⟨by omega, ?_⟩
      rw [if_neg (by omega), if_pos (by omega), show (4 * r + 1) / 4 = r by omega, h]
    · refine ⟨by omega, ?_⟩
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show (4 * r + 2) / 4 = r by omega, h]
  · rintro ⟨hc, h⟩
    by_cases h3 : c % 4 = 3
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h
      cases h
      exact Or.inl ⟨c / 4, by omega, rfl, by omega⟩
    · refine Or.inr ⟨c / 4, by omega, ?_⟩
      by_cases h0 : c % 4 = 0
      · rw [if_pos h0] at h; exact Or.inl ⟨by omega, h⟩
      · by_cases h1 : c % 4 = 1
        · rw [if_neg h0, if_pos h1] at h; exact Or.inr (Or.inl ⟨by omega, h⟩)
        · rw [if_neg h0, if_neg h1, if_pos (by omega)] at h; exact Or.inr (Or.inr ⟨by omega, h⟩)

theorem joins_oneSlot (rows : Array PcsQuotient.Row) (n : ℕ) : OneSlot (joins rows n) := by
  unfold OneSlot joins outJoins readJoins
  rw [List.map_append, List.map_map, List.map_flatMap]
  refine List.nodup_append.mpr ⟨?_, ?_, fun x hx y hy => ?_⟩
  · exact List.Nodup.map (f := fun r => 4 * r + 3) (fun a b h => by simp only at h; omega) List.nodup_range
  · refine (List.nodup_flatMap).mpr ⟨fun r _ => ?_, ?_⟩
    · unfold rowJoins
      simp only [List.filterMap_cons, List.filterMap_nil]
      cases kSlot (rows.getD r PcsQuotient.idle).x <;> cases kSlot (rows.getD r PcsQuotient.idle).y <;>
        cases kSlot (rows.getD r PcsQuotient.idle).c <;> simp <;> omega
    · refine List.nodup_range.pairwise_of_forall_ne fun r _ s _ hrs => ?_
      intro x hx hy
      simp only [List.mem_map] at hx hy
      obtain ⟨⟨a, c⟩, hc, rfl⟩ := hx
      obtain ⟨⟨b, d⟩, hd, hxy⟩ := hy
      rcases mem_rowJoins.mp hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
        rcases mem_rowJoins.mp hd with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp only at hxy <;> omega
  · simp only [List.mem_map, List.mem_range, Function.comp] at hx
    obtain ⟨r, _, rfl⟩ := hx
    simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hy
    obtain ⟨s, _, ⟨a, c⟩, hc, rfl⟩ := hy
    rcases mem_rowJoins.mp hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp only <;> omega

/-- The joins' slots and cells are in range, for rows reading slots below `n + 3`. -/
theorem joins_bounds (rows : Array PcsQuotient.Row) (n : ℕ)
    (hs : ∀ c < 4 * n, ∀ a, slotOfCell rows c = some a → a < n + 3) :
    ∀ p ∈ joins rows n, p.1 < n + 3 ∧ p.2 < 4 * n := by
  rintro ⟨a, c⟩ hp
  obtain ⟨hc, h⟩ := (mem_joins_iff rows n a c).mp hp
  exact ⟨hs c hc a h, hc⟩

/-- **The invariant of the joins**: σ the cyclic successor in each slot's list of cells, the cells joined to no
slot fixed. -/
theorem joins_inv (rows : Array PcsQuotient.Row) (n : ℕ)
    (hs : ∀ c < 4 * n, ∀ a, slotOfCell rows c = some a → a < n + 3) :
    JoinInv (joins rows n) (n + 3) (4 * n)
      ((joins rows n).foldl (fun st p => join st p.1 p.2) (joins₀ n)) := by
  have h := PcsCircuit.joinInv_foldl (S := n + 3) (N := 4 * n) (joins rows n) [] (joins₀ n)
    (by have := PcsCircuit.joinInv_nil (n + 3) (4 * n); exact this)
    (by rw [List.nil_append]; exact joins_oneSlot rows n)
    (by rw [List.nil_append]; exact joins_bounds rows n hs)
  rw [List.nil_append] at h
  exact h

/-! ## σ on the cells -/

section Sigma

variable (rows : Array PcsQuotient.Row) (n : ℕ)
  (hs : ∀ c < 4 * n, ∀ a, slotOfCell rows c = some a → a < n + 3)

/-- σ as a function. -/
def sig (st : Joins) (c : ℕ) : ℕ := st.sigma.getD c 0

theorem mem_cells {c a : ℕ} (hc : c < 4 * n) (h : slotOfCell rows c = some a) :
    c ∈ cellsOf (joins rows n) a :=
  PcsCircuit.mem_cellsOf_of_mem ((mem_joins_iff rows n a c).mpr ⟨hc, h⟩)

include hs in
/-- **σ keeps a cell's slot**, and maps the cells to cells. -/
theorem sigma_slot {c a : ℕ} (hc : c < 4 * n) (h : slotOfCell rows c = some a) :
    sig ((joins rows n).foldl (fun st p => join st p.1 p.2) (joins₀ n)) c < 4 * n ∧
      slotOfCell rows (sig ((joins rows n).foldl (fun st p => join st p.1 p.2) (joins₀ n)) c) = some a := by
  have hinv := joins_inv rows n hs
  have ha := hs c hc a h
  have hm := PcsCircuit.cyc_mem (hinv.cyc a ha) (mem_cells rows n hc h)
  exact (mem_joins_iff rows n a _).mp (PcsCircuit.mem_cellsOf hm)

include hs in
/-- **σ fixes a free cell.** -/
theorem sigma_free {c : ℕ} (hc : c < 4 * n) (h : slotOfCell rows c = none) :
    sig ((joins rows n).foldl (fun st p => join st p.1 p.2) (joins₀ n)) c = c := by
  refine (joins_inv rows n hs).fixed c hc fun hm => ?_
  obtain ⟨⟨a, c'⟩, hp, rfl⟩ := List.mem_map.mp hm
  rw [((mem_joins_iff rows n a _).mp hp).2] at h
  cases h

include hs in
theorem sigma_lt {c : ℕ} (hc : c < 4 * n) :
    sig ((joins rows n).foldl (fun st p => join st p.1 p.2) (joins₀ n)) c < 4 * n := by
  rcases h : slotOfCell rows c with _ | a
  · rw [sigma_free rows n hs hc h]; exact hc
  · exact (sigma_slot rows n hs hc h).1

include hs in
/-- **σ is injective on the cells.** -/
theorem sigma_inj {c d : ℕ} (hc : c < 4 * n) (hd : d < 4 * n)
    (h : sig ((joins rows n).foldl (fun st p => join st p.1 p.2) (joins₀ n)) c =
      sig ((joins rows n).foldl (fun st p => join st p.1 p.2) (joins₀ n)) d) : c = d := by
  have hinv := joins_inv rows n hs
  rcases hsc : slotOfCell rows c with _ | a <;> rcases hsd : slotOfCell rows d with _ | b
  · rwa [sigma_free rows n hs hc hsc, sigma_free rows n hs hd hsd] at h
  · rw [sigma_free rows n hs hc hsc] at h
    have := (sigma_slot rows n hs hd hsd).2
    rw [← h, hsc] at this
    cases this
  · rw [sigma_free rows n hs hd hsd] at h
    have := (sigma_slot rows n hs hc hsc).2
    rw [h, hsd] at this
    cases this
  · have h1 := (sigma_slot rows n hs hc hsc).2
    have h2 := (sigma_slot rows n hs hd hsd).2
    rw [h, h2] at h1
    cases h1
    exact PcsCircuit.cyc_inj (PcsCircuit.cellsOf_nodup (joins_oneSlot rows n) _)
      (hinv.cyc a (hs c hc a hsc)) (mem_cells rows n hc hsc) (mem_cells rows n hd hsd) h

include hs in
/-- **Two cells of one slot are on one cycle.** -/
theorem slot_reach {c d a : ℕ} (hc : c < 4 * n) (hd : d < 4 * n) (h1 : slotOfCell rows c = some a)
    (h2 : slotOfCell rows d = some a) :
    ∃ k, iter (sig ((joins rows n).foldl (fun st p => join st p.1 p.2) (joins₀ n))) k c = d :=
  PcsCircuit.cyc_reach ((joins_inv rows n hs).cyc a (hs c hc a h1)) (mem_cells rows n hc h1)
    (mem_cells rows n hd h2)

end Sigma

end Kc3Wiring
