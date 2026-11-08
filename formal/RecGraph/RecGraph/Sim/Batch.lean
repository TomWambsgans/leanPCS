-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecGraph.Sim.Claims
import RecGraph.Sim.Transcript
import RecGraph.Sim.ComposeSpec

/-!
# The simulation: the batch's framework

The pieces of the paired batch's simulation that the Keccak VM's (`RecGraphKeccak.Sim.BatchK`, `sim_batchK`) uses:

* **Recorded shapes** (`Out p Q`: the program's recorded output satisfies `Q` from every state): `out_bind`,
  `out_forIn`; the sumchecks' points have their variables' length (`sumcheckPairsDrawn_out`), so the batch's point
  reaches every block of every stack.
* `Sim.withRecord`: a part's outputs are its recording's.
* The openings (commitment, `r.take vars`, value) represented (`RpOpening`); the layouts' variables
  (`layoutAt_vars_le`, `limbs_vars_le`).
-/

-- `Sim.withRecord` is a rule of the judgment `RecGraph.Sim.Sim`, in the framework's namespace.
set_option linter.dupNamespace false

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

/-! ## Recorded shapes -/

/-- **A program's recorded output satisfies `Q`**, from every state. -/
def Out {α : Type} (p : Prog α) (Q : α → Prop) : Prop := ∀ st, Q (p.record st).1

theorem out_pure {α : Type} {a : α} {Q : α → Prop} (h : Q a) : Out (pure a) Q := fun _ ↦ h

theorem out_any {α : Type} (p : Prog α) : Out p fun _ ↦ True := fun _ ↦ trivial

theorem out_bind {α β : Type} {p : Prog α} {k : α → Prog β} {Q : α → Prop} {R : β → Prop} (hp : Out p Q)
    (hk : ∀ a, Q a → Out (k a) R) : Out (p >>= k) R := fun st ↦ by
  rw [record_bind]
  exact hk _ (hp st) _

theorem out_forIn {α β : Type} (f : α → β → Prog (ForInStep β)) (I : ℕ → β → Prop)
    (hf : ∀ k a b, I k b → Out (f a b) fun r ↦ ∃ b', r = .yield b' ∧ I (k + 1) b') :
    ∀ (l : List α) (k : ℕ) (init : β), I k init → Out (forIn l init f) (I (k + l.length)) := by
  intro l
  induction l with
  | nil => intro k init h; exact out_pure h
  | cons a l ih =>
    intro k init h
    rw [List.forIn_cons]
    refine out_bind (hf k a init h) fun r ⟨b', hr, hb'⟩ ↦ ?_
    subst hr
    have e : k + (a :: l).length = k + 1 + l.length := by simp; omega
    rw [e]
    exact ih (k + 1) b' hb'

theorem pairPoint_out (z : Nat) : Out (Pi1.pairPoint z) fun l ↦ l.length = 2 := by
  unfold Pi1.pairPoint
  exact out_bind (out_any _) fun _ _ ↦ out_bind (out_any _) fun _ _ ↦ out_bind (out_any _) fun _ _ ↦
    out_bind (out_any _) fun _ _ ↦ out_bind (out_any _) fun _ _ ↦ out_pure rfl

theorem sumcheckDrawn_out (claim count : Nat) (eqs : List (Option Nat)) (narrow : Bool) :
    Out (Pi1.sumcheckDrawn claim count eqs narrow) fun r ↦ r.1.length = eqs.length := by
  unfold Pi1.sumcheckDrawn
  refine out_bind (out_forIn _ (fun k (b : Array Nat × Nat) ↦ b.1.size = k) ?_ eqs 0 (#[], claim) rfl)
    fun r hr ↦ out_pure ?_
  · intro k _ b hb
    exact out_bind (out_any _) fun _ _ ↦ out_bind (out_any _) fun _ _ ↦ out_bind (out_any _) fun _ _ ↦
      out_pure ⟨_, rfl, by simp [hb]⟩
  · simpa using hr

/-- **The paired sumcheck's point has its variables' length.** -/
theorem sumcheckPairsDrawn_out (claim degree vars : Nat) (narrow : Bool) :
    Out (Pi1.sumcheckPairsDrawn claim degree vars narrow) fun r ↦ r.1.length = vars := by
  unfold Pi1.sumcheckPairsDrawn
  dsimp only
  rw [forIn_range]
  refine out_bind (out_forIn _ (fun k (b : Array Nat × Array Nat × Nat) ↦ b.1.size = 2 * k) ?_
    (List.range' 0 (vars / 2 - 0)) 0 (#[], #[], claim) rfl) fun r hr ↦ ?_
  · intro k _ b hb
    refine out_bind (out_any _) fun _ _ ↦ out_bind (out_any _) fun _ _ ↦ out_bind (pairPoint_out _) fun pp hpp ↦
      out_bind (out_any _) fun _ _ ↦ out_pure ⟨_, rfl, ?_⟩
    simp only [Array.size_append, List.size_toArray, hb, hpp]
    ring
  · simp only [List.length_range', Nat.sub_zero, zero_add] at hr
    by_cases hodd : vars % 2 = 1
    · simp only [hodd, ↓reduceIte]
      refine out_bind (sumcheckDrawn_out _ _ _ _) fun le hle ↦ ?_
      obtain ⟨last, end_⟩ := le
      refine out_pure ?_
      simp only [List.length_cons, List.length_nil] at hle
      simp only [Array.length_toList, Array.size_append, List.size_toArray, hr, hle]
      omega
    · simp only [hodd, ↓reduceIte]
      refine out_pure ?_
      simp only [Array.length_toList, hr]
      omega

/-! ## The batch -/

/-- A commitment's layout, as the batch looks it up. -/
def layoutAt (layouts : List (Commitment × StackLayout)) (c : Commitment) : StackLayout :=
  ((layouts.find? (·.1 == c)).map (·.2)).getD default

/-- The batch's variables: the longest stack's. -/
def bvars (layouts : List (Commitment × StackLayout)) : ℕ := (layouts.map (·.2.vars)).foldl max 0

theorem foldl_max_le (l : List ℕ) (a : ℕ) : a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    obtain ⟨h1, h2⟩ := ih (max a x)
    refine ⟨(le_max_left a x).trans h1, fun y hy ↦ ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact (le_max_right a y).trans h1
    · exact h2 y hy

theorem layoutAt_vars_le (layouts : List (Commitment × StackLayout)) (c : Commitment) :
    (layoutAt layouts c).vars ≤ bvars layouts := by
  unfold layoutAt bvars
  cases h : layouts.find? (·.1 == c) with
  | none => exact Nat.zero_le _
  | some x =>
    exact (foldl_max_le _ 0).2 _ (List.mem_map.mpr ⟨x, List.mem_of_find?_eq_some h, rfl⟩)

theorem phc_psim {st : RecState} {α β : Type} {p : Prog α} {b : β} {R : RecState → α → β → Prop}
    (h : PHc st p fun a st' ↦ R st' a b) : PSim st p b R := h

section Batch

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- **A part's outputs are its recording's.** -/
theorem Sim.withRecord {st : RecState} {α β : Type} {p : Prog α} {u : ChanM Id β} {n ch : Nat}
    {R : RecState → α → β → Prop} (h : Sim π iv publicInput stream st p u n ch R) :
    Sim π iv publicInput stream st p u n ch fun st' a b ↦ R st' a b ∧ a = (p.record st).1 := by
  intro c hc hle
  obtain ⟨hs, hf⟩ := h c hc hle
  refine ⟨fun hr ↦ ?_, hf⟩
  obtain ⟨b, c', hu, hc', hcur, hch, hg, hR⟩ := hs hr
  exact ⟨b, c', hu, hc', hcur, hch, hg, hR, rfl⟩

/-- **An opening, represented**: the same commitment; a point claim (no bit-slice claim), its point and value
represented. -/
def RpOpening (st : RecState) (x : Commitment × List Nat × Nat) (y : Commitment × Opening) : Prop :=
  x.1 = y.1 ∧ ∃ pt v, y.2 = .point pt v none ∧ RpL π iv publicInput stream st x.2.1 pt ∧
    Rp π iv publicInput stream st x.2.2 v

theorem RpOpening.pgrow {st st' : RecState} (hg : Good st) (hs : PStep st st') {x : Commitment × List Nat × Nat}
    {y : Commitment × Opening} (h : RpOpening π iv publicInput stream st x y) :
    RpOpening π iv publicInput stream st' x y := by
  obtain ⟨h1, pt, v, h2, h3, h4⟩ := h
  exact ⟨h1, pt, v, h2, RpL.pgrow hg hs h3, Rp.pgrow hg hs h4⟩

theorem RpOpening.grow {st st' : RecState} (hk : KInv st) (hgr : Grows st st') {x : Commitment × List Nat × Nat}
    {y : Commitment × Opening} (h : RpOpening π iv publicInput stream st x y) :
    RpOpening π iv publicInput stream st' x y := by
  obtain ⟨h1, pt, v, h2, h3, h4⟩ := h
  exact ⟨h1, pt, v, h2, RpL.grow π iv publicInput stream hk hgr h3, Rp.grow π iv publicInput stream hk hgr h4⟩

end Batch

/-! ## The tail of `reduce`: one claim per commitment, then the batch -/

/-- A layout's blocks lie inside its stack: each block's variables at most the stack's. -/
theorem limbs_vars_le {L : StackLayout} (hal : UniSound.Ids.LayoutAligned L) (col : Column) :
    ∀ b ∈ L.limbs col, b.2.1 ≤ L.vars := by
  intro b hb
  unfold StackLayout.limbs at hb
  obtain ⟨blk, hblk, he⟩ := List.mem_filterMap.mp hb
  obtain ⟨c, l, v, o⟩ := blk
  by_cases hc : c = col
  · simp only [hc, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at he
    subst he
    have h := (hal _ hblk).2
    have h2 : 2 ^ v ≤ 2 ^ L.vars := le_trans (Nat.le_add_left _ _) h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  · simp [hc] at he

theorem foldl_filterMapC {α β : Type} (f : α → Option β) (l : List α) (a0 : List β) :
    l.foldl (fun acc x ↦ acc ++ (f x).toList) a0 = a0 ++ l.filterMap f := by
  induction l generalizing a0 with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, List.filterMap_cons]
    cases f x <;> simp

section Tail

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

theorem filterMap_length_congrC {α β γ : Type} (f : α → Option β) (g : α → Option γ)
    (h : ∀ x, (f x).isSome = (g x).isSome) : ∀ l : List α, (l.filterMap f).length = (l.filterMap g).length
  | [] => rfl
  | x :: l => by
    rw [List.filterMap_cons, List.filterMap_cons]
    have hx := h x
    cases hf : f x <;> cases hg : g x <;> rw [hf, hg] at hx <;> simp at hx <;>
      simp [filterMap_length_congrC f g h l]

end Tail

end RecGraph.Sim
