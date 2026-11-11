-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: the four-root chain's bad events with each root's candidates pinned by its out-of-domain answer. The
-- parse, the collisions, the trace and the fresh-query engine are `ListChain4.lean`'s, `TwoOracle4.lean`'s and
-- `AdversaryLog4.lean`'s (this repository), reused as they are or copied with the candidates replaced.
import ComposePcs.AdversaryLog4

/-!
# The four-root chain, each root's candidates pinned by its out-of-domain answer

`ListChain4.lean` bounds each challenge after the four roots over every tuple of their list candidates
(`listFactor4 < 2^50` at the certified lists). But each root is absorbed with its out-of-domain answer `o`, and the
out-of-domain point `z` is a function of the root (`oodPointWith`: Keccak-256 at inputs of `46` bytes, never a
chain input). So the candidates a challenge must be good for are the **pinned** ones: those whose polynomial has
the answer `o` at `z`; and when the root's list is separated at `z` there is at most one.

**A pin** (`Pin`): a list commitment of the committed objects (`C`: a WHIR root's columns) and a predicate
`ok T r o n` (the object `n` has answer `o` at the root's point), which reads the table at the inputs `zin` only.
`Pin.Mem`: a pinned candidate; `Pin.One`: the root has at most one. `Pins4` holds the four roots' pins, F1's read
of `W`'s object (`rdW`) and the parts' assembly (`asm`), and the inputs `zin` the pins read, which are never chain
inputs (`zin_len`: no `32`, `128`, `192` or `320` bytes).

**The bad events** (`listBad4P`): a collision (`Coll4`, unchanged), or the chain's input after `W`'s commitment,
the parts', or the values, whose answer turns the reduction's state from lost to won for **the** pinned candidate
(tuple), each root having one (`Pins4.Tup`). The bad event reads the table at the out-of-domain inputs too, asked or
not: the fresh-query engine (`QuotientRpm.FreshBad`) lets it look at the whole table.

**`prEvent_pinned_le`**: in a uniform table, if `A m` reads the answers at `zin` only and has at most one solution
`m`, and `B m` reads the answers off `zin` only and has probability at most `ε` for each `m`, then
`∃ m, A m ∧ B m` has probability at most `ε`: the answers at `zin` fix the one `m`, then the others are uniform.
So **`prob_round4P`**: a fresh query's rounds are bad with probability at most `roundError` (no list factor),
**`prob_listBad4P`**: `(7 |H| + 6) / 2^256 + roundError`; **`prob_kcBad4P`**, **`prob_advBad4P`**: the same in
mumbai's model, with the answers at `zin` in the uniform part of the table (`hSz`), plus the roots answered after the
adversary (`4 / 2^256`). **`trace_core4P`**: a log holding the chain's inputs, with pinned candidates of the four
roots read off it, each its root's only one, satisfying the verifier's claims while the witness fails the relation,
has a bad fresh input.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace ComposePcs

open Compose QuotientRpm QuotientSecurity QuotientSecurity.Params

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]

/-! ## Pins -/

/-- **A commitment's candidates pinned by its out-of-domain answer**: the list commitment of the committed objects
(`C`), and `ok T r o n`, "the object `n` has the answer `o` at the root `r`'s out-of-domain point", which reads the
table at the inputs `zin` only. -/
structure Pin (zin : List UInt8 → Prop) (F N : Type) where
  C : ListCommit N
  ok : Table → Bytes32 → F → N → Prop
  ok_congr : ∀ (T T' : Table) (r : Bytes32) (o : F) (n : N), (∀ x, zin x → T x = T' x) → ok T r o n →
    ok T' r o n

namespace Pin

variable {zin : List UInt8 → Prop} {N : Type} (p : Pin zin F N)

/-- A pinned candidate: a candidate of the root with the answer. -/
def Mem (H : Hist) (T : Table) (r : Bytes32) (o : F) (n : N) : Prop :=
  n ∈ p.C.cands H T r ∧ p.ok T r o n

/-- The root has at most one pinned candidate. -/
def One (H : Hist) (T : Table) (r : Bytes32) (o : F) : Prop :=
  ∀ n n', p.Mem H T r o n → p.Mem H T r o n' → n = n'

theorem mem_congr {H : Hist} {T T' : Table} {r : Bytes32} {o : F} {n : N} (hH : ∀ d ∈ H, T d = T' d)
    (hz : ∀ x, zin x → T x = T' x) : p.Mem H T r o n ↔ p.Mem H T' r o n := by
  unfold Mem
  rw [p.C.congr H T T' r hH]
  exact and_congr_right fun _ =>
    ⟨p.ok_congr T T' r o n hz, p.ok_congr T' T r o n fun x hx => (hz x hx).symm⟩

theorem one_congr {H : Hist} {T T' : Table} {r : Bytes32} {o : F} (hH : ∀ d ∈ H, T d = T' d)
    (hz : ∀ x, zin x → T x = T' x) : p.One H T r o ↔ p.One H T' r o := by
  unfold One
  simp only [p.mem_congr hH hz]

theorem mem_of_cands {H H' : Hist} {T : Table} {r : Bytes32} {o : F} {n : N}
    (h : p.C.cands H T r = p.C.cands H' T r) : p.Mem H T r o n ↔ p.Mem H' T r o n := by
  unfold Mem
  rw [h]

theorem one_of_cands {H H' : Hist} {T : Table} {r : Bytes32} {o : F}
    (h : p.C.cands H T r = p.C.cands H' T r) : p.One H T r o ↔ p.One H' T r o := by
  unfold One
  simp only [p.mem_of_cands h]

end Pin

/-- **The four roots' pins**: the inputs `zin` they read (never a chain input: no `32`, `128`, `192` or `320`
bytes), `W`'s, `H`'s, `Q`'s and `G`'s, F1's first message read off `W`'s object, and the second message assembled
from the parts'. -/
structure Pins4 {P : Params F} (B : P.Bounds) (NW NH NQ NG : Type) where
  zin : List UInt8 → Prop
  zin_len : ∀ x, zin x → x.length ≠ 32 ∧ x.length ≠ 128 ∧ x.length ≠ 192 ∧ x.length ≠ 320
  pW : Pin zin F NW
  pH : Pin zin F NH
  pQ : Pin zin F NQ
  pG : Pin zin F NG
  rdW : NW → B.Msg₁
  asm : NH → NQ → NG → B.Msg₂

variable {P : Params F} {B : P.Bounds} (W : Wire P B) {NW NH NQ NG : Type} (K : Pins4 B NW NH NQ NG)

/-- **The pinned tuple**: a pinned candidate of each of the four roots, each root's only one. -/
def Pins4.Tup (H : Hist) (T : Table) (cW : Com F) (c3 : Com3 F) (u : NW × NH × NQ × NG) : Prop :=
  (K.pW.Mem H T cW.1 cW.2 u.1 ∧ K.pW.One H T cW.1 cW.2) ∧
    (K.pH.Mem H T c3.1.1 c3.1.2 u.2.1 ∧ K.pH.One H T c3.1.1 c3.1.2) ∧
    (K.pQ.Mem H T c3.2.1.1 c3.2.1.2 u.2.2.1 ∧ K.pQ.One H T c3.2.1.1 c3.2.1.2) ∧
    (K.pG.Mem H T c3.2.2.1 c3.2.2.2 u.2.2.2 ∧ K.pG.One H T c3.2.2.1 c3.2.2.2)

theorem Pins4.tup_unique {H : Hist} {T : Table} {cW : Com F} {c3 : Com3 F} {u u' : NW × NH × NQ × NG}
    (h : K.Tup H T cW c3 u) (h' : K.Tup H T cW c3 u') : u = u' := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩⟩ := h
  obtain ⟨⟨a1', -⟩, ⟨b1', -⟩, ⟨c1', -⟩, ⟨d1', -⟩⟩ := h'
  exact Prod.ext (a2 _ _ a1 a1') (Prod.ext (b2 _ _ b1 b1') (Prod.ext (c2 _ _ c1 c1') (d2 _ _ d1 d1')))

theorem Pins4.tup_congr {H : Hist} {T T' : Table} {cW : Com F} {c3 : Com3 F} {u : NW × NH × NQ × NG}
    (hH : ∀ d ∈ H, T d = T' d) (hz : ∀ x, K.zin x → T x = T' x) :
    K.Tup H T cW c3 u ↔ K.Tup H T' cW c3 u := by
  unfold Pins4.Tup
  rw [K.pW.mem_congr hH hz, K.pW.one_congr hH hz, K.pH.mem_congr hH hz, K.pH.one_congr hH hz,
    K.pQ.mem_congr hH hz, K.pQ.one_congr hH hz, K.pG.mem_congr hH hz, K.pG.one_congr hH hz]

/-! ## The bad events -/

/-- The triple the input after `W`'s commitment leads to, its states not asked before, makes the first round's
state go from lost to won for **the** pinned candidate of `W`'s root. -/
def FreshFirst4P (H : Hist) (x : List UInt8) (T : Table) (pre : Pre F) (cW : Com F) : Prop :=
  (T x).toList ∉ H ∧ (T (T x).toList).toList ∉ H ∧ (T (T x).toList).toList ≠ (T x).toList ∧
    ∃ n, (K.pW.Mem H T cW.1 cW.2 n ∧ K.pW.One H T cW.1 cW.2) ∧ ¬ State₁ (W.decode pre.2.2) (K.rdW n) ∧
      State₂ (W.decode pre.2.2) (K.rdW n) (W.chal (T x), W.chal (T (T x).toList),
        W.chal (T (T (T x).toList).toList))

/-- The first round, for the pinned candidate. -/
def FirstBad4P (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  ∃ pre cW, ParseFirst4 W H x T pre cW ∧ FreshFirst4P W K H x T pre cW

/-- The second round, for the pinned tuple. -/
def SecondBad4P (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  ∃ pre cW c3 c, ParseSecond4 W H x T pre cW c3 c ∧ ∃ u, K.Tup H T cW c3 u ∧
    ¬ State₃ (W.decode pre.2.2) (K.rdW u.1) c (K.asm u.2.1 u.2.2.1 u.2.2.2) ∧
      State₄ (W.decode pre.2.2) (K.rdW u.1) c (K.asm u.2.1 u.2.2.1 u.2.2.2) (W.chal (T x))

/-- The third round, for the pinned tuple. -/
def ThirdBad4P (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  ∃ pre cW c3 c t v, ParseThird4 W H x T pre cW c3 c t v ∧ ∃ u, K.Tup H T cW c3 u ∧
    ¬ State₄ (W.decode pre.2.2) (K.rdW u.1) c (K.asm u.2.1 u.2.2.1 u.2.2.2) t ∧
      State₆ (W.decode pre.2.2) (K.rdW u.1) c (K.asm u.2.1 u.2.2.1 u.2.2.2) t v (W.chal (T x))

/-- **A bad fresh query**, the candidates pinned. -/
def listBad4P (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  Coll4 H x T ∨ FirstBad4P W K H x T ∨ SecondBad4P W K H x T ∨ ThirdBad4P W K H x T

/-! ## One draw fixes the pinned candidate, another is uniform -/

section Split

variable {S : Finset (List UInt8)}

/-- Two completions of one cache give one answer where they agree. -/
theorem tableOf_agree (c : SCache S) {g g' : ↥S → Bytes32} {Z : List UInt8 → Prop}
    (h : ∀ x : ↥S, Z x.1 → g x = g' x) {y : List UInt8} (hy : Z y) : tableOf c g y = tableOf c g' y := by
  by_cases hS : y ∈ S
  · rw [show y = (⟨y, hS⟩ : ↥S).1 from rfl, tableOf_subtype, tableOf_subtype]
    simp [completeTable, h ⟨y, hS⟩ hy]
  · simp [tableOf, extendTable, hS]

open Classical in
/-- **Pinned, then uniform.** In a uniform table on `S`, if `A m` reads the answers at the inputs `Z` only and has
at most one solution, and `B m` reads the other answers only and has probability at most `ε` for each `m`, then
some `m` satisfies both with probability at most `ε`. -/
theorem prEvent_pinned_le (Z : List UInt8 → Prop) {M : Type} (A B : M → (↥S → Bytes32) → Prop) (ε : ℝ≥0∞)
    (hA : ∀ m (g g' : ↥S → Bytes32), (∀ x : ↥S, Z x.1 → g x = g' x) → A m g → A m g')
    (hB : ∀ m (g g' : ↥S → Bytes32), (∀ x : ↥S, ¬ Z x.1 → g x = g' x) → B m g → B m g')
    (huniq : ∀ m m' g, A m g → A m' g → m = m')
    (hε : ∀ m, Pr{let g ← $ᵗ (↥S → Bytes32)}[B m g] ≤ ε) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[∃ m, A m g ∧ B m g] ≤ ε := by
  let p : ↥S → Prop := fun x => Z x.1
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => Bytes32)
  have he : ∀ (a : {x // p x} → Bytes32) (b : {x // ¬ p x} → Bytes32) (x : ↥S),
      e.symm (a, b) x = if h : p x then a ⟨x, h⟩ else b ⟨x, h⟩ := fun a b x => rfl
  -- The table's answers on and off `Z`.
  have hsplit : ∀ E : (↥S → Bytes32) → Prop, (Finset.univ.filter E).card =
      ∑ a : ({x // p x} → Bytes32), (Finset.univ.filter fun b : ({x // ¬ p x} → Bytes32) =>
        E (e.symm (a, b))).card := by
    intro E
    rw [← Fintype.card_subtype]
    rw [Fintype.card_congr (e.subtypeEquiv (q := fun ab => E (e.symm ab)) fun g => by
      rw [Equiv.symm_apply_apply])]
    rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun a b => E (e.symm (a, b))),
      Fintype.card_sigma]
    exact Finset.sum_congr rfl fun a _ => Fintype.card_subtype _
  have hU : ((Fintype.card (↥S → Bytes32) : ℕ) : ℝ≥0∞) =
      (Fintype.card ({x // p x} → Bytes32) : ℝ≥0∞) * (Fintype.card ({x // ¬ p x} → Bytes32) : ℝ≥0∞) := by
    rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul]
  have hUa0 : (Fintype.card ({x // p x} → Bytes32) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hUaT : (Fintype.card ({x // p x} → Bytes32) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hUb0 : (Fintype.card ({x // ¬ p x} → Bytes32) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hUbT : (Fintype.card ({x // ¬ p x} → Bytes32) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  let a₀ : {x // p x} → Bytes32 := fun _ => Vector.replicate 32 0
  let b₀ : {x // ¬ p x} → Bytes32 := fun _ => Vector.replicate 32 0
  -- `B m` reads the answers off `Z` only, `A m` those on `Z` only.
  have hBa : ∀ m a b, B m (e.symm (a, b)) ↔ B m (e.symm (a₀, b)) := fun m a b =>
    ⟨hB m _ _ fun x hx => by rw [he, he]; simp [p, hx],
      hB m _ _ fun x hx => by rw [he, he]; simp [p, hx]⟩
  have hAb : ∀ m a b, A m (e.symm (a, b)) → A m (e.symm (a, b₀)) := fun m a b =>
    hA m _ _ fun x hx => by rw [he, he]; simp [p, hx]
  let β : M → ℕ := fun m => (Finset.univ.filter fun b => B m (e.symm (a₀, b))).card
  have hβ : ∀ m, (β m : ℝ≥0∞) ≤ ε * Fintype.card ({x // ¬ p x} → Bytes32) := by
    intro m
    have h := hε m
    rw [SampleableType.prEvent_uniformSample (fun g => B m g), hsplit] at h
    have hs : ∑ a : ({x // p x} → Bytes32), (Finset.univ.filter fun b => B m (e.symm (a, b))).card =
        Fintype.card ({x // p x} → Bytes32) * β m := by
      rw [Finset.sum_congr rfl fun a _ => congrArg Finset.card
        (Finset.filter_congr fun b _ => hBa m a b), Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [hs, hU, Nat.cast_mul, ENNReal.mul_div_mul_left _ _ hUa0 hUaT] at h
    exact (ENNReal.div_le_iff hUb0 hUbT).mp h
  have hfib : ∀ a : ({x // p x} → Bytes32),
      (((Finset.univ.filter fun b => ∃ m, A m (e.symm (a, b)) ∧ B m (e.symm (a, b))).card : ℕ) : ℝ≥0∞) ≤
        ε * Fintype.card ({x // ¬ p x} → Bytes32) := by
    intro a
    by_cases hex : ∃ m, A m (e.symm (a, b₀))
    · obtain ⟨m, hm⟩ := hex
      refine le_trans ?_ (hβ m)
      refine Nat.cast_le.mpr (Finset.card_le_card fun b hb => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      obtain ⟨m', hA', hB'⟩ := hb
      rw [huniq m' m _ (hAb m' a b hA') hm] at hB'
      exact (hBa m a b).mp hB'
    · have h0 : (Finset.univ.filter fun b => ∃ m, A m (e.symm (a, b)) ∧ B m (e.symm (a, b))) = ∅ :=
        Finset.filter_false_of_mem fun b _ ⟨m, hm, _⟩ => hex ⟨m, hAb m a b hm⟩
      rw [h0, Finset.card_empty, Nat.cast_zero]
      exact zero_le
  rw [SampleableType.prEvent_uniformSample, hsplit, Nat.cast_sum, hU]
  refine ENNReal.div_le_of_le_mul ?_
  calc ∑ a : ({x // p x} → Bytes32), (((Finset.univ.filter fun b =>
        ∃ m, A m (e.symm (a, b)) ∧ B m (e.symm (a, b))).card : ℕ) : ℝ≥0∞)
      ≤ ∑ _a : ({x // p x} → Bytes32), ε * Fintype.card ({x // ¬ p x} → Bytes32) :=
        Finset.sum_le_sum fun a _ => hfib a
    _ = ε * ((Fintype.card ({x // p x} → Bytes32) : ℝ≥0∞) *
          (Fintype.card ({x // ¬ p x} → Bytes32) : ℝ≥0∞)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Split

/-! ## Each fresh query is bad with probability at most the round error -/

section Probability

variable {S : Finset (List UInt8)}

/-- **The rounds' bad events, the candidates pinned, have probability at most the largest round error**: the parse
is read off the history; the answers at the out-of-domain inputs fix the pinned candidate (tuple), and the answers
the round reads are uniform. -/
theorem prob_round4P (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[FirstBad4P W K (histOf c) t.1 (tableOf c g) ∨
      SecondBad4P W K (histOf c) t.1 (tableOf c g) ∨ ThirdBad4P W K (histOf c) t.1 (tableOf c g)] ≤
      (roundError P B : ℝ≥0∞) := by
  let g₀ : ↥S → Bytes32 := fun _ => Vector.replicate 32 0
  have hcg : ∀ g, ∀ d ∈ histOf c, tableOf c g d = tableOf c g₀ d := fun g _ hd =>
    tableOf_eq_of_mem c hd g g₀
  have hhA : ∀ g g' : ↥S → Bytes32, ∀ d ∈ histOf c, tableOf c g d = tableOf c g' d := fun g g' _ hd =>
    tableOf_eq_of_mem c hd g g'
  have hzA : ∀ g g' : ↥S → Bytes32, (∀ x : ↥S, K.zin x.1 → g x = g' x) →
      ∀ x, K.zin x → tableOf c g x = tableOf c g' x := fun g g' h x hx => tableOf_agree c (Z := K.zin) h hx
  have hnz : ∀ y : List UInt8, (y.length = 32 ∨ y.length = 128 ∨ y.length = 192 ∨ y.length = 320) →
      ¬ K.zin y := fun y hy hz => by
    have := K.zin_len y hz
    omega
  have h32 : ∀ v : Bytes32, ¬ K.zin v.toList := fun v => hnz _ (Or.inl (by simp))
  by_cases h1 : ∃ pre cW, ParseFirst4 W (histOf c) t.1 (tableOf c g₀) pre cW
  · obtain ⟨pre, cW, hp⟩ := h1
    have hlen : t.1.length = 128 := by
      obtain ⟨st₀, -, hx, -⟩ := hp
      rw [hx]
      simp
    refine (prEvent_mono _ _ (fun g => ∃ n, (K.pW.Mem (histOf c) (tableOf c g) cW.1 cW.2 n ∧
      K.pW.One (histOf c) (tableOf c g) cW.1 cW.2) ∧ ((tableOf c g t.1).toList ∉ histOf c ∧
      (tableOf c g (tableOf c g t.1).toList).toList ∉ histOf c ∧
      (tableOf c g (tableOf c g t.1).toList).toList ≠ (tableOf c g t.1).toList ∧
      ¬ State₁ (W.decode pre.2.2) (K.rdW n) ∧
      State₂ (W.decode pre.2.2) (K.rdW n) (W.chal (tableOf c g t.1),
        W.chal (tableOf c g (tableOf c g t.1).toList),
        W.chal (tableOf c g (tableOf c g (tableOf c g t.1).toList).toList))))
      fun g h => ?_).trans ?_
    · rcases h with ⟨pre', cW', hp', hf⟩ | ⟨pre', cW', c3', c', hp', -⟩ |
        ⟨pre', cW', c3', c', tt, v, hp', -⟩
      · rw [parseFirst4_congr (hcg g)] at hp'
        obtain ⟨rfl, rfl⟩ := parseFirst4_unique hp' hp
        obtain ⟨f1, f2, f3, n, hn, f4, f5⟩ := hf
        exact ⟨n, hn, f1, f2, f3, f4, f5⟩
      · rw [parseSecond4_congr (hcg g)] at hp'
        exact (parseFirst4_parseSecond4 hp hp').elim
      · rw [parseThird4_congr (hcg g)] at hp'
        exact (parseFirst4_parseThird4 hp hp').elim
    · refine prEvent_pinned_le K.zin _ _ _ (fun n g g' h hn => ?_) (fun n g g' h hb => ?_)
        (fun n n' g hn hn' => hn.2 n n' hn.1 hn'.1)
        (fun n => prob_freshFirst4_one W hS₀ c t ht hlen pre.2.2 (K.rdW n))
      · exact ⟨(K.pW.mem_congr (hhA g g') (hzA g g' h)).mp hn.1,
          (K.pW.one_congr (hhA g g') (hzA g g' h)).mp hn.2⟩
      · have e1 : tableOf c g t.1 = tableOf c g' t.1 :=
          tableOf_agree c (Z := fun y => ¬ K.zin y) h (hnz _ (Or.inr (Or.inl hlen)))
        have e2 : tableOf c g (tableOf c g' t.1).toList = tableOf c g' (tableOf c g' t.1).toList :=
          tableOf_agree c (Z := fun y => ¬ K.zin y) h (h32 _)
        have e3 : tableOf c g (tableOf c g' (tableOf c g' t.1).toList).toList =
            tableOf c g' (tableOf c g' (tableOf c g' t.1).toList).toList :=
          tableOf_agree c (Z := fun y => ¬ K.zin y) h (h32 _)
        obtain ⟨f1, f2, f3, f4, f5⟩ := hb
        rw [e1] at f1 f2 f3 f5
        rw [e2] at f2 f3 f5
        rw [e3] at f5
        exact ⟨f1, f2, f3, f4, f5⟩
  by_cases h2 : ∃ pre cW c3 c', ParseSecond4 W (histOf c) t.1 (tableOf c g₀) pre cW c3 c'
  · obtain ⟨pre, cW, c3, c', hp⟩ := h2
    have hlen : t.1.length = 320 := by
      obtain ⟨_, _, _, _, _, _, _, _, hx, _⟩ := hp
      rw [hx]
      simp
    refine (prEvent_mono _ _ (fun g => ∃ u, K.Tup (histOf c) (tableOf c g) cW c3 u ∧
      (¬ State₃ (W.decode pre.2.2) (K.rdW u.1) c' (K.asm u.2.1 u.2.2.1 u.2.2.2) ∧
        State₄ (W.decode pre.2.2) (K.rdW u.1) c' (K.asm u.2.1 u.2.2.1 u.2.2.2) (W.chal (g t))))
      fun g h => ?_).trans ?_
    · rcases h with ⟨pre', cW', hp', -⟩ | ⟨pre', cW', c3', c'', hp', u, hu, hf⟩ |
        ⟨pre', cW', c3', c'', tt, v, hp', -⟩
      · rw [parseFirst4_congr (hcg g)] at hp'
        exact (parseFirst4_parseSecond4 hp' hp).elim
      · rw [parseSecond4_congr (hcg g)] at hp'
        obtain ⟨rfl, rfl, rfl, rfl⟩ := parseSecond4_unique hp' hp
        rw [tableOf_fresh c ht g] at hf
        exact ⟨u, hu, hf⟩
      · rw [parseThird4_congr (hcg g)] at hp'
        exact (parseSecond4_parseThird4 hp hp').elim
    · refine prEvent_pinned_le K.zin _ _ _
        (fun u g g' h hu => (K.tup_congr (hhA g g') (hzA g g' h)).mp hu)
        (fun u g g' h hb => by rwa [← h t (hnz _ (Or.inr (Or.inr (Or.inr hlen))))])
        (fun u u' g hu hu' => K.tup_unique hu hu')
        (fun u => (prEvent_cell t (fun s => ¬ State₃ (W.decode pre.2.2) (K.rdW u.1) c'
            (K.asm u.2.1 u.2.2.1 u.2.2.2) ∧
          State₄ (W.decode pre.2.2) (K.rdW u.1) c' (K.asm u.2.1 u.2.2.1 u.2.2.2) (W.chal s))).trans
          (prob_second_chain W _ _ c' _))
  by_cases h3 : ∃ pre cW c3 c' tt v,
      ParseThird4 W (histOf c) t.1 (tableOf c g₀) pre cW c3 c' tt v
  · obtain ⟨pre, cW, c3, c', tt, v, hp⟩ := h3
    have hlen : t.1.length = 192 := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hx, _⟩ := hp
      rw [hx]
      simp
    refine (prEvent_mono _ _ (fun g => ∃ u, K.Tup (histOf c) (tableOf c g) cW c3 u ∧
      (¬ State₄ (W.decode pre.2.2) (K.rdW u.1) c' (K.asm u.2.1 u.2.2.1 u.2.2.2) tt ∧
        State₆ (W.decode pre.2.2) (K.rdW u.1) c' (K.asm u.2.1 u.2.2.1 u.2.2.2) tt v (W.chal (g t))))
      fun g h => ?_).trans ?_
    · rcases h with ⟨pre', cW', hp', -⟩ | ⟨pre', cW', c3', c'', hp', -⟩ |
        ⟨pre', cW', c3', c'', tt', v', hp', u, hu, hf⟩
      · rw [parseFirst4_congr (hcg g)] at hp'
        exact (parseFirst4_parseThird4 hp' hp).elim
      · rw [parseSecond4_congr (hcg g)] at hp'
        exact (parseSecond4_parseThird4 hp' hp).elim
      · rw [parseThird4_congr (hcg g)] at hp'
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := parseThird4_unique hp' hp
        rw [tableOf_fresh c ht g] at hf
        exact ⟨u, hu, hf⟩
    · refine prEvent_pinned_le K.zin _ _ _
        (fun u g g' h hu => (K.tup_congr (hhA g g') (hzA g g' h)).mp hu)
        (fun u g g' h hb => by rwa [← h t (hnz _ (Or.inr (Or.inr (Or.inl hlen))))])
        (fun u u' g hu hu' => K.tup_unique hu hu')
        (fun u => (prEvent_cell t (fun s => ¬ State₄ (W.decode pre.2.2) (K.rdW u.1) c'
            (K.asm u.2.1 u.2.2.1 u.2.2.2) tt ∧
          State₆ (W.decode pre.2.2) (K.rdW u.1) c' (K.asm u.2.1 u.2.2.1 u.2.2.2) tt v (W.chal s))).trans
          (prob_third_chain W _ _ c' _ tt v))
  · rw [prEvent_eq_zero_of_forall_not _ _ fun g h => ?_]
    · simp
    rcases h with ⟨pre, cW, hp, -⟩ | ⟨pre, cW, c3, c', hp, -⟩ | ⟨pre, cW, c3, c', tt, v, hp, -⟩
    · exact h1 ⟨pre, cW, (parseFirst4_congr (hcg g) _ _ _).mp hp⟩
    · exact h2 ⟨pre, cW, c3, c', (parseSecond4_congr (hcg g) _ _ _ _ _).mp hp⟩
    · exact h3 ⟨pre, cW, c3, c', tt, v, (parseThird4_congr (hcg g) _ _ _ _ _ _ _).mp hp⟩

/-- **A fresh query is bad, the candidates pinned, with probability at most
`(7 |H| + 6) / 2^256 + roundError`.** -/
theorem prob_listBad4P (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[listBad4P W K (histOf c) t.1 (tableOf c g)] ≤
      ((7 * (histOf c).card + 6 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (roundError P B : ℝ≥0∞) :=
  (prEvent_or_le _ _ _).trans (add_le_add (prob_coll4 c t ht) (prob_round4P W K hS₀ c t ht))

end Probability

/-! ## The trace -/

section Trace

/-- No collision makes the order of the queries the order of what they refer to. -/
theorem refers4_beforeP {L : List (List UInt8)} {T : Table} (hnb : ¬ FreshBad (listBad4P W K) T ∅ L) :
    ∀ y ∈ L, ∀ z ∈ L, Refers4 z (T y) → y ∈ before L z := by
  have nb : ∀ y ∈ L, ¬ listBad4P W K (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBad4P W K) T ∅ L hnb y hy (Finset.notMem_empty _)
  intro y hy z hz h
  by_contra hb
  by_cases hyz : y = z
  · subst hyz
    exact nb y hy (Or.inl (Or.inr ⟨y, Finset.mem_insert_self _ _, h⟩))
  · rcases before_trichotomy L y z hy hz hyz with h' | h'
    · exact hb h'
    · exact nb y hy (Or.inl (Or.inr ⟨z, Finset.mem_insert_of_mem h', h⟩))

/-- No collision: the table is injective on the log. -/
theorem injOn_of_not_freshBad4P {L : List (List UInt8)} {T : Table}
    (hnb : ¬ FreshBad (listBad4P W K) T ∅ L) : ∀ y ∈ L, ∀ z ∈ L, T y = T z → y = z := by
  have nb : ∀ y ∈ L, ¬ listBad4P W K (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBad4P W K) T ∅ L hnb y hy (Finset.notMem_empty _)
  intro y hy z hz hyz
  by_contra hne
  rcases before_trichotomy L y z hy hz hne with h | h
  · exact nb z hz (Or.inl (Or.inl ⟨y, h, hyz⟩))
  · exact nb y hy (Or.inl (Or.inl ⟨z, h, hyz.symm⟩))

/-- A pinned candidate and its root's uniqueness, read off a later history. -/
theorem pin_stab {L : List (List UInt8)} {T : Table}
    (hord : ∀ y ∈ L, ∀ z ∈ L, Refers4 z (T y) → y ∈ before L z) {zin : List UInt8 → Prop} {N : Type}
    (p : Pin zin F N) (r : Bytes32) (o : F) (n : N) (y z : List UInt8) (hy : y ∈ L) (hry : Refers4 y r)
    (hyz : y = z ∨ y ∈ before L z) (hm : p.Mem L.toFinset T r o n) (h1 : p.One L.toFinset T r o) :
    p.Mem (before L z) T r o n ∧ p.One (before L z) T r o := by
  have e := stab4 hord p.C r y z hy hry hyz
  exact ⟨(p.mem_of_cands e).mp hm, (p.one_of_cands e).mp h1⟩

/-- **The trace, the candidates pinned**: if the log holds the chain's six inputs, and pinned candidates of the four
roots, read off the log, each its root's only one, satisfy the verifier's claims at the chain's challenges while the
witness's cells fail the relation, then some fresh input of the log is bad. -/
theorem trace_core4P (L : List (List UInt8)) (T : Table) (π : RootProof4 F) (uW : NW) (uH : NH) (uQ : NQ)
    (uG : NG) :
    let x₀ := labelOf4 W π.pre
    let x₁ := afterW W (T x₀) π.comW
    let x₂ := (T x₁).toList
    let x₃ := (T x₂).toList
    let x₄ := afterHQG W (T x₃) π.comHQG
    let x₅ := W.afterValues (T x₄) π.v
    (∀ y ∈ [x₀, x₁, x₂, x₃, x₄, x₅], y ∈ L) →
      K.pW.Mem L.toFinset T π.rW π.oW uW → K.pW.One L.toFinset T π.rW π.oW →
      K.pH.Mem L.toFinset T π.rH π.oH uH → K.pH.One L.toFinset T π.rH π.oH →
      K.pQ.Mem L.toFinset T π.rQ π.oQ uQ → K.pQ.One L.toFinset T π.rQ π.oQ →
      K.pG.Mem L.toFinset T π.rG π.oG uG → K.pG.One L.toFinset T π.rG π.oG →
      P.Accepts (W.decode π.stmt) (K.rdW uW).1 (K.asm uH uQ uG).1 (W.chal (T x₁)) (W.chal (T x₂))
        (W.chal (T x₃)) (W.chal (T x₄)) π.v.1 π.v.2 (W.chal (T x₅)) →
      ¬ P.Sat (W.decode π.stmt) (P.cells (K.rdW uW).1) → FreshBad (listBad4P W K) T ∅ L := by
  intro x₀ x₁ x₂ x₃ x₄ x₅ mem hW hW1 hH hH1 hQ hQ1 hG hG1 hacc hsat
  by_contra hnb
  have nb : ∀ y ∈ L, ¬ listBad4P W K (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBad4P W K) T ∅ L hnb y hy (Finset.notMem_empty _)
  have hinj := injOn_of_not_freshBad4P W K hnb
  have hord := refers4_beforeP W K hnb
  have injB : ∀ y, Set.InjOn T ↑(before L y) := fun y a ha b hb hab =>
    hinj a (mem_of_mem_before L a y ha) b (mem_of_mem_before L b y hb) hab
  have m0 := mem x₀ (by simp)
  have m1 := mem x₁ (by simp)
  have m2 := mem x₂ (by simp)
  have m3 := mem x₃ (by simp)
  have m4 := mem x₄ (by simp)
  have m5 := mem x₅ (by simp)
  have take32 : ∀ st : Bytes32, st.toList.take 32 = st.toList := fun st =>
    List.take_of_length_le (by simp)
  -- The chain's inputs come in their order.
  have b01 : x₀ ∈ before L x₁ := hord x₀ m0 x₁ m1 (Or.inl (Or.inl (take_afterW W _ _).symm))
  have b12 : x₁ ∈ before L x₂ := hord x₁ m1 x₂ m2 (Or.inl (Or.inl (take32 _).symm))
  have b23 : x₂ ∈ before L x₃ := hord x₂ m2 x₃ m3 (Or.inl (Or.inl (take32 _).symm))
  have b34 : x₃ ∈ before L x₄ := hord x₃ m3 x₄ m4 (Or.inl (Or.inl (take_afterHQG W _ _).symm))
  have b45 : x₄ ∈ before L x₅ := hord x₄ m4 x₅ m5 (Or.inl (Or.inl (W.take_afterValues _ _).symm))
  have s12 := before_subset_of_mem L x₁ x₂ b12
  have s23 := before_subset_of_mem L x₂ x₃ b23
  have s34 := before_subset_of_mem L x₃ x₄ b34
  have s45 := before_subset_of_mem L x₄ x₅ b45
  have c04 : x₀ ∈ before L x₄ := s34 (s23 (s12 b01))
  have c14 : x₁ ∈ before L x₄ := s34 (s23 b12)
  have c24 : x₂ ∈ before L x₄ := s34 b23
  -- The roots the chain absorbs.
  have hrW : Refers4 x₁ π.rW := Or.inr (Or.inl (rootPart_afterW W (T x₀) π.comW).symm)
  have hrH : Refers4 x₄ π.rH := Or.inr (Or.inl (rootPart_afterHQG₁ W (T x₃) π.comHQG).symm)
  have hrQ : Refers4 x₄ π.rQ := Or.inr (Or.inr (Or.inl (rootPart_afterHQG₂ W (T x₃) π.comHQG).symm))
  have hrG : Refers4 x₄ π.rG := Or.inr (Or.inr (Or.inr (rootPart_afterHQG₃ W (T x₃) π.comHQG).symm))
  have w1 := pin_stab hord K.pW π.rW π.oW uW x₁ x₁ m1 hrW (Or.inl rfl) hW hW1
  have w4 := pin_stab hord K.pW π.rW π.oW uW x₁ x₄ m1 hrW (Or.inr c14) hW hW1
  have w5 := pin_stab hord K.pW π.rW π.oW uW x₁ x₅ m1 hrW (Or.inr (s45 c14)) hW hW1
  have T4 : K.Tup (before L x₄) T π.comW π.comHQG (uW, uH, uQ, uG) :=
    ⟨w4, pin_stab hord K.pH π.rH π.oH uH x₄ x₄ m4 hrH (Or.inl rfl) hH hH1,
      pin_stab hord K.pQ π.rQ π.oQ uQ x₄ x₄ m4 hrQ (Or.inl rfl) hQ hQ1,
      pin_stab hord K.pG π.rG π.oG uG x₄ x₄ m4 hrG (Or.inl rfl) hG hG1⟩
  have T5 : K.Tup (before L x₅) T π.comW π.comHQG (uW, uH, uQ, uG) :=
    ⟨w5, pin_stab hord K.pH π.rH π.oH uH x₄ x₅ m4 hrH (Or.inr b45) hH hH1,
      pin_stab hord K.pQ π.rQ π.oQ uQ x₄ x₅ m4 hrQ (Or.inr b45) hQ hQ1,
      pin_stab hord K.pG π.rG π.oG uG x₄ x₅ m4 hrG (Or.inr b45) hG hG1⟩
  -- The round that F1's trace names.
  let π' : Proof P B := ⟨W.decode π.stmt, K.rdW uW, K.asm uH uQ uG, π.v⟩
  let tbl : ∀ k, Answer P B k := fun k => match k with
    | .first .. => (W.chal (T x₁), W.chal (T x₂), W.chal (T x₃))
    | .second .. => W.chal (T x₄)
    | .third .. => W.chal (T x₅)
  rcases bad_of_accepts π' tbl hacc hsat with hb | hb | hb
  · obtain ⟨h1, h2⟩ := hb
    refine nb x₁ m1 (Or.inr (Or.inl ⟨π.pre, π.comW, ⟨T x₀, ⟨b01, rfl⟩, rfl, injB x₁⟩,
      ⟨fun h => not_mem_before_of_mem_before b12 h, fun h => ?_, fun h => ?_, uW, w1, h1, h2⟩⟩))
    · exact not_mem_before_of_mem_before (s23 b12) h
    · have e : x₃ = x₂ := h
      rw [e] at b23
      exact not_mem_before_self L x₂ b23
  · obtain ⟨h1, h2⟩ := hb
    exact nb x₄ m4 (Or.inr (Or.inr (Or.inl ⟨π.pre, π.comW, π.comHQG, _, ⟨T x₀, T x₁, T x₂, T x₃,
      ⟨c04, rfl⟩, ⟨c14, rfl⟩, ⟨c24, rfl⟩, ⟨b34, rfl⟩, rfl, rfl, injB x₄⟩, (uW, uH, uQ, uG), T4, h1,
      h2⟩)))
  · obtain ⟨h1, h2⟩ := hb
    exact nb x₅ m5 (Or.inr (Or.inr (Or.inr ⟨π.pre, π.comW, π.comHQG, _, _, π.v,
      ⟨T x₀, T x₁, T x₂, T x₃, T x₄, ⟨s45 c04, rfl⟩, ⟨s45 c14, rfl⟩, ⟨s45 c24, rfl⟩,
        ⟨s45 b34, rfl⟩, ⟨b45, rfl⟩, rfl, rfl, rfl, injB x₅⟩, (uW, uH, uQ, uG), T5, h1, h2⟩)))

end Trace

/-! ## In mumbai's two-oracle model -/

open LeanVM LeanVM.Protocol LeanVM.Semantics

/-- **A bad query of both oracles, the candidates pinned**: a Keccak-256 query bad for the view; never a Keccak-f
query. -/
def kcBad4P (H : Finset (List UInt8 ⊕ KeccakState)) (d : List UInt8 ⊕ KeccakState) (T : KTable) : Prop :=
  match d with
  | .inl x => listBad4P W K (viewH H) x (viewT T)
  | .inr _ => False

/-- A bad fresh Keccak-256 input of the view is a bad fresh query. -/
theorem freshBad_kc4P (T : KTable) : ∀ (H : Finset (List UInt8 ⊕ KeccakState))
    (L : List (List UInt8 ⊕ KeccakState)),
    FreshBad (listBad4P W K) (viewT T) (viewH H) (L.filterMap Sum.getLeft?) →
      FreshBad (kcBad4P W K) T H L
  | _, [], h => by simp [FreshBad] at h
  | H, .inl x :: L, h => by
    simp only [List.filterMap_cons, Sum.getLeft?_inl, FreshBad] at h ⊢
    rcases h with ⟨hx, hb⟩ | h
    · exact Or.inl ⟨fun hm => hx (mem_viewH.mpr hm), hb⟩
    · refine Or.inr (freshBad_kc4P T _ L ?_)
      rwa [viewH_insert_inl]
  | H, .inr s :: L, h => by
    simp only [List.filterMap_cons, Sum.getLeft?_inr, FreshBad] at h ⊢
    refine Or.inr (freshBad_kc4P T _ L ?_)
    rwa [viewH_insert_inr]

/-- `listBad4P` reads the table on the inputs asked, at the fresh input, at the 32-byte inputs (the states the first
round's lookahead hashes) and at the pins' inputs. -/
theorem listBad4P_congr {H : Hist} {x : List UInt8} {T T' : Table} (hH : ∀ d ∈ H, T d = T' d)
    (hx : T x = T' x) (hs : ∀ v : Bytes32, T v.toList = T' v.toList) (hz : ∀ y, K.zin y → T y = T' y) :
    listBad4P W K H x T ↔ listBad4P W K H x T' := by
  have hcoll : Coll4 H x T ↔ Coll4 H x T' := by
    unfold Coll4
    rw [hx]
    constructor
    · rintro (⟨y, hy, h⟩ | h)
      · exact Or.inl ⟨y, hy, (hH y hy).symm.trans h⟩
      · exact Or.inr h
    · rintro (⟨y, hy, h⟩ | h)
      · exact Or.inl ⟨y, hy, (hH y hy).trans h⟩
      · exact Or.inr h
  have htup : ∀ cW c3 u, K.Tup H T cW c3 u ↔ K.Tup H T' cW c3 u := fun _ _ _ => K.tup_congr hH hz
  have hmW : ∀ r o n, K.pW.Mem H T r o n ↔ K.pW.Mem H T' r o n := fun _ _ _ => K.pW.mem_congr hH hz
  have hoW : ∀ r o, K.pW.One H T r o ↔ K.pW.One H T' r o := fun _ _ => K.pW.one_congr hH hz
  unfold listBad4P FirstBad4P SecondBad4P ThirdBad4P ParseFirst4 FreshFirst4P ParseSecond4 ParseThird4
  simp only [hcoll, hx, hs, htup, hmW, hoW, has_congr hH, injOn_congr hH]

/-- **Each fresh query of both oracles is bad, the candidates pinned, with probability at most
`(7 |H| + 6) / 2^256 + roundError`**, the pins' inputs in the table's uniform part. -/
theorem prob_kcBad4P (S : Finset (List UInt8 ⊕ KeccakState))
    (hS₀ : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S)
    (hSz : ∀ x, K.zin x → (Sum.inl x : List UInt8 ⊕ KeccakState) ∈ S)
    (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[kcBad4P W K
        ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
        (extendTable S (completeTable c g))] ≤
      ((7 * (cacheDom c).card + 6 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (roundError P B : ℝ≥0∞) := by
  obtain ⟨d, hd⟩ := t
  cases d with
  | inr s =>
    refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_not _ _ ?_)) bot_le
    intro g h
    exact h
  | inl x =>
    have hx : x ∈ viewH S := mem_viewH.mpr hd
    have hS₁ : ∀ v : Bytes32, v.toList ∈ viewH S := fun v => mem_viewH.mpr (hS₀ v)
    have hc₁ : viewC S c ⟨x, hx⟩ = none := by simp [viewC, ht]
    have hH : histOf (viewC S c) ⊆ viewH S := fun y hy => (mem_histOf.mp hy).1
    have hev : ∀ g, kcBad4P W K ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) (.inl x)
        (extendTable S (completeTable c g)) ↔
        listBad4P W K (histOf (viewC S c)) x (tableOf (viewC S c) (viewG S g)) := by
      intro g
      show listBad4P W K _ x _ ↔ _
      rw [← histOf_viewC]
      exact listBad4P_congr W K (fun y hy => viewT_extendTable c g (hH hy))
        (viewT_extendTable c g hx) (fun v => viewT_extendTable c g (hS₁ v))
        (fun y hy => viewT_extendTable c g (mem_viewH.mpr (hSz y hy)))
    refine (prEvent_mono _ _ (fun g => listBad4P W K (histOf (viewC S c)) x
      (tableOf (viewC S c) (viewG S g))) fun g h => (hev g).mp h).trans ?_
    rw [prEvent_view S (fun h => listBad4P W K (histOf (viewC S c)) x (tableOf (viewC S c) h))]
    refine (prob_listBad4P W K hS₁ (viewC S c) ⟨x, hx⟩ hc₁).trans ?_
    gcongr
    have hcard : (histOf (viewC S c)).card ≤ (cacheDom c).card := by
      rw [histOf_viewC]
      refine (Finset.card_le_card_of_injOn
        (t := (cacheDom c).map (Function.Embedding.subtype (· ∈ S))) Sum.inl (fun y hy => ?_)
        Sum.inl_injective.injOn).trans (Finset.card_map (Function.Embedding.subtype (· ∈ S))).le
      exact mem_viewH.mp hy
    omega

/-- A bad query: `kcBad4P`, or a fresh answer that is an announced root. -/
def advBad4P {O : Type} (A : OracleComp KeccakCalls (RootProof4 F × O))
    (H : Finset (List UInt8 ⊕ KeccakState)) (d : List UInt8 ⊕ KeccakState) (T : KTable) : Prop :=
  kcBad4P W K H d T ∨ rootBad4 A H d T

/-- **Each fresh query is bad, the candidates pinned, with probability at most
`(7 |H| + 10) / 2^256 + roundError`.** -/
theorem prob_advBad4P {O : Type} (A : OracleComp KeccakCalls (RootProof4 F × O))
    (S : Finset (List UInt8 ⊕ KeccakState))
    (hS₀ : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S)
    (hSz : ∀ x, K.zin x → (Sum.inl x : List UInt8 ⊕ KeccakState) ∈ S)
    (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[advBad4P W K A
        ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
        (extendTable S (completeTable c g))] ≤
      ((7 * (cacheDom c).card + 10 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (roundError P B : ℝ≥0∞) := by
  refine (prEvent_or_le _ _ _).trans ((add_le_add (prob_kcBad4P W K S hS₀ hSz c t ht)
    (prob_rootBad4 A S c t ht)).trans (le_of_eq ?_))
  rw [add_comm (((7 * (cacheDom c).card + 6 : ℕ) : ℝ≥0∞) / 2 ^ 256), add_assoc,
    ENNReal.div_add_div_same, add_comm]
  congr 2
  push_cast
  ring

end ComposePcs
