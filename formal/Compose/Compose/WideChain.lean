-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Adapts `ListChainU.lean` and `ListChainU128.lean` (the
-- chain over an encoding, the walk back separated by the label's first 32 bytes, the bad events and the trace) to
-- rounds whose challenges are one call's whole rate (π1-rec4's wide draws, `WideSpec.lean`).
import Compose.ListChainU128
import Compose.WideSpec

/-!
# The wide chain: one Keccak-256 call a round, its challenges read off the rate

`ListChainU.lean`'s chain draws a round's `ns + 1` challenges from `ns + 1` successive Keccak-256 calls (the first
absorbing the round's message, the others the state alone). π1-rec4's (`UniStatement.sampleWide`) draws them from
**one** call: the call absorbs the state and the round's message, its digest is the next state, and its challenges
are the rate's (`chalsW`: the digest's, then the tail's). Here the chain is any chain of that form (`ChainSpecW`):

* the rounds and limbs (`K`, a `ChainSpec` whose label is not read; every round at most five challenges, `ns_le`);
  the label of a statement (the seed's input); the statement's bytes before round `0`'s message (`pre`);
* **a round-indexed encoding** (`enc j`, injective on the messages fitting a round): π1-rec4's `C2` call absorbs the
  slices **before** `C2`'s root, so a root's place in the bytes depends on the round;
* what an input refers to (`Rf`): `Refers`, and each round's root where its encoding writes it (`rf_enc`,
  `rf_pre`, for messages fitting the round).

On a table of digests `T` and a table of tails `τ` (the rate model's table split, `WideSpec.lean`), the chain's
inputs are `ListChainK.lean`'s (`allIn`: one per round), its challenges `chalsTW`. The bad events are
`ListChainU128.lean`'s with one call a round: a collision (`CollW`, of the digest), or a bad round (`RoundBadW`: the
call's answer, digest and tail, turns the state from lost to won); **`trace_coreW`**: a run lost at the start and won
at the end, whose log holds no answer equal to the label's first 32 bytes, asks a bad fresh query.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm

/-! ## The bytes each round absorbs -/

section Enc

variable {F : Type} (e : ℕ → RMsg F → List UInt8)

/-- **The bytes each step absorbs**, one step a round: round `i`'s message as `e` encodes it at its index. -/
def absorbsW : ℕ → List RoundSpec → List (RMsg F) → List (List UInt8)
  | _, [], _ => []
  | i, _ :: rs, ms => e i (ms.headD (none, [])) :: absorbsW (i + 1) rs ms.tail

theorem length_absorbsW : ∀ (i : ℕ) (rs : List RoundSpec) (ms : List (RMsg F)),
    (absorbsW e i rs ms).length = rs.length
  | _, [], _ => rfl
  | i, _ :: rs, ms => by simp [absorbsW, length_absorbsW (i + 1) rs ms.tail]

theorem absorbsW_append : ∀ (i : ℕ) (rs₁ rs₂ : List RoundSpec) (ms₁ ms₂ : List (RMsg F)),
    ms₁.length = rs₁.length →
      absorbsW e i (rs₁ ++ rs₂) (ms₁ ++ ms₂) = absorbsW e i rs₁ ms₁ ++ absorbsW e (i + rs₁.length) rs₂ ms₂
  | i, [], _, [], _, _ => by simp [absorbsW]
  | i, s :: rs₁, rs₂, m :: ms₁, ms₂, h => by
    simp only [List.cons_append, absorbsW, List.headD_cons, List.tail_cons,
      absorbsW_append (i + 1) rs₁ rs₂ ms₁ ms₂ (by simpa using h), List.length_cons]
    rw [show i + 1 + rs₁.length = i + (rs₁.length + 1) by omega]
  | _, [], _, _ :: _, _, h => by simp at h
  | _, _ :: _, _, [], _, h => by simp at h

theorem absorbsW_single (i : ℕ) (s : RoundSpec) (m : RMsg F) : absorbsW e i [s] [m] = [e i m] := rfl

/-- **The messages are determined by the bytes the steps absorb**, for an encoding injective on each round's
messages. -/
theorem absorbsW_inj
    (he : ∀ j {sp : RoundSpec} {m m' : RMsg F}, m.Fits sp → m'.Fits sp → e j m = e j m' → m = m') :
    ∀ {i : ℕ} {rs : List RoundSpec} {ms ms' : List (RMsg F)}, FitsAll rs ms → FitsAll rs ms' →
      absorbsW e i rs ms = absorbsW e i rs ms' → ms = ms'
  | _, [], [], [], _, _, _ => rfl
  | i, s :: rs, m :: ms, m' :: ms', h, h', hq => by
    simp only [absorbsW, List.headD_cons, List.tail_cons, List.cons.injEq] at hq
    obtain ⟨h1, h2⟩ := hq
    rw [he i h.1 h'.1 h1, absorbsW_inj he h.2 h'.2 h2]
  | _, [], _ :: _, _, h, _, _ => h.elim
  | _, [], [], _ :: _, _, h', _ => h'.elim
  | _, _ :: _, [], _, h, _, _ => h.elim
  | _, _ :: _, _ :: _, [], _, h', _ => h'.elim

/-- A round's message, at its index, is among the bytes the steps absorb. -/
theorem getElem_mem_absorbsW : ∀ (i₀ : ℕ) (rs : List RoundSpec) (ms : List (RMsg F)),
    ms.length = rs.length → ∀ i (h : i < ms.length), e (i₀ + i) ms[i] ∈ absorbsW e i₀ rs ms
  | _, [], [], _, i, h => by simp at h
  | i₀, s :: rs, m :: ms, _, 0, _ => by simp [absorbsW]
  | i₀, s :: rs, m :: ms, hl, i + 1, h => by
    simp only [absorbsW, List.headD_cons, List.tail_cons, List.getElem_cons_succ, List.mem_cons]
    refine Or.inr ?_
    have := getElem_mem_absorbsW (i₀ + 1) rs ms (by simpa using hl) i (by simpa using h)
    rwa [show i₀ + 1 + i = i₀ + (i + 1) by omega] at this
  | _, [], _ :: _, hl, _, _ => by simp at hl
  | _, _ :: _, [], hl, _, _ => by simp at hl

end Enc

/-! ## The challenges on a table of digests and a table of tails -/

section Chals

variable {F : Type}

/-- **The challenges of a wide chain on a table**, one list per round: the wide draw on each round's input's answer
(the digest `T x`, the tail `τ x`). -/
def chalsTW (lim : F ≃ Limbs) (T : Table) (τ : List UInt8 → TailP) (y : List UInt8) (rs : List RoundSpec)
    (es : List (List UInt8)) : List (List F) :=
  (rs.zip (allIn T y es).tail).map fun p => chalsW lim (p.1.ns + 1) (T p.2) (τ p.2)

theorem length_chalsTW (lim : F ≃ Limbs) (T : Table) (τ : List UInt8 → TailP) (y : List UInt8)
    (rs : List RoundSpec) (es : List (List UInt8)) (h : es.length = rs.length) :
    (chalsTW lim T τ y rs es).length = rs.length := by
  rw [chalsTW, List.length_map, List.length_zip, length_tail_allIn, h, min_self]

theorem chalsTW_append (lim : F ≃ Limbs) (T : Table) (τ : List UInt8 → TailP) (y : List UInt8)
    (rs₀ rs₂ : List RoundSpec) (es₀ es₂ : List (List UInt8)) (h : es₀.length = rs₀.length) :
    chalsTW lim T τ y (rs₀ ++ rs₂) (es₀ ++ es₂) =
      chalsTW lim T τ y rs₀ es₀ ++ chalsTW lim T τ (lastIn T y es₀) rs₂ es₂ := by
  unfold chalsTW
  rw [tail_allIn_append, List.zip_append (by rw [length_tail_allIn, h]), List.map_append]

theorem chalsTW_cons (lim : F ≃ Limbs) (T : Table) (τ : List UInt8 → TailP) (y : List UInt8) (s : RoundSpec)
    (rs : List RoundSpec) (e : List UInt8) (es : List (List UInt8)) :
    chalsTW lim T τ y (s :: rs) (e :: es) =
      chalsW lim (s.ns + 1) (T (stepIn (T y) e)) (τ (stepIn (T y) e)) ::
        chalsTW lim T τ (stepIn (T y) e) rs es := by
  unfold chalsTW
  rw [allIn, List.tail_cons, allIn_cons_tail]
  rfl

/-- The challenges read the tables at the chain's inputs only. -/
theorem chalsTW_congr {T T' : Table} {τ τ' : List UInt8 → TailP} (lim : F ≃ Limbs) (y : List UInt8)
    (rs : List RoundSpec) (es : List (List UInt8)) (h : ∀ z ∈ allIn T y es, T z = T' z)
    (hτ : ∀ z ∈ allIn T y es, τ z = τ' z) :
    chalsTW lim T' τ' y rs es = chalsTW lim T τ y rs es := by
  obtain ⟨e1, -⟩ := allIn_congr y es h
  unfold chalsTW
  rw [e1]
  refine List.map_congr_left fun p hp => ?_
  have hz : p.2 ∈ allIn T y es := List.mem_of_mem_tail (List.of_mem_zip hp).2
  rw [h p.2 hz, hτ p.2 hz]

end Chals

/-! ## The chain's specification -/

/-- **A wide chain**: the rounds and the limbs (`K`; at most five challenges a round), the label of a statement, the
statement's bytes before round `0`'s message, the messages' round-indexed encoding, and what an input refers to
(`Rf`: `Refers`, and each round's root where its encoding writes it, at most `nRf` digests an input). -/
structure ChainSpecW (F St : Type) where
  K : ChainSpec F St
  ns_le : ∀ sp ∈ K.rounds, sp.ns ≤ 4
  label : St → List UInt8
  pre : St → List UInt8
  pre_len : ∀ s s', (pre s).length = (pre s').length
  stmt_inj : ∀ s s', label s = label s' → pre s = pre s' → s = s'
  enc : ℕ → RMsg F → List UInt8
  enc_inj : ∀ j {sp : RoundSpec} {m m' : RMsg F}, m.Fits sp → m'.Fits sp → enc j m = enc j m' → m = m'
  Rf : List UInt8 → Bytes32 → Prop
  nRf : ℕ
  refs : List UInt8 → List Bytes32
  rf_refs : ∀ y d, Rf y d → d ∈ refs y
  length_refs : ∀ y, (refs y).length ≤ nRf
  refers_rf : ∀ y d, Refers y d → Rf y d
  rf_enc : ∀ (j : ℕ) (st r : Bytes32) (l : List F), RMsg.Fits (K.spec j) ((some r, l) : RMsg F) →
    Rf (stepIn st (enc j (some r, l))) r
  rf_pre : ∀ (s : St) (st r : Bytes32) (l : List F), RMsg.Fits (K.spec 0) ((some r, l) : RMsg F) →
    Rf (stepIn st (pre s ++ enc 0 (some r, l))) r

namespace ChainSpecW

variable {F St : Type} (W : ChainSpecW F St)

/-- Round `j`'s message as the chain hashes it: round `0`'s after the statement's bytes. -/
def encAt (s : St) (j : ℕ) (m : RMsg F) : List UInt8 :=
  if j = 0 then W.pre s ++ W.enc 0 m else W.enc j m

/-- The bytes the steps of the rounds `rs` absorb, for the statement `s`. -/
def absorbsS (s : St) (rs : List RoundSpec) (ms : List (RMsg F)) : List (List UInt8) :=
  absorbsW (W.encAt s) 0 rs ms

/-- The challenges of the chain of the statement `s` on the tables, over the rounds `rs`. -/
def chalsT (T : Table) (τ : List UInt8 → TailP) (s : St) (rs : List RoundSpec) (ms : List (RMsg F)) :
    List (List F) :=
  chalsTW W.K.lim T τ (W.label s) rs (W.absorbsS s rs ms)

/-- **The chain over a hash answering a digest and a tail in any monad**, from the input `y`: every answer, the
first the seed's. -/
def runMW {m : Type → Type} [Monad m] (H : List UInt8 → m (Bytes32 × TailP)) :
    List UInt8 → List (List UInt8) → m (List (Bytes32 × TailP))
  | y, [] => H y >>= fun a => pure [a]
  | y, e :: es => H y >>= fun a => runMW H (stepIn a.1 e) es >>= fun rest => pure (a :: rest)

/-- The challenges, one list per round, from the chain's answers. -/
def chalsOf (ans : List (Bytes32 × TailP)) : List (List F) :=
  (W.K.rounds.zip ans.tail).map fun p => chalsW W.K.lim (p.1.ns + 1) p.2.1 p.2.2

/-- **The wide chain** of a statement and its messages, over a hash answering digests and tails. -/
def chain {m : Type → Type} [Monad m] (H : List UInt8 → m (Bytes32 × TailP)) (s : St)
    (ms : List (RMsg F)) : m (List (List F)) :=
  W.chalsOf <$> runMW H (W.label s) (W.absorbsS s W.K.rounds ms)

/-- The chain's number of queries: the label and one per round. -/
def nQ : ℕ := W.K.rounds.length + 1

/-- **A collision**: the fresh digest repeats an earlier one, or an input asked before, or `x`, refers to it. -/
def CollW (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  (∃ y ∈ H, T y = T x) ∨ ∃ y ∈ insert x H, W.Rf y (T x)

theorem encAt_inj {s : St} {j : ℕ} {sp : RoundSpec} {m m' : RMsg F} (h : m.Fits sp)
    (h' : m'.Fits sp) (he : W.encAt s j m = W.encAt s j m') : m = m' := by
  unfold encAt at he
  split_ifs at he with hj
  · subst hj
    exact W.enc_inj 0 h h' (List.append_cancel_left he)
  · exact W.enc_inj j h h' he

theorem encAt_zero (s s' : St) (m m' : RMsg F) (he : W.encAt s 0 m = W.encAt s' 0 m') :
    W.pre s = W.pre s' ∧ W.enc 0 m = W.enc 0 m' := by
  simp only [encAt, ite_true] at he
  exact List.append_inj he (W.pre_len s s')

theorem ns_le_spec (j : ℕ) : (W.K.spec j).ns ≤ 4 := by
  unfold ChainSpec.spec
  rw [List.getD_eq_getElem?_getD]
  cases h : W.K.rounds[j]? with
  | none => simp
  | some sp => exact W.ns_le sp (List.mem_of_getElem? h)

end ChainSpecW

/-! ## The bad events -/

section Bad

variable {F St M : Type} [SampleableType F] (W : ChainSpecW F St) (C : ℕ → ListCommit M)
  (R : Piop W.K M)

/-- **`x` is round `j`'s input**: for a statement `s`, the messages `ms` of the rounds before and `m` of round `j`,
fitting them, the chain before `x` was asked (its inputs in `H`), without collision, and no answer of the history
the label's first 32 bytes. -/
def ParseW (H : Hist) (x : List UInt8) (T : Table) (j : ℕ) (s : St) (ms : List (RMsg F)) (m : RMsg F) : Prop :=
  j < W.K.rounds.length ∧ FitsAll (W.K.rounds.take j) ms ∧ m.Fits (W.K.spec j) ∧
    x = lastIn T (W.label s) (W.absorbsS s (W.K.rounds.take j) ms ++ [W.encAt s j m]) ∧
    (∀ y ∈ prevIn T (W.label s) (W.absorbsS s (W.K.rounds.take j) ms ++ [W.encAt s j m]), y ∈ H) ∧
    Set.InjOn T ↑H ∧ NoPre (W.label s) H T

/-- **Round `j` is bad at its input**: its wide draw (the digest and the tail of `x`'s answer) turns the state from
lost to won for some candidates of the roots of the rounds up to `j`, read off the history. -/
def RoundBadW (H : Hist) (x : List UInt8) (T : Table) (τ : List UInt8 → TailP) : Prop :=
  ∃ j s ms m, ParseW W H x T j s ms m ∧
    ∃ cs c, List.Forall₂ (· ∈ ·) cs (candLists C H T 0 ms) ∧ c ∈ optC (C j) H T m ∧
      ¬ R.pre s (opened cs ms (W.chalsT T τ s (W.K.rounds.take j) ms)) (c, m.2) ∧
      R.post s (opened cs ms (W.chalsT T τ s (W.K.rounds.take j) ms)) (c, m.2)
        (chalsW W.K.lim ((W.K.spec j).ns + 1) (T x) (τ x))

/-- **A bad fresh query**: a collision or a bad round. -/
def listBadW (τ : List UInt8 → TailP) (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  W.CollW H x T ∨ RoundBadW W C R H x T τ

variable {W}

theorem parseW_congr {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d) (x : List UInt8)
    (j : ℕ) (s : St) (ms : List (RMsg F)) (m : RMsg F) :
    ParseW W H x T j s ms m ↔ ParseW W H x T' j s ms m := by
  unfold ParseW
  constructor
  · rintro ⟨h1, h2, h3, hx, hH, hi, hn⟩
    obtain ⟨e1, e2⟩ := chain_congr (T := T) (T' := T') _ _ fun z hz => h z (hH z hz)
    refine ⟨h1, h2, h3, hx.trans e2.symm, fun y hy => hH y (by rwa [e1] at hy),
      (injOn_congr h).mp hi, (noPre_congr h).mp hn⟩
  · rintro ⟨h1, h2, h3, hx, hH, hi, hn⟩
    obtain ⟨e1, e2⟩ := chain_congr (T := T') (T' := T) _ _ fun z hz => (h z (hH z hz)).symm
    refine ⟨h1, h2, h3, hx.trans e2.symm, fun y hy => hH y (by rwa [e1] at hy),
      (injOn_congr h).mpr hi, (noPre_congr h).mpr hn⟩

theorem ParseW.length_eq {H : Hist} {x : List UInt8} {T : Table} {j : ℕ} {s : St}
    {ms : List (RMsg F)} {m : RMsg F} (h : ParseW W H x T j s ms m) : ms.length = j := by
  rw [h.2.1.length_eq, List.length_take]
  exact min_eq_left (le_of_lt h.1)

/-- The chain before round `j`'s input was asked. -/
theorem ParseW.allIn_sub {H : Hist} {x : List UInt8} {T : Table} {j : ℕ} {s : St}
    {ms : List (RMsg F)} {m : RMsg F} (h : ParseW W H x T j s ms m) :
    ∀ z ∈ allIn T (W.label s) (W.absorbsS s (W.K.rounds.take j) ms), z ∈ H := by
  intro z hz
  refine h.2.2.2.2.1 z ?_
  rw [prevIn_concat]
  exact hz

/-- **The parse is unique.** -/
theorem parseW_unique {H : Hist} {x : List UInt8} {T : Table} {j j' : ℕ} {s s' : St}
    {ms ms' : List (RMsg F)} {m m' : RMsg F} (h : ParseW W H x T j s ms m)
    (h' : ParseW W H x T j' s' ms' m') : j = j' ∧ s = s' ∧ ms = ms' ∧ m = m' := by
  obtain ⟨hj, hf, hm, hx, hH, hi, hn⟩ := h
  obtain ⟨hj', hf', hm', hx', hH', -, hn'⟩ := h'
  obtain ⟨hlab, hes⟩ := chain_uniqueU' T hi _ _ _ _ hn hn' hH hH' (hx.symm.trans hx')
  have hl := congrArg List.length hes
  simp only [ChainSpecW.absorbsS, List.length_append, List.length_singleton, length_absorbsW,
    List.length_take] at hl
  have hjj : j = j' := by omega
  subst hjj
  obtain ⟨ha, he⟩ := List.append_inj hes (by simp [ChainSpecW.absorbsS, length_absorbsW])
  simp only [List.cons.injEq, and_true] at he
  -- The statement: from the label and the bytes before round `0`'s message.
  have hpre : W.pre s = W.pre s' := by
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · exact (W.encAt_zero s s' m m' he).1
    · obtain ⟨r₀, rest, hr⟩ : ∃ r₀ rest, W.K.rounds.take j = r₀ :: rest := by
        rcases htk : W.K.rounds.take j with _ | ⟨r₀, rest⟩
        · rw [List.take_eq_nil_iff] at htk
          rcases htk with htk | htk
          · omega
          · rw [htk] at hj
            simp at hj
        · exact ⟨r₀, rest, rfl⟩
      rw [hr] at hf hf' ha
      rcases ms with _ | ⟨m₀, ms₀⟩
      · exact hf.elim
      rcases ms' with _ | ⟨m₀', ms₀'⟩
      · exact hf'.elim
      simp only [ChainSpecW.absorbsS, absorbsW, List.headD_cons, List.cons.injEq] at ha
      exact (W.encAt_zero s s' m₀ m₀' ha.1).1
  have hs : s = s' := W.stmt_inj s s' hlab hpre
  subst hs
  refine ⟨rfl, rfl, ?_, W.encAt_inj hm hm' he⟩
  exact absorbsW_inj (W.encAt s) (fun _ _ _ _ h1 h2 h3 => W.encAt_inj h1 h2 h3) hf hf' ha

variable (W)

/-- **`listBadW` reads the digests on the inputs asked and at the fresh input, and the tails there.** -/
theorem listBadW_congr {H : Hist} {x : List UInt8} {T T' : Table} {τ τ' : List UInt8 → TailP}
    (hH : ∀ d ∈ H, T d = T' d) (hx : T x = T' x) (hτH : ∀ d ∈ H, τ d = τ' d) (hτx : τ x = τ' x) :
    listBadW W C R τ H x T ↔ listBadW W C R τ' H x T' := by
  have hcoll : W.CollW H x T ↔ W.CollW H x T' := by
    unfold ChainSpecW.CollW
    rw [hx]
    constructor
    · rintro (⟨y, hy, h⟩ | h)
      · exact Or.inl ⟨y, hy, (hH y hy).symm.trans h⟩
      · exact Or.inr h
    · rintro (⟨y, hy, h⟩ | h)
      · exact Or.inl ⟨y, hy, (hH y hy).trans h⟩
      · exact Or.inr h
  have hround : ∀ (T₁ T₂ : Table) (τ₁ τ₂ : List UInt8 → TailP), (∀ d ∈ H, T₁ d = T₂ d) → T₁ x = T₂ x →
      (∀ d ∈ H, τ₁ d = τ₂ d) → τ₁ x = τ₂ x → RoundBadW W C R H x T₁ τ₁ → RoundBadW W C R H x T₂ τ₂ := by
    intro T₁ T₂ τ₁ τ₂ h12 hx12 hτ12 hτx12 hb
    obtain ⟨j, s, ms, m, hp, cs, c, hcs, hc, h3, h4⟩ := hb
    have hch : W.chalsT T₂ τ₂ s (W.K.rounds.take j) ms = W.chalsT T₁ τ₁ s (W.K.rounds.take j) ms :=
      chalsTW_congr _ _ _ _ (fun z hz => h12 z (hp.allIn_sub z hz))
        (fun z hz => hτ12 z (hp.allIn_sub z hz))
    refine ⟨j, s, ms, m, (parseW_congr h12 x j s ms m).mp hp, cs, c,
      by rwa [← candLists_congr C h12], by rwa [← optC_congr (C j) h12], by rw [hch]; exact h3, ?_⟩
    rw [hch, ← hx12, ← hτx12]
    exact h4
  unfold listBadW
  rw [hcoll]
  exact or_congr_right ⟨hround T T' τ τ' hH hx hτH hτx, hround T' T τ' τ (fun d hd => (hH d hd).symm) hx.symm
    (fun d hd => (hτH d hd).symm) hτx.symm⟩

end Bad

/-! ## The trace: a winning run asks a bad fresh query -/

section Trace

variable {F St M : Type} [SampleableType F] (W : ChainSpecW F St) (C : ℕ → ListCommit M)
  (R : Piop W.K M) (τ : List UInt8 → TailP)

variable {W C R τ} in
/-- No collision makes the order of the queries the order of what they refer to (`Rf`). -/
theorem rf_beforeW {L : List (List UInt8)} {T : Table}
    (hnb : ¬ FreshBad (listBadW W C R τ) T ∅ L) :
    ∀ y ∈ L, ∀ z ∈ L, W.Rf z (T y) → y ∈ before L z := by
  have nb : ∀ y ∈ L, ¬ listBadW W C R τ (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBadW W C R τ) T ∅ L hnb y hy (Finset.notMem_empty _)
  intro y hy z hz h
  by_contra hb
  by_cases hyz : y = z
  · subst hyz
    exact nb y hy (Or.inl (Or.inr ⟨y, Finset.mem_insert_self _ _, h⟩))
  · rcases before_trichotomy L y z hy hz hyz with h' | h'
    · exact hb h'
    · exact nb y hy (Or.inl (Or.inr ⟨z, Finset.mem_insert_of_mem h', h⟩))

variable {W C R τ} in
/-- No collision: the table is injective on the log. -/
theorem injOn_of_not_freshBadW {L : List (List UInt8)} {T : Table}
    (hnb : ¬ FreshBad (listBadW W C R τ) T ∅ L) : Set.InjOn T ↑L.toFinset := by
  have nb : ∀ y ∈ L, ¬ listBadW W C R τ (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBadW W C R τ) T ∅ L hnb y hy (Finset.notMem_empty _)
  intro y hy w hw hyw
  have hy' := List.mem_toFinset.mp hy
  have hw' := List.mem_toFinset.mp hw
  by_contra hne
  rcases before_trichotomy L y w hy' hw' hne with h | h
  · exact nb w hw' (Or.inl (Or.inl ⟨y, h, hyw⟩))
  · exact nb y hy' (Or.inl (Or.inl ⟨w, h, hyw.symm⟩))

theorem fitsAll_getElem : ∀ {rs : List RoundSpec} {ms : List (RMsg F)}, FitsAll rs ms →
    ∀ (i : ℕ) (hi : i < ms.length) (hir : i < rs.length), ms[i].Fits rs[i]
  | _ :: _, _ :: _, h, 0, _, _ => h.1
  | _ :: _, _ :: _, h, i + 1, hi, hir => fitsAll_getElem h.2 i (by simpa using hi) (by simpa using hir)
  | [], _, _, _, _, hir => by simp at hir
  | _ :: _, [], h, _, _, _ => h.elim

/-- A message of the rounds' messages fits its round's specification. -/
theorem fits_spec_of_mem {rs : List RoundSpec} {ms : List (RMsg F)} (K : ChainSpec F St)
    (hrs : ∃ rest, K.rounds = rs ++ rest) (hf : FitsAll rs ms) :
    ∀ i (hi : i < ms.length), ms[i].Fits (K.spec i) := by
  obtain ⟨rest, hr⟩ := hrs
  have hl : ms.length = rs.length := hf.length_eq
  intro i hi
  have hir : i < rs.length := hl ▸ hi
  have hspec : K.spec i = rs[i] := by
    rw [ChainSpec.spec, hr, List.getD_eq_getElem?_getD, List.getElem?_append_left hir,
      List.getElem?_eq_getElem hir, Option.getD_some]
  rw [hspec]
  exact fitsAll_getElem hf i hi hir

open Classical in
/-- **The trace, on a log**: if the log holds the chain's inputs, no answer of the log is the label's first 32
bytes (`hseed`), and some candidates of the rounds' roots, read off the log, make the transcript lost at the start
and won at the end, then some fresh input of the log is bad. -/
theorem trace_coreW (L : List (List UInt8)) (T : Table) (s : St) (ms : List (RMsg F))
    (cs : List (Option M)) (hfit : FitsAll W.K.rounds ms)
    (hmem : ∀ y ∈ allIn T (W.label s) (W.absorbsS s W.K.rounds ms), y ∈ L)
    (hcs : List.Forall₂ (· ∈ ·) cs (candLists C L.toFinset T 0 ms))
    (hwin : R.LostWon s (opened cs ms (W.chalsT T τ s W.K.rounds ms)))
    (hseed : ∀ z ∈ L, (T z).toList ≠ (W.label s).take 32) :
    FreshBad (listBadW W C R τ) T ∅ L := by
  by_contra hnb
  have nb : ∀ y ∈ L, ¬ listBadW W C R τ (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBadW W C R τ) T ∅ L hnb y hy (Finset.notMem_empty _)
  have hinj : ∀ y ∈ L, ∀ z ∈ L, T y = T z → y = z := by
    intro y hy z hz hyz
    by_contra hne
    rcases before_trichotomy L y z hy hz hne with h | h
    · exact nb z hz (Or.inl (Or.inl ⟨y, h, hyz⟩))
    · exact nb y hy (Or.inl (Or.inl ⟨z, h, hyz.symm⟩))
  have hordF := rf_beforeW hnb
  have hord : ∀ y ∈ L, ∀ z ∈ L, Refers z (T y) → y ∈ before L z :=
    fun y hy z hz h => hordF y hy z hz (W.refers_rf _ _ h)
  have injB : ∀ y, Set.InjOn T ↑(before L y) := fun y a ha b hb hab =>
    hinj a (mem_of_mem_before L a y ha) b (mem_of_mem_before L b y hb) hab
  have nopre : ∀ y, NoPre (W.label s) (before L y) T := fun y z hz =>
    hseed z (mem_of_mem_before L z y hz)
  -- After a root is absorbed, its candidates are the ones the history already fixed.
  have stab : ∀ {N : Type} (Cn : ListCommit N) (r : Bytes32) (y z : List UInt8), y ∈ L →
      W.Rf y r → (y = z ∨ y ∈ before L z) →
        Cn.cands L.toFinset T r = Cn.cands (before L z) T r := by
    intro N Cn r y z hy hry hyz
    have hsub : ∀ w, w ∈ before L y → w ∈ before L z := by
      rcases hyz with rfl | h
      · exact fun w hw => hw
      · exact fun w hw => before_subset_of_mem L y z h hw
    refine Cn.stable (before L z) L.toFinset T r (fun w hw => List.mem_toFinset.mpr
      (mem_of_mem_before L w z hw)) (fun w hw hwr => ?_) (fun y' hy' w hw h => ?_)
    · rw [← hwr] at hry
      exact hsub w (hordF w (List.mem_toFinset.mp hw) y hy hry)
    · exact before_subset_of_mem L y' z hy' (hord w (List.mem_toFinset.mp hw) y'
        (mem_of_mem_before L y' z hy') h)
  -- The round that turns the state from lost to won.
  obtain ⟨p, m', c', rest, hfull, hpre, hpost⟩ := R.exists_bad_of_lostWon s _ hwin
  obtain ⟨cs₀, c, cs₁, ms₀, m, ms₁, chs₀, ch, chs₁, ecs, ems, echs, l1, l2, l3, ep, em, ec⟩ :=
    opened_eq_append_cons p cs ms _ m' c' rest
      (by rw [ChainSpecW.chalsT, length_chalsTW _ _ _ _ _ _ (by
        rw [ChainSpecW.absorbsS, length_absorbsW]), hfit.length_eq]) hfull
  have hfit₀ := hfit
  rw [ems] at hfit
  obtain ⟨rs₀, s₁, rs₁, ers, hf0, hfm, hf1⟩ := fitsAll_split W.K.rounds ms₀ m ms₁ hfit
  have hl0 : ms₀.length = rs₀.length := hf0.length_eq
  have htake : W.K.rounds.take rs₀.length = rs₀ := by
    rw [ers]
    exact List.take_left' rfl
  have hspec : W.K.spec rs₀.length = s₁ := by
    rw [ChainSpec.spec, ers, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
    simp
  have hjlt : rs₀.length < W.K.rounds.length := by
    rw [ers]
    simp
  -- The round's input.
  set lab := W.label s
  set e := W.encAt s
  set y₀ := lastIn T lab (absorbsW e 0 rs₀ ms₀)
  set x := stepIn (T y₀) (e rs₀.length m) with hx
  have hxl : x = lastIn T lab (absorbsW e 0 rs₀ ms₀ ++ [e rs₀.length m]) := by
    rw [lastIn_concat]
  -- The challenges split at the round.
  have hchs : W.chalsT T τ s W.K.rounds ms =
      chalsTW W.K.lim T τ lab rs₀ (absorbsW e 0 rs₀ ms₀) ++
        (chalsW W.K.lim (s₁.ns + 1) (T x) (τ x) ::
          chalsTW W.K.lim T τ x rs₁ (absorbsW e (rs₀.length + 1) rs₁ ms₁)) := by
    rw [ChainSpecW.chalsT, ChainSpecW.absorbsS, ers, ems,
      absorbsW_append e 0 rs₀ (s₁ :: rs₁) ms₀ (m :: ms₁) hl0,
      chalsTW_append _ _ _ _ _ _ _ _ (by rw [length_absorbsW])]
    simp only [Nat.zero_add, absorbsW, List.headD_cons, List.tail_cons]
    rw [chalsTW_cons]
  rw [echs] at hchs
  have hl0' : chs₀.length = (chalsTW W.K.lim T τ lab rs₀ (absorbsW e 0 rs₀ ms₀)).length := by
    rw [l3, ← l2, hl0, length_chalsTW _ _ _ _ _ _ (by rw [length_absorbsW])]
  obtain ⟨hc0, hc1⟩ := List.append_inj hchs hl0'
  simp only [List.cons.injEq] at hc1
  -- The chain's inputs, up to the round's input.
  have hchain : allIn T lab (W.absorbsS s W.K.rounds ms) =
      prevIn T lab (absorbsW e 0 rs₀ ms₀ ++ [e rs₀.length m]) ++
        allIn T x (absorbsW e (rs₀.length + 1) rs₁ ms₁) := by
    rw [ChainSpecW.absorbsS, ers, ems, absorbsW_append e 0 rs₀ (s₁ :: rs₁) ms₀ (m :: ms₁) hl0]
    rw [show absorbsW e (0 + rs₀.length) (s₁ :: rs₁) (m :: ms₁) =
      [e rs₀.length m] ++ absorbsW e (rs₀.length + 1) rs₁ ms₁ by simp [absorbsW]]
    rw [← List.append_assoc, allIn_append, ← hxl]
  have hpw := chain_pairwise hord _ _ hmem
  rw [hchain, List.pairwise_append] at hpw
  obtain ⟨-, -, hcross⟩ := hpw
  have hxmem : x ∈ L := hmem x (by rw [hchain]; simp [head_mem_allIn])
  -- The chain before `x` was asked before it.
  have hprev : ∀ z ∈ prevIn T lab (absorbsW e 0 rs₀ ms₀ ++ [e rs₀.length m]), z ∈ before L x :=
    fun z hz => hcross z hz x (head_mem_allIn _ _ _)
  -- The candidates of the rounds up to `j`, read off the history before `x`.
  have hfits : ∀ i (hi : i < (ms₀ ++ [m]).length), (ms₀ ++ [m])[i].Fits (W.K.spec i) :=
    fits_spec_of_mem W.K ⟨rs₁, by rw [ers]; simp⟩ (fitsAll_append hf0 (show FitsAll [s₁] [m] from ⟨hfm, trivial⟩))
  have hroots : ∀ m₂ ∈ ms₀ ++ [m], ∀ r, m₂.1 = some r → ∀ k,
      (C k).cands L.toFinset T r = (C k).cands (before L x) T r := by
    intro m₂ hm₂ r hr k
    obtain ⟨i, hi, hmi⟩ := List.mem_iff_getElem.mp hm₂
    have hfi := hfits i hi
    rw [hmi] at hfi
    have he : e i m₂ ∈ absorbsW e 0 rs₀ ms₀ ++ [e rs₀.length m] := by
      rcases Nat.lt_or_ge i ms₀.length with hi0 | hi0
      · have h0 := getElem_mem_absorbsW e 0 rs₀ ms₀ hl0 i hi0
        rw [List.getElem_append_left hi0] at hmi
        rw [Nat.zero_add, hmi] at h0
        exact List.mem_append_left _ h0
      · have hi' : i = ms₀.length := by
          simp only [List.length_append, List.length_singleton] at hi
          omega
        subst hi'
        have hm₂m : m₂ = m := by
          rw [← hmi]
          simp
        rw [hm₂m, hl0]
        exact List.mem_append_right _ (List.mem_singleton_self _)
    obtain ⟨st, hst⟩ := step_mem_allIn T lab _ _ he
    obtain ⟨o, l'⟩ := m₂
    simp only at hr
    subst hr
    rw [allIn_eq, ← hxl] at hst
    have hy : stepIn st (e i (some r, l')) ∈ L := by
      rcases List.mem_append.mp hst with h | h
      · exact mem_of_mem_before L _ x (hprev _ h)
      · rw [List.mem_singleton.mp h]
        exact hxmem
    have hrf : W.Rf (stepIn st (e i (some r, l'))) r := by
      show W.Rf (stepIn st (W.encAt s i (some r, l'))) r
      unfold ChainSpecW.encAt
      split_ifs with hi0
      · subst hi0
        exact W.rf_pre s st r l' hfi
      · exact W.rf_enc i st r l' hfi
    refine stab (C k) r _ x hy hrf ?_
    rcases List.mem_append.mp hst with h | h
    · exact Or.inr (hprev _ h)
    · exact Or.inl (List.mem_singleton.mp h)
  rw [ecs, ems, candLists_append] at hcs
  have hlc : cs₀.length = (candLists C L.toFinset T 0 ms₀).length := by
    rw [length_candLists, l1, l2]
  obtain ⟨hcs0, hcs1⟩ := forall₂_append_split hlc hcs
  simp only [candLists, Nat.zero_add] at hcs1
  have hc : c ∈ optC (C ms₀.length) L.toFinset T m := by
    cases hcs1 with
    | cons h _ => exact h
  rw [candLists_stable C 0 ms₀ fun m₂ hm₂ => hroots m₂ (List.mem_append_left _ hm₂)] at hcs0
  rw [optC_stable (C ms₀.length) m fun r hr => hroots m (by simp) r hr _] at hc
  -- The bad round.
  refine nb x hxmem (Or.inr ⟨rs₀.length, s, ms₀, m, ⟨hjlt, by rw [htake]; exact hf0,
    by rw [hspec]; exact hfm, by rw [ChainSpecW.absorbsS, htake]; exact hxl, fun z hz => by
      rw [ChainSpecW.absorbsS, htake] at hz
      exact hprev z hz, injB x, nopre x⟩, cs₀, c, hcs0, ?_, ?_, ?_⟩)
  · rwa [hl0] at hc
  · rw [ChainSpecW.chalsT, ChainSpecW.absorbsS, htake, ← hc0, ← ep, ← em]
    exact hpre
  · rw [ChainSpecW.chalsT, ChainSpecW.absorbsS, htake, ← hc0, ← ep, ← em, hspec, ← hc1.1, ← ec]
    exact hpost

end Trace

end Compose

/-- info: 'Compose.trace_coreW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.trace_coreW
