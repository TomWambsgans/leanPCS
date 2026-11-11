-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π1-rec4's analogue of `Rec3ProbChain.lean`
-- (`prEvent_staged2_le`) and `Rec3ProbStaged.lean` (`KStaged3`, `prEvent_run_false_le3`), on the five-digest reading of
-- the rate (`Rec4Couple.lean`); uses `Chain.lean`'s lemmas (`prEvent_query_le`, `sum_bad_le`, `prEvent_tquery_le`) and
-- `formal/EndToEnd/Completeness/E2ECompleteness/Chain.lean`'s (`prEvent_final_le`, `cache_of_hashOK`, `Regular`), and
-- leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two
-- calls `KeccakCalls` and their lazy random oracles.
import UniKeccakComplete.K.Rec4Exp
import UniKeccakComplete.K.Rec3ProbStaged

/-!
# π1-rec4's staged run in the random-oracle model

Read through `tauW` (`Rec4Couple.lean`), π1-rec4's wide draws are five digest queries (`rate5`): the input `x` and its
four tails. The challenges a draw gives are read off `mkRate d t₁ t₂ t₃ t₄`: challenge `0` is the first digest's
(`challengeAt_mkRate_zero`: `challengeOf d`), challenge `1` the second's (`challengeAt_mkRate_one`: `chalTail t₁`, a
regular challenge map, `chalTail_regular`).

**The staged run** (`KStaged4`): `A` up to the bus draw's input (`inp`, `112` bytes); the bus draw (`α = squares c 4`,
`c` its challenge `0`, `β` its challenge `1`); `B` up to the point draw's input (`tin`; `pr` the prior `t`'s bad set
depends on, Flock's point); the point draw (`t` its challenge `0`); `C` the rest. **`prEvent_run_false_le4`**: the
run is rejected with probability at most

  `Nbad / 2^192 + (ct / 2^192 + εt) + εpow`,

* `Nbad / 2^192` (`prEvent_bus4_le`): the bus draw's input is fresh by its length, its tails by theirs (`GoodL5`: what
  `A` hashes is of another length than `32` and `112`, or a tail of such an input), so `c` and `β` are the challenges
  of two fresh uniform digests, `β` bad for `α` with probability at most `Nbad · 2^64 / 2^256`;
* `ct / 2^192 + εt`: `t` is the challenge of the point draw's first digest (`Prob.prEvent_tquery_le`), `εt` bounding
  the probability that the draw's input was hashed before (`Good.tFresh`);
* `εpow`: rejected at good challenges (`Good.rejectGood`, the grinding).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open E2ECompleteness (ro Cache HashOK hashOK cache_of_hashOK prEvent_final_le Regular simulateQ_callKeccak256)
open UniKeccakComplete.Prob (GoodL prEvent_query_le sum_const_div sum_bad_le prEvent_tquery_le)
open UniStatement
open scoped ENNReal

set_option autoImplicit false

namespace UniKeccakComplete.Rec4

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The challenges of a five-digest rate -/

theorem beWord_append_right (a b : List UInt8) (s : ℕ) :
    PcsQuotient.Transcript.beWord (a ++ b) (a.length + s) = PcsQuotient.Transcript.beWord b s := by
  rw [E2ECompleteness.beWord_drop, E2ECompleteness.beWord_drop b, List.drop_append, List.drop_eq_nil_of_le
    (by omega), List.nil_append, show a.length + s - a.length = s by omega]

/-- **Challenge `0` of a five-digest rate is the first digest's.** -/
theorem challengeAt_mkRate_zero (d t1 t2 t3 t4 : Digest) :
    challengeAt (mkRate d t1 t2 t3 t4).toList 0 = PcsQuotient.Transcript.challengeOf d := by
  have hl := digestBytes_length d
  simp only [challengeAt, PcsQuotient.Transcript.challengeOf, mkRate_toList, List.append_assoc, Nat.mul_zero,
    Nat.zero_add]
  rw [beWord_append _ _ _ (by omega), beWord_append _ _ _ (by omega), beWord_append _ _ _ (by omega)]

/-- A digest read with its last lane first. -/
def rotD (t : Digest) : Digest := #v[t[3], t[0], t[1], t[2]]

/-- The inverse rotation. -/
def unrotD (t : Digest) : Digest := #v[t[1], t[2], t[3], t[0]]

/-- **The rotation of a digest.** -/
def rotEquiv : Digest ≃ Digest where
  toFun := rotD
  invFun := unrotD
  left_inv t := by
    obtain ⟨⟨l⟩, hl⟩ := t
    match l, hl with
    | [_, _, _, _], _ => rfl
  right_inv t := by
    obtain ⟨⟨l⟩, hl⟩ := t
    match l, hl with
    | [_, _, _, _], _ => rfl

/-- **The challenge of a tail digest**: its bytes `0 … 24` read as a challenge reads a digest's `8 … 32`. -/
def chalTail (t : Digest) : E := PcsQuotient.Transcript.challengeOf (rotD t)

theorem beWord_pre (a b : List UInt8) (n s : ℕ) (h : a.length = n) :
    PcsQuotient.Transcript.beWord (a ++ b) (n + s) = PcsQuotient.Transcript.beWord b s := by
  rw [← h]; exact beWord_append_right a b s

theorem beWord_word (x : UInt64) (b : List UInt8) :
    PcsQuotient.Transcript.beWord (wordBytes x ++ b) 0 = PcsQuotient.Transcript.beWord (wordBytes x) 0 :=
  beWord_append _ _ 0 (by simp [LeanVM.Rpm.wordBytes_len])

/-- **Challenge `1` of a five-digest rate is the second digest's tail challenge.** -/
theorem challengeAt_mkRate_one (d t1 t2 t3 t4 : Digest) :
    challengeAt (mkRate d t1 t2 t3 t4).toList 1 = chalTail t1 := by
  obtain ⟨⟨l⟩, hl'⟩ := t1
  match l, hl' with
  | [a0, a1, a2, a3], _ =>
    have hd := digestBytes_length d
    have w := LeanVM.Rpm.wordBytes_len
    have hdb : digestBytes (⟨⟨[a0, a1, a2, a3]⟩, rfl⟩ : Digest) =
        wordBytes a0 ++ (wordBytes a1 ++ (wordBytes a2 ++ wordBytes a3)) := by simp [digestBytes]
    have hrot : digestBytes (rotD ⟨⟨[a0, a1, a2, a3]⟩, rfl⟩) =
        wordBytes a3 ++ (wordBytes a0 ++ (wordBytes a1 ++ wordBytes a2)) := by
      simp [digestBytes, rotD]
    simp only [challengeAt, chalTail, PcsQuotient.Transcript.challengeOf, mkRate_toList, List.append_assoc, hdb,
      hrot, Nat.reduceMul, Nat.reduceAdd]
    generalize digestBytes t2 ++ (digestBytes t3 ++ List.take 8 (digestBytes t4)) = R
    have e48 : PcsQuotient.Transcript.beWord (digestBytes d ++ (wordBytes a0 ++ (wordBytes a1 ++
        (wordBytes a2 ++ (wordBytes a3 ++ R))))) 48 = PcsQuotient.Transcript.beWord (wordBytes a2) 0 := by
      rw [show (48 : ℕ) = 32 + (8 + (8 + 0)) from rfl, beWord_pre _ _ 32 _ hd, beWord_pre _ _ 8 _ (w a0),
        beWord_pre _ _ 8 _ (w a1), beWord_word]
    have e40 : PcsQuotient.Transcript.beWord (digestBytes d ++ (wordBytes a0 ++ (wordBytes a1 ++
        (wordBytes a2 ++ (wordBytes a3 ++ R))))) 40 = PcsQuotient.Transcript.beWord (wordBytes a1) 0 := by
      rw [show (40 : ℕ) = 32 + (8 + 0) from rfl, beWord_pre _ _ 32 _ hd, beWord_pre _ _ 8 _ (w a0), beWord_word]
    have e32 : PcsQuotient.Transcript.beWord (digestBytes d ++ (wordBytes a0 ++ (wordBytes a1 ++
        (wordBytes a2 ++ (wordBytes a3 ++ R))))) 32 = PcsQuotient.Transcript.beWord (wordBytes a0) 0 := by
      rw [show (32 : ℕ) = 32 + 0 from rfl, beWord_pre _ _ 32 _ hd, beWord_word]
    have r24 : PcsQuotient.Transcript.beWord (wordBytes a3 ++ (wordBytes a0 ++ (wordBytes a1 ++ wordBytes a2))) 24 =
        PcsQuotient.Transcript.beWord (wordBytes a2) 0 := by
      rw [show (24 : ℕ) = 8 + (8 + (8 + 0)) from rfl, beWord_pre _ _ 8 _ (w a3), beWord_pre _ _ 8 _ (w a0),
        beWord_pre _ _ 8 _ (w a1)]
    have r16 : PcsQuotient.Transcript.beWord (wordBytes a3 ++ (wordBytes a0 ++ (wordBytes a1 ++ wordBytes a2))) 16 =
        PcsQuotient.Transcript.beWord (wordBytes a1) 0 := by
      rw [show (16 : ℕ) = 8 + (8 + 0) from rfl, beWord_pre _ _ 8 _ (w a3), beWord_pre _ _ 8 _ (w a0), beWord_word]
    have r8 : PcsQuotient.Transcript.beWord (wordBytes a3 ++ (wordBytes a0 ++ (wordBytes a1 ++ wordBytes a2))) 8 =
        PcsQuotient.Transcript.beWord (wordBytes a0) 0 := by
      rw [show (8 : ℕ) = 8 + 0 from rfl, beWord_pre _ _ 8 _ (w a3), beWord_word]
    rw [e48, e40, e32, r24, r16, r8]

/-- **The tail challenge is regular**: at most `2^64` digests share one. -/
theorem chalTail_regular : Regular chalTail := by
  intro e
  have h := E2ECompleteness.challengeOf_regular e
  have hs : (Finset.univ.filter fun d : Digest ↦ chalTail d = e) =
      (Finset.univ.filter fun d : Digest ↦ PcsQuotient.Transcript.challengeOf d = e).map
        rotEquiv.symm.toEmbedding := by
    ext d
    rw [Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_filter, Finset.mem_filter]
    exact ⟨fun h ↦ ⟨Finset.mem_univ _, h.2⟩, fun h ↦ ⟨Finset.mem_univ _, h.2⟩⟩
  rw [hs, Finset.card_map]
  exact h

/-! ## The five-digest reading of a hash -/

/-- leanerVM's two calls with the hash read as the first of five digests (`hash5`). -/
def iota5 : QueryImpl KeccakCalls (OracleComp KeccakCalls)
  | .inl x => hash5 x
  | .inr s => callKeccakF1600 s

/-- **What the five-digest reading hashes**: an input satisfying `P`, or a tail of a short one. -/
def P5 (P : Bytes → Prop) (m : Bytes) : Prop := P m ∨ ∃ i m', 1 ≤ i ∧ i ≤ 4 ∧ Short m' ∧ P m' ∧ m = extIn i m'

theorem hashOK_rate5 {P : Bytes → Prop} {x : Bytes} (hx : P x) (hs : Short x) : HashOK (P5 P) (rate5 x) := by
  have ht : ∀ i, 1 ≤ i → i ≤ 4 → HashOK (P5 P) (callKeccak256 (extIn i x)) := fun i hi hi' ↦
    E2ECompleteness.hashOK_callKeccak256 (Or.inr ⟨i, x, hi, hi', hs, hx, rfl⟩)
  unfold rate5
  exact E2ECompleteness.HashOK.bind (E2ECompleteness.hashOK_callKeccak256 (Or.inl hx)) fun _ ↦
    E2ECompleteness.HashOK.bind (ht 1 le_rfl (by norm_num)) fun _ ↦
    E2ECompleteness.HashOK.bind (ht 2 (by norm_num) (by norm_num)) fun _ ↦
    E2ECompleteness.HashOK.bind (ht 3 (by norm_num) (by norm_num)) fun _ ↦
    E2ECompleteness.HashOK.bind (ht 4 (by norm_num) le_rfl) fun _ ↦ E2ECompleteness.HashOK.pure _ _

theorem hashOK_hash5 {P : Bytes → Prop} {x : Bytes} (hx : P x) (hs : Short x) : HashOK (P5 P) (hash5 x) :=
  E2ECompleteness.HashOK.map _ (hashOK_rate5 hx hs)

/-- **The five-digest reading of a computation hashing short inputs satisfying `P` hashes `P5 P`.** -/
theorem hashOK_iota5 {P : Bytes → Prop} (hP : ∀ m, P m → Short m) {α : Type} {X : OracleComp KeccakCalls α}
    (h : HashOK P X) : HashOK (P5 P) (simulateQ iota5 X) := by
  induction X using OracleComp.inductionOn with
  | pure a => rw [simulateQ_pure]; exact E2ECompleteness.HashOK.pure _ _
  | query_bind t k ih =>
    obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).1 h
    rw [simulateQ_query_bind]
    rcases t with x | s
    · exact E2ECompleteness.HashOK.bind (hashOK_hash5 ht (hP x ht)) fun u ↦ ih u (hk u)
    · exact E2ECompleteness.HashOK.bind (E2ECompleteness.hashOK_callKeccakF1600 _ s) fun u ↦ ih u (hk u)

/-- **What is hashed before the bus draw**: short inputs of another length than the chain's (`32`, `112`), or their
tails. -/
def GoodL5 : Bytes → Prop := P5 fun m ↦ Short m ∧ GoodL 112 m

theorem short_of_length {x : Bytes} (h : x.length = 112) : Short x := by
  unfold Short lenB; omega

/-- The bus draw's input is fresh. -/
theorem fresh_x1 {c : Cache} (hc : ∀ m, c (.inl m) ≠ none → GoodL5 m) {x : Bytes} (hx : x.length = 112) :
    c (.inl x) = none := by
  by_contra h
  rcases hc x h with ⟨_, h2⟩ | ⟨i, m', hi, _, _, _, rfl⟩
  · exact h2.2 hx
  · exact extIn_not_short hi m' (short_of_length hx)

/-- The bus draw's first tail is fresh, after the draw's input. -/
theorem fresh_e1 {c : Cache} (hc : ∀ m, c (.inl m) ≠ none → GoodL5 m) {x : Bytes} (hx : x.length = 112)
    (d : Digest) : (c.cacheQuery (.inl x) d) (.inl (extIn 1 x)) = none := by
  rw [QueryCache.cacheQuery_of_ne _ _ (ne_inl (extIn_ne_short le_rfl x x (short_of_length hx)))]
  by_contra h
  rcases hc _ h with ⟨h1, _⟩ | ⟨i, m', _, _, h3, h4, h5⟩
  · exact extIn_not_short le_rfl x h1
  · obtain ⟨-, rfl⟩ := extIn_inj (short_of_length hx) h3 h5
    exact h4.2.2 hx

/-! ## The bus draw -/

/-- **π1-rec4's `α`** from the bus draw: `squares c 4`, `c` its challenge `0`. -/
def alphaOf4 (r : RateB) : List E := squares (challengeAt r.toList 0) 4

theorem prEvent_le_ite {γ : Type} (X : ProbComp γ) (ev : γ → Prop) (P : Prop) [Decidable P]
    (h : ∀ z ∈ support X, ev z → P) : Pr{let z ← X}[ev z] ≤ if P then 1 else 0 := by
  split_ifs with hP
  · exact prEvent_le_one _
  · exact le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz he ↦ hP (h z hz he))

/-- **π1-rec4's bus challenges in the random-oracle model**: from a stage `A` hashing `GoodL5` inputs only, the bus
draw on a `112`-byte input, a bad set with at most `Nbad` values of `β` for each `α`: the bad event has probability
at most `Nbad / 2^192`. -/
theorem prEvent_bus4_le {α γ : Type} (bad : List E → E → Prop) (Nbad : ℕ)
    (hbad : ∀ as, ∃ T : Finset E, T.card ≤ Nbad ∧ ∀ b, bad as b → b ∈ T)
    (inp : α → Bytes) (hinp : ∀ a, (inp a).length = 112) (A : OracleComp KeccakCalls α)
    (C : α → RateB → OracleComp KeccakCalls γ) (hA : HashOK GoodL5 A) :
    Pr{let z ← (simulateQ ro (do
        let a ← A
        let r ← rate5 (inp a)
        let z ← C a r
        pure (z, (alphaOf4 r, challengeAt r.toList 1)))).run ∅}[bad z.1.2.1 z.1.2.2] ≤
      (Nbad : ℝ≥0∞) / 2 ^ 192 := by
  classical
  set B : ℝ≥0∞ := (Nbad : ℝ≥0∞) / 2 ^ 192
  simp only [rate5, simulateQ_bind, simulateQ_pure, simulateQ_callKeccak256, StateT.run_bind, StateT.run_pure,
    bind_assoc, pure_bind, alphaOf4, challengeAt_mkRate_zero, challengeAt_mkRate_one]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hp ↦ ?_
  have hc₁ : ∀ m, p.2 (.inl m) ≠ none → GoodL5 m := fun m hm ↦
    (cache_of_hashOK hA ∅ hp m hm).elim (fun h ↦ absurd rfl h) id
  refine (prEvent_query_le _ _ False (fun _ ↦ fresh_x1 hc₁ (hinp p.1)) _ _ (fun _ ↦ B) fun d ↦ ?_).trans ?_
  rotate_left
  · simp only [↓reduceIte, zero_add]
    exact le_of_eq (sum_const_div B)
  refine (prEvent_query_le _ _ False (fun _ ↦ fresh_e1 hc₁ (hinp p.1) d) _ _
    (fun t1 ↦ if bad (squares (PcsQuotient.Transcript.challengeOf d) 4) (chalTail t1) then 1 else 0)
    fun t1 ↦ ?_).trans ?_
  rotate_left
  · simp only [↓reduceIte, zero_add]
    exact sum_bad_le chalTail chalTail_regular _ Nbad (hbad _)
  refine prEvent_le_ite _ _ _ fun z hz he ↦ ?_
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hz
  exact he

/-! ## The staged run -/

/-- **π1-rec4's experiment's stages** in the five-digest reading (no coins): `A` up to the bus draw's input (`inp`),
the bus draw, `B` up to the point draw's input (`tin`; `pr` the prior `t`'s bad set depends on), the point draw, `C`
the rest, its output the verdict. -/
structure KStaged4 where
  α : Type
  β : Type
  inp : α → Bytes
  A : OracleComp KeccakCalls α
  B : α → RateB → OracleComp KeccakCalls β
  tin : β → Bytes
  pr : β → List E
  C : β → RateB → OracleComp KeccakCalls Bool

/-- **The staged run**: the verdict with `t`'s stage, and the bus challenges `(α, β)`. -/
def KStaged4.run (S : KStaged4) : OracleComp KeccakCalls ((Bool × (List E × E)) × (List E × E)) := do
  let a ← S.A
  let r₁ ← rate5 (S.inp a)
  let b ← S.B a r₁
  let r₂ ← rate5 (S.tin b)
  let z ← S.C b r₂
  return ((z, (S.pr b, challengeAt r₂.toList 0)), (alphaOf4 r₁, challengeAt r₁.toList 1))

/-- **The run up to the point draw**: `B`'s output and the bus challenges. -/
def KStaged4.pre (S : KStaged4) : OracleComp KeccakCalls (S.β × (List E × E)) := do
  let a ← S.A
  let r₁ ← rate5 (S.inp a)
  let b ← S.B a r₁
  return (b, (alphaOf4 r₁, challengeAt r₁.toList 1))

/-- **The probability conditions** of a staged run: bad sets `bad` (bus challenges, at most `Nbad` values of `β` per
`α`) and `badT` (`t`, at most `ct` values per prior), the point draw's cache-hit probability `εt` and a grinding error
`εpow`. -/
structure KStaged4.Good (S : KStaged4) (bad badT : List E → E → Prop) (Nbad ct : ℕ) (εt εpow : ℝ≥0∞) : Prop where
  /-- The bus draw's input has `112` bytes. -/
  inp_length : ∀ a, (S.inp a).length = 112
  /-- Before it, nothing of the chain's lengths (`32`, `112`) is hashed, but tails of other inputs. -/
  hashA : HashOK GoodL5 S.A
  /-- At most `Nbad` bad values of `β` for each `α`. -/
  badCard : ∀ alphas, ∃ T : Finset E, T.card ≤ Nbad ∧ ∀ b, bad alphas b → b ∈ T
  /-- At most `ct` bad values of `t` for each prior. -/
  badTCard : ∀ fp, ∃ T : Finset E, T.card ≤ ct ∧ ∀ t, badT fp t → t ∈ T
  /-- The point draw's input is already hashed before its query with probability at most `εt`. -/
  tFresh : Pr{let p ← (simulateQ ro S.pre).run ∅}[p.2 (.inl (S.tin p.1.1)) ≠ none] ≤ εt
  /-- **Grinding**: rejected at good challenges with probability at most `εpow`. -/
  rejectGood : Pr{let z ← (simulateQ ro S.run).run' ∅}[
    z.1.1 = false ∧ ¬ bad z.2.1 z.2.2 ∧ ¬ badT z.1.2.1 z.1.2.2] ≤ εpow

/-- **The run, cut at the point draw.** -/
theorem KStaged4.run_eq (S : KStaged4) :
    S.run = S.pre >>= fun x ↦ callKeccak256 (S.tin x.1) >>= fun d ↦ (do
      let t1 ← callKeccak256 (extIn 1 (S.tin x.1))
      let t2 ← callKeccak256 (extIn 2 (S.tin x.1))
      let t3 ← callKeccak256 (extIn 3 (S.tin x.1))
      let t4 ← callKeccak256 (extIn 4 (S.tin x.1))
      S.C x.1 (mkRate d t1 t2 t3 t4)) >>= fun z ↦
        pure ((z, (S.pr x.1, PcsQuotient.Transcript.challengeOf d)), x.2) := by
  simp only [KStaged4.run, KStaged4.pre, rate5, bind_assoc, pure_bind, challengeAt_mkRate_zero]

/-- **One staged run**: rejected with probability at most the bus challenges' `Nbad / 2^192`, `t`'s
`ct / 2^192 + εt` and `εpow`. -/
theorem prEvent_run_false_le4 (S : KStaged4) {bad badT : List E → E → Prop} {Nbad ct : ℕ} {εt εpow : ℝ≥0∞}
    (h : S.Good bad badT Nbad ct εt εpow) :
    Pr{let z ← (simulateQ ro S.run).run' ∅}[z.1.1 = false] ≤
      (Nbad : ℝ≥0∞) / 2 ^ 192 + ((ct : ℝ≥0∞) / 2 ^ 192 + εt) + εpow := by
  have hab : Pr{let z ← (simulateQ ro S.run).run' ∅}[bad z.2.1 z.2.2] ≤ (Nbad : ℝ≥0∞) / 2 ^ 192 := by
    rw [StateT.run'_eq, prEvent_map]
    have e : S.run = (do
        let a ← S.A
        let r ← rate5 (S.inp a)
        let z ← (S.B a r >>= fun b ↦ rate5 (S.tin b) >>= fun r₂ ↦ S.C b r₂ >>= fun z ↦
          pure (z, (S.pr b, challengeAt r₂.toList 0)))
        pure (z, (alphaOf4 r, challengeAt r.toList 1))) := by
      simp only [KStaged4.run, bind_assoc, pure_bind]
    rw [e]
    exact prEvent_bus4_le bad Nbad h.badCard S.inp h.inp_length S.A _ h.hashA
  have ht : Pr{let z ← (simulateQ ro S.run).run' ∅}[badT z.1.2.1 z.1.2.2] ≤ εt + (ct : ℝ≥0∞) / 2 ^ 192 := by
    rw [StateT.run'_eq, prEvent_map, S.run_eq]
    refine (prEvent_tquery_le _ E2ECompleteness.challengeOf_regular badT ct h.badTCard S.pre
      (fun x ↦ S.tin x.1) (fun x ↦ S.pr x.1) (fun x d ↦ (do
        let t1 ← callKeccak256 (extIn 1 (S.tin x.1))
        let t2 ← callKeccak256 (extIn 2 (S.tin x.1))
        let t3 ← callKeccak256 (extIn 3 (S.tin x.1))
        let t4 ← callKeccak256 (extIn 4 (S.tin x.1))
        S.C x.1 (mkRate d t1 t2 t3 t4)))
      (fun x d z ↦ ((z, (S.pr x.1, PcsQuotient.Transcript.challengeOf d)), x.2))
      (fun w ↦ badT w.1.2.1 w.1.2.2) (fun _ _ _ hw ↦ hw) ∅).trans ?_
    exact add_le_add h.tFresh le_rfl
  have hsplit : Pr{let z ← (simulateQ ro S.run).run' ∅}[z.1.1 = false] ≤
      Pr{let z ← (simulateQ ro S.run).run' ∅}[bad z.2.1 z.2.2] +
        (Pr{let z ← (simulateQ ro S.run).run' ∅}[badT z.1.2.1 z.1.2.2] +
          Pr{let z ← (simulateQ ro S.run).run' ∅}[
            z.1.1 = false ∧ ¬ bad z.2.1 z.2.2 ∧ ¬ badT z.1.2.1 z.1.2.2]) := by
    refine (prEvent_le_prEvent_add_prEvent_and_not _ _ (fun z : (Bool × (List E × E)) × (List E × E) ↦
      bad z.2.1 z.2.2)).trans (add_le_add le_rfl ?_)
    refine (prEvent_le_prEvent_add_prEvent_and_not _ _ (fun z : (Bool × (List E × E)) × (List E × E) ↦
      badT z.1.2.1 z.1.2.2)).trans (add_le_add le_rfl (le_of_eq ?_))
    simp only [and_assoc]
  refine hsplit.trans ?_
  calc _ ≤ (Nbad : ℝ≥0∞) / 2 ^ 192 + ((εt + (ct : ℝ≥0∞) / 2 ^ 192) + εpow) :=
        add_le_add hab (add_le_add ht h.rejectGood)
    _ = (Nbad : ℝ≥0∞) / 2 ^ 192 + ((ct : ℝ≥0∞) / 2 ^ 192 + εt) + εpow := by
        rw [add_comm εt]
        ac_rfl

end UniKeccakComplete.Rec4

/-- info: 'UniKeccakComplete.Rec4.prEvent_run_false_le4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.prEvent_run_false_le4
