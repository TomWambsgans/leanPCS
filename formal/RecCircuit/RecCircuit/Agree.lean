-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecCircuit.Sound
import RecGraph.Values

/-!
# This library's graph semantics is `RecGraph`'s

`Graph.step` (the transcription of `eval.rs`) and `RecGraph.stepP` (`RecGraph`'s, over a permutation) give every node
the same value (`Corr`) when its operands have the same values and its reads are in range (`step_corr`): the
big-endian words of a read (`beWordAt`, `beWord` on `UInt64` against `beNat`), the challenge and the narrow one, the
bit fields (`intBits`), the seed and the hashes (Keccak-256 over Keccak-f[1600]). So on an accepted circuit every live
node of the expanded graph has the same value in both semantics (`agree`).
-/

namespace RecCircuit

open Primitives LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement

/-! ## Words -/

theorem ofLane_eq (w : UInt64) : K.ofLane w = F64.ofU64 w := rfl

theorem ofLane_ofNat (n : ℕ) : K.ofLane (UInt64.ofNat n) = F64.ofNat n := rfl

theorem lane_ofLane (w : UInt64) : (K.ofLane w).lane = w := rfl

theorem toU64_eq_lane (a : F64) : F64.toU64 a = K.lane a := rfl

theorem orShift (x : UInt64) (b : UInt8) (hx : x.toNat < 2 ^ 56) :
    ((x <<< 8) ||| b.toUInt64).toNat = x.toNat * 256 + b.toNat := by
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64]
  have h8 : (8 : UInt64).toNat % 64 = 8 := rfl
  rw [h8, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by have := b.toNat_lt; omega)]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, show x.toNat * 2 ^ 8 = 2 ^ 8 * x.toNat by ring, show x.toNat * 256 + b.toNat = 2 ^ 8 * x.toNat + b.toNat by ring,
    Nat.testBit_two_pow_mul_add _ (show b.toNat < 2 ^ 8 from b.toNat_lt)]
  rw [show 2 ^ 8 * x.toNat = 2 ^ 8 * x.toNat + 0 by rfl, Nat.testBit_two_pow_mul_add _ (by norm_num)]
  by_cases hi : i < 8
  · simp [hi]
  · simp [hi, testBit_byte b i (by omega)]

/-- A big-endian fold of bytes into a `UInt64` is their `beNat`, for at most 8 bytes. -/
theorem beFold_toNat (f : ℕ → UInt8) : ∀ m ≤ 8,
    ((List.range m).foldl (fun (acc : UInt64) k => (acc <<< 8) ||| (f k).toUInt64) (0 : UInt64)).toNat =
      beNat ((List.range m).map f)
  | 0, _ => by simp [beNat]
  | m + 1, hm => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, List.map_append, List.map_cons,
      List.map_nil, beNat_append, ← beFold_toNat f m (by omega)]
    apply orShift
    rw [beFold_toNat f m (by omega)]
    have := beNat_lt ((List.range m).map f)
    simp only [List.length_map, List.length_range] at this
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem slice_eq_map (bytes : List UInt8) (a n : ℕ) (h : a + n ≤ bytes.length) :
    slice bytes a n = (List.range n).map fun k => bytes.getD (a + k) 0 := by
  apply List.ext_getElem
  · simp [slice]; omega
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    have := slice_getD bytes a n i (by simpa using h2)
    rw [List.getD_eq_getElem _ _ h1] at this
    exact this

theorem beWord_eq (bytes : List UInt8) (start : ℕ) (h : start + 8 ≤ bytes.length) :
    K.ofLane (PcsQuotient.Transcript.beWord bytes start) = F64.ofNat (beNat (slice bytes start 8)) := by
  rw [ofLane_eq, F64.ofU64_eq_ofNat]
  unfold PcsQuotient.Transcript.beWord
  rw [beFold_toNat (fun k => bytes.getD (start + k) 0) 8 le_rfl, slice_eq_map _ _ _ h]

theorem beWordAt_eq (a : Array UInt8) (start : ℕ) (h : start + 8 ≤ a.size) :
    K.ofLane (beWordAt a start) = F64.ofNat (beNat (slice a.toList start 8)) := by
  rw [ofLane_eq, F64.ofU64_eq_ofNat]
  unfold beWordAt
  rw [beFold_toNat (fun k => a.getD (start + k) 0) 8 le_rfl, slice_eq_map _ _ _ (by simpa using h)]
  congr 2
  apply List.map_congr_left
  intro k _
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem extract_toList (s : List UInt8) (a b : ℕ) : (s.toArray.extract a b).toList = slice s a (b - a) := by
  simp [slice, List.extract_eq_drop_take]

theorem eK_eq (c0 : UInt64) : eK c0 = F192.ofLimbs (F64.ofU64 c0) 0 0 := rfl

theorem elemOfNats_zero (n : ℕ) : elemOfNats n 0 0 = F192.ofLimbs (F64.ofNat n) 0 0 := by
  simp [elemOfNats, Primitives.F64.ofNat_zero]

theorem beWord_toNat (bytes : List UInt8) (start : ℕ) (h : start + 8 ≤ bytes.length) :
    (PcsQuotient.Transcript.beWord bytes start).toNat = beNat (slice bytes start 8) := by
  unfold PcsQuotient.Transcript.beWord
  rw [beFold_toNat (fun k => bytes.getD (start + k) 0) 8 le_rfl, slice_eq_map _ _ _ h]

/-! ## Node by node -/

/-- The reads a node's value needs in range: a statement word in the public input, a scalar's or a root half's bytes
in the stream. -/
def RangeOk (pubLen streamLen : ℕ) : Node → Prop
  | .statement k => 8 * k + 8 ≤ pubLen
  | .input o l => (l = 24 ∨ l = 16) → o + l ≤ streamLen
  | _ => True

/-- RecGraph's step over Keccak-f[1600], the expanded graph's kernels none. -/
abbrev rgStep (iv pub stream : List UInt8) (vals : Array RecGraph.Value) (n : Node) : RecGraph.Value :=
  RecGraph.stepP keccakF1600 iv pub stream.toArray #[] vals (toRGNode n)

/-- A transcript state's value: the seed's or a hash's. -/
def Value.IsSt : Value → Prop
  | .e _ => False
  | _ => True

theorem corr_toState {a : Value} {b : RecGraph.Value} (ha : a.IsSt) (h : Corr a b)
    {vals : Array RecGraph.Value} {i : ℕ} (hb : vals[i]? = some b) : a.toState = digestBytes (RecGraph.valState vals i) := by
  cases a with
  | e x => exact absurd ha id
  | state s =>
    cases b with
    | state d => simp only [Corr] at h; simp [Value.toState, RecGraph.valState, hb, h]
    | _ => cases h
  | sponge st =>
    cases b with
    | sponge st' => simp only [Corr] at h; subst h; simp [Value.toState, RecGraph.valState, hb]
    | _ => cases h

theorem corr_toRate {a : Value} {b : RecGraph.Value} (h : Corr a b)
    {vals : Array RecGraph.Value} {i : ℕ} (hb : vals[i]? = some b) : a.toRate = RecGraph.valRate vals i := by
  cases a with
  | e x =>
    cases b with
    | elem y => simp [Value.toRate, RecGraph.valRate, hb]
    | _ => cases h
  | state s =>
    cases b with
    | state d => simp [Value.toRate, RecGraph.valRate, hb]
    | _ => cases h
  | sponge st =>
    cases b with
    | sponge st' => simp only [Corr] at h; subst h; simp [Value.toRate, RecGraph.valRate, hb]
    | _ => cases h

/-- `challenge_at` on a sponge's rate, in both semantics. -/
theorem challengeAt_corr (st : KeccakState) (k : ℕ) (hk : k < 5) :
    challengeAtL (UniStatement.rateBytesOf st) k = UniStatement.challengeAt (UniStatement.rateBytesOf st) k := by
  have h136 := Compiled.rateBytesOf_length st
  unfold challengeAtL UniStatement.challengeAt
  simp only [elemOfNats]
  rw [beWord_eq _ _ (by omega), beWord_eq _ _ (by omega), beWord_eq _ _ (by omega)]
  rfl

theorem challenge_corr (d : Digest) :
    challengeOf (digestBytes d) = PcsQuotient.Transcript.challengeOf d := by
  have h32 := PcsCircuit.digestBytes_length d
  unfold challengeOf PcsQuotient.Transcript.challengeOf
  simp only [elemOfNats]
  rw [beWord_eq _ _ (by omega), beWord_eq _ _ (by omega), beWord_eq _ _ (by omega)]
  rfl

theorem narrow_corr (d : Digest) :
    narrowOf (digestBytes d) = narrowE (PcsQuotient.Transcript.challengeOf d) := by
  have h32 := PcsCircuit.digestBytes_length d
  unfold narrowOf narrowE PcsQuotient.Transcript.challengeOf
  simp only [elemOfNats]
  show _ = F192.ofLimbs (K.ofLane (K.ofLane _).lane) (K.ofLane (K.ofLane _).lane) (K.ofLane ((K.ofLane _).lane &&& _))
  rw [lane_ofLane, lane_ofLane, lane_ofLane, beWord_eq _ _ (by omega), beWord_eq _ _ (by omega), ofLane_eq,
    F64.ofU64_eq_ofNat, UInt64.toNat_and, beWord_toNat _ _ (by omega)]
  congr 1
  rw [show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem bits_corr (x : F192) (s w : ℕ) : bitsOf x s w = RecGraph.bitsValue x s w := by
  unfold bitsOf RecGraph.bitsValue intBits
  simp only [elemOfNats, eK, eNew]
  rw [ofLane_ofNat, show (0 : UInt64) = UInt64.ofNat 0 from rfl, ofLane_ofNat]
  have hn : x.c0.toNat < 2 ^ 64 := UInt64.toNat_lt _
  have e1 : (E.limb x 0).lane = x.c0 := rfl
  rw [e1, Nat.shiftRight_eq_div_pow]
  congr 2
  have hd : x.c0.toNat / 2 ^ s < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) hn
  rcases Nat.lt_or_ge w 64 with hw | hw
  · rw [min_eq_left hw.le]
  · rw [min_eq_right hw, Nat.mod_eq_of_lt hd,
      Nat.mod_eq_of_lt (lt_of_lt_of_le hd (Nat.pow_le_pow_right (by norm_num) hw))]

theorem input_corr (stream : List UInt8) (o l : ℕ) (h : (l = 24 ∨ l = 16) → o + l ≤ stream.length) :
    inputValue stream o l = RecGraph.inputValue (stream.toArray.extract o (o + l)) l := by
  unfold inputValue RecGraph.inputValue
  have hb : (stream.toArray.extract o (o + l)).toList = slice stream o l := by
    rw [extract_toList]; congr 1; omega
  by_cases h24 : l = 24
  · subst h24
    have hsz : (stream.toArray.extract o (o + 24)).size = 24 := by
      simp [Array.size_extract]; have := h (Or.inl rfl); omega
    simp only [if_pos rfl, eNew]
    rw [beWordAt_eq _ _ (by omega), beWordAt_eq _ _ (by omega), beWordAt_eq _ _ (by omega), hb]
    rfl
  · by_cases h16 : l = 16
    · subst h16
      have hsz : (stream.toArray.extract o (o + 16)).size = 16 := by
        simp [Array.size_extract]; have := h (Or.inr rfl); omega
      simp only [if_neg (by decide : (16 : ℕ) ≠ 24), if_pos rfl, eNew]
      rw [beWordAt_eq _ _ (by omega), beWordAt_eq _ _ (by omega), hb]
      rfl
    · simp only [if_neg h24, if_neg h16, eK, eNew]
      rw [ofLane_ofNat, ← Array.foldl_toList, hb]
      rfl

/-- **A node's value in both semantics**, from its operands'. -/
theorem step_corr (g : Graph) (iv pub stream : List UInt8) (mine : Array Value) (theirs : Array RecGraph.Value)
    (n : Node) (hrw : ∀ k m, n ≠ .ringWeight k m)
    (hops : ∀ o ∈ n.ops, ∃ b, theirs[o]? = some b ∧ Corr (mine.getD o default) b)
    (hst : ∀ o ∈ n.ops, (∀ a b, n ≠ .add a b) → (∀ a b, n ≠ .mul a b) → (∀ v s w, n ≠ .bits v s w) →
      (mine.getD o default).IsSt)
    (hwide : ∀ h k, n = .wide h k → k < 5 ∧ ∃ st, mine.getD h default = .sponge st)
    (hrange : RangeOk pub.length stream.length n) :
    Corr (g.step iv pub stream mine n) (rgStep iv pub stream theirs n) := by
  have hE : ∀ o ∈ n.ops, (mine.getD o default).toE = RecGraph.valE theirs o := fun o ho => by
    obtain ⟨b, hb, hc⟩ := hops o ho; exact Corr.toE hc hb
  have hS : ∀ o ∈ n.ops, (∀ a b, n ≠ .add a b) → (∀ a b, n ≠ .mul a b) → (∀ v s w, n ≠ .bits v s w) →
      (mine.getD o default).toState = digestBytes (RecGraph.valState theirs o) := fun o ho h1 h2 h3 => by
    obtain ⟨b, hb, hc⟩ := hops o ho
    exact corr_toState (hst o ho h1 h2 h3) hc hb
  cases n with
  | const a b d => rfl
  | statement k =>
    simp only [RangeOk] at hrange
    show elemOfNats _ 0 0 = eK (beWordAt pub.toArray (8 * k))
    rw [eK, eNew, beWordAt_eq _ _ (by simpa using hrange)]
    simp [elemOfNats, Primitives.F64.ofNat_zero]
    rfl
  | input o l =>
    simp only [RangeOk] at hrange
    exact input_corr stream o l hrange
  | add a b =>
    show _ + _ = _ + _
    simp only [hE a (by simp [Node.ops]), hE b (by simp [Node.ops])]
  | mul a b =>
    show _ * _ = _ * _
    simp only [hE a (by simp [Node.ops]), hE b (by simp [Node.ops])]
  | seed => rfl
  | hash s f t =>
    show keccakState (_ ++ _) = Id.run (keccak256StateWith _ (_ ++ _))
    rw [hS s (by simp [Node.ops]) (by intros; simp) (by intros; simp) (by intros; simp), extract_toList]
    rfl
  | wide h k =>
    obtain ⟨hk, st, hst'⟩ := hwide h k rfl
    obtain ⟨b, hb, hc⟩ := hops h (by simp [Node.ops])
    have hR := corr_toRate hc hb
    show challengeAtL _ _ = UniStatement.challengeAt _ _
    rw [← hR, hst', Value.toRate, challengeAt_corr st k hk]
  | low h =>
    show challengeOf _ = _
    rw [hS h (by simp [Node.ops]) (by intros; simp) (by intros; simp) (by intros; simp), challenge_corr]
  | narrow h =>
    show narrowOf _ = _
    rw [hS h (by simp [Node.ops]) (by intros; simp) (by intros; simp) (by intros; simp), narrow_corr]
  | bits v s w =>
    show bitsOf _ s w = _
    simp only [hE v (by simp [Node.ops]), bits_corr]
  | ringWeight k m => exact absurd rfl (hrw k m)

/-! ## Every live node -/

theorem toRG_operands (n : Node) (h : ∀ k m, n ≠ .ringWeight k m) :
    RecGraph.reads #[] (toRGNode n) = n.ops := by
  cases n <;> first | rfl | exact absurd rfl (h _ _)

namespace Compiled

variable {c : Compiled} {r : Recorded}

/-- **`RecGraph`'s values of the expanded graph**, over Keccak-f[1600]. -/
def rgX (c : Compiled) (iv pub stream : List UInt8) : Array RecGraph.Value :=
  RecGraph.evalP keccakF1600 iv pub stream.toArray #[] #[] (c.nodes.toList.map toRGNode)

theorem rgX_node (c : Compiled) (iv pub stream : List UInt8) {i : ℕ} (hi : i < c.nodes.size)
    (hrw : ∀ k m, c.nodes.getD i default ≠ .ringWeight k m) (hops : ∀ o ∈ (c.nodes.getD i default).ops, o < i) :
    (c.rgX iv pub stream)[i]? = some (rgStep iv pub stream (c.rgX iv pub stream) (c.nodes.getD i default)) := by
  have hl : i < (c.nodes.toList.map toRGNode).length := by simpa using hi
  unfold rgX
  rw [RecGraph.evalP_get _ _ _ _ _ _ _ hl]
  have hn : (c.nodes.toList.map toRGNode)[i] = toRGNode (c.nodes.getD i default) := by
    simp [Array.getD_eq_getD_getElem?, hi]
  rw [hn]
  congr 1
  apply RecGraph.stepP_local _ _ _ _ _ _ _ _ i
  · rw [toRG_operands _ hrw]; exact hops
  · intro j hj
    exact RecGraph.evalP_take_agree _ _ _ _ _ _ _ hl.le j hj

/-- A live node's reads are in range. -/
theorem range_ok (hc : c.Checked r) {id : ℕ} (hid : id < c.nodes.size) (hl : c.live.getD id false = true) :
    RangeOk 32 r.graph.streamLen (c.nodes.getD id default) := by
  have hok := hc.nodes id hid hl
  cases hn : c.nodes.getD id default with
  | statement k =>
    simp only [nodeOk, hn, Bool.and_eq_true, decide_eq_true_eq] at hok
    show 8 * k + 8 ≤ 32
    have := hok.1.1.1.1; omega
  | input off len =>
    intro _
    by_cases hf : (c.freeReads.any fun e => e.1 == off && e.2 == c.limbsOf id) = true
    · simp only [nodeOk, hn, hf, ite_true, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨a, ha, hpa⟩ := Array.any_eq_true.mp hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hpa
      have hg : c.freeReads.getD a default = c.freeReads[a] := by simp [Array.getD_eq_getD_getElem?, ha]
      have := ((freeReads_parts hc.free).1 a ha).2.1
      rw [hg, hpa.1] at this
      rw [hok.2]; exact this
    · simp only [nodeOk, hn, hf, Bool.false_eq_true, ite_false, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, List.mem_range] at hok
      obtain ⟨_, ⟨hlen1, hall⟩, _⟩ := hok
      have hsz := hc.sizes.2.2.2.1
      have := hall (8 * len - 1) (by omega)
      by_contra hcon
      have : c.bitSelf.size ≤ 8 * off + (8 * len - 1) := by omega
      simp [Array.getD_eq_getD_getElem?, this] at *
  | _ => trivial

/-- A live seed's or hash's value, in this library's semantics, is a state. -/
theorem state_val (hc : c.Checked r) (iv pub stream : List UInt8) {o : ℕ} (ho : o < c.nodes.size)
    (hl : c.live.getD o false = true) (hk : isStateNode (c.nodes.getD o default) = true) :
    (((c.egraph r).eval iv pub stream).getD o default).IsSt := by
  rw [Graph.eval_step (c.egraph r) _ _ _ o ho (not_ringWeight hc ho hl)
    (fun a ha => ((graphOk_parts hc.graph).1 o ho hl a ha).1)]
  show ((c.egraph r).step iv pub stream _ (c.nodes.getD o default)).IsSt
  cases hn : c.nodes.getD o default <;> simp [hn, isStateNode] at hk <;> trivial

/-- A live hash's value, in this library's semantics, is a sponge. -/
theorem sponge_val (hc : c.Checked r) (iv pub stream : List UInt8) {o : ℕ} (ho : o < c.nodes.size)
    (hl : c.live.getD o false = true) (hk : Node.isHash (c.nodes.getD o default) = true) :
    ∃ st, ((c.egraph r).eval iv pub stream).getD o default = .sponge st := by
  rw [Graph.eval_step (c.egraph r) _ _ _ o ho (not_ringWeight hc ho hl)
    (fun a ha => ((graphOk_parts hc.graph).1 o ho hl a ha).1)]
  show ∃ st, (c.egraph r).step iv pub stream _ (c.nodes.getD o default) = _
  cases hn : c.nodes.getD o default <;> simp [hn, Node.isHash] at hk <;> exact ⟨_, rfl⟩

/-- **On an accepted circuit, every live node of the expanded graph has the same value in this library's semantics
and in `RecGraph`'s** (over Keccak-f[1600]), on a 32-byte public input and a stream of the graph's length. -/
theorem agree (hc : c.Checked r) (pub stream : List UInt8) (hpub : pub.length = 32)
    (hstr : stream.length = r.graph.streamLen) :
    ∀ id < c.nodes.size, c.live.getD id false = true →
      ∃ b, (c.rgX r.iv pub stream)[id]? = some b ∧ Corr (((c.egraph r).eval r.iv pub stream).getD id default) b := by
  intro id
  induction id using Nat.strong_induction_on with
  | _ id ih =>
    intro hid hl
    have hops := (graphOk_parts hc.graph).1 id hid hl
    have hrw := not_ringWeight hc hid hl
    refine ⟨_, rgX_node c r.iv pub stream hid hrw (fun o ho => (hops o ho).1), ?_⟩
    rw [Graph.eval_step (c.egraph r) _ _ _ id hid hrw (fun o ho => (hops o ho).1)]
    apply step_corr
    · exact hrw
    · intro o ho
      exact ih o (hops o ho).1 (lt_trans (hops o ho).1 hid) (hops o ho).2
    · intro o ho h1 h2 h3
      change o ∈ (c.nodes.getD id default).ops at ho
      change ∀ a b, c.nodes.getD id default ≠ Node.add a b at h1
      change ∀ a b, c.nodes.getD id default ≠ Node.mul a b at h2
      change ∀ v s w, c.nodes.getD id default ≠ Node.bits v s w at h3
      have ho' := hops o ho
      apply state_val hc _ _ _ (lt_trans ho'.1 hid) ho'.2
      have hok := hc.nodes id hid hl
      cases hn : c.nodes.getD id default with
      | low h =>
        rw [hn] at ho; simp [Node.ops] at ho; subst ho
        exact nodeOk_low_kind hc hid hl (Or.inl hn)
      | narrow h =>
        rw [hn] at ho; simp [Node.ops] at ho; subst ho
        exact nodeOk_low_kind hc hid hl (Or.inr hn)
      | hash s f t =>
        rw [hn] at ho; simp [Node.ops] at ho; subst ho
        simp only [nodeOk, hn] at hok
        split at hok
        · simp only [Bool.and_eq_true] at hok; exact hok.1.1.2
        · cases hok
      | wide h k =>
        rw [hn] at ho; simp [Node.ops] at ho; subst ho
        simp only [nodeOk, hn] at hok
        split at hok
        · simp only [Bool.and_eq_true] at hok
          exact isStateNode_of_isHash _ hok.1.1.1.1.1.1
        · cases hok
      | add a b => exact absurd hn (h1 a b)
      | mul a b => exact absurd hn (h2 a b)
      | bits v s w => exact absurd hn (h3 v s w)
      | _ => rw [hn] at ho; simp [Node.ops] at ho
    · intro h k hn
      change c.nodes.getD id default = Node.wide h k at hn
      have hok := hc.nodes id hid hl
      simp only [nodeOk, hn] at hok
      split at hok
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
        have hh : h ∈ (c.nodes.getD id default).ops := by rw [hn]; simp [Node.ops]
        exact ⟨hok.1.1.1.1.1.2, sponge_val hc _ _ _ (lt_trans (hops h hh).1 hid) (hops h hh).2 hok.1.1.1.1.1.1⟩
      · cases hok
    · rw [hpub, hstr]; exact range_ok hc hid hl

end Compiled

end RecCircuit
