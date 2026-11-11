-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here.
import ZK.PcsStream

/-!
# The ideal challenges are elements of the stream

Run with the stream `es` (`interpS`), every tracked query of `phaseF` reads its answer's element back as the
challenge or out-of-domain coordinate it computes, so the challenges are fixed positions of the stream
(`phaseF_challenges`: `Φ mv es`); `phaseF` has `113` tracked queries at the membership circuit (`countQ_phaseF`).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open PcsQuotient.Transcript
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open FProg

variable {A α β : Type}

theorem countQ_ret (a : α) : CountQ (FProg.ret (A := A) a) 0 := rfl

theorem CountQ.congr {P : FProg A α} {a b : ℕ} (h : CountQ P a) (hab : a = b) : CountQ P b := hab ▸ h

theorem interpS_bind {P : FProg A α} {a : ℕ} (hP : CountQ P a) (f : α → FProg A β) (es : List E) :
    interpS (P.bind f) es = interpS P es >>= fun x ↦ interpS (f x) (es.drop a) := by
  induction P generalizing a es with
  | ret x =>
    simp only [CountQ] at hP
    subst hP
    simp [FProg.bind, interpS]
  | step m k ih =>
    simp only [FProg.bind, interpS, bind_assoc]
    exact congrArg _ (funext fun b ↦ ih b (hP b) _)
  | q x k ih =>
    obtain ⟨n', rfl, hk⟩ := hP
    simp only [FProg.bind, interpS, bind_assoc]
    refine congrArg _ (funext fun y ↦ ?_)
    rw [ih y (hk y)]
    simp

theorem mem_step {γ : Type} {m : StateT (Edges × A) ProbComp γ} {k : γ → FProg A α} {es : List E} {s : Edges × A}
    {o : α × (Edges × A)} (ho : o ∈ support ((interpS (.step m k) es).run s)) :
    ∃ p ∈ support (m.run s), o ∈ support ((interpS (k p.1) es).run p.2) := by
  rw [show (interpS (.step m k) es).run s = m.run s >>= fun p ↦ (interpS (k p.1) es).run p.2 from
    StateT.run_bind _ _ _] at ho
  exact mem_support_bind_iff _ _ _ |>.1 ho

theorem mem_bind {P : FProg A α} {a : ℕ} (hP : CountQ P a) {f : α → FProg A β} {es : List E} {s : Edges × A}
    {o : β × (Edges × A)} (ho : o ∈ support ((interpS (P.bind f) es).run s)) :
    ∃ p ∈ support ((interpS P es).run s), o ∈ support ((interpS (f p.1) (es.drop a)).run p.2) := by
  rw [interpS_bind hP, StateT.run_bind] at ho
  exact mem_support_bind_iff _ _ _ |>.1 ho

theorem mem_q {x : KeccakState} {k : KeccakState → FProg A α} {es : List E} {s : Edges × A}
    {o : α × (Edges × A)} (ho : o ∈ support ((interpS (.q x k) es).run s)) :
    ∃ w s', o ∈ support ((interpS (k (mk (es.headD 0) w)) es.tail).run s') := by
  rw [show (interpS (.q x k) es).run s = (idealPermE (es.headD 0) x).run s >>= fun p ↦ (interpS (k p.1) es.tail).run p.2
    from StateT.run_bind _ _ _] at ho
  obtain ⟨p, hp, ho⟩ := mem_support_bind_iff _ _ _ |>.1 ho
  simp only [idealPermE, StateT.run, support_map, Set.mem_image] at hp
  obtain ⟨w, -, rfl⟩ := hp
  exact ⟨w, _, ho⟩

/-! ### Keccak-256, the out-of-domain points, the chain -/

theorem countQ_absorbF : ∀ (b : ℕ) (st : KeccakState) (d : List UInt8), CountQ (absorbF (A := A) b st d) (b + 1)
  | 0, _, _ => ⟨0, rfl, fun _ ↦ rfl⟩
  | b + 1, _, _ => ⟨b + 1, rfl, fun _ ↦ countQ_absorbF b _ _⟩

theorem out_absorbF : ∀ (b : ℕ) (st : KeccakState) (d : List UInt8) (es : List E) (s : Edges × A)
    (o : KeccakState × (Edges × A)), o ∈ support ((interpS (absorbF b st d) es).run s) →
    ∃ w, o.1 = mk (es.getD b 0) w
  | 0, st, d, es, s, o, ho => by
    obtain ⟨w, s', ho⟩ := mem_q ho
    simp only [interpS, StateT.run_pure, support_pure, Set.mem_singleton_iff] at ho
    subst ho
    exact ⟨w, by cases es <;> rfl⟩
  | b + 1, st, d, es, s, o, ho => by
    obtain ⟨w, s', ho⟩ := mem_q ho
    obtain ⟨w', hw'⟩ := out_absorbF b _ _ _ _ _ ho
    exact ⟨w', by rw [hw']; cases es <;> simp⟩

theorem countQ_keccakF (data : List UInt8) : CountQ (keccakF (A := A) data) (data.length / rate + 1) :=
  ((countQ_absorbF _ _ _).bind fun _ ↦ countQ_ret _).congr (by omega)

theorem out_keccakF (data : List UInt8) (es : List E) (s : Edges × A) (o : Digest × (Edges × A))
    (ho : o ∈ support ((interpS (keccakF data) es).run s)) :
    ∃ w, o.1 = digestOf (mk (es.getD (data.length / rate) 0) w) := by
  obtain ⟨p, hp, ho⟩ := mem_bind (countQ_absorbF _ _ _) ho
  simp only [interpS, StateT.run_pure, support_pure, Set.mem_singleton_iff] at ho
  subst ho
  obtain ⟨w, hw⟩ := out_absorbF _ _ _ _ _ _ hp
  exact ⟨w, by rw [hw]⟩

theorem digestBytes_len (d : Digest) : (digestBytes d).length = 32 := by
  obtain ⟨⟨l⟩, hl⟩ := d
  match l, hl with
  | [_, _, _, _], _ => rfl

theorem scalarBytes_len (x : E) : (scalarBytes x).length = 32 := by
  simp [scalarBytes, beBytes, LeanVM.Rpm.wordBytes_len]

theorem loop_length (bs : ByteArray) : ∀ (k i : ℕ) (r : List UInt8), bs.size - i = k →
    (ByteArray.toList.loop bs i r).length = r.length + (bs.size - i)
  | 0, i, r, hk => by
    rw [ByteArray.toList.loop, ite_eq_right (by omega)]
    simp; omega
  | k + 1, i, r, hk => by
    rw [ByteArray.toList.loop, ite_eq_left (by omega), loop_length bs k (i + 1) _ (by omega)]
    simp; omega

theorem oodTag_length : oodTag.length = 11 := by
  have h : "leanPCS-ood".toUTF8.size = 11 := by
    simp only [String.toUTF8, String.size_toByteArray]
    decide
  unfold oodTag
  simp only [ByteArray.toList]
  rw [loop_length _ _ 0 [] rfl, h]
  rfl

theorem oodInput_len (n : ℕ) (r : Digest) (j : ℕ) : (oodInput n r j).length = 46 := by
  simp [oodInput, oodTag_length, digestBytes_len]

theorem countQ_listF {γ δ : Type} (f : γ → FProg A δ) (hf : ∀ b, CountQ (f b) 1) :
    ∀ l : List γ, CountQ (listF l f) l.length
  | [] => rfl
  | b :: l => ((hf b).bind fun _ ↦ (countQ_listF f hf l).bind fun _ ↦
      countQ_ret _).congr (by simp; omega)

theorem out_listF {γ : Type} (f : γ → FProg A E) (hf : ∀ b, CountQ (f b) 1)
    (hout : ∀ b es s (o : E × (Edges × A)), o ∈ support ((interpS (f b) es).run s) → o.1 = es.getD 0 0) :
    ∀ (l : List γ) (es : List E) (s : Edges × A) (o : List E × (Edges × A)),
      o ∈ support ((interpS (listF l f) es).run s) → o.1 = (List.range l.length).map fun j ↦ es.getD j 0
  | [], es, s, o, ho => by
    simp only [listF, interpS, StateT.run_pure, support_pure, Set.mem_singleton_iff] at ho
    subst ho; rfl
  | b :: l, es, s, o, ho => by
    obtain ⟨p, hp, ho⟩ := mem_bind (hf b) ho
    obtain ⟨p', hp', ho⟩ := mem_bind (countQ_listF f hf l) ho
    simp only [interpS, StateT.run_pure, support_pure, Set.mem_singleton_iff] at ho
    subst ho
    rw [hout b es s p hp, out_listF f hf hout l _ _ p' hp', List.length_cons, List.range_succ_eq_map]
    simp [List.getD_eq_getElem?_getD]

theorem countQ_oodF (n : ℕ) (r : Digest) : CountQ (oodF (A := A) n r) n := by
  refine (countQ_listF _ (fun j ↦ ((countQ_keccakF _).bind fun _ ↦
    countQ_ret _).congr ?_) _).congr (by simp)
  rw [oodInput_len]; rfl

theorem out_oodF (n : ℕ) (r : Digest) (es : List E) (s : Edges × A) (o : List E × (Edges × A))
    (ho : o ∈ support ((interpS (oodF n r) es).run s)) : o.1 = (List.range n).map fun j ↦ es.getD j 0 := by
  have := out_listF _ (fun j ↦ ((countQ_keccakF (A := A) (oodInput n r j)).bind fun _ ↦
    countQ_ret _).congr (by rw [oodInput_len]; rfl)) ?_ _ es s o ho
  · simpa using this
  · intro j es' s' o' ho'
    obtain ⟨p, hp, ho'⟩ := mem_bind (countQ_keccakF _) ho'
    simp only [interpS, StateT.run_pure, support_pure, Set.mem_singleton_iff] at ho'
    subst ho'
    obtain ⟨w, hw⟩ := out_keccakF _ _ _ _ hp
    rw [hw, elementOf_eq, oodInput_len, laneE_digestOf_mk]
    rfl

/-- The length of a chain's message. -/
theorem chainMsg_len (c : Chain) :
    (digestBytes c.state ++ c.pending.flatMap scalarBytes).length = 32 + 32 * c.pending.length := by
  simp only [List.length_append, digestBytes_len, List.length_flatMap, scalarBytes_len]
  simp [Nat.mul_comm]

theorem countQ_squeezeF (c : Chain) : CountQ (squeezeF (A := A) c) ((32 + 32 * c.pending.length) / rate + 1) :=
  ((countQ_keccakF _).bind fun _ ↦ countQ_ret _).congr
    (by rw [chainMsg_len])

theorem out_squeezeF (c : Chain) (es : List E) (s : Edges × A) (o : (E × Chain) × (Edges × A))
    (ho : o ∈ support ((interpS (squeezeF c) es).run s)) :
    o.1.1 = es.getD ((32 + 32 * c.pending.length) / rate) 0 ∧ o.1.2.pending = [] := by
  obtain ⟨p, hp, ho⟩ := mem_bind (countQ_keccakF _) ho
  simp only [interpS, StateT.run_pure, support_pure, Set.mem_singleton_iff] at ho
  subst ho
  obtain ⟨w, hw⟩ := out_keccakF _ _ _ _ hp
  refine ⟨?_, rfl⟩
  simp only [hw, challengeOf_eq, laneE_digestOf_mk, chainMsg_len]

/-! ### The phase -/

/-- **The positions of the challenges in the stream**: `W`'s point, `α, β, γ`, the parts' points, `t` (the last
of its three calls), `ρ` (the last of its two). -/
def Φ (mv : ℕ) (es : List E) : Challenges :=
  ⟨(List.range (mv + 1)).map fun j ↦ es.getD j 0, (List.range (mv + 3)).map fun j ↦ es.getD (mv + 4 + j) 0,
    (List.range (mv + 4)).map fun j ↦ es.getD (2 * mv + 7 + j) 0,
    (List.range (mv + 1)).map fun j ↦ es.getD (3 * mv + 11 + j) 0,
    es.getD (mv + 1) 0, es.getD (mv + 2) 0, es.getD (mv + 3) 0, es.getD (4 * mv + 14) 0, es.getD (4 * mv + 16) 0⟩

theorem countQ_phaseF (circuit : Circuit) (stmt : Statement) :
    CountQ (phaseF (A := A) circuit stmt) (4 * cellVars circuit.logRows + 17) := by
  simp only [phaseF]
  intro p1 rW
  refine CountQ.congr (CountQ.bind (b := 3 * cellVars circuit.logRows + 16) (countQ_oodF _ _) fun zW ↦ ?_) (by ring)
  intro d oW
  refine CountQ.congr (CountQ.bind (b := 3 * cellVars circuit.logRows + 15) ((countQ_squeezeF _).congr (b := 1)
    (by simp [Chain.absorbCommitment, Chain.absorb, rate])) fun pα ↦ ?_) (by ring)
  refine CountQ.congr (CountQ.bind (b := 3 * cellVars circuit.logRows + 14) ((countQ_squeezeF _).congr (b := 1)
    (by simp [rate])) fun pβ ↦ ?_) (by ring)
  refine CountQ.congr (CountQ.bind (b := 3 * cellVars circuit.logRows + 13) ((countQ_squeezeF _).congr (b := 1)
    (by simp [rate])) fun pγ ↦ ?_) (by ring)
  intro rH
  refine CountQ.congr (CountQ.bind (b := 2 * cellVars circuit.logRows + 10) (countQ_oodF _ _) fun zH ↦ ?_) (by ring)
  intro rQ
  refine CountQ.congr (CountQ.bind (b := cellVars circuit.logRows + 6) (countQ_oodF _ _) fun zQ ↦ ?_) (by ring)
  intro rG
  refine CountQ.congr (CountQ.bind (b := 5) (countQ_oodF _ _) fun zG ↦ ?_) (by ring)
  intro oQ oG oH
  refine CountQ.congr (CountQ.bind (b := 2) ((countQ_squeezeF _).congr (b := 3)
    (by simp [Chain.absorbCommitment, Chain.absorb, rate])) fun pt ↦ ?_) rfl
  intro a1 a2 a3 a0
  refine CountQ.congr (CountQ.bind (b := 0) ((countQ_squeezeF _).congr (b := 2)
    (by simp [Chain.absorb, rate])) fun pρ ↦ ?_) rfl
  intro vq vg
  rfl

theorem getD_drop (l : List E) (a k : ℕ) : (l.drop a).getD k 0 = l.getD (a + k) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **The ideal challenges are the stream's elements at `Φ`.** -/
theorem phaseF_challenges (circuit : Circuit) (stmt : Statement) (es : List E) (s : Edges × A)
    (o : (Challenges × PhaseOut) × (Edges × A)) (ho : o ∈ support ((interpS (phaseF circuit stmt) es).run s)) :
    o.1.1 = Φ (cellVars circuit.logRows) es := by
  simp only [phaseF] at ho
  obtain ⟨p1, -, ho⟩ := mem_step ho
  obtain ⟨p2, -, ho⟩ := mem_step ho
  obtain ⟨p3, h3, ho⟩ := mem_bind (countQ_oodF _ _) ho
  obtain ⟨p4, -, ho⟩ := mem_step ho
  obtain ⟨p5, -, ho⟩ := mem_step ho
  obtain ⟨p6, h6, ho⟩ := mem_bind (countQ_squeezeF _) ho
  obtain ⟨p7, h7, ho⟩ := mem_bind (countQ_squeezeF _) ho
  obtain ⟨p8, h8, ho⟩ := mem_bind (countQ_squeezeF _) ho
  obtain ⟨p9, -, ho⟩ := mem_step ho
  obtain ⟨p10, h10, ho⟩ := mem_bind (countQ_oodF _ _) ho
  obtain ⟨p11, -, ho⟩ := mem_step ho
  obtain ⟨p12, h12, ho⟩ := mem_bind (countQ_oodF _ _) ho
  obtain ⟨p13, -, ho⟩ := mem_step ho
  obtain ⟨p14, h14, ho⟩ := mem_bind (countQ_oodF _ _) ho
  obtain ⟨p15, -, ho⟩ := mem_step ho
  obtain ⟨p16, -, ho⟩ := mem_step ho
  obtain ⟨p17, -, ho⟩ := mem_step ho
  obtain ⟨p18, h18, ho⟩ := mem_bind (countQ_squeezeF _) ho
  obtain ⟨p19, -, ho⟩ := mem_step ho
  obtain ⟨p20, -, ho⟩ := mem_step ho
  obtain ⟨p21, -, ho⟩ := mem_step ho
  obtain ⟨p22, -, ho⟩ := mem_step ho
  obtain ⟨p23, h23, ho⟩ := mem_bind (countQ_squeezeF _) ho
  obtain ⟨p24, -, ho⟩ := mem_step ho
  obtain ⟨p25, -, ho⟩ := mem_step ho
  simp only [interpS, StateT.run_pure, support_pure, Set.mem_singleton_iff] at ho
  subst ho
  have e3 := out_oodF _ _ _ _ _ h3
  have e6 := (out_squeezeF _ _ _ _ h6).1
  have e7 := (out_squeezeF _ _ _ _ h7).1
  have e8 := (out_squeezeF _ _ _ _ h8).1
  have e10 := out_oodF _ _ _ _ _ h10
  have e12 := out_oodF _ _ _ _ _ h12
  have e14 := out_oodF _ _ _ _ _ h14
  have e18 := (out_squeezeF _ _ _ _ h18).1
  have e23 := (out_squeezeF _ _ _ _ h23).1
  simp only [Chain.absorbCommitment, Chain.absorb, List.length_append, List.length_nil, List.length_cons,
    List.foldl_cons, List.foldl_nil, Vector.toList_mk, rate] at e6 e7 e8 e18 e23
  simp only [e3, e6, e7, e8, e10, e12, e14, e18, e23, Φ, getD_drop, List.drop_drop, rate]
  simp only [Chain.absorbCommitment, Chain.absorb, List.length_append, List.length_nil, List.length_cons,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  ring_nf

end PcsQuotient.EndToEnd
