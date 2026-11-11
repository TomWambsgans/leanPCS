-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls
-- `KeccakCalls`, their lazy random oracles, `common`'s byte reading of a digest (`digestEquiv`); VCVio's uniform
-- samples (`SampleableType.uniformSample_prod_eq_bind`, `map_uniformSample_evalDistEq_of_bijective`,
-- `evalDist_uniformSample_prod_bind_fst`); and `formal/EndToEnd/Completeness/E2ECompleteness/Chain.lean` (`ro`,
-- `Cache`).
import UniKeccakComplete.K.Rec4Rate
import E2ECompleteness.Chain

/-!
# The rate's random oracle as five digests (`romW_evalDistEq`)

The transfer (`Rec4Rate.lean`) leaves π1-rec4's honest computation `G` against two random oracles, `H` answering
136 uniform bytes (`roW`). The probability layer of the main line and π1-rec3 is written for the two-call random
oracles of leanerVM's `KeccakCalls` (`E2ECompleteness.ro`, `H` answering 32 bytes). **`romW_evalDistEq`**: if every
hash input of `G` is short (`HashOKW Short G`, fewer than `2^60` bytes), `G` against `roW` has the outputs of
`simulateQ tauW G` against `ro`, where `tauW` answers a rate query on `m` by five digest queries (`rate5`), on `m`
and on its four **tail inputs** `extIn i m = m ++ 0^(i · 2^60)` (`i = 1 … 4`: long, pairwise distinct, never a
short input), the rate being the first digest's 32 bytes, the next three's, and 8 bytes of the fifth (`mkRate`; the
first digest is the rate's digest, `digestOfRate_mkRate`).

The proof relates the caches query by query (`projT`: a short input's rate read off its five digests; `InvT`: a
cached short input has its four tails cached, a cached long input is a tail of a cached short input): a fresh rate
query is five fresh digest queries, whose `mkRate` is uniform (`mkRate_uniform`: `mkRate` is the first projection of
a bijection `digest5Equiv` of five digests onto a rate and 24 spare bytes).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open E2ECompleteness (ro Cache)
open scoped ENNReal

set_option autoImplicit false

namespace UniKeccakComplete.Rec4

/-! ## Hash inputs of a computation over π1-rec4's calls -/

/-- A query is allowed when it is a permutation call, or a hash of an input satisfying `P`. -/
def hashOKW (P : Bytes → Prop) : (Bytes ⊕ KeccakState) → Unit → Prop
  | .inl x, _ => P x
  | .inr _, _ => True

/-- **Every hash query of `oa` satisfies `P`**, along every path. -/
def HashOKW (P : Bytes → Prop) {α : Type} (oa : OracleComp KeccakCallsW α) : Prop :=
  oa.IsQueryBound () (hashOKW P) (fun _ _ ↦ ())

theorem HashOKW.pure (P : Bytes → Prop) {α : Type} (a : α) :
    HashOKW P (pure a : OracleComp KeccakCallsW α) := trivial

theorem HashOKW.bind {P : Bytes → Prop} {α β : Type} {oa : OracleComp KeccakCallsW α}
    {f : α → OracleComp KeccakCallsW β} (h₁ : HashOKW P oa) (h₂ : ∀ a, HashOKW P (f a)) :
    HashOKW P (oa >>= f) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using h₂ a
  | query_bind t k ih =>
    rw [bind_assoc]
    exact (isQueryBound_query_bind_iff _ _ _ _ _).2
      ⟨((isQueryBound_query_bind_iff _ _ _ _ _).1 h₁).1,
        fun u ↦ ih u (((isQueryBound_query_bind_iff _ _ _ _ _).1 h₁).2 u)⟩

theorem HashOKW.map {P : Bytes → Prop} {α β : Type} {oa : OracleComp KeccakCallsW α} (f : α → β)
    (h : HashOKW P oa) : HashOKW P (f <$> oa) :=
  (isQueryBound_map_iff oa f _ _ _).2 h

/-- A weaker predicate on the hashed inputs. -/
theorem HashOKW.mono {P Q : Bytes → Prop} (hPQ : ∀ m, P m → Q m) {α : Type} {oa : OracleComp KeccakCallsW α}
    (h : HashOKW P oa) : HashOKW Q oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).1 h
    refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨?_, fun u ↦ ih u (hk u)⟩
    rcases t with x | s
    · exact hPQ x ht
    · trivial

theorem hashOKW_callRate {P : Bytes → Prop} {x : Bytes} (hx : P x) : HashOKW P (callRate x) :=
  (isQueryBound_query_iff (spec := KeccakCallsW) (.inl x) () _ _).2 hx

theorem hashOKW_callFW (P : Bytes → Prop) (s : KeccakState) : HashOKW P (callFW s) :=
  (isQueryBound_query_iff (spec := KeccakCallsW) (.inr s) () _ _).2 trivial

/-- **A block count bounds every hash input's length**: a hash of `n` bytes costs `⌊n / 136⌋ + 1` blocks. -/
theorem hashOKW_of_cost {α : Type} {X : OracleComp KeccakCallsW α} {N : ℕ}
    (h : Common.QueryCostAtMost X hashBlocksW N) : HashOKW (fun m ↦ m.length / 136 + 1 ≤ N) X := by
  induction X using OracleComp.inductionOn generalizing N with
  | pure a => trivial
  | query_bind t k ih =>
    rw [Common.isWeightBound_query_bind_iff] at h
    refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨?_, fun u ↦ ?_⟩
    · rcases t with x | s
      · exact h.1
      · trivial
    · exact HashOKW.mono (fun m hm ↦ by omega) (ih u (h.2 u))

/-! ## Short inputs and their tails -/

/-- The bound of a short input's length: `2^60` bytes. -/
def lenB : ℕ := 1152921504606846976

theorem lenB_eq : lenB = 2 ^ 60 := by norm_num [lenB]

/-- **A short input**: fewer than `2^60` bytes. -/
def Short (m : Bytes) : Prop := m.length < lenB

instance : DecidablePred Short := fun m ↦ inferInstanceAs (Decidable (m.length < lenB))

/-- **Tail input `i`** of `m` (`i = 1 … 4`): `m` and `i · 2^60` zero bytes. -/
def extIn (i : ℕ) (m : Bytes) : Bytes := m ++ List.replicate (i * lenB) 0

theorem length_extIn (i : ℕ) (m : Bytes) : (extIn i m).length = m.length + i * lenB := by
  simp [extIn]

theorem extIn_not_short {i : ℕ} (hi : 1 ≤ i) (m : Bytes) : ¬ Short (extIn i m) := by
  unfold Short
  rw [length_extIn]
  unfold lenB
  omega

theorem extIn_ne_short {i : ℕ} (hi : 1 ≤ i) (m m' : Bytes) (hm' : Short m') : extIn i m ≠ m' := by
  rintro rfl
  exact extIn_not_short hi m hm'

/-- **Tails are injective**: on short inputs, tail `i` of `m` is tail `j` of `m'` only if `i = j` and `m = m'`. -/
theorem extIn_inj {i j : ℕ} {m m' : Bytes} (hm : Short m) (hm' : Short m') (h : extIn i m = extIn j m') :
    i = j ∧ m = m' := by
  have hl := congrArg List.length h
  rw [length_extIn, length_extIn] at hl
  unfold Short lenB at hm hm'
  unfold lenB at hl
  have hij : i = j := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have : i * 1152921504606846976 + 1152921504606846976 ≤ j * 1152921504606846976 := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hlt
      omega
    · have : j * 1152921504606846976 + 1152921504606846976 ≤ i * 1152921504606846976 := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hlt
      omega
  subst hij
  refine ⟨rfl, ?_⟩
  exact (List.append_inj h (by omega)).1

/-- A tail is none of the short input's other tails. -/
theorem extIn_ne_extIn {i j : ℕ} (hij : i ≠ j) (m : Bytes) (hm : Short m) : extIn i m ≠ extIn j m :=
  fun h ↦ hij (extIn_inj hm hm h).1

/-! ## The rate of five digests -/

/-- The 160 bytes of five 32-byte vectors. -/
def cat5 (x : Common.DigestBytes × Common.DigestBytes × Common.DigestBytes × Common.DigestBytes ×
    Common.DigestBytes) : List UInt8 :=
  x.1.toList ++ x.2.1.toList ++ x.2.2.1.toList ++ x.2.2.2.1.toList ++ x.2.2.2.2.toList

theorem length_cat5 (x : Common.DigestBytes × Common.DigestBytes × Common.DigestBytes × Common.DigestBytes ×
    Common.DigestBytes) : (cat5 x).length = 160 := by
  simp [cat5]

/-- A list of `n` bytes as a vector. -/
def vecOf (n : ℕ) (l : List UInt8) (h : l.length = n) : Vector UInt8 n := ⟨l.toArray, by simpa using h⟩

@[simp] theorem toList_vecOf (n : ℕ) (l : List UInt8) (h : l.length = n) : (vecOf n l h).toList = l := rfl

/-- Five 32-byte vectors as a rate and 24 spare bytes: the rate is the first four and 8 bytes of the fifth. -/
def bytes5Equiv :
    Common.DigestBytes × Common.DigestBytes × Common.DigestBytes × Common.DigestBytes × Common.DigestBytes ≃
      RateB × Vector UInt8 24 where
  toFun x := (vecOf 136 ((cat5 x).take 136) (by simp [length_cat5]),
    vecOf 24 ((cat5 x).drop 136) (by simp [length_cat5]))
  invFun y :=
    let l := y.1.toList ++ y.2.toList
    (vecOf 32 (l.take 32) (by simp [l]), vecOf 32 ((l.drop 32).take 32) (by simp [l]),
      vecOf 32 ((l.drop 64).take 32) (by simp [l]), vecOf 32 ((l.drop 96).take 32) (by simp [l]),
      vecOf 32 (l.drop 128) (by simp [l]))
  left_inv x := by
    obtain ⟨a, b, c, d, e⟩ := x
    have hl : ((cat5 (a, b, c, d, e)).take 136 ++ (cat5 (a, b, c, d, e)).drop 136) =
        a.toList ++ (b.toList ++ (c.toList ++ (d.toList ++ e.toList))) := by
      rw [List.take_append_drop]; simp [cat5]
    simp only [toList_vecOf, hl]
    refine Prod.ext (Vector.toList_inj.mp ?_) (Prod.ext (Vector.toList_inj.mp ?_)
      (Prod.ext (Vector.toList_inj.mp ?_) (Prod.ext (Vector.toList_inj.mp ?_) (Vector.toList_inj.mp ?_)))) <;>
      simp only [toList_vecOf]
    · exact List.take_left' (by simp)
    · rw [List.drop_left' (by simp)]; exact List.take_left' (by simp)
    · rw [show (64 : ℕ) = 32 + 32 from rfl, ← List.drop_drop, List.drop_left' (by simp),
        List.drop_left' (by simp)]
      exact List.take_left' (by simp)
    · rw [show (96 : ℕ) = 32 + 32 + 32 from rfl, ← List.drop_drop, ← List.drop_drop, List.drop_left' (by simp),
        List.drop_left' (by simp), List.drop_left' (by simp)]
      exact List.take_left' (by simp)
    · rw [show (128 : ℕ) = 32 + 32 + 32 + 32 from rfl, ← List.drop_drop, ← List.drop_drop, ← List.drop_drop,
        List.drop_left' (by simp), List.drop_left' (by simp), List.drop_left' (by simp), List.drop_left' (by simp)]
  right_inv y := by
    obtain ⟨r, v⟩ := y
    have hc : cat5 (vecOf 32 ((r.toList ++ v.toList).take 32) (by simp),
        vecOf 32 (((r.toList ++ v.toList).drop 32).take 32) (by simp),
        vecOf 32 (((r.toList ++ v.toList).drop 64).take 32) (by simp),
        vecOf 32 (((r.toList ++ v.toList).drop 96).take 32) (by simp),
        vecOf 32 ((r.toList ++ v.toList).drop 128) (by simp)) = r.toList ++ v.toList := by
      simp only [cat5, toList_vecOf]
      generalize r.toList ++ v.toList = l
      rw [List.append_assoc, List.append_assoc, List.append_assoc]
      conv_rhs => rw [← List.take_append_drop 32 l]
      congr 1
      conv_rhs => rw [← List.take_append_drop 32 (l.drop 32)]
      rw [List.drop_drop]
      congr 1
      conv_rhs => rw [← List.take_append_drop 32 (l.drop 64)]
      rw [List.drop_drop]
      congr 1
      conv_rhs => rw [← List.take_append_drop 32 (l.drop 96)]
      rw [List.drop_drop]
    refine Prod.ext (Vector.toList_inj.mp ?_) (Vector.toList_inj.mp ?_)
    · show ((cat5 _).take 136) = r.toList
      rw [hc]; exact List.take_left' (by simp)
    · show ((cat5 _).drop 136) = v.toList
      rw [hc]; exact List.drop_left' (by simp)

/-- **Five digests as a rate and 24 spare bytes.** -/
def digest5Equiv : Digest × Digest × Digest × Digest × Digest ≃ RateB × Vector UInt8 24 :=
  (Equiv.prodCongr digestEquiv (Equiv.prodCongr digestEquiv (Equiv.prodCongr digestEquiv
    (Equiv.prodCongr digestEquiv digestEquiv)))).trans bytes5Equiv

/-- **The rate of five digests**: the first four's bytes and 8 bytes of the fifth. -/
def mkRate (d t1 t2 t3 t4 : Digest) : RateB := (digest5Equiv (d, t1, t2, t3, t4)).1

/-- **The rate's bytes**: the first four digests' bytes, then the first 8 of the fifth's. -/
theorem mkRate_toList (d t1 t2 t3 t4 : Digest) :
    (mkRate d t1 t2 t3 t4).toList =
      digestBytes d ++ digestBytes t1 ++ digestBytes t2 ++ digestBytes t3 ++ (digestBytes t4).take 8 := by
  have hd : ∀ x : Digest, (Digest.toRpm x).toList = digestBytes x := fun x ↦ toList_digestToRpm x
  simp only [mkRate, digest5Equiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, digestEquiv_apply,
    bytes5Equiv, Equiv.coe_fn_mk, toList_vecOf, cat5, hd]
  have hl : (digestBytes d ++ digestBytes t1 ++ digestBytes t2 ++ digestBytes t3).length = 128 := by
    simp [digestBytes_length]
  rw [show (136 : ℕ) = (digestBytes d ++ digestBytes t1 ++ digestBytes t2 ++ digestBytes t3).length + 8 by
    rw [hl], List.take_length_add_append]

theorem mkRate_getElem_lt (d t1 t2 t3 t4 : Digest) (k : ℕ) (hk : k < 32) :
    (mkRate d t1 t2 t3 t4)[k] = (Digest.toRpm d)[k] := by
  rw [← Vector.getElem_toList (by rw [Vector.length_toList]; omega),
    ← Vector.getElem_toList (by rw [Vector.length_toList]; omega)]
  simp only [mkRate_toList, toList_digestToRpm, List.append_assoc]
  rw [List.getElem_append_left (by rw [digestBytes_length]; omega)]
  rfl

/-- **The rate's digest is the first digest.** -/
theorem digestOfRate_mkRate (d t1 t2 t3 t4 : Digest) : digestOfRate (mkRate d t1 t2 t3 t4) = d := by
  have e : (Vector.ofFn fun i : Fin 32 ↦ (mkRate d t1 t2 t3 t4)[i.val]) = Digest.toRpm d :=
    Vector.ext fun k hk ↦ by rw [Vector.getElem_ofFn, mkRate_getElem_lt _ _ _ _ _ k hk]
  rw [digestOfRate, e, digestOfRpm_toRpm]

/-- **Five uniform digests give a uniform rate.** -/
theorem mkRate_uniform :
    (do
      let d ← $ᵗ Digest
      let t1 ← $ᵗ Digest
      let t2 ← $ᵗ Digest
      let t3 ← $ᵗ Digest
      let t4 ← $ᵗ Digest
      pure (mkRate d t1 t2 t3 t4) : ProbComp RateB) =ᵈ ($ᵗ RateB : ProbComp RateB) := by
  have e : (do
      let d ← $ᵗ Digest
      let t1 ← $ᵗ Digest
      let t2 ← $ᵗ Digest
      let t3 ← $ᵗ Digest
      let t4 ← $ᵗ Digest
      pure (mkRate d t1 t2 t3 t4) : ProbComp RateB) =
      (fun p : RateB × Vector UInt8 24 ↦ p.1) <$>
        (digest5Equiv <$> ($ᵗ (Digest × Digest × Digest × Digest × Digest))) := by
    simp only [SampleableType.uniformSample_prod_eq_bind, bind_assoc, pure_bind, map_bind, map_pure]
    rfl
  rw [e]
  refine (EvalDistEq.map (SampleableType.map_uniformSample_evalDistEq_of_bijective digest5Equiv.bijective) _).trans ?_
  let : MeasurableSpace RateB := ⊤
  refine EvalDistEq.of_evalDist_eq ?_
  have h := SampleableType.evalDist_uniformSample_prod_bind_fst (α := RateB) (β := Vector UInt8 24)
    (fun a ↦ (pure a : ProbComp RateB))
  simpa [map_eq_bind_pure_comp] using h

/-! ## The rate answered by five digest queries -/

/-- **A rate query answered by five digest queries**: on `m` and on its four tails. -/
def rate5 (m : Bytes) : OracleComp KeccakCalls RateB := do
  let d ← callKeccak256 m
  let t1 ← callKeccak256 (extIn 1 m)
  let t2 ← callKeccak256 (extIn 2 m)
  let t3 ← callKeccak256 (extIn 3 m)
  let t4 ← callKeccak256 (extIn 4 m)
  pure (mkRate d t1 t2 t3 t4)

/-- **π1-rec4's calls answered by leanerVM's two calls**: a rate by five digests, the permutation by itself. -/
def tauW : QueryImpl KeccakCallsW (OracleComp KeccakCalls)
  | .inl m => rate5 m
  | .inr s => callKeccakF1600 s

/-! ## The caches -/

/-- **The two caches' invariant**: a cached short input has its four tails cached; a cached long input is a tail of
a cached short input. -/
def InvT (c : Cache) : Prop :=
  ∀ x, c (.inl x) ≠ none →
    (Short x ∧ ∀ i, 1 ≤ i → i ≤ 4 → c (.inl (extIn i x)) ≠ none) ∨
      ∃ i m, 1 ≤ i ∧ i ≤ 4 ∧ Short m ∧ x = extIn i m ∧ c (.inl m) ≠ none

/-- **The rate cache of a digest cache**: a short input's rate from its five digests, the permutation's answers as
they are. -/
def projT (c : Cache) : KeccakCallsW.QueryCache :=
  QueryCache.ofFn fun
    | .inl m => if Short m then
        (c (.inl m)).bind fun d ↦ (c (.inl (extIn 1 m))).bind fun t1 ↦ (c (.inl (extIn 2 m))).bind fun t2 ↦
          (c (.inl (extIn 3 m))).bind fun t3 ↦ (c (.inl (extIn 4 m))).map fun t4 ↦ mkRate d t1 t2 t3 t4
      else none
    | .inr s => c (.inr s)

theorem projT_inr (c : Cache) (s : KeccakState) : projT c (.inr s) = c (.inr s) := rfl

theorem projT_inl (c : Cache) (m : Bytes) : projT c (.inl m) = if Short m then
    (c (.inl m)).bind fun d ↦ (c (.inl (extIn 1 m))).bind fun t1 ↦ (c (.inl (extIn 2 m))).bind fun t2 ↦
      (c (.inl (extIn 3 m))).bind fun t3 ↦ (c (.inl (extIn 4 m))).map fun t4 ↦ mkRate d t1 t2 t3 t4
    else none := rfl

theorem projT_empty : projT ∅ = ∅ := by
  refine QueryCache.ext fun t ↦ ?_
  rcases t with m | s
  · rw [projT_inl]; split <;> rfl
  · rfl

theorem invT_empty : InvT ∅ := fun _ h ↦ absurd rfl h

/-- Caching the permutation's answer. -/
theorem projT_cacheQuery_inr (c : Cache) (s v : KeccakState) :
    projT (c.cacheQuery (.inr s) v) = (projT c).cacheQuery (.inr s) v := by
  refine QueryCache.ext fun t ↦ ?_
  rcases t with m | s'
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp), projT_inl, projT_inl]
    simp only [QueryCache.cacheQuery_of_ne _ _ (show (Sum.inl _ : Bytes ⊕ KeccakState) ≠ .inr s by simp)]
  · by_cases h : s' = s
    · subst h
      rw [projT_inr, QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
    · rw [projT_inr, QueryCache.cacheQuery_of_ne _ _ (by simpa using h),
        QueryCache.cacheQuery_of_ne _ _ (by simpa using h), projT_inr]

theorem invT_cacheQuery_inr {c : Cache} (h : InvT c) (s v : KeccakState) : InvT (c.cacheQuery (.inr s) v) := by
  intro x hx
  have e : ∀ y : Bytes, (c.cacheQuery (.inr s) v) (.inl y) = c (.inl y) := fun y ↦
    QueryCache.cacheQuery_of_ne _ _ (by simp)
  rw [e] at hx
  rcases h x hx with ⟨h1, h2⟩ | ⟨i, m, h1, h2, h3, h4, h5⟩
  · exact Or.inl ⟨h1, fun i hi hi' ↦ by rw [e]; exact h2 i hi hi'⟩
  · exact Or.inr ⟨i, m, h1, h2, h3, h4, by rw [e]; exact h5⟩

/-- The five cached digests of a fresh short input. -/
def cache5 (c : Cache) (m : Bytes) (d t1 t2 t3 t4 : Digest) : Cache :=
  ((((c.cacheQuery (.inl m) d).cacheQuery (.inl (extIn 1 m)) t1).cacheQuery (.inl (extIn 2 m)) t2).cacheQuery
    (.inl (extIn 3 m)) t3).cacheQuery (.inl (extIn 4 m)) t4

/-- A short input's five inputs are pairwise distinct. -/
structure Distinct5 (m : Bytes) : Prop where
  h01 : m ≠ extIn 1 m
  h02 : m ≠ extIn 2 m
  h03 : m ≠ extIn 3 m
  h04 : m ≠ extIn 4 m
  h12 : extIn 1 m ≠ extIn 2 m
  h13 : extIn 1 m ≠ extIn 3 m
  h14 : extIn 1 m ≠ extIn 4 m
  h23 : extIn 2 m ≠ extIn 3 m
  h24 : extIn 2 m ≠ extIn 4 m
  h34 : extIn 3 m ≠ extIn 4 m

theorem distinct5 {m : Bytes} (hm : Short m) : Distinct5 m where
  h01 := fun h ↦ extIn_ne_short (by norm_num) m m hm h.symm
  h02 := fun h ↦ extIn_ne_short (by norm_num) m m hm h.symm
  h03 := fun h ↦ extIn_ne_short (by norm_num) m m hm h.symm
  h04 := fun h ↦ extIn_ne_short (by norm_num) m m hm h.symm
  h12 := extIn_ne_extIn (by norm_num) m hm
  h13 := extIn_ne_extIn (by norm_num) m hm
  h14 := extIn_ne_extIn (by norm_num) m hm
  h23 := extIn_ne_extIn (by norm_num) m hm
  h24 := extIn_ne_extIn (by norm_num) m hm
  h34 := extIn_ne_extIn (by norm_num) m hm

theorem ne_inl {x y : Bytes} (h : x ≠ y) : (Sum.inl x : Bytes ⊕ KeccakState) ≠ .inl y := by simpa using h

theorem cache5_self {m : Bytes} (hm : Short m) (c : Cache) (d t1 t2 t3 t4 : Digest) :
    cache5 c m d t1 t2 t3 t4 (.inl m) = some d := by
  have h := distinct5 hm
  unfold cache5
  rw [QueryCache.cacheQuery_of_ne _ _ (ne_inl h.h04), QueryCache.cacheQuery_of_ne _ _ (ne_inl h.h03),
    QueryCache.cacheQuery_of_ne _ _ (ne_inl h.h02), QueryCache.cacheQuery_of_ne _ _ (ne_inl h.h01),
    QueryCache.cacheQuery_self]

theorem cache5_e1 {m : Bytes} (hm : Short m) (c : Cache) (d t1 t2 t3 t4 : Digest) :
    cache5 c m d t1 t2 t3 t4 (.inl (extIn 1 m)) = some t1 := by
  have h := distinct5 hm
  unfold cache5
  rw [QueryCache.cacheQuery_of_ne _ _ (ne_inl h.h14), QueryCache.cacheQuery_of_ne _ _ (ne_inl h.h13),
    QueryCache.cacheQuery_of_ne _ _ (ne_inl h.h12), QueryCache.cacheQuery_self]

theorem cache5_e2 {m : Bytes} (hm : Short m) (c : Cache) (d t1 t2 t3 t4 : Digest) :
    cache5 c m d t1 t2 t3 t4 (.inl (extIn 2 m)) = some t2 := by
  have h := distinct5 hm
  unfold cache5
  rw [QueryCache.cacheQuery_of_ne _ _ (ne_inl h.h24), QueryCache.cacheQuery_of_ne _ _ (ne_inl h.h23),
    QueryCache.cacheQuery_self]

theorem cache5_e3 {m : Bytes} (hm : Short m) (c : Cache) (d t1 t2 t3 t4 : Digest) :
    cache5 c m d t1 t2 t3 t4 (.inl (extIn 3 m)) = some t3 := by
  have h := distinct5 hm
  unfold cache5
  rw [QueryCache.cacheQuery_of_ne _ _ (ne_inl h.h34), QueryCache.cacheQuery_self]

theorem cache5_e4 (m : Bytes) (c : Cache) (d t1 t2 t3 t4 : Digest) :
    cache5 c m d t1 t2 t3 t4 (.inl (extIn 4 m)) = some t4 := by
  unfold cache5
  rw [QueryCache.cacheQuery_self]

theorem cache5_other (c : Cache) (m : Bytes) (d t1 t2 t3 t4 : Digest) (y : Bytes) (h0 : y ≠ m)
    (h1 : y ≠ extIn 1 m) (h2 : y ≠ extIn 2 m) (h3 : y ≠ extIn 3 m) (h4 : y ≠ extIn 4 m) :
    cache5 c m d t1 t2 t3 t4 (.inl y) = c (.inl y) := by
  unfold cache5
  rw [QueryCache.cacheQuery_of_ne _ _ (ne_inl h4), QueryCache.cacheQuery_of_ne _ _ (ne_inl h3),
    QueryCache.cacheQuery_of_ne _ _ (ne_inl h2), QueryCache.cacheQuery_of_ne _ _ (ne_inl h1),
    QueryCache.cacheQuery_of_ne _ _ (ne_inl h0)]

theorem cache5_inr (c : Cache) (m : Bytes) (d t1 t2 t3 t4 : Digest) (s : KeccakState) :
    cache5 c m d t1 t2 t3 t4 (.inr s) = c (.inr s) := by
  have e : ∀ x : Bytes, (Sum.inr s : Bytes ⊕ KeccakState) ≠ .inl x := fun _ ↦ by simp
  unfold cache5
  rw [QueryCache.cacheQuery_of_ne _ _ (e _), QueryCache.cacheQuery_of_ne _ _ (e _),
    QueryCache.cacheQuery_of_ne _ _ (e _), QueryCache.cacheQuery_of_ne _ _ (e _),
    QueryCache.cacheQuery_of_ne _ _ (e _)]

/-- **Caching the five digests of a short input caches its rate.** -/
theorem projT_cache5 {m : Bytes} (hm : Short m) (c : Cache) (d t1 t2 t3 t4 : Digest) :
    projT (cache5 c m d t1 t2 t3 t4) = (projT c).cacheQuery (.inl m) (mkRate d t1 t2 t3 t4) := by
  refine QueryCache.ext fun t ↦ ?_
  rcases t with m' | s
  · by_cases hmm : m' = m
    · rw [hmm, QueryCache.cacheQuery_self, projT_inl, ite_eq_left_of_eq_true _ _ (eq_true hm), cache5_self hm, cache5_e1 hm, cache5_e2 hm,
        cache5_e3 hm, cache5_e4]
      rfl
    · rw [QueryCache.cacheQuery_of_ne _ _ (ne_inl hmm), projT_inl, projT_inl]
      by_cases hs : Short m'
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hs), ite_eq_left_of_eq_true _ _ (eq_true hs)]
        have hne : ∀ i j, 1 ≤ i → 1 ≤ j → extIn i m' ≠ extIn j m := fun i j _ _ h ↦ hmm (extIn_inj hs hm h).2
        have hne0 : ∀ i, 1 ≤ i → extIn i m' ≠ m := fun i hi ↦ extIn_ne_short hi m' m hm
        have hneS : ∀ j, 1 ≤ j → m' ≠ extIn j m := fun j hj h ↦ extIn_ne_short hj m m' hs h.symm
        have o : ∀ i, 1 ≤ i → cache5 c m d t1 t2 t3 t4 (.inl (extIn i m')) = c (.inl (extIn i m')) :=
          fun i hi ↦ cache5_other _ _ _ _ _ _ _ _ (hne0 i hi) (hne i 1 hi le_rfl) (hne i 2 hi (by norm_num))
            (hne i 3 hi (by norm_num)) (hne i 4 hi (by norm_num))
        rw [cache5_other _ _ _ _ _ _ _ _ hmm (hneS 1 le_rfl) (hneS 2 (by norm_num)) (hneS 3 (by norm_num))
          (hneS 4 (by norm_num)), o 1 le_rfl, o 2 (by norm_num), o 3 (by norm_num), o 4 (by norm_num)]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hs), ite_eq_right_of_eq_false _ _ (eq_false hs)]
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp), projT_inr, projT_inr, cache5_inr]

theorem invT_cache5 {c : Cache} (hc : InvT c) {m : Bytes} (hm : Short m) (d t1 t2 t3 t4 : Digest) :
    InvT (cache5 c m d t1 t2 t3 t4) := by
  have hcached : ∀ i, 1 ≤ i → i ≤ 4 → cache5 c m d t1 t2 t3 t4 (.inl (extIn i m)) ≠ none := by
    intro i hi hi'
    interval_cases i
    · rw [cache5_e1 hm]; simp
    · rw [cache5_e2 hm]; simp
    · rw [cache5_e3 hm]; simp
    · rw [cache5_e4]; simp
  have hold : ∀ y, c (.inl y) ≠ none → cache5 c m d t1 t2 t3 t4 (.inl y) ≠ none := by
    intro y hy
    by_cases h0 : y = m
    · rw [h0, cache5_self hm]; simp
    by_cases h1 : y = extIn 1 m
    · rw [h1]; exact hcached 1 le_rfl (by norm_num)
    by_cases h2 : y = extIn 2 m
    · rw [h2]; exact hcached 2 (by norm_num) (by norm_num)
    by_cases h3 : y = extIn 3 m
    · rw [h3]; exact hcached 3 (by norm_num) (by norm_num)
    by_cases h4 : y = extIn 4 m
    · rw [h4]; exact hcached 4 (by norm_num) le_rfl
    rw [cache5_other _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4]
    exact hy
  intro x hx
  by_cases h0 : x = m
  · subst h0
    exact Or.inl ⟨hm, hcached⟩
  by_cases hext : ∃ i, 1 ≤ i ∧ i ≤ 4 ∧ x = extIn i m
  · obtain ⟨i, hi, hi', rfl⟩ := hext
    exact Or.inr ⟨i, m, hi, hi', hm, rfl, by rw [cache5_self hm]; simp⟩
  · have hx' : c (.inl x) ≠ none := by
      rwa [cache5_other _ _ _ _ _ _ _ _ h0 (fun h ↦ hext ⟨1, le_rfl, by norm_num, h⟩)
        (fun h ↦ hext ⟨2, by norm_num, by norm_num, h⟩) (fun h ↦ hext ⟨3, by norm_num, by norm_num, h⟩)
        (fun h ↦ hext ⟨4, by norm_num, le_rfl, h⟩)] at hx
    rcases hc x hx' with ⟨h1, h2⟩ | ⟨i, m', h1, h2, h3, h4, h5⟩
    · exact Or.inl ⟨h1, fun i hi hi' ↦ hold _ (h2 i hi hi')⟩
    · exact Or.inr ⟨i, m', h1, h2, h3, h4, hold _ h5⟩

/-! ## One query -/

theorem run_rate5_fresh {c : Cache} (hc : InvT c) {m : Bytes} (hm : Short m) (hfresh : c (.inl m) = none) :
    (simulateQ ro (rate5 m)).run c = (do
      let d ← $ᵗ Digest
      let t1 ← $ᵗ Digest
      let t2 ← $ᵗ Digest
      let t3 ← $ᵗ Digest
      let t4 ← $ᵗ Digest
      pure (mkRate d t1 t2 t3 t4, cache5 c m d t1 t2 t3 t4)) := by
  have htail : ∀ i, 1 ≤ i → i ≤ 4 → c (.inl (extIn i m)) = none := by
    intro i hi hi'
    by_contra hne
    rcases hc _ hne with ⟨h1, _⟩ | ⟨j, m', _, _, h3, h4, h5⟩
    · exact extIn_not_short hi m h1
    · rw [(extIn_inj hm h3 h4).2] at hfresh
      exact h5 hfresh
  have hne : ∀ i j, i ≠ j → extIn i m ≠ extIn j m := fun i j h ↦ extIn_ne_extIn h m hm
  have hne0 : ∀ i, 1 ≤ i → extIn i m ≠ m := fun i hi ↦ extIn_ne_short hi m m hm
  simp only [rate5, simulateQ_bind, simulateQ_pure, E2ECompleteness.simulateQ_callKeccak256, StateT.run_bind,
    StateT.run_pure]
  rw [E2ECompleteness.ro_run_fresh _ _ hfresh]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun d ↦ ?_
  rw [E2ECompleteness.ro_run_fresh _ _ (by
    rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using hne0 1 le_rfl)]; exact htail 1 le_rfl (by norm_num))]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun t1 ↦ ?_
  rw [E2ECompleteness.ro_run_fresh _ _ (by
    rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using hne 2 1 (by norm_num)),
      QueryCache.cacheQuery_of_ne _ _ (by simpa using hne0 2 (by norm_num))]
    exact htail 2 (by norm_num) (by norm_num))]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun t2 ↦ ?_
  rw [E2ECompleteness.ro_run_fresh _ _ (by
    rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using hne 3 2 (by norm_num)),
      QueryCache.cacheQuery_of_ne _ _ (by simpa using hne 3 1 (by norm_num)),
      QueryCache.cacheQuery_of_ne _ _ (by simpa using hne0 3 (by norm_num))]
    exact htail 3 (by norm_num) (by norm_num))]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun t3 ↦ ?_
  rw [E2ECompleteness.ro_run_fresh _ _ (by
    rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using hne 4 3 (by norm_num)),
      QueryCache.cacheQuery_of_ne _ _ (by simpa using hne 4 2 (by norm_num)),
      QueryCache.cacheQuery_of_ne _ _ (by simpa using hne 4 1 (by norm_num)),
      QueryCache.cacheQuery_of_ne _ _ (by simpa using hne0 4 (by norm_num))]
    exact htail 4 (by norm_num) le_rfl)]
  simp only [bind_assoc, pure_bind]
  rfl

theorem run_rate5_cached {c : Cache} (hc : InvT c) {m : Bytes} (hm' : Short m) {d : Digest}
    (hd : c (.inl m) = some d) :
    ∃ t1 t2 t3 t4 : Digest, projT c (.inl m) = some (mkRate d t1 t2 t3 t4) ∧
      (simulateQ ro (rate5 m)).run c = pure (mkRate d t1 t2 t3 t4, c) := by
  rcases hc m (by rw [hd]; simp) with ⟨hm, h⟩ | ⟨i, m', hi, _, h3, h4, _⟩
  · obtain ⟨t1, e1⟩ := Option.ne_none_iff_exists'.mp (h 1 le_rfl (by norm_num))
    obtain ⟨t2, e2⟩ := Option.ne_none_iff_exists'.mp (h 2 (by norm_num) (by norm_num))
    obtain ⟨t3, e3⟩ := Option.ne_none_iff_exists'.mp (h 3 (by norm_num) (by norm_num))
    obtain ⟨t4, e4⟩ := Option.ne_none_iff_exists'.mp (h 4 (by norm_num) le_rfl)
    refine ⟨t1, t2, t3, t4, ?_, ?_⟩
    · rw [projT_inl, ite_eq_left_of_eq_true _ _ (eq_true hm), hd, e1, e2, e3, e4]; rfl
    · simp only [rate5, simulateQ_bind, simulateQ_pure, E2ECompleteness.simulateQ_callKeccak256, StateT.run_bind,
        StateT.run_pure, randomOracle.run_eq, hd, e1, e2, e3, e4, pure_bind]
  · exact absurd (h4 ▸ hm') (extIn_not_short hi m')

/-- **One rate query of a short input**, as five digest queries: the caches related by `projT`. -/
theorem step_rate5 {c : Cache} (hc : InvT c) {m : Bytes} (hm : Short m) :
    Prod.map id projT <$> (simulateQ ro (rate5 m)).run c =ᵈ (roW (.inl m)).run (projT c) := by
  rcases h : c (.inl m) with _ | d
  · rw [run_rate5_fresh hc hm h, randomOracle.run_eq]
    have hp : projT c (.inl m) = none := by rw [projT_inl, ite_eq_left_of_eq_true _ _ (eq_true hm), h]; rfl
    rw [hp]
    simp only [map_bind, map_pure, Prod.map, id, projT_cache5 hm]
    have e : (do
        let d ← $ᵗ Digest
        let t1 ← $ᵗ Digest
        let t2 ← $ᵗ Digest
        let t3 ← $ᵗ Digest
        let t4 ← $ᵗ Digest
        pure (mkRate d t1 t2 t3 t4, (projT c).cacheQuery (.inl m) (mkRate d t1 t2 t3 t4)) :
          ProbComp (RateB × KeccakCallsW.QueryCache)) =
        (fun r ↦ (r, (projT c).cacheQuery (.inl m) r)) <$> (do
          let d ← $ᵗ Digest
          let t1 ← $ᵗ Digest
          let t2 ← $ᵗ Digest
          let t3 ← $ᵗ Digest
          let t4 ← $ᵗ Digest
          pure (mkRate d t1 t2 t3 t4) : ProbComp RateB) := by
      simp only [map_bind, map_pure]
    rw [e]
    refine (EvalDistEq.map mkRate_uniform _).trans ?_
    rw [map_eq_bind_pure_comp]
    exact EvalDistEq.rfl
  · obtain ⟨t1, t2, t3, t4, hp, hr⟩ := run_rate5_cached hc hm h
    rw [hr, randomOracle.run_eq, hp]
    simp only [map_pure, Prod.map, id]
    exact EvalDistEq.rfl

theorem invT_rate5 {c : Cache} (hc : InvT c) {m : Bytes} (hm : Short m) :
    ∀ z ∈ support ((simulateQ ro (rate5 m)).run c), InvT z.2 := by
  intro z hz
  rcases h : c (.inl m) with _ | d
  · rw [run_rate5_fresh hc hm h] at hz
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
    obtain ⟨d, -, t1, -, t2, -, t3, -, t4, -, rfl⟩ := hz
    exact invT_cache5 hc hm d t1 t2 t3 t4
  · obtain ⟨t1, t2, t3, t4, -, hr⟩ := run_rate5_cached hc hm h
    rw [hr, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact hc

/-- **One permutation call.** -/
theorem step_F (c : Cache) (s : KeccakState) :
    Prod.map id projT <$> (simulateQ ro (callKeccakF1600 s)).run c =ᵈ (roW (.inr s)).run (projT c) := by
  have e : simulateQ ro (callKeccakF1600 s) = ro (.inr s) := by
    unfold callKeccakF1600; exact simulateQ_spec_query _ _
  rw [e, randomOracle.run_eq, randomOracle.run_eq, projT_inr]
  rcases c (.inr s) with _ | v
  · simp only [map_bind, map_pure, Prod.map, id, projT_cacheQuery_inr]
    exact EvalDistEq.rfl
  · simp only [map_pure, Prod.map, id]
    exact EvalDistEq.rfl

theorem invT_F {c : Cache} (hc : InvT c) (s : KeccakState) :
    ∀ z ∈ support ((simulateQ ro (callKeccakF1600 s)).run c), InvT z.2 := by
  intro z hz
  have e : simulateQ ro (callKeccakF1600 s) = ro (.inr s) := by
    unfold callKeccakF1600; exact simulateQ_spec_query _ _
  rw [e] at hz
  rcases E2ECompleteness.mem_support_ro_run hz with h | ⟨v, h⟩
  · rw [h]; exact hc
  · rw [h]; exact invT_cacheQuery_inr hc s v

/-! ## The coupling -/

/-- **A computation over π1-rec4's calls with short hash inputs**, against the rate's random oracles, is its
five-digest reading against leanerVM's two random oracles, the caches related by `projT`. -/
theorem map_run_tauW {β : Type} (G : OracleComp KeccakCallsW β) (hG : HashOKW Short G) (c : Cache) (hc : InvT c) :
    Prod.map id projT <$> (simulateQ ro (simulateQ tauW G)).run c =ᵈ (simulateQ roW G).run (projT c) := by
  induction G using OracleComp.inductionOn generalizing c with
  | pure a => simp
  | query_bind t k ih =>
    obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).1 hG
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, map_bind]
    have hstep : Prod.map id projT <$> (simulateQ ro (tauW t)).run c =ᵈ (roW t).run (projT c) ∧
        ∀ z ∈ support ((simulateQ ro (tauW t)).run c), InvT z.2 := by
      rcases t with m | s
      · exact ⟨step_rate5 hc ht, invT_rate5 hc ht⟩
      · exact ⟨step_F c s, invT_F hc s⟩
    calc ((simulateQ ro (tauW t)).run c >>= fun z ↦
          Prod.map id projT <$> (simulateQ ro (simulateQ tauW (k z.1))).run z.2)
        =ᵈ ((simulateQ ro (tauW t)).run c >>= fun z ↦ (simulateQ roW (k z.1)).run (projT z.2)) :=
          EvalDistEq.bind_congr_of_support _ fun z hz ↦ ih z.1 (hk z.1) z.2 (hstep.2 z hz)
      _ = ((Prod.map id projT <$> (simulateQ ro (tauW t)).run c) >>= fun z ↦
            (simulateQ roW (k z.1)).run z.2) := by
          rw [bind_map_left]; rfl
      _ =ᵈ ((roW t).run (projT c) >>= fun z ↦ (simulateQ roW (k z.1)).run z.2) :=
          EvalDistEq.bind_left hstep.1 _

/-- **The coupling**: a computation over π1-rec4's calls with short hash inputs has, against the rate's random
oracles, the outputs of its five-digest reading against leanerVM's two random oracles. -/
theorem romW_evalDistEq {β : Type} (G : OracleComp KeccakCallsW β) (hG : HashOKW Short G) :
    (simulateQ roW G).run' ∅ =ᵈ (simulateQ ro (simulateQ tauW G)).run' ∅ := by
  have h := (map_run_tauW G hG ∅ invT_empty).map Prod.fst
  simp only [Functor.map_map, projT_empty] at h
  simpa [StateT.run'_eq] using h.symm

/-- **Any event**, in either model. -/
theorem prEvent_romW_eq {β : Type} (G : OracleComp KeccakCallsW β) (hG : HashOKW Short G) (p : β → Prop) :
    Pr{let v ← (simulateQ roW G).run' ∅}[p v] = Pr{let v ← (simulateQ ro (simulateQ tauW G)).run' ∅}[p v] :=
  (romW_evalDistEq G hG).prEvent_eq p

end UniKeccakComplete.Rec4

/-- info: 'UniKeccakComplete.Rec4.romW_evalDistEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.romW_evalDistEq
