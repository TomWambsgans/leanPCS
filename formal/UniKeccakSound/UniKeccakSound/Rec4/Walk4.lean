-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `Fs/WalkK3.lean`'s walk (`uniWalkK3`, `uniWalkRejectK3`)
-- for π1-rec4's verifier (`runWithK4`), with `UniSound/FsWalkProof.lean`'s generic lemmas (`progRun`, `Consumes`, …)
-- extended to the wide chain programs of `Rec4/ProgW.lean` (`progRunW`, `consumes_runW`).
import UniKeccakSound.Rec4.Bridge4
import UniKeccakSound.Rec4.Link4Base
import UniKeccakSound.Fs.WalkK3

/-!
# π1-rec4's walk is the wide chain (`UniWalkK4`, `UniWalkRejectK4`)

The two halves of `Bridge4.lean`'s walk, proved for **every** deployment, `κ`, `nV`, `np` and code-level link
`C : UniCodeK4 D κ nV np` (no hypothesis):

* **`uniWalkK4 : UniWalkK4 D κ nV np C`**: on a stream of `uLen4` bytes, in every lawful monad and over every
  permutation, the walk's verdict and result are `uAccB4` and `uOut4` at the wide chain's challenges over Keccak-256's
  rate (`hashRP P`);
* **`uniWalkRejectK4 : UniWalkRejectK4 D κ nV np`**: on a stream of another length, every outcome rejects.

The route is `Fs/WalkK3.lean`'s:

* **The walk's wrapper** (`runWithK4_pair`): `runWithK4` is the seed, `reduceWithK4`, then `finish`; its verdict and
  result are `walkOf3` of `obsOf3`, so the code-level link `C.link` replaces `reduceWithK4` by `readCounts` then
  `C.prog`'s `runW`.
* **The wide draw** (`sampleWide_bind`, `chals_eq`): the draw's `n ≤ 5` challenges off the sponge's rate are the
  wide chain's (`chalsW uLimbs n` of the digest's bytes and the tail, `tailOfState`), and the channel's new state is
  the digest (`sampledW_eq`).
* **A wide chain program on a stream holding its bytes** (`progRunW`, for any `ChainProgW` whose scalars before a
  root fit their round, `PvFits`, and whose rounds draw at most five): its run is the wide chain's answers
  (`stepsW (hashRP F)`: one call a round, of the state and the bytes `wAbsW` lists: round `j`'s message read with
  `pv j` scalars before its root, `msgOfW`), mapped by `progOutW`.
* **The chain absorbs the walk's bytes** (`absorbsW_wAbsW`): `uniEncW (pv j)` of a stream message is the stream's
  bytes it is read from (`uniEncW_msgOfW`), round `0`'s after the row counts' `24` bytes.
* **Rejection** (`Consumes`): every successful outcome of the wide chain program reads exactly `uLen4` bytes
  (`consumes_runW`, the wide draw reading none: `consumes_sampleWide`).
-/

namespace UniKeccakSound.Rec4

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile WhirBridge UniStatement UniSound UniKeccak LeanVM.Semantics
open OracleSpec OracleComp

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.setupStackK UniKeccak.setupOodK

/-! ## The wide draw's challenges -/

/-- **Challenge `k ≤ 4` of a wide draw** off the sponge's rate is the wide chain's, of the digest and the tail. -/
theorem challengeAt_eq_chalW (st : KeccakState) (k : ℕ) (hk : k < 5) :
    challengeAt (rateBytesOf st) k = chalW uLimbs (toB (digestOfState st)) (tailOfState st) k := by
  rcases k with _ | k
  · rw [challengeAt_zero]
    show _ = chalL uLimbs _
    rw [← chalL_eq, Soundness.ofB_toB_root]
  · have hk' : k < 4 := by omega
    simp only [chalW, hk', ↓reduceIte]
    interval_cases k <;> rfl

/-- **A wide draw of `n ≤ 5`** is the wide chain's `chalsW`. -/
theorem chals_eq (st : KeccakState) (n : ℕ) (hn : n ≤ 5) :
    (List.range n).map (challengeAt (rateBytesOf st)) =
      chalsW uLimbs n (toB (digestOfState st)) (tailOfState st) := by
  unfold chalsW
  exact List.map_congr_left fun k hk => challengeAt_eq_chalW st k (by rw [List.mem_range] at hk; omega)

/-- The channel after a wide draw of `n` answered `a` (the digest's bytes and the tail). -/
def sampW (c : Chan) (a : Bytes32 × TailP) (n : ℕ) : Chan :=
  { c with absorbed := c.cursor, state := ofB a.1, challenges := c.challenges ++ (chalsW uLimbs n a.1 a.2).toArray }

theorem sampledW_eq (c : Chan) (st : KeccakState) (n : ℕ) (hn : n ≤ 5) :
    sampledW c st n = sampW c (toB (digestOfState st), tailOfState st) n := by
  simp only [sampledW, sampW, Soundness.ofB_toB_root, chals_eq st n hn]

/-! ## The chain's answers -/

section Steps

variable {m : Type → Type} [Monad m]

/-- **The wide chain's answers from a state**: each step's input the state's bytes, then the step's bytes. -/
def stepsW (H : List UInt8 → m (Bytes32 × TailP)) : Bytes32 → List (List UInt8) → m (List (Bytes32 × TailP))
  | _, [] => pure []
  | st, e :: es => H (stepIn st e) >>= fun a => (a :: ·) <$> stepsW H a.1 es

variable [LawfulMonad m]

theorem runMW_eq (H : List UInt8 → m (Bytes32 × TailP)) :
    ∀ (y : List UInt8) (es : List (List UInt8)),
      ChainSpecW.runMW H y es = H y >>= fun a => (a :: ·) <$> stepsW H a.1 es
  | y, [] => by simp only [ChainSpecW.runMW, stepsW, map_pure]
  | y, e :: es => by
    simp only [ChainSpecW.runMW, stepsW, runMW_eq H _ es, map_bind, bind_assoc, Functor.map_map]
    refine bind_congr fun a => bind_congr fun b => ?_
    rw [bind_map_left, map_eq_bind_pure_comp]
    rfl

/-- **Two readings of the answers agreeing on lists of the steps' length** read them alike. -/
theorem map_stepsW_congr {β : Type} (H : List UInt8 → m (Bytes32 × TailP)) :
    ∀ (st : Bytes32) (es : List (List UInt8)) (G G' : List (Bytes32 × TailP) → β),
      (∀ as, as.length = es.length → G as = G' as) → G <$> stepsW H st es = G' <$> stepsW H st es
  | st, [], G, G', h => by
    simp only [stepsW, map_pure]
    rw [h [] rfl]
  | st, e :: es, G, G', h => by
    simp only [stepsW, map_bind, Functor.map_map]
    refine bind_congr fun a => ?_
    exact map_stepsW_congr H a.1 es (fun as => G (a :: as)) (fun as => G' (a :: as))
      (fun as has => h _ (by simp [has]))

end Steps

/-! ## A round's bytes -/

/-- **The bytes each wide step absorbs**, round by round from byte `o`: the bytes not yet absorbed (`pre`), then the
round's message. -/
def wAbsW (b : Array UInt8) : ℕ → List UInt8 → List RoundSpec → List (List UInt8)
  | _, _, [] => []
  | o, pre, r :: rs => (pre ++ bytesAt b o (roundBytes r)) :: wAbsW b (o + roundBytes r) [] rs

theorem length_wAbsW (b : Array UInt8) : ∀ (o : ℕ) (pre : List UInt8) (rs : List RoundSpec),
    (wAbsW b o pre rs).length = rs.length
  | _, _, [] => rfl
  | o, pre, r :: rs => by simp [wAbsW, length_wAbsW b _ _ rs]

/-- **The scalars before each root fit their round**, from round `j` on. -/
def PvFits (pv : ℕ → ℕ) : ℕ → List RoundSpec → Prop
  | _, [] => True
  | j, r :: rs => pv j ≤ r.nv ∧ PvFits pv (j + 1) rs

theorem pvFits_of (pv : ℕ → ℕ) : ∀ (j : ℕ) (rs : List RoundSpec),
    (∀ k < rs.length, pv (j + k) ≤ (rs.getD k ⟨false, 0, 0⟩).nv) → PvFits pv j rs
  | _, [], _ => trivial
  | j, r :: rs, h => by
    refine ⟨by simpa using h 0 (by simp), pvFits_of pv (j + 1) rs fun k hk => ?_⟩
    rw [show j + 1 + k = j + (k + 1) by omega]
    simpa using h (k + 1) (by simp; omega)

/-- **π1-rec4's scalars before its roots fit**: `C2`'s `64` slices of its `65` scalars. -/
theorem pvFits_rec4 (κ nV np : ℕ) : PvFits (pv4 κ) 0 (rec4Rounds κ nV np) := by
  refine pvFits_of _ 0 _ fun k _ => ?_
  rw [Nat.zero_add]
  unfold pv4
  split_ifs with h
  · subst h
    rw [show (rec4Rounds κ nV np).getD (28 + κ) ⟨false, 0, 0⟩ = ⟨true, 65, 4⟩ from rec4Rounds_spec_c2 κ nV np]
    decide
  · exact Nat.zero_le _

/-- **A round's message read with `p` scalars before its root**: those scalars, the root, the others. -/
theorem msgOfW_eq (b : Array UInt8) (p o : ℕ) (r : RoundSpec) (hp : p ≤ r.nv) :
    msgOfW b p o r = ((if r.root then some (halvesAt b (o + 24 * p)) else none),
      scalarsAt b o p ++ scalarsAt b (o + 24 * p + (if r.root then 32 else 0)) (r.nv - p)) := by
  obtain ⟨q, hq⟩ : ∃ q, r.nv = p + q := ⟨r.nv - p, by omega⟩
  unfold msgOfW scalarsAt
  refine Prod.ext rfl ?_
  simp only
  rw [hq, List.range_add, List.map_append, List.map_map, Nat.add_sub_cancel_left]
  refine congrArg₂ (· ++ ·) (List.map_congr_left fun k hk => ?_) (List.map_congr_left fun k _ => ?_)
  · have hk' : ¬ p ≤ k := by rw [List.mem_range] at hk; omega
    simp [hk']
  · simp only [Function.comp_apply, Nat.le_add_right, decide_true, Bool.and_true]
    rw [show o + (if r.root = true then 32 else 0) + 24 * (p + k) =
      o + 24 * p + (if r.root = true then 32 else 0) + 24 * k by omega]

/-- **A round's message as the wide chain hashes it** is the stream's bytes it is read from. -/
theorem uniEncW_msgOfW (b : Array UInt8) (p o : ℕ) (r : RoundSpec) (hp : p ≤ r.nv)
    (h : o + roundBytes r ≤ b.size) : uniEncW p (toRMsg (msgOfW b p o r)) = bytesAt b o (roundBytes r) := by
  rw [msgOfW_eq b p o r hp]
  have hl : (scalarsAt b o p).length = p := by simp [scalarsAt]
  rcases r with ⟨root, nv, ns⟩
  simp only at hp
  cases root with
  | false =>
    simp only [roundBytes, Bool.false_eq_true, ite_false, Nat.zero_add, Nat.add_zero] at h ⊢
    simp only [uniEncW, toRMsg, Option.map_none, List.take_left' hl, List.drop_left' hl, List.append_nil]
    rw [scalars24_scalarsAt b p o (by omega), scalars24_scalarsAt b (nv - p) (o + 24 * p) (by omega),
      ← bytesAt_add, show 24 * p + 24 * (nv - p) = 24 * nv by omega]
  | true =>
    simp only [roundBytes, ite_true] at h ⊢
    simp only [uniEncW, toRMsg, Option.map_some, List.take_left' hl, List.drop_left' hl]
    rw [scalars24_scalarsAt b p o (by omega), revRoot_halvesAt b _ (by omega),
      scalars24_scalarsAt b (nv - p) (o + 24 * p + 32) (by omega), ← bytesAt_add,
      ← bytesAt_add_of b (show o + (24 * p + 32) = o + 24 * p + 32 by omega),
      show 24 * p + 32 + 24 * (nv - p) = 32 + 24 * nv by omega]

/-- **The wide chain absorbs what the walk absorbs**: the encoding of the stream's messages at round `i`, round `0`'s
after the statement's bytes `pre`, are the stream's bytes. -/
theorem absorbsW_wAbsW (b : Array UInt8) (pre : List UInt8) (pv : ℕ → ℕ) :
    ∀ (i o : ℕ) (rs : List RoundSpec), o + roundsBytes rs ≤ b.size → PvFits pv i rs →
      absorbsW (fun j msg => if j = 0 then pre ++ uniEncW (pv 0) msg else uniEncW (pv j) msg) i rs
          ((msgsAtW b pv i o rs).map toRMsg) =
        wAbsW b o (if i = 0 then pre else []) rs
  | _, _, [], _, _ => rfl
  | i, o, r :: rs, h, hpv => by
    obtain ⟨hp0, hp1⟩ := hpv
    simp only [roundsBytes] at h
    rw [msgsAtW, List.map_cons, absorbsW, List.headD_cons, List.tail_cons, wAbsW,
      absorbsW_wAbsW b pre pv (i + 1) (o + roundBytes r) rs (by omega) hp1]
    simp only [Nat.add_one_ne_zero, ite_false]
    split_ifs with hi
    · subst hi
      rw [uniEncW_msgOfW b (pv 0) o r hp0 (by omega)]
    · rw [uniEncW_msgOfW b (pv i) o r hp0 (by omega), List.nil_append]

/-! ## The channel's reads -/

/-- The bytes read since the last draw, after `n` more. -/
theorem preOf_advance (c : Chan) (n : ℕ) (zs : List E) (hab : c.absorbed ≤ c.cursor) :
    preOf (collectZ { c with cursor := c.cursor + n } zs) = preOf c ++ bytesAt c.data c.cursor n := by
  simp only [preOf, collectZ, toList_extract_eq]
  rw [show c.cursor + n - c.absorbed = (c.cursor - c.absorbed) + n by omega,
    bytesAt_add_of c.data (show c.absorbed + (c.cursor - c.absorbed) = c.cursor by omega)]

/-- The channel after a wide round: its message read, its zeros `zs` collected, its draw answered `a`. -/
def roundChanW (c : Chan) (r : RoundSpec) (zs : List E) (a : Bytes32 × TailP) : Chan :=
  sampW (collectZ { c with cursor := c.cursor + roundBytes r } zs) a (r.ns + 1)

theorem roundChanW_data (c : Chan) (r : RoundSpec) (zs : List E) (a : Bytes32 × TailP) :
    (roundChanW c r zs a).data = c.data := rfl

theorem roundChanW_cursor (c : Chan) (r : RoundSpec) (zs : List E) (a : Bytes32 × TailP) :
    (roundChanW c r zs a).cursor = c.cursor + roundBytes r := rfl

theorem roundChanW_state (c : Chan) (r : RoundSpec) (zs : List E) (a : Bytes32 × TailP) :
    toB (roundChanW c r zs a).state = a.1 := toB_ofB a.1

theorem preOf_roundChanW (c : Chan) (r : RoundSpec) (zs : List E) (a : Bytes32 × TailP) :
    preOf (roundChanW c r zs a) = [] := preOf_self _ rfl

theorem roundChanW_zeros (c : Chan) (r : RoundSpec) (zs : List E) (a : Bytes32 × TailP) :
    (roundChanW c r zs a).zeros.toList = c.zeros.toList ++ zs := by
  simp only [roundChanW, sampW, collectZ, foldl_push_toList]

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- A wide round's reads: `p` scalars, the root (if any), the other scalars. -/
def readsW (p : ℕ) (r : RoundSpec) : ChanM m UMsg := do
  let pre ← nextScalars (m := m) p
  let root ← rootRead (m := m) r.root
  let post ← nextScalars (m := m) (r.nv - p)
  pure (root, pre ++ post)

theorem readsW_ok (p : ℕ) (r : RoundSpec) (hp : p ≤ r.nv) (c : Chan)
    (hsz : c.cursor + roundBytes r ≤ c.data.size) :
    (readsW (m := m) p r).run.run c =
      pure (.ok (msgOfW c.data p c.cursor r), { c with cursor := c.cursor + roundBytes r }) := by
  have hR : c.cursor + roundBytes r = c.cursor + 24 * p + (if r.root then 32 else 0) + 24 * (r.nv - p) := by
    unfold roundBytes
    omega
  unfold readsW
  rw [run_bind_ok (nextScalars_ok p c (by omega))]
  rw [run_bind_ok (rootRead_ok r.root _ (by dsimp only; omega))]
  rw [run_bind_ok (nextScalars_ok (r.nv - p) _ (by dsimp only; omega))]
  rw [run_pure_chan, msgOfW_eq _ _ _ _ hp, hR]

theorem sampleWide_bind {β : Type} (F : KeccakState → m KeccakState) (n : ℕ) (Kt : List E → ChanM m β)
    (c : Chan) :
    (sampleWide F n >>= Kt).run.run c =
      keccak256StateWith F (digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList) >>= fun st =>
        (Kt ((List.range n).map (challengeAt (rateBytesOf st)))).run.run (sampledW c st n) := by
  simp only [ExceptT.run_bind, StateT.run_bind, sampleWide_run, bind_map_left]

/-- **A wide round**: its message the stream's (`msgOfW`), its zeros collected, its draw the wide chain's step on the
bytes not yet absorbed. -/
theorem roundW_bind {β : Type} (F : KeccakState → m KeccakState) (r : RoundSpec) (p : ℕ) (hp : p ≤ r.nv)
    (hns : r.ns ≤ 4) (Z : UMsg → List E) (Kt : UMsg → List E → ChanM m β) (c : Chan)
    (hab : c.absorbed ≤ c.cursor) (hsz : c.cursor + roundBytes r ≤ c.data.size) :
    (do
      let pre ← nextScalars (m := m) p
      let root ← rootRead (m := m) r.root
      let post ← nextScalars (m := m) (r.nv - p)
      ChainProg.requireZeros (Z (root, pre ++ post))
      let chs ← sampleWide F (r.ns + 1)
      Kt (root, pre ++ post) chs).run.run c =
    hashRP F (stepIn (toB c.state) (preOf c ++ bytesAt c.data c.cursor (roundBytes r))) >>= fun a =>
      (Kt (msgOfW c.data p c.cursor r) (chalsW uLimbs (r.ns + 1) a.1 a.2)).run.run
        (roundChanW c r (Z (msgOfW c.data p c.cursor r)) a) := by
  have e : (do
      let pre ← nextScalars (m := m) p
      let root ← rootRead (m := m) r.root
      let post ← nextScalars (m := m) (r.nv - p)
      ChainProg.requireZeros (Z (root, pre ++ post))
      let chs ← sampleWide F (r.ns + 1)
      Kt (root, pre ++ post) chs) = (do
      let msg ← readsW (m := m) p r
      ChainProg.requireZeros (Z msg)
      let chs ← sampleWide F (r.ns + 1)
      Kt msg chs) := by
    simp only [readsW, bind_assoc, pure_bind]
  have hin : digestBytes (collectZ { c with cursor := c.cursor + roundBytes r }
        (Z (msgOfW c.data p c.cursor r))).state ++
      ((collectZ { c with cursor := c.cursor + roundBytes r } (Z (msgOfW c.data p c.cursor r))).data.extract
        (collectZ { c with cursor := c.cursor + roundBytes r } (Z (msgOfW c.data p c.cursor r))).absorbed
        (collectZ { c with cursor := c.cursor + roundBytes r } (Z (msgOfW c.data p c.cursor r))).cursor).toList =
      stepIn (toB c.state) (preOf c ++ bytesAt c.data c.cursor (roundBytes r)) := by
    show digestBytes c.state ++
      preOf (collectZ { c with cursor := c.cursor + roundBytes r } (Z (msgOfW c.data p c.cursor r))) = _
    rw [preOf_advance c _ _ hab, stepIn, Bridge.toB_toList]
  rw [e, run_bind_ok (readsW_ok p r hp c hsz), run_bind_ok (requireZeros_run _ _), sampleWide_bind, hin, hashRP,
    bind_map_left]
  refine bind_congr fun st => ?_
  rw [sampledW_eq _ st _ (by omega), chals_eq st _ (by omega)]
  rfl

end Monad

/-! ## A wide chain program on a stream holding its bytes -/

section Prog

variable {α : Type}

/-- **The transcript and channel after the wide rounds**, from the chain's answers. -/
def runOutW (P : ChainProgW α) : List RoundSpec → Done → Chan → List (Bytes32 × TailP) → Done × Chan
  | [], done, c, _ => (done, c)
  | _ :: _, done, c, [] => (done, c)
  | r :: rs, done, c, a :: as =>
    runOutW P rs (done ++ [(msgOfW c.data (P.pv done.length) c.cursor r, chalsW uLimbs (r.ns + 1) a.1 a.2)])
      (roundChanW c r (P.zeros done (msgOfW c.data (P.pv done.length) c.cursor r)) a) as

theorem runOutW_data (P : ChainProgW α) : ∀ (rs : List RoundSpec) (done : Done) (c : Chan)
    (as : List (Bytes32 × TailP)), (runOutW P rs done c as).2.data = c.data
  | [], _, _, _ => rfl
  | _ :: _, _, _, [] => rfl
  | r :: rs, done, c, a :: as => by
    simp only [runOutW]
    rw [runOutW_data P rs, roundChanW_data]

theorem runOutW_cursor_le (P : ChainProgW α) : ∀ (rs : List RoundSpec) (done : Done) (c : Chan)
    (as : List (Bytes32 × TailP)), (runOutW P rs done c as).2.cursor ≤ c.cursor + roundsBytes rs
  | [], _, _, _ => Nat.le_refl _
  | _ :: _, _, _, [] => Nat.le_add_right _ _
  | r :: rs, done, c, a :: as => by
    simp only [runOutW]
    refine (runOutW_cursor_le P rs _ _ as).trans ?_
    rw [roundChanW_cursor, roundsBytes, Nat.add_assoc]

theorem runOutW_cursor (P : ChainProgW α) : ∀ (rs : List RoundSpec) (done : Done) (c : Chan)
    (as : List (Bytes32 × TailP)), rs.length ≤ as.length →
      (runOutW P rs done c as).2.cursor = c.cursor + roundsBytes rs
  | [], _, _, _, _ => rfl
  | _ :: _, _, _, [], h => absurd h (by simp)
  | r :: rs, done, c, a :: as, h => by
    simp only [runOutW]
    rw [runOutW_cursor P rs _ _ as (by simpa using h), roundChanW_cursor, roundsBytes, Nat.add_assoc]

theorem runOutW_done (P : ChainProgW α) : ∀ (rs : List RoundSpec) (done : Done) (c : Chan)
    (as : List (Bytes32 × TailP)), (runOutW P rs done c as).1 =
      done ++ (msgsAtW c.data P.pv done.length c.cursor rs).zip
        ((rs.zip as).map fun q => chalsW uLimbs (q.1.ns + 1) q.2.1 q.2.2)
  | [], _, _, _ => by simp [runOutW, msgsAtW]
  | _ :: _, _, _, [] => by simp [runOutW]
  | r :: rs, done, c, a :: as => by
    simp only [runOutW]
    rw [runOutW_done P rs, roundChanW_data, roundChanW_cursor]
    simp [msgsAtW]

theorem runOutW_zeros (P : ChainProgW α) : ∀ (rs : List RoundSpec) (done : Done) (c : Chan)
    (as : List (Bytes32 × TailP)), (runOutW P rs done c as).2.zeros.toList = c.zeros.toList ++
      zerosFrom P.toChainProg done ((msgsAtW c.data P.pv done.length c.cursor rs).zip
        ((rs.zip as).map fun q => chalsW uLimbs (q.1.ns + 1) q.2.1 q.2.2))
  | [], _, _, _ => by simp [runOutW, msgsAtW, zerosFrom]
  | _ :: _, _, _, [] => by simp [runOutW, zerosFrom]
  | r :: rs, done, c, a :: as => by
    simp only [runOutW]
    rw [runOutW_zeros P rs, roundChanW_data, roundChanW_cursor, roundChanW_zeros]
    simp [msgsAtW, zerosFrom]

/-- The wide program's result and channel, from the chain's answers. -/
def progOutW (P : ChainProgW α) (c : Chan) (as : List (Bytes32 × TailP)) : Except UniError α × Chan :=
  (.ok (P.out (runOutW P P.rounds [] c as).1
      (scalarsAt (runOutW P P.rounds [] c as).2.data (runOutW P P.rounds [] c as).2.cursor P.tail)),
    collectZ { (runOutW P P.rounds [] c as).2 with
      cursor := (runOutW P P.rounds [] c as).2.cursor + 24 * P.tail }
      (P.tailZeros (runOutW P P.rounds [] c as).1
        (scalarsAt (runOutW P P.rounds [] c as).2.data (runOutW P P.rounds [] c as).2.cursor P.tail)))

theorem progOutW_fst (P : ChainProgW α) (c : Chan) (as : List (Bytes32 × TailP)) :
    (progOutW P c as).1 = .ok (P.out (runOutW P P.rounds [] c as).1
      (scalarsAt (runOutW P P.rounds [] c as).2.data (runOutW P P.rounds [] c as).2.cursor P.tail)) := rfl

theorem progOutW_data (P : ChainProgW α) (c : Chan) (as : List (Bytes32 × TailP)) :
    (progOutW P c as).2.data = c.data := by
  simp only [progOutW, collectZ, runOutW_data]

theorem progOutW_cursor (P : ChainProgW α) (c : Chan) (as : List (Bytes32 × TailP))
    (h : P.rounds.length ≤ as.length) :
    (progOutW P c as).2.cursor = c.cursor + roundsBytes P.rounds + 24 * P.tail := by
  simp only [progOutW, collectZ, runOutW_cursor P _ _ _ _ h]

theorem progOutW_zeros (P : ChainProgW α) (c : Chan) (as : List (Bytes32 × TailP)) :
    (progOutW P c as).2.zeros.toList = c.zeros.toList ++ zerosFrom P.toChainProg [] (runOutW P P.rounds [] c as).1 ++
      P.tailZeros (runOutW P P.rounds [] c as).1
        (scalarsAt (runOutW P P.rounds [] c as).2.data (runOutW P P.rounds [] c as).2.cursor P.tail) := by
  simp only [progOutW, collectZ, foldl_push_toList, runOutW_zeros, runOutW_done, List.nil_append]

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **The rounds of a wide chain program**, on a stream holding their bytes: the wide chain's steps on `wAbsW`, the
transcript and channel `runOutW`. -/
theorem runRoundsW_run (P : ChainProgW α) (F : KeccakState → m KeccakState) :
    ∀ (rs : List RoundSpec) (done : Done) (c : Chan), c.absorbed ≤ c.cursor →
      c.cursor + roundsBytes rs ≤ c.data.size → PvFits P.pv done.length rs → (∀ s ∈ rs, s.ns ≤ 4) →
      (P.runRoundsW F rs done).run.run c =
        (fun as => (Except.ok (runOutW P rs done c as).1, (runOutW P rs done c as).2)) <$>
          stepsW (hashRP F) (toB c.state) (wAbsW c.data c.cursor (preOf c) rs)
  | [], done, c, _, _, _, _ => by
    simp only [ChainProgW.runRoundsW, wAbsW, stepsW, map_pure, runOutW]
    rfl
  | r :: rs, done, c, hab, hsz, hpv, hns => by
    obtain ⟨hp0, hp1⟩ := hpv
    simp only [roundsBytes] at hsz
    rw [runRoundsW_cons]
    refine (roundW_bind F r (P.pv done.length) hp0 (hns r List.mem_cons_self) (P.zeros done)
      (fun msg chs => P.runRoundsW F rs (done ++ [(msg, chs)])) c hab (by omega)).trans ?_
    have IH : ∀ a : Bytes32 × TailP,
        (P.runRoundsW F rs (done ++ [(msgOfW c.data (P.pv done.length) c.cursor r,
            chalsW uLimbs (r.ns + 1) a.1 a.2)])).run.run
            (roundChanW c r (P.zeros done (msgOfW c.data (P.pv done.length) c.cursor r)) a) =
          (fun as => (Except.ok (runOutW P (r :: rs) done c (a :: as)).1,
            (runOutW P (r :: rs) done c (a :: as)).2)) <$>
            stepsW (hashRP F) a.1 (wAbsW c.data (c.cursor + roundBytes r) [] rs) := by
      intro a
      rw [runRoundsW_run P F rs _ _ (le_of_eq rfl) (by rw [roundChanW_cursor, roundChanW_data]; omega)
        (by rw [List.length_append, List.length_singleton]; exact hp1)
        (fun s hs => hns s (List.mem_cons_of_mem _ hs)),
        roundChanW_state, roundChanW_data, roundChanW_cursor, preOf_roundChanW]
      rfl
    simp only [IH]
    simp only [wAbsW, stepsW, map_bind, Functor.map_map]

/-- **A wide chain program on a stream holding its bytes** (its rounds' and its tail's, from the cursor), its scalars
before a root fitting their round and its draws at most five: the wide chain's steps on `wAbsW`, its result and
channel `progOutW`. -/
theorem progRunW (P : ChainProgW α) (F : KeccakState → m KeccakState) (c : Chan) (hab : c.absorbed ≤ c.cursor)
    (hsz : c.cursor + roundsBytes P.rounds + 24 * P.tail ≤ c.data.size) (hpv : PvFits P.pv 0 P.rounds)
    (hns : ∀ s ∈ P.rounds, s.ns ≤ 4) :
    (P.runW F).run.run c =
      progOutW P c <$> stepsW (hashRP F) (toB c.state) (wAbsW c.data c.cursor (preOf c) P.rounds) := by
  simp only [ChainProgW.runW, ExceptT.run_bind, StateT.run_bind,
    runRoundsW_run P F P.rounds [] c hab (by omega) hpv hns, bind_map_left]
  rw [map_eq_bind_pure_comp]
  congr 1
  funext as
  have h1 := runOutW_cursor_le P P.rounds [] c as
  rw [nextScalars_ok P.tail _ (by rw [runOutW_data]; omega)]
  simp only [pure_bind, StateT.run_bind, requireZeros_run, ExceptT.run_pure, StateT.run_pure,
    Function.comp_apply]
  rfl

end Monad

/-! ## Consumption -/

theorem consumes_sampleWide (F : KeccakState → OC KeccakState) (n : ℕ) : Consumes 0 (sampleWide F n) := by
  intro c y hc hy a _
  rw [sampleWide_run, support_map] at hy
  obtain ⟨st, -, rfl⟩ := hy
  exact ⟨rfl, rfl, hc⟩

theorem consumes_runRoundsW (P : ChainProgW α) (F : KeccakState → OC KeccakState) :
    ∀ (rs : List RoundSpec) (done : Done), PvFits P.pv done.length rs →
      Consumes (roundsBytes rs) (P.runRoundsW F rs done)
  | [], done, _ => consumes_pure done
  | r :: rs, done, hpv => by
    obtain ⟨hp0, hp1⟩ := hpv
    rw [runRoundsW_cons]
    refine ((consumes_nextScalars _).bind fun _ => (consumes_rootRead r.root).bind fun _ =>
      (consumes_nextScalars _).bind fun _ => (consumes_requireZeros _).bind fun _ =>
        (consumes_sampleWide F _).bind fun _ => consumes_runRoundsW P F rs _
          (by rw [List.length_append, List.length_singleton]; exact hp1)).mono_eq ?_
    simp only [roundsBytes, roundBytes]
    omega

theorem consumes_runW (P : ChainProgW α) (F : KeccakState → OC KeccakState) (hpv : PvFits P.pv 0 P.rounds) :
    Consumes (roundsBytes P.rounds + (P.tail * 24 + (0 + 0))) (P.runW F) :=
  (consumes_runRoundsW P F _ _ hpv).bind fun _ => (consumes_nextScalars _).bind fun _ =>
    (consumes_requireZeros _).bind fun _ => consumes_pure _

end Prog

/-! ## π1-rec4's chain read off the stream -/

/-- **The bytes π1-rec4's chain absorbs** are the stream's from byte `24`, round `0`'s after the row counts'. -/
theorem absorbsS_uView4 (κ nV np : ℕ) (π : UPf)
    (h : 24 + roundsBytes (rec4Rounds κ nV np) ≤ π.proof.stream.size) :
    (uSpec4 κ nV np).absorbsS (uView4 κ nV np π).1 (uSpec4 κ nV np).K.rounds (uView4 κ nV np π).2 =
      wAbsW π.proof.stream 24 (bytesAt π.proof.stream 0 24) (rec4Rounds κ nV np) := by
  have hS : ∀ (s : FSt) (rs : List RoundSpec) (ms : List (RMsg E)), (uSpec4 κ nV np).absorbsS s rs ms =
      absorbsW (fun j msg => if j = 0 then (uSpec4 κ nV np).pre s ++ (uSpec4 κ nV np).enc 0 msg
        else (uSpec4 κ nV np).enc j msg) 0 rs ms := fun _ _ _ => rfl
  have hv : (uView4 κ nV np π).1 = (π.iv, π.input, rowBytes π.proof.stream) := rfl
  have hpre : ∀ s : FSt, (uSpec4 κ nV np).pre s = s.2.2.toList := fun _ => rfl
  have henc : ∀ j, (uSpec4 κ nV np).enc j = uniEncW (pv4 κ j) := fun _ => rfl
  have hms : (uView4 κ nV np π).2 = (msgsAtW π.proof.stream (pv4 κ) 0 24 (rec4Rounds κ nV np)).map toRMsg := rfl
  rw [hS, hv, hpre, uSpec4_rounds, hms]
  simp only [henc]
  rw [absorbsW_wAbsW π.proof.stream _ (pv4 κ) 0 24 (rec4Rounds κ nV np) h (pvFits_rec4 κ nV np),
    rowBytes_toList π.proof.stream (by omega)]
  rfl

section Chain

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **π1-rec4's wide chain** over `hashRP P`: the seed's Keccak-256 state, then the steps on the stream's bytes. -/
theorem chain_uSpec4 (κ nV np : ℕ) (P : KeccakState → m KeccakState) (π : UPf)
    (h : 24 + roundsBytes (rec4Rounds κ nV np) ≤ π.proof.stream.size) :
    (uSpec4 κ nV np).chain (hashRP P) (uView4 κ nV np π).1 (uView4 κ nV np π).2 =
      keccak256StateWith P (name ++ π.iv.toList ++ π.input.toList) >>= fun st =>
        (fun as => (uSpec4 κ nV np).chalsOf ((toB (digestOfState st), tailOfState st) :: as)) <$>
          stepsW (hashRP P) (toB (digestOfState st))
            (wAbsW π.proof.stream 24 (bytesAt π.proof.stream 0 24) (rec4Rounds κ nV np)) := by
  rw [ChainSpecW.chain, runMW_eq, map_bind, hashRP, bind_map_left]
  refine bind_congr fun st => ?_
  show (uSpec4 κ nV np).chalsOf <$> ((fun x => (toB (digestOfState st), tailOfState st) :: x) <$>
      stepsW (hashRP P) (toB (digestOfState st))
        ((uSpec4 κ nV np).absorbsS (uView4 κ nV np π).1 (uSpec4 κ nV np).K.rounds (uView4 κ nV np π).2)) = _
  rw [absorbsS_uView4 κ nV np π h, Functor.map_map]

/-- **The Keccak walk at π1-rec4's verdict and result** are `walkOf3` of what `obsOf3` keeps of `reduceWithK4`'s run
from the seed's channel. -/
theorem runWithK4_pair (P : KeccakState → m KeccakState) (shape : UniStatement.Shape) (iv input : List UInt8)
    (stream : Array UInt8) (v : KeccakVariant) (mode : ClaimsMode) :
    (fun o : UniStatement.Outcome => (o.accepts, o.result)) <$> runWithK4 P shape iv input stream v mode =
      seedWith P iv input >>= fun seed => (fun x => walkOf3 (obsOf3 x)) <$>
        (reduceWithK4 P shape (publicWordsOf input) v mode).run.run (Chan.start seed stream) := by
  simp only [runWithK4, map_bind]
  congr 1
  funext seed
  simp only [ExceptT.run_bind, StateT.run_bind, bind_assoc]
  rw [map_eq_bind_pure_comp]
  congr 1
  funext x
  rcases x with ⟨r, c⟩
  cases r with
  | error e => simp [walkOf3, obsOf3, UniStatement.Outcome.accepts]
  | ok a =>
    simp only [StateT.run_bind, finish_run]
    split_ifs with h <;> simp [walkOf3, obsOf3, UniStatement.Outcome.accepts, h]

end Chain

/-! ## WALK -/

/-- **WALK** (π1-rec4): on a stream of π1-rec4's length, the deployed walk is the wide chain: its verdict `uAccB4`,
its result `uOut4`, at the chain's challenges over Keccak-256's rate (`hashRP P`). -/
theorem uniWalkK4 (D : KDeployment) (κ nV np : ℕ) (C : UniCodeK4 D κ nV np) : UniWalkK4 D κ nV np C := by
  intro m _ _ P π hlen
  have hsz : π.proof.stream.size = 24 + roundsBytes (rec4Rounds κ nV np) + 24 * 3 := hlen
  have h6 : D.shape.heights.length = 6 := D.valid.1
  have hrows : countsAt π.proof.stream 0 6 = (uSt4 κ nV np π).2 := countsAt_rows _ (by omega)
  rw [runWithK4_pair]
  have hlink : ∀ c, (fun x => walkOf3 (obsOf3 x)) <$>
      (reduceWithK4 P D.shape (publicWordsOf π.input.toList) keccakRec4 .point).run.run c =
      (fun x => walkOf3 (obsOf3 x)) <$>
        (readCounts D.shape.heights >>= fun rows => (C.prog π.input rows).runW P).run.run c := by
    intro c
    have h := congrArg (fun z => walkOf3 <$> z) (C.link π.input P c)
    simpa only [Functor.map_map] using h
  simp only [hlink]
  have hrc : ∀ seed : Digest,
      (readCounts D.shape.heights >>= fun rows => (C.prog π.input rows).runW P).run.run
          (Chan.start seed π.proof.stream) =
        ((C.prog (uSt4 κ nV np π).1 (uSt4 κ nV np π).2).runW P).run.run
          (collectZ { Chan.start seed π.proof.stream with cursor := 24 }
            (countZeros D.shape.heights (uSt4 κ nV np π).2)) := by
    intro seed
    rw [run_bind_ok (readCounts_ok D.shape.heights _ (by simp only [Chan.start, h6]; omega))]
    simp only [Chan.start, h6, hrows]
    rfl
  simp only [hrc]
  have hpr : ∀ seed : Digest,
      ((C.prog (uSt4 κ nV np π).1 (uSt4 κ nV np π).2).runW P).run.run
          (collectZ { Chan.start seed π.proof.stream with cursor := 24 }
            (countZeros D.shape.heights (uSt4 κ nV np π).2)) =
        progOutW (C.prog (uSt4 κ nV np π).1 (uSt4 κ nV np π).2)
            (collectZ { Chan.start seed π.proof.stream with cursor := 24 }
              (countZeros D.shape.heights (uSt4 κ nV np π).2)) <$>
          stepsW (hashRP P) (toB seed)
            (wAbsW π.proof.stream 24 (bytesAt π.proof.stream 0 24) (rec4Rounds κ nV np)) := by
    intro seed
    rw [progRunW _ P _ (by simp [collectZ, Chan.start])
      (by simp only [collectZ, Chan.start, C.rounds_eq, C.tail_eq]; omega)
      (by rw [C.pv_eq, C.rounds_eq]; exact pvFits_rec4 κ nV np)
      (by rw [C.rounds_eq]; exact rec4Rounds_ns_le κ nV np)]
    simp only [preOf, collectZ, Chan.start, toList_extract_eq, C.rounds_eq, Nat.sub_zero]
  simp only [hpr]
  rw [seedWith, keccak256With_eq, bind_map_left, chain_uSpec4 κ nV np P π (by omega), map_bind]
  refine congrArg (fun f => keccak256StateWith P (name ++ π.iv.toList ++ π.input.toList) >>= f)
    (funext fun st => ?_)
  rw [Functor.map_map, Functor.map_map]
  refine map_stepsW_congr _ _ _ _ _ fun as has => ?_
  rw [length_wAbsW] at has
  set Pg := C.prog (uSt4 κ nV np π).1 (uSt4 κ nV np π).2 with hPg
  set c1 := collectZ { Chan.start (digestOfState st) π.proof.stream with cursor := 24 }
    (countZeros D.shape.heights (uSt4 κ nV np π).2) with hc1
  set ch := (uSpec4 κ nV np).chalsOf ((toB (digestOfState st), tailOfState st) :: as) with hch
  have hd : c1.data = π.proof.stream := rfl
  have hcu : c1.cursor = 24 := rfl
  have hz0 : c1.zeros.toList = countZeros D.shape.heights (uSt4 κ nV np π).2 := by
    simp only [hc1, collectZ, Chan.start, foldl_push_toList, List.nil_append]
  have hlen' : Pg.rounds.length ≤ as.length := by rw [C.rounds_eq, has]
  have hN : (runOutW Pg Pg.rounds [] c1 as).1 = uDone4 κ nV np π ch := by
    rw [runOutW_done, C.rounds_eq, C.pv_eq, List.nil_append]
    rfl
  have htl : scalarsAt (runOutW Pg Pg.rounds [] c1 as).2.data (runOutW Pg Pg.rounds [] c1 as).2.cursor
      Pg.tail = uTail4 κ nV np π := by
    rw [runOutW_data, runOutW_cursor _ _ _ _ _ hlen', C.rounds_eq, C.tail_eq, hd, hcu]
    rfl
  have hcur : (progOutW Pg c1 as).2.cursor = (progOutW Pg c1 as).2.data.size := by
    rw [progOutW_cursor _ _ _ hlen', progOutW_data, C.rounds_eq, C.tail_eq, hd, hcu]
    omega
  rw [walkOf3_ok _ _ (progOutW_fst Pg c1 as) hcur, hN, htl]
  refine Prod.ext ?_ rfl
  show _ = uAccB4 D κ nV np C π ch
  rw [Bool.eq_iff_iff, all_zero_iff, uAccB4, @decide_eq_true_iff _ (Classical.propDecidable _),
    progOutW_zeros, hN, htl, hz0]
  unfold UAcc4 ChainProg.ZerosVanish
  have hzf := zerosFrom_iff Pg.toChainProg [] (uDone4 κ nV np π ch)
  simp only [List.nil_append] at hzf
  rw [← hzf]
  simp only [List.mem_append]
  constructor
  · intro h
    exact ⟨fun z hz => h z (Or.inl (Or.inl hz)), fun z hz => h z (Or.inl (Or.inr hz)),
      fun z hz => h z (Or.inr hz)⟩
  · rintro ⟨h1, h2, h3⟩ z ((hz | hz) | hz)
    exacts [h1 z hz, h2 z hz, h3 z hz]

/-! ## WALK REJECTS -/

/-- **π1-rec4's wide chain program consumes its length**, `uLen4`. -/
theorem consumes_main4 (D : KDeployment) (κ nV np : ℕ) (C : UniCodeK4 D κ nV np) (input : Vector UInt8 32)
    (P : KeccakState → OC KeccakState) :
    Consumes (uLen4 κ nV np) (readCounts D.shape.heights >>= fun rows => (C.prog input rows).runW P) := by
  refine ((consumes_readCounts _).bind (k := roundsBytes (rec4Rounds κ nV np) + (3 * 24 + (0 + 0)))
    fun rows => ?_).mono_eq ?_
  · have h := consumes_runW (C.prog input rows) P (by rw [C.pv_eq, C.rounds_eq]; exact pvFits_rec4 κ nV np)
    rw [C.rounds_eq, C.tail_eq] at h
    exact h
  · rw [D.valid.1, uLen4]
    ring

/-- **WALK REJECTS** (π1-rec4): on a stream of another length, every outcome of the deployed walk rejects. -/
theorem uniWalkRejectK4 (D : KDeployment) (κ nV np : ℕ) (C : UniCodeK4 D κ nV np) :
    UniWalkRejectK4 D κ nV np := by
  intro π hne o ho
  have key := runWithK4_pair (m := OC) Common.queryPermutation D.shape π.iv.toList π.input.toList
    π.proof.stream keccakRec4 .point
  have h1 : (o.accepts, o.result) ∈ support ((fun o : UniStatement.Outcome => (o.accepts, o.result)) <$>
      runWithK4 Common.queryPermutation D.shape π.iv.toList π.input.toList π.proof.stream
        keccakRec4 .point) := by
    rw [support_map]
    exact ⟨o, ho, rfl⟩
  rw [key, mem_support_bind_iff] at h1
  obtain ⟨seed, -, h2⟩ := h1
  have hl := congrArg (fun z => walkOf3 <$> z)
    (C.link π.input Common.queryPermutation (Chan.start seed π.proof.stream))
  simp only [Functor.map_map] at hl
  rw [hl, support_map] at h2
  obtain ⟨y, hy, hyo⟩ := h2
  have hc := consumes_main4 D κ nV np C π.input Common.queryPermutation
    (Chan.start seed π.proof.stream) y (by simp [Chan.start]) hy
  have hacc : (walkOf3 (obsOf3 y)).1 = false := by
    rcases y with ⟨r, c'⟩
    cases r with
    | error e => rfl
    | ok a =>
      obtain ⟨h3, h4, -⟩ := hc a rfl
      simp only [Chan.start] at h3 h4
      simp only [obsOf3, walkOf3]
      split_ifs with h
      · exact absurd (by rw [← h3, ← h, h4, Nat.zero_add]) hne
      · rfl
  have := congrArg Prod.fst hyo
  simp only at this
  rw [← this]
  exact hacc

end UniKeccakSound.Rec4

/-- info: 'UniKeccakSound.Rec4.uniWalkK4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Rec4.uniWalkK4

/-- info: 'UniKeccakSound.Rec4.uniWalkRejectK4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Rec4.uniWalkRejectK4
