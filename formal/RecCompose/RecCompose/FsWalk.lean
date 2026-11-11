-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md; conventions: see AGENTS.md. The port of
-- `formal/UniSound/UniSound/FsWalkProof.lean`
-- (`uniWalk`, `uniWalkReject`) to π2's run (`formal/RecStatement/RecStatement/Verifier.lean`: `reduceWith`, `runWith`),
-- with that file's channel lemmas (`nextRoot_ok`, `nextScalars_ok`, `sample_bind`, `steps`, `wAbs`, `absorbsI_wAbs`,
-- `chainU_eq`) and `formal/RecCompose/RecCompose/Pi2Run.lean`'s (`runWith_post`).
import RecCompose.FsDefs
import UniSound.FsWalkProof

/-!
# π2's walk is the chain (`Pi2Walk`, `Pi2WalkReject`)

The verifier bridge's walk (`FsDefs.lean`) for π2's run at the real circuit `cc`, proved with no hypothesis:

* **`pi2Walk : Pi2Walk`**: on a stream of `544` bytes, in every lawful monad and over every permutation, `runWith`'s
  verdict and result (on the frame words of the declared claims, `frameOf`) are the chain's challenges
  (`pi2Spec.chain` over `keccak256With F`) read by `p2Reduced`: the seed is the label's hash
  (`name ‖ iv ‖ input ‖ frame words`, `frameList`); the reads (the three frame words) read no stream byte, hash nothing
  and collect `pi2Pubs` (`forIn_bind_run`); then `W`'s commitment and `α, β, γ` (the first sample absorbs `W`'s root and
  answer), `Q`'s and `t`, the `16` fold values, `ξ`, `s` and `ρ` (`reduceWith_bind_run`); `finish` finds the stream read
  to its end.
* **`pi2WalkReject : Pi2WalkReject`**: on a stream of another length the run fails (`runWith_post`: a success reads
  `pi2Bytes = 544` bytes), so it rejects.
* **`pi2Scalars_real`**: the contract's public scalars (`pi2Scalars`, the run over Keccak-f[1600] at any IV) are
  `pi2Pubs` on a stream of `544` bytes; **`pi2Pubs_cc`**: they are the input's four words and the three frame words'.

Decisions: the walk is computed in continuation form, one read or sample at a time, against the chain's steps peeled
one at a time (`steps_cons_bind`); the reads loop by an equation-form `ROk` (`rok_forIn`; `Pi2Run.lean`'s `Reads` gives
postconditions only). `Spec.of cc` is read through `reads` and `logRow` only (`spec_reads`, `spec_logRow`, by `rfl`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics
open UniStatement (Chan ChanM publicWordsOf)
open OracleSpec OracleComp

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.setupStack

/-! ## The circuit's reads -/

theorem spec_reads : (Spec.of cc).reads = Data.reads := rfl

theorem spec_logRow : (Spec.of cc).logRow = 4 := rfl

theorem reads_bytes : (Data.reads.map Read.bytes).sum = pLen := by decide

theorem pi2Bytes_cc : pi2Bytes (Spec.of cc) = sLen := by
  unfold pi2Bytes
  rw [spec_reads, spec_logRow, reads_bytes]
  rfl

/-! ## Reads that hash nothing, as equations -/

section ROk

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **`X` reads `n` bytes and hashes nothing**: from a channel with `n` bytes left it returns `v` of the data and the
cursor, the cursor advanced by `n`. -/
def ROk {α : Type} (X : ChanM m α) (n : ℕ) (v : Array UInt8 → ℕ → α) : Prop :=
  ∀ c : Chan, c.cursor + n ≤ c.data.size →
    X.run.run c = pure (.ok (v c.data c.cursor), { c with cursor := c.cursor + n })

theorem rok_forIn {γ β : Type} (k : γ → ℕ) (g : Array UInt8 → ℕ → γ → β → β)
    (f : γ → β → ChanM m (ForInStep β)) (hf : ∀ x b, ROk (f x b) (k x) fun d cur => .yield (g d cur x b)) :
    ∀ (l : List γ) (b : β), ROk (forIn l b f) ((l.map k).sum) fun d cur => foldReads k g d cur l b
  | [], b => by
    intro c _
    simp only [List.forIn_nil, List.map_nil, List.sum_nil, foldReads, Nat.add_zero]
    rfl
  | x :: l, b => by
    intro c hc
    simp only [List.map_cons, List.sum_cons] at hc
    rw [List.forIn_cons, UniSound.run_bind_ok (hf x b c (by omega))]
    simp only
    rw [rok_forIn k g f hf l _ _ (by simp only; omega)]
    simp only [foldReads, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- **A `for` loop that hashes nothing, then a continuation**. -/
theorem forIn_bind_run {γ β δ : Type} (k : γ → ℕ) (g : Array UInt8 → ℕ → γ → β → β)
    {f : γ → β → ChanM m (ForInStep β)} (hf : ∀ x b, ROk (f x b) (k x) fun d cur => .yield (g d cur x b))
    (l : List γ) (b : β) (K : β → ChanM m δ) (c : Chan) (hc : c.cursor + (l.map k).sum ≤ c.data.size) :
    (forIn l b f >>= K).run.run c =
      (K (foldReads k g c.data c.cursor l b)).run.run { c with cursor := c.cursor + (l.map k).sum } :=
  UniSound.run_bind_ok (rok_forIn k g f hf l b c hc)

theorem nextInteger_okN (n : ℕ) (c : Chan) (h : c.cursor + n ≤ c.data.size) :
    (UniStatement.nextInteger (m := m) n).run.run c =
      pure (.ok (integerAt c.data c.cursor n), { c with cursor := c.cursor + n }) := by
  simp only [UniStatement.nextInteger, ExceptT.run_bind, StateT.run_bind, UniSound.takeBytes_ok n c h, pure_bind,
    ExceptT.run_pure, StateT.run_pure]
  rfl

theorem nextNarrow_ok (c : Chan) (h : c.cursor + 20 ≤ c.data.size) :
    (RecStatement.nextNarrow (m := m)).run.run c =
      pure (.ok (narrowAt c.data c.cursor), { c with cursor := c.cursor + 20 }) := by
  simp only [RecStatement.nextNarrow, ExceptT.run_bind, StateT.run_bind, UniSound.takeBytes_ok 20 c h, pure_bind,
    ExceptT.run_pure, StateT.run_pure]
  rfl

end ROk

theorem halfAt_eq (d : Array UInt8) (cur : ℕ) (h : cur + 16 ≤ d.size) :
    halfAt d cur = UniStatement.eNew (UniStatement.beWordAt d (cur + 8)) (UniStatement.beWordAt d cur) 0 := by
  unfold halfAt
  dsimp only
  rw [UniSound.beWordAt_extract d cur 16 8 h (by norm_num), UniSound.beWordAt_extract d cur 16 0 h (by norm_num)]
  rfl

theorem scalarAt_eq (d : Array UInt8) (cur : ℕ) (h : cur + 24 ≤ d.size) :
    RecCompose.scalarAt d cur = UniSound.scalarAt d cur := by
  unfold RecCompose.scalarAt UniSound.scalarAt
  dsimp only
  rw [UniSound.beWordAt_extract d cur 24 16 h (by norm_num), UniSound.beWordAt_extract d cur 24 8 h (by norm_num),
    UniSound.beWordAt_extract d cur 24 0 h (by norm_num)]
  rfl

/-! ## The public data -/

theorem extract_congr (d d' : Array UInt8) (a c : ℕ) (hd : c ≤ d.size) (hd' : c ≤ d'.size)
    (h : ∀ i, a ≤ i → i < c → d.getD i 0 = d'.getD i 0) : d.extract a c = d'.extract a c := by
  apply Array.ext
  · simp only [Array.size_extract]
    omega
  · intro i h1 h2
    simp only [Array.size_extract] at h1
    simp only [Array.getElem_extract]
    have := h (a + i) (by omega) (by omega)
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega : a + i < d.size),
      Array.getElem?_eq_getElem (by omega : a + i < d'.size), Option.getD_some] at this
    exact this

theorem readValue_congr (fa : ℕ → List UInt8) (d d' : Array UInt8) (cur : ℕ) (rd : Read) (N : ℕ)
    (hN : cur + rd.bytes ≤ N) (hd : N ≤ d.size) (hd' : N ≤ d'.size) (h : ∀ i, i < N → d.getD i 0 = d'.getD i 0) :
    readValue fa d cur rd = readValue fa d' cur rd := by
  have hc : ∀ a n, a + n ≤ N → d.extract a (a + n) = d'.extract a (a + n) := fun a n hn ↦
    extract_congr d d' a (a + n) (by omega) (by omega) fun i _ hi ↦ h i (by omega)
  cases rd with
  | integer b =>
    simp only [Read.bytes] at hN
    simp only [readValue, integerAt, hc cur b hN]
  | root =>
    simp only [Read.bytes] at hN
    simp only [readValue, halfAt, hc cur 16 (by omega), hc (cur + 16) 16 (by omega)]
  | scalar =>
    simp only [Read.bytes] at hN
    simp only [readValue, RecCompose.scalarAt, hc cur 24 hN]
  | narrow =>
    simp only [Read.bytes] at hN
    simp only [readValue, narrowAt, hc cur 20 hN]
  | frame p => rfl

/-- **The real circuit's public scalars**: the input's four words, then the three frame words' (no stream byte). -/
theorem pi2Pubs_cc (input : List UInt8) (fa : ℕ → List UInt8) (d : Array UInt8) :
    pi2Pubs (Spec.of cc) input fa d =
      publicWordsOf input ++ publicWordsOf (fa 0) ++ publicWordsOf (fa 1) ++ publicWordsOf (fa 2) := by
  unfold pi2Pubs
  rw [spec_reads]
  rfl

/-- The real circuit's public scalars read the frame's payloads `0, 1, 2` only. -/
theorem pi2Pubs_cc_congr (input : List UInt8) (fa fa' : ℕ → List UInt8) (d d' : Array UInt8)
    (h : ∀ p < 3, fa p = fa' p) : pi2Pubs (Spec.of cc) input fa d = pi2Pubs (Spec.of cc) input fa' d' := by
  rw [pi2Pubs_cc, pi2Pubs_cc, h 0 (by decide), h 1 (by decide), h 2 (by decide)]

/-! ## The contract's public scalars -/

/-- **The contract's public scalars are `pi2Pubs`** on a stream of `544` bytes (the run over Keccak-f[1600] at any
IV, at the real circuit, on the frame words of the declared claims). -/
theorem pi2Scalars_real (D : RecDeployment) (hD : ∀ roots, (D.pi2 roots).circuit = cc) (roots : RecSetupRoots)
    (input : Vector UInt8 32) (proof : RecProof) (h : proof.stream.size = sLen) :
    pi2Scalars D roots input proof =
      pi2Pubs (Spec.of cc) input.toList (frameOf proof.pi1Claims) proof.stream := by
  have hc : (D.circuitAt roots.pi1).circuit = cc := hD _
  unfold pi2Scalars
  rw [hc]
  have hh := holds_id (runWith_post (m := Id) (fun x ↦ pure (keccakF1600 x)) (Spec.of cc) [] input.toList
    (frameOf proof.pi1Claims) proof.stream)
  obtain ⟨r, hr⟩ := hh.2 (by rw [pi2Bytes_cc]; exact h)
  obtain ⟨-, hsc, -⟩ := hh.1 r hr
  have hrun : RecStatement.run (Spec.of cc) [] input.toList (frameOf proof.pi1Claims) proof.stream =
      Id.run (runWith (m := Id) (fun x ↦ pure (keccakF1600 x)) (Spec.of cc) [] input.toList
        (frameOf proof.pi1Claims) proof.stream) := rfl
  rw [hrun, hr]
  exact hsc

/-! ## WALK REJECTS -/

theorem holds_support_oc {ι : Type} {spec : OracleSpec ι} {α : Type} {X : OracleComp spec α} {P : α → Prop}
    (hX : Holds X P) : ∀ x ∈ support X, P x := by
  intro x hx
  have h : (x, P x) ∈ support ((fun x ↦ (x, P x)) <$> X) := by
    rw [support_map]; exact ⟨x, hx, rfl⟩
  unfold Holds at hX
  rw [hX, support_map] at h
  obtain ⟨y, -, hy⟩ := h
  have := congrArg Prod.snd hy
  simp only at this
  exact this ▸ trivial

/-- **WALK REJECTS**: on a stream of another length than `544`, the run fails, so it rejects. -/
theorem pi2WalkReject : Pi2WalkReject := by
  intro π hlen o ho
  have hh := holds_support_oc (runWith_post Common.queryPermutation (Spec.of cc) π.iv.toList π.input.toList
    (frameOf π.proof.pi1Claims) π.proof.stream) o ho
  unfold RecStatement.Outcome.accepts
  rcases hres : o.result with e | r
  · rfl
  · exact absurd ((hh.1 r hres).1.trans pi2Bytes_cc) hlen

/-! ## The walk -/

/-- The bytes each of the chain's steps absorbs, on a stream of `544` bytes: `W`'s commitment, nothing twice, `Q`'s
commitment, the `18` values. -/
def p2Es (b : Array UInt8) : List (List UInt8) :=
  [UniSound.bytesAt b 0 56, [], [], UniSound.bytesAt b 56 56, UniSound.bytesAt b 112 432]

/-- **The run's result** from the frame, the stream and the chain's answers. -/
def red0 (stmt : List E) (fa : ℕ → List UInt8) (b : Array UInt8) (sts : List Bytes32) : RecStatement.Reduced :=
  let pubs := foldReads Read.bytes (pubsStep fa) b 0 Data.reads stmt
  let x := sts.map (chalL UniSound.uLimbs)
  let inp : Inputs E := ⟨pubs, x.getD 0 0, x.getD 1 0, x.getD 2 0, x.getD 3 0, UniSound.scalarsAt b 112 16,
    UniSound.scalarAt b 496, UniSound.scalarAt b 520, x.getD 4 0⟩
  ⟨pubs, pubs.map pairPoint, (UniSound.halvesAt b 0, UniSound.halvesAt b 56),
    (UniSound.scalarAt b 32, UniSound.scalarAt b 88), inp, (Spec.of cc).core.run inp⟩

/-- **The channel at the run's end** from the stream and the chain's answers. -/
def cw (b : Array UInt8) (sts : List Bytes32) : Chan :=
  ⟨b, sLen, sLen, ofB (sts.getD 4 default), (sts.map (chalL UniSound.uLimbs)).toArray, #[]⟩

section Walk

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem bind_eq_of {α β : Type} {x x' : m α} {f f' : α → m β} (hx : x = x') (hf : ∀ a, f a = f' a) :
    x >>= f = x' >>= f' := by
  subst hx
  exact bind_congr hf

theorem steps_cons_bind {β : Type} (H : List UInt8 → m Bytes32) (st : Bytes32) (e : List UInt8)
    (es : List (List UInt8)) (f : List Bytes32 → m β) :
    UniSound.steps H st (e :: es) >>= f =
      H (stepIn st e) >>= fun st' => UniSound.steps H st' es >>= fun l => f (st' :: l) := by
  simp only [UniSound.steps, bind_assoc, bind_map_left]

theorem nextRoot_bind {β : Type} (K : E × E → ChanM m β) (c : Chan) (h : c.cursor + 32 ≤ c.data.size) :
    (UniStatement.nextRoot >>= K).run.run c =
      (K (UniSound.halvesAt c.data c.cursor)).run.run { c with cursor := c.cursor + 32 } :=
  UniSound.run_bind_ok (UniSound.nextRoot_ok c h)

theorem nextScalar_bind {β : Type} (K : E → ChanM m β) (c : Chan) (h : c.cursor + 24 ≤ c.data.size) :
    (UniStatement.nextScalar >>= K).run.run c =
      (K (UniSound.scalarAt c.data c.cursor)).run.run { c with cursor := c.cursor + 24 } :=
  UniSound.run_bind_ok (UniSound.nextScalar_ok c h)

theorem nextScalars_bind {β : Type} (n : ℕ) (K : List E → ChanM m β) (c : Chan)
    (h : c.cursor + 24 * n ≤ c.data.size) :
    (UniStatement.nextScalars n >>= K).run.run c =
      (K (UniSound.scalarsAt c.data c.cursor n)).run.run { c with cursor := c.cursor + 24 * n } :=
  UniSound.run_bind_ok (UniSound.nextScalars_ok n c h)

set_option maxHeartbeats 1600000 in
/-- **π2's reduction on a stream of `544` bytes**, in continuation form: the chain's steps on `p2Es` from the seed,
the result `red0` and the channel `cw`. -/
theorem reduceWith_bind_run {δ : Type} (F : KeccakState → m KeccakState) (b : Array UInt8) (hb : b.size = sLen)
    (stmt : List E) (fa : ℕ → List UInt8) (seed : Digest) (K : RecStatement.Reduced → ChanM m δ) :
    (RecStatement.reduceWith F (Spec.of cc) stmt fa >>= K).run.run (Chan.start seed b) =
      UniSound.steps (UniSound.kB F) (toB seed) (p2Es b) >>= fun sts =>
        (K (red0 stmt fa b sts)).run.run (cw b sts) := by
  have hb' : b.size = 544 := hb
  unfold RecStatement.reduceWith
  rw [spec_logRow, spec_reads]
  simp only [bind_assoc, pure_bind]
  rw [forIn_bind_run Read.bytes (pubsStep fa) ?hf _ _ _ _ (by simp only [Chan.start, reads_bytes, pLen]; omega)]
  case hf =>
    intro x pubs c hc
    cases x with
    | integer n =>
      simp only [Read.bytes] at hc
      simp only
      rw [UniSound.run_bind_ok (nextInteger_okN n c hc)]
      rfl
    | root =>
      simp only [Read.bytes] at hc
      simp only
      rw [UniSound.run_bind_ok (UniSound.nextRoot_ok c hc)]
      simp only [pubsStep, readValue, halfAt_eq c.data c.cursor (by omega),
        halfAt_eq c.data (c.cursor + 16) (by omega)]
      rfl
    | scalar =>
      simp only [Read.bytes] at hc
      simp only
      rw [UniSound.run_bind_ok (UniSound.nextScalar_ok c hc)]
      simp only [pubsStep, readValue, scalarAt_eq c.data c.cursor hc]
      rfl
    | narrow =>
      simp only [Read.bytes] at hc
      simp only
      rw [UniSound.run_bind_ok (nextNarrow_ok c hc)]
      rfl
    | frame p =>
      rfl
  -- `W`'s root and out-of-domain answer
  rw [nextRoot_bind _ _ ?_]
  swap
  · simp only [Chan.start, reads_bytes, pLen]
    omega
  rw [nextScalar_bind _ _ ?_]
  swap
  · simp only [Chan.start, reads_bytes, pLen]
    omega
  -- `α`: `W`'s commitment absorbed
  rw [UniSound.sample_bind, p2Es, steps_cons_bind]
  refine bind_eq_of ?_ fun s1 => ?_
  · simp only [UniSound.preOf, Chan.start, UniSound.toList_extract_eq, reads_bytes, pLen]
  -- `β`, `γ`
  rw [UniSound.sample_bind, steps_cons_bind]
  refine bind_eq_of (by rw [UniSound.toB_sampOne, UniSound.preOf_self _ rfl]) fun s2 => ?_
  rw [UniSound.sample_bind, steps_cons_bind]
  refine bind_eq_of (by rw [UniSound.toB_sampOne, UniSound.preOf_self _ rfl]) fun s3 => ?_
  -- `Q`'s root and out-of-domain answer
  rw [nextRoot_bind _ _ ?_]
  swap
  · simp only [UniSound.sampOne, Chan.start, reads_bytes, pLen]
    omega
  rw [nextScalar_bind _ _ ?_]
  swap
  · simp only [UniSound.sampOne, Chan.start, reads_bytes, pLen]
    omega
  -- `t`
  rw [UniSound.sample_bind, steps_cons_bind]
  refine bind_eq_of ?_ fun s4 => ?_
  · simp only [UniSound.preOf, UniSound.sampOne, Chan.start, UniSound.toList_extract_eq, reads_bytes, pLen,
      UniSound.toB_ofB]
  -- the fold values, `ξ`
  rw [nextScalars_bind _ _ _ ?_]
  swap
  · simp only [UniSound.sampOne, Chan.start, reads_bytes, pLen]
    omega
  rw [nextScalar_bind _ _ ?_]
  swap
  · simp only [UniSound.sampOne, Chan.start, reads_bytes, pLen]
    omega
  rw [nextScalar_bind _ _ ?_]
  swap
  · simp only [UniSound.sampOne, Chan.start, reads_bytes, pLen]
    omega
  -- `ρ`
  rw [UniSound.sample_bind, steps_cons_bind]
  refine bind_eq_of ?_ fun s5 => ?_
  · simp only [UniSound.preOf, UniSound.sampOne, Chan.start, UniSound.toList_extract_eq, reads_bytes, pLen,
      UniSound.toB_ofB]
    rfl
  rw [UniSound.steps, pure_bind]
  rfl

theorem finish_cw (b : Array UInt8) (hb : b.size = sLen) (sts : List Bytes32) {β : Type}
    (g : PUnit → ChanM m β) :
    (UniStatement.finish >>= g).run.run (cw b sts) = (g ()).run.run (cw b sts) := by
  refine UniSound.run_bind_ok ?_
  rw [RecCompose.finish_run, ite_eq_left (show (cw b sts).cursor = (cw b sts).data.size from hb.symm)]

end Walk

/-! ## The chain's statement and messages, read off -/

theorem roundsBytes_pi2 : UniSound.roundsBytes (RecPiop.pi2Rounds 4) = 544 := by
  simp [UniSound.roundsBytes, UniSound.roundBytes, RecPiop.pi2Rounds]

/-- **The rounds' messages** the stream carries: `W`'s commitment at byte `0` (its root, its out-of-domain answer),
`Q`'s at `56`, the `18` values from `112`. -/
theorem p2Msgs_eq (π : P2Pf) :
    p2Msgs π = [(some (UniSound.halvesAt π.proof.stream 0), [UniSound.scalarAt π.proof.stream 32]),
      (some (UniSound.halvesAt π.proof.stream 56), [UniSound.scalarAt π.proof.stream 88]),
      (none, (List.range 18).map fun k => UniSound.scalarAt π.proof.stream (112 + 24 * k))] := by
  unfold p2Msgs
  simp only [RecPiop.pi2Rounds, UniSound.msgsAt, UniSound.roundBytes, ↓reduceIte, Bool.false_eq_true,
    Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, pLen, List.range_one, List.map_cons,
    List.map_nil]

/-- **The bytes the chain absorbs** are `p2Es`: `W`'s commitment, then `Q`'s, then the values. -/
theorem absorbsS_p2 (π : P2Pf) (h : π.proof.stream.size = sLen) :
    pi2Spec.absorbsS (p2View π).1 pi2Spec.K.rounds (p2View π).2 = p2Es π.proof.stream := by
  have hb : π.proof.stream.size = 544 := h
  have h2 : pi2Spec.enc = UniSound.uniEnc := rfl
  have hf : pi2Spec.encAt (p2View π).1 = fun j m => if j = 0 then ([] : List UInt8) ++
      UniSound.uniEnc m else UniSound.uniEnc m := by
    funext j m
    rw [ChainSpecU.encAt, h2]
    rfl
  have hv : (p2View π).2 = (UniSound.msgsAt π.proof.stream pLen (RecPiop.pi2Rounds 4)).map UniSound.toRMsg := rfl
  have hr : UniSound.roundsBytes (RecPiop.pi2Rounds 4) = 544 := roundsBytes_pi2
  rw [ChainSpecU.absorbsS, hf, hv, pi2Spec_rounds,
    UniSound.absorbsI_wAbs _ _ 0 pLen _ (hr ▸ hb ▸ (by decide : pLen + 544 ≤ 544))]
  simp only [↓reduceIte, p2Es, RecPiop.pi2Rounds, UniSound.wAbs, UniSound.roundBytes]
  simp only [↓reduceIte, Bool.false_eq_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, List.replicate,
    List.nil_append, List.cons_append, pLen, Nat.zero_add]

theorem getD_take_map {α : Type} (l : List α) (n i : ℕ) (d : α) (h : i < n) : (l.take n).getD i d = l.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, h, ite_true]

theorem getD_drop {α : Type} (l : List α) (n i : ℕ) (d : α) : (l.drop n).getD i d = l.getD (n + i) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **The frame words of the composed view are the declared claims'** (payloads `0, 1, 2`). -/
theorem stOf_p2View_eq (π : P2Pf) (d : Array UInt8) :
    (stOf (p2View π).1).2 = pi2Pubs (Spec.of cc) π.input.toList (frameOf π.proof.pi1Claims) d :=
  pi2Pubs_cc_congr _ _ _ _ _ fun p hp ↦ frameAtB_frameBytes π.proof p hp

/-- **The transcript's inputs** at the chain's challenges. -/
theorem p2Inputs_eq (π : P2Pf) (_h : π.proof.stream.size = sLen) (sts : List Bytes32) :
    p2Inputs π (groupK (RecPiop.pi2Rounds 4) (sts.map (chalL UniSound.uLimbs))) =
      ⟨foldReads Read.bytes (pubsStep (frameOf π.proof.pi1Claims)) π.proof.stream 0 Data.reads
          (publicWordsOf π.input.toList),
        (sts.map (chalL UniSound.uLimbs)).getD 0 0, (sts.map (chalL UniSound.uLimbs)).getD 1 0,
        (sts.map (chalL UniSound.uLimbs)).getD 2 0, (sts.map (chalL UniSound.uLimbs)).getD 3 0,
        UniSound.scalarsAt π.proof.stream 112 16, UniSound.scalarAt π.proof.stream 496,
        UniSound.scalarAt π.proof.stream 520, (sts.map (chalL UniSound.uLimbs)).getD 4 0⟩ := by
  have hs : (stOf (p2View π).1).2 =
      foldReads Read.bytes (pubsStep (frameOf π.proof.pi1Claims)) π.proof.stream 0 Data.reads
        (publicWordsOf π.input.toList) := by
    rw [stOf_p2View_eq π π.proof.stream]
    unfold pi2Pubs
    rw [spec_reads]
  unfold p2Inputs
  rw [hs, p2Msgs_eq]
  simp only [groupK, RecPiop.pi2Rounds, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd]
  simp only [getD_take_map _ _ _ _ (by norm_num : (0 : ℕ) < 3), getD_take_map _ _ _ _ (by norm_num : (1 : ℕ) < 3),
    getD_take_map _ _ _ _ (by norm_num : (2 : ℕ) < 3), getD_take_map _ _ _ _ (by norm_num : (0 : ℕ) < 1),
    getD_drop, Nat.reduceAdd]
  have ha : List.take 16 (List.map (fun k => UniSound.scalarAt π.proof.stream (112 + 24 * k)) (List.range 18)) =
      UniSound.scalarsAt π.proof.stream 112 16 := by
    rw [← List.map_take, List.take_range]
    rfl
  have hξ : (List.map (fun k => UniSound.scalarAt π.proof.stream (112 + 24 * k)) (List.range 18)).getD 16 0 =
      UniSound.scalarAt π.proof.stream 496 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by norm_num)]
    rfl
  have hs' : (List.map (fun k => UniSound.scalarAt π.proof.stream (112 + 24 * k)) (List.range 18)).getD 17 0 =
      UniSound.scalarAt π.proof.stream 520 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by norm_num)]
    rfl
  rw [ha, hξ, hs']

/-- **The run's result is `p2Reduced`** at the chain's challenges. -/
theorem red0_eq (π : P2Pf) (h : π.proof.stream.size = sLen) (sts : List Bytes32) :
    red0 (publicWordsOf π.input.toList) (frameOf π.proof.pi1Claims) π.proof.stream sts =
      p2Reduced π (groupK (RecPiop.pi2Rounds 4) (sts.map (chalL UniSound.uLimbs))) := by
  unfold red0 p2Reduced p2Out
  rw [p2Inputs_eq π h sts, p2Msgs_eq]
  rfl

/-! ## WALK -/

/-- **The seed's input is the label**: `name ‖ iv ‖ input ‖ frame words`. -/
theorem seed_label (π : P2Pf) :
    RecStatement.name ++ π.iv.toList ++ π.input.toList ++
        (frameReads (Spec.of cc).reads).flatMap (frameOf π.proof.pi1Claims) = pi2Spec.label (p2View π).1 := by
  show _ = p2Label (π.iv, π.input, frameBytes π.proof)
  unfold p2Label
  rw [frameBytes_toList, spec_reads]
  rfl

/-- **WALK**: on a stream of `544` bytes, π2's run is the chain over `keccak256With F`, its verdict and result read
off `p2Reduced` at the chain's challenges. -/
theorem pi2Walk : Pi2Walk := by
  intro m _ _ F π hlen
  unfold RecStatement.runWith
  dsimp only
  rw [seed_label, UniSound.keccak_eq, bind_map_left]
  change _ = _ <$> pi2Spec.chain (UniSound.kB F) _ _
  rw [UniSound.chainU_eq, absorbsS_p2 π hlen, map_bind, map_bind]
  refine bind_eq_of rfl fun st0 => ?_
  rw [reduceWith_bind_run F π.proof.stream hlen _ _ (ofB st0), UniSound.toB_ofB]
  simp only [finish_cw π.proof.stream hlen, ExceptT.run_pure, StateT.run_pure, bind_assoc, pure_bind, map_bind,
    map_pure, Functor.map_map]
  rw [map_eq_bind_pure_comp]
  refine bind_congr fun sts => ?_
  simp only [Function.comp_apply, red0_eq π hlen sts]
  rfl

end RecCompose

/-- info: 'RecCompose.pi2Walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2Walk

/-- info: 'RecCompose.pi2WalkReject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2WalkReject

/-- info: 'RecCompose.pi2Scalars_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2Scalars_real
