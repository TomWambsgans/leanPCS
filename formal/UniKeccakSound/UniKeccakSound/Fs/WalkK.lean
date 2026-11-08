-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `UniSound/FsWalk.lean` and `UniSound/FsWalkProof.lean`
-- (`uniWalk`, `uniWalkReject`, whose generic lemmas are reused) for the Keccak walk, `formal/UniKeccak`'s `runWithK`.
import UniKeccakSound.Fs.CoupleK
import UniSound.FsWalkProof

/-!
# The Keccak walk is the chain (`UniWalkK`, `UniWalkRejectK`)

The verifier bridge's two halves at the walk, for the Keccak verifier (`runWithK`: the seed, `reduceWithK`,
`finish`), proved for **every** Keccak deployment, Flock phase, `nV`, `V` and code-level link `C` (no hypothesis):

* **`uniWalkK : UniWalkK D Fl nV V C`**: on a stream of `uLenK` bytes (the row counts' `24`, the rounds' messages,
  the tail's three scalars), in every lawful monad and over every permutation, the walk's verdict and result are
  `uAccBK` and `uOutK` at the chain's challenges over Keccak-256 `= keccak256With F`;
* **`uniWalkRejectK : UniWalkRejectK D Fl nV V`**: on a stream of another length, every outcome of the walk over the
  random permutation's oracles rejects.

The proofs are `UniSound.uniWalk`'s and `uniWalkReject`'s, through the code-level link `C.link` (`reduceWithK` is
`readCounts` then `C.prog`), with `UniSound/FsWalkProof.lean`'s generic lemmas (`progRun`, `readCounts_ok`,
`absorbsI_wAbs`, `walkOf_ok`, `Consumes`, `consumes_run`, `consumes_readCounts`).
-/

namespace UniKeccakSound

open Compose QuotientRpm LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics UniStatement UniSound UniKeccak
open OracleSpec OracleComp

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.layoutWordsK UniKeccak.setupStackK

section Walk

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain) (nV V : ℕ)
  (C : UniCodeK D Fl nV V)

/-- **The stream's length the main line reads**: the row counts' `24` bytes, the rounds' messages, the tail's three
scalars. -/
def uLenK : ℕ := 24 + roundsBytes (uRoundsK Fl nV V) + 24 * 3

/-- **The walk accepts**: the row counts' range checks vanish, and every value the chain program requires zero
does. -/
def UAccK (π : UPf) (ch : List (List E)) : Prop :=
  (∀ z ∈ countZeros D.shape.heights (uStK Fl nV V π).2, z = 0) ∧
    (C.prog (uStK Fl nV V π).1 (uStK Fl nV V π).2).ZerosVanish (uDone (uRoundsK Fl nV V) π ch)
      (uTailK (uRoundsK Fl nV V) π)

open Classical in
/-- `UAccK` as a verdict. -/
noncomputable def uAccBK (π : UPf) (ch : List (List E)) : Bool := decide (UAccK D Fl nV V C π ch)

/-- **WALK**: on a stream of the main line's length, in every lawful monad and over every permutation, the Keccak
walk's verdict and result are the chain's challenges read by `uAccBK` and the chain program's result `uOutK`. -/
def UniWalkK : Prop :=
  ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (P : KeccakState → m KeccakState) (π : UPf),
    π.proof.stream.size = uLenK Fl nV V →
      (fun o : UniStatement.Outcome => (o.accepts, o.result)) <$>
          runWithK P D.shape π.iv.toList π.input.toList π.proof.stream keccakMain .point =
        (fun ch => (uAccBK D Fl nV V C π ch,
            (Except.ok (uOutK D Fl nV V C π ch) : Except UniError Reduced))) <$>
          (uSpecK Fl nV V).chain (fun x => toB <$> keccak256With P x) (uView (uRoundsK Fl nV V) π).1
            (uView (uRoundsK Fl nV V) π).2

/-- **WALK REJECTS**: on a stream of any other length, every outcome of the Keccak walk over `π` rejects. -/
def UniWalkRejectK : Prop :=
  ∀ π : UPf, π.proof.stream.size ≠ uLenK Fl nV V →
    ∀ o ∈ support (runWithK Common.queryPermutation D.shape π.iv.toList π.input.toList
      π.proof.stream keccakMain .point), o.accepts = false

end Walk

/-! ## The walk's wrapper -/

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **The Keccak walk's verdict and result** are `walkOf` of what `obsOf` keeps of `reduceWithK`'s run from the
seed's channel. -/
theorem runWithK_pair (P : KeccakState → m KeccakState) (shape : UniStatement.Shape) (iv input : List UInt8)
    (stream : Array UInt8) (v : KeccakVariant) (mode : ClaimsMode) :
    (fun o : Outcome => (o.accepts, o.result)) <$> runWithK P shape iv input stream v mode =
      seedWith P iv input >>= fun seed => (fun x => walkOf (obsOf x)) <$>
        (reduceWithK P shape (publicWordsOf input) v mode).run.run (Chan.start seed stream) := by
  simp only [runWithK, map_bind]
  congr 1
  funext seed
  simp only [ExceptT.run_bind, StateT.run_bind, bind_assoc]
  rw [map_eq_bind_pure_comp]
  congr 1
  funext x
  rcases x with ⟨r, c⟩
  cases r with
  | error e => simp [walkOf, obsOf, Outcome.accepts]
  | ok a =>
    simp only [StateT.run_bind, finish_run]
    split_ifs with h <;> simp [walkOf, obsOf, Outcome.accepts, h]

end Monad

/-! ## WALK -/

/-- **WALK**: on a stream of the main line's length, the Keccak walk is the chain: its verdict `uAccBK`, its result
`uOutK`, at the chain's challenges over Keccak-256 `= keccak256With P`. -/
theorem uniWalkK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (nV V : ℕ) (C : UniCodeK D Fl nV V) : UniWalkK D Fl nV V C := by
  intro m _ _ P π hlen
  have hsz : π.proof.stream.size = 24 + roundsBytes (uRoundsK Fl nV V) + 24 * 3 := hlen
  have hsz' : π.proof.stream.size = 24 + roundsBytes (uniRounds Fl.prog.rounds nV V) + 24 * 3 := hlen
  have h6 : D.shape.heights.length = 6 := D.valid.1
  have hrows : countsAt π.proof.stream 0 6 = (uStK Fl nV V π).2 := countsAt_rows _ (by omega)
  rw [runWithK_pair]
  have hlink : ∀ c, (fun x => walkOf (obsOf x)) <$>
      (reduceWithK P D.shape (publicWordsOf π.input.toList) keccakMain .point).run.run c =
      (fun x => walkOf (obsOf x)) <$>
        (readCounts D.shape.heights >>= fun rows => (C.prog π.input rows).run P).run.run c := by
    intro c
    have h := congrArg (fun z => walkOf <$> z) (C.link π.input P c)
    simpa only [Functor.map_map] using h
  simp only [hlink]
  have hrc : ∀ seed : Digest,
      (readCounts D.shape.heights >>= fun rows => (C.prog π.input rows).run P).run.run
          (Chan.start seed π.proof.stream) =
        ((C.prog (uStK Fl nV V π).1 (uStK Fl nV V π).2).run P).run.run
          (collectZ { Chan.start seed π.proof.stream with cursor := 24 }
            (countZeros D.shape.heights (uStK Fl nV V π).2)) := by
    intro seed
    rw [run_bind_ok (readCounts_ok D.shape.heights _ (by simp only [Chan.start, h6]; omega))]
    simp only [Chan.start, h6, hrows]
    rfl
  simp only [hrc]
  have hpr : ∀ seed : Digest,
      ((C.prog (uStK Fl nV V π).1 (uStK Fl nV V π).2).run P).run.run
          (collectZ { Chan.start seed π.proof.stream with cursor := 24 }
            (countZeros D.shape.heights (uStK Fl nV V π).2)) =
        progOut (C.prog (uStK Fl nV V π).1 (uStK Fl nV V π).2)
            (collectZ { Chan.start seed π.proof.stream with cursor := 24 }
              (countZeros D.shape.heights (uStK Fl nV V π).2)) <$>
          steps (kB P) (toB seed)
            (wAbs π.proof.stream 24 (bytesAt π.proof.stream 0 24) (uRoundsK Fl nV V)) := by
    intro seed
    rw [progRun _ P _ (by simp [collectZ, Chan.start])
      (by simp only [collectZ, Chan.start, C.rounds_eq, C.tail_eq]; omega)]
    simp only [preOf, collectZ, Chan.start, toList_extract_eq, C.rounds_eq, Nat.sub_zero]
  simp only [hpr]
  rw [seedWith, keccak_eq, bind_map_left]
  change _ = _ <$> (uSpecK Fl nV V).chain (kB P) _ _
  rw [chainU_eq, map_bind, uView_eq]
  simp only [uniSpec_label, uniSpec_absorbsS, uniSpec_rounds, uniSpec_lim,
    rowBytes_toList _ (by omega : 24 ≤ π.proof.stream.size)]
  rw [absorbsI_wAbs π.proof.stream _ 0 24 _ (by omega)]
  simp only [↓reduceIte]
  refine congrArg (fun f => kB P (name ++ π.iv.toList ++ π.input.toList) >>= f) (funext fun st0 => ?_)
  rw [toB_ofB, Functor.map_map, Functor.map_map]
  refine congrArg (fun f => f <$> steps (kB P) st0
    (wAbs π.proof.stream 24 (bytesAt π.proof.stream 0 24) (uRoundsK Fl nV V))) (funext fun sts => ?_)
  set Pg := C.prog (uStK Fl nV V π).1 (uStK Fl nV V π).2 with hPg
  set c1 := collectZ { Chan.start (ofB st0) π.proof.stream with cursor := 24 }
    (countZeros D.shape.heights (uStK Fl nV V π).2) with hc1
  have hd : c1.data = π.proof.stream := rfl
  have hcu : c1.cursor = 24 := rfl
  have hz0 : c1.zeros.toList = countZeros D.shape.heights (uStK Fl nV V π).2 := by
    simp only [hc1, collectZ, Chan.start, foldl_push_toList, List.nil_append]
  set ch := groupK (uRoundsK Fl nV V) (List.map (chalL uLimbs) sts) with hch
  have hN : (runOut Pg Pg.rounds [] c1 sts).1 = uDone (uRoundsK Fl nV V) π ch := by
    rw [runOut_done, C.rounds_eq, List.nil_append, hd, hcu]
    rfl
  have htl : scalarsAt (runOut Pg Pg.rounds [] c1 sts).2.data (runOut Pg Pg.rounds [] c1 sts).2.cursor
      Pg.tail = uTailK (uRoundsK Fl nV V) π := by
    rw [runOut_data, runOut_cursor, C.rounds_eq, C.tail_eq, hd, hcu]
    rfl
  have hcur : (progOut Pg c1 sts).2.cursor = (progOut Pg c1 sts).2.data.size := by
    rw [progOut_cursor, progOut_data, C.rounds_eq, C.tail_eq, hd, hcu]
    omega
  rw [walkOf_ok _ _ (progOut_fst Pg c1 sts) hcur, hN, htl]
  refine Prod.ext ?_ rfl
  show _ = uAccBK D Fl nV V C π ch
  rw [Bool.eq_iff_iff, all_zero_iff, uAccBK, @decide_eq_true_iff _ (Classical.propDecidable _),
    progOut_zeros, hN, htl, hz0]
  unfold UAccK ChainProg.ZerosVanish
  have hzf := zerosFrom_iff Pg [] (uDone (uRoundsK Fl nV V) π ch)
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

/-- **The Keccak main line consumes the main line's length**, `uLenK`. -/
theorem consumes_mainK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (nV V : ℕ) (C : UniCodeK D Fl nV V) (input : Vector UInt8 32) (P : KeccakState → OC KeccakState) :
    Consumes (uLenK Fl nV V) (readCounts D.shape.heights >>= fun rows => (C.prog input rows).run P) := by
  refine ((consumes_readCounts _).bind (k := roundsBytes (uRoundsK Fl nV V) + (3 * 24 + (0 + 0)))
    fun rows => ?_).mono_eq ?_
  · have h := consumes_run (C.prog input rows) P
    rw [C.rounds_eq, C.tail_eq] at h
    exact h
  · rw [D.valid.1, uLenK]
    ring

/-- **WALK REJECTS**: on a stream of another length, every outcome of the Keccak walk over `π` rejects. -/
theorem uniWalkRejectK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (nV V : ℕ) (C : UniCodeK D Fl nV V) : UniWalkRejectK D Fl nV V := by
  intro π hne o ho
  have key := runWithK_pair (m := OC) Common.queryPermutation D.shape π.iv.toList π.input.toList
    π.proof.stream keccakMain .point
  have h1 : (o.accepts, o.result) ∈ support ((fun o : Outcome => (o.accepts, o.result)) <$>
      runWithK Common.queryPermutation D.shape π.iv.toList π.input.toList π.proof.stream
        keccakMain .point) := by
    rw [support_map]
    exact ⟨o, ho, rfl⟩
  rw [key, mem_support_bind_iff] at h1
  obtain ⟨seed, -, h2⟩ := h1
  have hl := congrArg (fun z => walkOf <$> z)
    (C.link π.input Common.queryPermutation (Chan.start seed π.proof.stream))
  simp only [Functor.map_map] at hl
  rw [hl, support_map] at h2
  obtain ⟨y, hy, hyo⟩ := h2
  have hc := consumes_mainK D Fl nV V C π.input Common.queryPermutation
    (Chan.start seed π.proof.stream) y (by simp [Chan.start]) hy
  have hacc : (walkOf (obsOf y)).1 = false := by
    rcases y with ⟨r, c'⟩
    cases r with
    | error e => rfl
    | ok a =>
      obtain ⟨h3, h4, -⟩ := hc a rfl
      simp only [Chan.start] at h3 h4
      simp only [obsOf, walkOf]
      split_ifs with h
      · exact absurd (by rw [← h3, ← h, h4, Nat.zero_add]) hne
      · rfl
  have := congrArg Prod.fst hyo
  simp only at this
  rw [← this]
  exact hacc

end UniKeccakSound

/-- info: 'UniKeccakSound.uniWalkK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniWalkK

/-- info: 'UniKeccakSound.uniWalkRejectK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniWalkRejectK
