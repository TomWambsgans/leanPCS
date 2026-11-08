-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The Keccak main line's `Fs/WalkK.lean` at π1-rec3's
-- shape (`runWithK … keccakRec3`, the link up to `obsOf3`), as `UniSound/Rec3/FsWalkProof3.lean`.
import UniKeccakSound.Fs.CoupleK3
import UniKeccakSound.Fs.WalkK
import UniSound.Rec3.FsWalkProof3

/-!
# The Keccak walk at π1-rec3's shape is the chain (`UniWalkK3`, `UniWalkRejectK3`)

`WalkK.lean`'s two halves at `keccakRec3`, for **every** deployment, Flock phase, `nV`, `np` and link `C`: the walk's
verdict and result are `walkOf3` of what `obsOf3` keeps of `reduceWithK`'s run (`runWithK_pair3`; π1-rec3's batch
records its narrow challenges in the channel, which `obsOf3` and the chain never read), the code-level link
(`UniCodeK3.link`, up to `obsOf3`) replaces it by `readCounts` then `C.prog`, and `UniSound/FsWalkProof.lean`'s
generic lemmas do the rest (`uniWalkK3`, `uniWalkRejectK3`).
-/

namespace UniKeccakSound

open Compose QuotientRpm LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics UniStatement UniSound UniKeccak
open OracleSpec OracleComp

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.layoutWordsK UniKeccak.setupStackK

section Walk

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3) (nV np : ℕ)
  (C : UniCodeK3 D F3 nV np)

/-- **The stream's length π1-rec3 reads**: the row counts' `24` bytes, the rounds' messages, the tail's three
scalars. -/
def uLenK3 : ℕ := 24 + roundsBytes (uRoundsK3 F3 nV np) + 24 * 3

/-- **The walk accepts**: the row counts' range checks vanish, and every value the chain program requires zero
does. -/
def UAccK3 (π : UPf) (ch : List (List E)) : Prop :=
  (∀ z ∈ countZeros D.shape.heights (uStK3 F3 nV np π).2, z = 0) ∧
    (C.prog (uStK3 F3 nV np π).1 (uStK3 F3 nV np π).2).ZerosVanish (uDone (uRoundsK3 F3 nV np) π ch)
      (uTailK (uRoundsK3 F3 nV np) π)

open Classical in
/-- `UAccK3` as a verdict. -/
noncomputable def uAccBK3 (π : UPf) (ch : List (List E)) : Bool := decide (UAccK3 D F3 nV np C π ch)

/-- **WALK**: on a stream of π1-rec3's length, in every lawful monad and over every permutation, the Keccak
walk's verdict and result are the chain's challenges read by `uAccBK3` and the chain program's result `uOutK3`. -/
def UniWalkK3 : Prop :=
  ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (P : KeccakState → m KeccakState) (π : UPf),
    π.proof.stream.size = uLenK3 F3 nV np →
      (fun o : UniStatement.Outcome => (o.accepts, o.result)) <$>
          runWithK P D.shape π.iv.toList π.input.toList π.proof.stream keccakRec3 .point =
        (fun ch => (uAccBK3 D F3 nV np C π ch,
            (Except.ok (uOutK3 D F3 nV np C π ch) : Except UniError Reduced))) <$>
          (uSpecK3 F3 nV np).chain (fun x => toB <$> keccak256With P x) (uView (uRoundsK3 F3 nV np) π).1
            (uView (uRoundsK3 F3 nV np) π).2

/-- **WALK REJECTS**: on a stream of any other length, every outcome of the Keccak walk over `π` rejects. -/
def UniWalkRejectK3 : Prop :=
  ∀ π : UPf, π.proof.stream.size ≠ uLenK3 F3 nV np →
    ∀ o ∈ support (runWithK Common.queryPermutation D.shape π.iv.toList π.input.toList
      π.proof.stream keccakRec3 .point), o.accepts = false

end Walk

/-! ## The walk's wrapper -/

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **The Keccak walk's verdict and result** are `walkOf3` of what `obsOf3` keeps of `reduceWithK`'s run from the
seed's channel. -/
theorem runWithK_pair3 (P : KeccakState → m KeccakState) (shape : UniStatement.Shape) (iv input : List UInt8)
    (stream : Array UInt8) (v : KeccakVariant) (mode : ClaimsMode) :
    (fun o : Outcome => (o.accepts, o.result)) <$> runWithK P shape iv input stream v mode =
      seedWith P iv input >>= fun seed => (fun x => walkOf3 (obsOf3 x)) <$>
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
  | error e => simp [walkOf3, obsOf3, Outcome.accepts]
  | ok a =>
    simp only [StateT.run_bind, finish_run]
    split_ifs with h <;> simp [walkOf3, obsOf3, Outcome.accepts, h]

end Monad

/-! ## WALK -/

/-- **WALK**: on a stream of π1-rec3's length, the Keccak walk is the chain: its verdict `uAccBK3`, its result
`uOutK3`, at the chain's challenges over Keccak-256 `= keccak256With P`. -/
theorem uniWalkK3 (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (nV np : ℕ) (C : UniCodeK3 D F3 nV np) : UniWalkK3 D F3 nV np C := by
  intro m _ _ P π hlen
  have hsz : π.proof.stream.size = 24 + roundsBytes (uRoundsK3 F3 nV np) + 24 * 3 := hlen
  have hsz' : π.proof.stream.size = 24 + roundsBytes (rec3Rounds F3.prog.rounds nV np) + 24 * 3 := hlen
  have h6 : D.shape.heights.length = 6 := D.valid.1
  have hrows : countsAt π.proof.stream 0 6 = (uStK3 F3 nV np π).2 := countsAt_rows _ (by omega)
  rw [runWithK_pair3]
  have hlink : ∀ c, (fun x => walkOf3 (obsOf3 x)) <$>
      (reduceWithK P D.shape (publicWordsOf π.input.toList) keccakRec3 .point).run.run c =
      (fun x => walkOf3 (obsOf3 x)) <$>
        (readCounts D.shape.heights >>= fun rows => (C.prog π.input rows).run P).run.run c := by
    intro c
    have h := congrArg (fun z => walkOf3 <$> z) (C.link π.input P c)
    simpa only [Functor.map_map] using h
  simp only [hlink]
  have hrc : ∀ seed : Digest,
      (readCounts D.shape.heights >>= fun rows => (C.prog π.input rows).run P).run.run
          (Chan.start seed π.proof.stream) =
        ((C.prog (uStK3 F3 nV np π).1 (uStK3 F3 nV np π).2).run P).run.run
          (collectZ { Chan.start seed π.proof.stream with cursor := 24 }
            (countZeros D.shape.heights (uStK3 F3 nV np π).2)) := by
    intro seed
    rw [run_bind_ok (readCounts_ok D.shape.heights _ (by simp only [Chan.start, h6]; omega))]
    simp only [Chan.start, h6, hrows]
    rfl
  simp only [hrc]
  have hpr : ∀ seed : Digest,
      ((C.prog (uStK3 F3 nV np π).1 (uStK3 F3 nV np π).2).run P).run.run
          (collectZ { Chan.start seed π.proof.stream with cursor := 24 }
            (countZeros D.shape.heights (uStK3 F3 nV np π).2)) =
        progOut (C.prog (uStK3 F3 nV np π).1 (uStK3 F3 nV np π).2)
            (collectZ { Chan.start seed π.proof.stream with cursor := 24 }
              (countZeros D.shape.heights (uStK3 F3 nV np π).2)) <$>
          steps (kB P) (toB seed)
            (wAbs π.proof.stream 24 (bytesAt π.proof.stream 0 24) (uRoundsK3 F3 nV np)) := by
    intro seed
    rw [progRun _ P _ (by simp [collectZ, Chan.start])
      (by simp only [collectZ, Chan.start, C.rounds_eq, C.tail_eq]; omega)]
    simp only [preOf, collectZ, Chan.start, toList_extract_eq, C.rounds_eq, Nat.sub_zero]
  simp only [hpr]
  rw [seedWith, keccak_eq, bind_map_left]
  change _ = _ <$> (uSpecK3 F3 nV np).chain (kB P) _ _
  rw [chainU_eq, map_bind, uView_eq]
  simp only [uniSpec_label, uniSpec_absorbsS, uniSpec_rounds, uniSpec_lim,
    rowBytes_toList _ (by omega : 24 ≤ π.proof.stream.size)]
  rw [absorbsI_wAbs π.proof.stream _ 0 24 _ (by omega)]
  simp only [↓reduceIte]
  refine congrArg (fun f => kB P (name ++ π.iv.toList ++ π.input.toList) >>= f) (funext fun st0 => ?_)
  rw [toB_ofB, Functor.map_map, Functor.map_map]
  refine congrArg (fun f => f <$> steps (kB P) st0
    (wAbs π.proof.stream 24 (bytesAt π.proof.stream 0 24) (uRoundsK3 F3 nV np))) (funext fun sts => ?_)
  set Pg := C.prog (uStK3 F3 nV np π).1 (uStK3 F3 nV np π).2 with hPg
  set c1 := collectZ { Chan.start (ofB st0) π.proof.stream with cursor := 24 }
    (countZeros D.shape.heights (uStK3 F3 nV np π).2) with hc1
  have hd : c1.data = π.proof.stream := rfl
  have hcu : c1.cursor = 24 := rfl
  have hz0 : c1.zeros.toList = countZeros D.shape.heights (uStK3 F3 nV np π).2 := by
    simp only [hc1, collectZ, Chan.start, foldl_push_toList, List.nil_append]
  set ch := groupK (uRoundsK3 F3 nV np) (List.map (chalL uLimbs) sts) with hch
  have hN : (runOut Pg Pg.rounds [] c1 sts).1 = uDone (uRoundsK3 F3 nV np) π ch := by
    rw [runOut_done, C.rounds_eq, List.nil_append, hd, hcu]
    rfl
  have htl : scalarsAt (runOut Pg Pg.rounds [] c1 sts).2.data (runOut Pg Pg.rounds [] c1 sts).2.cursor
      Pg.tail = uTailK (uRoundsK3 F3 nV np) π := by
    rw [runOut_data, runOut_cursor, C.rounds_eq, C.tail_eq, hd, hcu]
    rfl
  have hcur : (progOut Pg c1 sts).2.cursor = (progOut Pg c1 sts).2.data.size := by
    rw [progOut_cursor, progOut_data, C.rounds_eq, C.tail_eq, hd, hcu]
    omega
  rw [walkOf3_ok _ _ (progOut_fst Pg c1 sts) hcur, hN, htl]
  refine Prod.ext ?_ rfl
  show _ = uAccBK3 D F3 nV np C π ch
  rw [Bool.eq_iff_iff, all_zero_iff, uAccBK3, @decide_eq_true_iff _ (Classical.propDecidable _),
    progOut_zeros, hN, htl, hz0]
  unfold UAccK3 ChainProg.ZerosVanish
  have hzf := zerosFrom_iff Pg [] (uDone (uRoundsK3 F3 nV np) π ch)
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

/-- **The Keccak code at π1-rec3's shape consumes its length**, `uLenK3`. -/
theorem consumes_mainK3 (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (nV np : ℕ) (C : UniCodeK3 D F3 nV np) (input : Vector UInt8 32) (P : KeccakState → OC KeccakState) :
    Consumes (uLenK3 F3 nV np) (readCounts D.shape.heights >>= fun rows => (C.prog input rows).run P) := by
  refine ((consumes_readCounts _).bind (k := roundsBytes (uRoundsK3 F3 nV np) + (3 * 24 + (0 + 0)))
    fun rows => ?_).mono_eq ?_
  · have h := consumes_run (C.prog input rows) P
    rw [C.rounds_eq, C.tail_eq] at h
    exact h
  · rw [D.valid.1, uLenK3]
    ring

/-- **WALK REJECTS**: on a stream of another length, every outcome of the Keccak walk over `π` rejects. -/
theorem uniWalkRejectK3 (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (nV np : ℕ) (C : UniCodeK3 D F3 nV np) : UniWalkRejectK3 D F3 nV np := by
  intro π hne o ho
  have key := runWithK_pair3 (m := OC) Common.queryPermutation D.shape π.iv.toList π.input.toList
    π.proof.stream keccakRec3 .point
  have h1 : (o.accepts, o.result) ∈ support ((fun o : Outcome => (o.accepts, o.result)) <$>
      runWithK Common.queryPermutation D.shape π.iv.toList π.input.toList π.proof.stream
        keccakRec3 .point) := by
    rw [support_map]
    exact ⟨o, ho, rfl⟩
  rw [key, mem_support_bind_iff] at h1
  obtain ⟨seed, -, h2⟩ := h1
  have hl := congrArg (fun z => walkOf3 <$> z)
    (C.link π.input Common.queryPermutation (Chan.start seed π.proof.stream))
  simp only [Functor.map_map] at hl
  rw [hl, support_map] at h2
  obtain ⟨y, hy, hyo⟩ := h2
  have hc := consumes_mainK3 D F3 nV np C π.input Common.queryPermutation
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

end UniKeccakSound

/-- info: 'UniKeccakSound.uniWalkK3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniWalkK3

/-- info: 'UniKeccakSound.uniWalkRejectK3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniWalkRejectK3
