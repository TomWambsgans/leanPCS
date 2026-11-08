-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The program is `formal/UniKeccak`'s `reduceWithK` at
-- `keccakRec3` (`Verifier.lean`; `batchK` at `.rec3`: `sumcheckPairsDrawn`, narrow draws); Flock's phase is cited
-- through `KFlockSound.link`. The proof is `formal/UniSound/UniSound/Rec3/CodeLink3.lean`'s (`uniCode3`) and
-- `Rec3/CodeBatch3.lean`'s (`batchFs3_eq`) on the Keccak verifier.
import UniSound.Rec3.CodeLink3
import UniKeccakSound.Code.Link
import UniKeccakSound.FinalK3

/-!
# The Keccak verifier's code-level link at π1-rec3's shape (`UniCodeK3`)

**`uniCodeK3 D F3 hκ np hV : UniCodeK3 D F3 valsCountK np`** (and `uniCodeK3At` at any `nV = valsCountK`), for every
deployment `D` whose batch has `2 np + 1` variables (`hV : varsOf (layoutsOfK D.shape) = 2 * np + 1`) and every
Flock phase `F3 : KFlockSound F κ keccakRec3` with `D.shape.heights.getD opBlake2s 0 = κ`: after the row counts,
`reduceWithK` at the deployment's shape, `keccakRec3`, point claims, is the chain program `main3ProgK` on
`rec3Rounds F3.prog.rounds valsCountK np`, with a tail of three, up to `obsOf3`. Its rounds:

* `C1`'s root and **three** challenges `c, β, γ` (`drawRun .rec3 4` is one draw and `squares c 4`);
* Flock's rounds on the Keccak-f block (`F3.link`; its zeros, the structured terminal among them, are the main
  program's there, its tail zeros the `C2` round's);
* `C2`'s root and `t`; the `valsCountK` values at `t` (as the main line's) and `ρ, λ`;
* the batch's `np` pair rounds (`8` scalars, one draw) and its last plain round (`2` scalars, one draw): the chain
  draws `x`, the program reads `narrowE x` (`batchPureWK narrowE`), where the verifier draws `narrowE x` itself
  (`sampleNarrow`); the two agree up to the channel's record of the challenges, which `obsOf3` does not keep;

then the three stacks' values, the terminal zero `sum + last` (`batchPureWK`), and the result (`main3OutK`).

**Why `hV`**: `rec3Rounds` has a last plain round, so the batch's variables must be odd; the verifier's own rounds
are `batchNvs (varsOf …)` (`vars / 2` pairs, `vars % 2` plain rounds). `uniCodeK3Odd` takes
`np = varsOf (layoutsOfK D.shape) / 2` and the oddness instead. At the reference shape `varsOf = 27`, `np = 13`.

Also **`uniOutRootsK3_uniCodeK3At`** (`UniOutRootsK3`: the result names the roots of rounds `0` and `nF + 1`) and
**`countsZeroK3_of_fits`** (the chain program's zeros vanishing put the row counts in range).
-/

namespace UniKeccakSound

open UniStatement UniSound UniKeccak LeanVM.Parameters LeanVM.Semantics FlockSound.Uni

/-! ## The batch at π1-rec3's shape -/

/-- **What the Keccak batch computes at π1-rec3's shape** from `λ`, its records `brs` (each challenge read through
`nw`) and the stacks' values `tl`: the terminal zero `sum + last` and the point claims (`batchPureW` with
`weightAtK`, no bit-slice claim). -/
def batchPureWK (nw : E → E) (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List E)) (lambda : E) (brs : Done) (tl : List E) :
    List E × List (Commitment × Opening) :=
  let fo := batchFoldK combined layouts ringMap lambda
    (pointAfter3 cantorBeta1 nw (varsOf layouts / 2) (roundsOf brs)) tl
  ([fo.1 + claimAfter3 nw (varsOf layouts / 2) (batchTarget combined lambda).1 (roundsOf brs)], fo.2.2.toList)

/-- **The batch's result on narrowed records is the PIOP's reading of the raw ones.** -/
theorem batchPureWK_narrow (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List E)) (lambda : E) (brs : Done) (tl : List E) :
    batchPureWK id combined layouts ringMap lambda (brs.map narrowRec) tl =
      batchPureWK narrowE combined layouts ringMap lambda brs tl := by
  unfold batchPureWK
  rw [roundsOf_narrow, claimAfter3_narrow, pointAfter3_narrow]

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **The Keccak batch at π1-rec3's shape** (`batchK P .rec3`): `λ`, the rounds `batchNvs vars`, the stacks'
values, the terminal zero, the result (`batchPureWK id`). -/
theorem batchK3_eq (P : KeccakState → m KeccakState) (combined : List (Commitment × Combined))
    (layouts : List (Commitment × StackLayout)) (ringMap : Option (List E)) :
    batchK P .rec3 combined layouts ringMap = (do
      let lambda ← sample P
      let brs ← readRoundsN P (batchNvs (varsOf layouts))
      let tl ← nextScalars (m := m) combined.length
      ChainProg.requireZeros (batchPureWK id combined layouts ringMap lambda brs tl).1
      pure (batchPureWK id combined layouts ringMap lambda brs tl).2) := by
  unfold batchK
  refine bind_congr fun lambda => ?_
  have hv : (layouts.map (·.2.vars)).foldl max 0 = varsOf layouts := rfl
  simp only [hv]
  rw [← bind_assoc, bind_pure_comp, sumcheckPairsDrawn_eq, bind_map_left]
  refine bind_congr fun brs => ?_
  refine bind_congr fun values => ?_
  simp [batchPureWK, batchFoldK, batchTarget, layoutOf, varsOf, ChainProg.requireZeros]

end Monad

/-! ## The program -/

/-- **The result at π1-rec3's shape** from its rounds' records (`C1`'s round `r0`: `c, β, γ`; Flock's `fd`; `C2`'s
`r2`; the values' `r3`; the batch's `brs`, raw draws) and the tail `tl`: the batch's zero and the `Reduced`. -/
def main3OutK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (input : Vector UInt8 32) (rows : List ℕ) (r0 : UMsg × List E) (fd : Done) (r2 r3 : UMsg × List E)
    (brs : Done) (tl : List E) : List E × Reduced :=
  let fl := F3.prog.out fd []
  let mr := mainRelsK D.shape (publicWordsOf input.toList) (countsBits D.shape.heights rows)
    (squares (r0.2.headD 0) 4) (r0.2.getD 1 0) (r0.2.getD 2 0) (r2.2.headD 0) r3.1.2
  let fc := flockClaimK mr.1 fl
  let combined := commitments.filterMap fun c => (combine fc.1.toList c (r3.2.headD 0)).map fun x => (c, x)
  let stackLayouts := layoutsK D.shape mr.2
  let bp := batchPureWK narrowE combined stackLayouts fc.2 (r3.2.getD 1 0) brs tl
  (bp.1, ⟨(r0.1.1.getD default, r2.1.1.getD default), bp.2, none, fc.1.size,
    stackLayouts.map fun x => (x.1, x.2.vars), stackLayouts⟩)

/-- **The chain program at π1-rec3's shape without the counts' zero.** -/
def main3Prog0K (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (np : ℕ) (input : Vector UInt8 32) (rows : List ℕ) : ChainProg Reduced where
  rounds := rec3Rounds F3.prog.rounds valsCountK np
  zeros := mainZerosK F3.prog
  tail := 3
  tailZeros done tl := (main3OutK D F3 input rows (done.getD 0 default)
    ((done.drop 1).take F3.prog.rounds.length) (done.getD (F3.prog.rounds.length + 1) default)
    (done.getD (F3.prog.rounds.length + 2) default) (done.drop (F3.prog.rounds.length + 3)) tl).1
  out done tl := (main3OutK D F3 input rows (done.getD 0 default)
    ((done.drop 1).take F3.prog.rounds.length) (done.getD (F3.prog.rounds.length + 1) default)
    (done.getD (F3.prog.rounds.length + 2) default) (done.drop (F3.prog.rounds.length + 3)) tl).2

/-- **The Keccak verifier at π1-rec3's shape as a chain program**: `main3Prog0K` with the counts' zero in round
`0`. -/
def main3ProgK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (np : ℕ) (input : Vector UInt8 32) (rows : List ℕ) : ChainProg Reduced :=
  (main3Prog0K D F3 np input rows).withHead [countsZeroK D.shape.heights rows]

section Defs

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3) (np : ℕ)
  (input : Vector UInt8 32) (rows : List ℕ)

theorem main3ProgK_rounds : (main3ProgK D F3 np input rows).rounds = rec3Rounds F3.prog.rounds valsCountK np :=
  rfl

theorem main3ProgK_tail : (main3ProgK D F3 np input rows).tail = 3 := rfl

/-- The zeros in round `0`: the counts' zero. -/
theorem main3ProgK_zeros_nil (msg : UMsg) :
    (main3ProgK D F3 np input rows).zeros [] msg = [countsZeroK D.shape.heights rows] := by
  simp [main3ProgK, ChainProg.withHead]

/-- After round `0`: Flock's zeros (in its rounds) and its tail zeros (in `C2`'s round). -/
theorem main3ProgK_zeros_ne {done : Done} (hd : done ≠ []) :
    (main3ProgK D F3 np input rows).zeros done = mainZerosK F3.prog done :=
  withHead_zeros_ne _ _ hd

/-- The tail's zeros: the batch's terminal `sum + last`. -/
theorem main3ProgK_tailZeros (done : Done) (tl : List E) :
    (main3ProgK D F3 np input rows).tailZeros done tl = (main3OutK D F3 input rows (done.getD 0 default)
      ((done.drop 1).take F3.prog.rounds.length) (done.getD (F3.prog.rounds.length + 1) default)
      (done.getD (F3.prog.rounds.length + 2) default) (done.drop (F3.prog.rounds.length + 3)) tl).1 := rfl

/-- The result. -/
theorem main3ProgK_out (done : Done) (tl : List E) :
    (main3ProgK D F3 np input rows).out done tl = (main3OutK D F3 input rows (done.getD 0 default)
      ((done.drop 1).take F3.prog.rounds.length) (done.getD (F3.prog.rounds.length + 1) default)
      (done.getD (F3.prog.rounds.length + 2) default) (done.drop (F3.prog.rounds.length + 3)) tl).2 := rfl

theorem main3Prog0K_rounds : (main3Prog0K D F3 np input rows).rounds = [⟨true, 0, 2⟩] ++ F3.prog.rounds ++
    [⟨true, 0, 0⟩, ⟨false, valsCountK, 1⟩] ++ (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩]) := by
  show rec3Rounds _ _ _ = _
  rw [rec3Rounds, List.append_assoc]

theorem main3Prog0K_zeros : (main3Prog0K D F3 np input rows).zeros = mainZerosK F3.prog := rfl

end Defs

theorem keccakRec3_fs : keccakRec3.fs = .rec3 := rfl

theorem mainZerosK_batch {β : Type} (FP : ChainProg β) (d : Done) (msg : UMsg)
    (h : FP.rounds.length + 3 ≤ d.length) : mainZerosK FP d msg = [] := by
  unfold mainZerosK
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-! ## The link -/

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

section Main

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3) (np : ℕ)
  (input : Vector UInt8 32) (rows : List ℕ)

theorem main3Prog0K_flock (P : KeccakState → m KeccakState) (x : UMsg × List E) :
    (main3Prog0K D F3 np input rows).runRounds P F3.prog.rounds ([] ++ [x]) =
      (fun d' => [] ++ [x] ++ d') <$> F3.prog.runRounds P F3.prog.rounds [] := by
  have h := runRounds_shift (main3Prog0K D F3 np input rows) F3.prog P ([] ++ [x]) F3.prog.rounds.length
    (fun e msg he => by rw [main3Prog0K_zeros]; exact mainZerosK_flock F3.prog x e msg he) F3.prog.rounds []
    (by simp)
  rw [List.append_nil] at h
  exact h

theorem main3Prog0K_batch (P : KeccakState → m KeccakState) (d : Done)
    (hd : F3.prog.rounds.length + 3 ≤ d.length) :
    (main3Prog0K D F3 np input rows).runRounds P (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩]) d =
      (fun e => d ++ e) <$> readRounds P (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩]) := by
  refine runRounds_noZeros _ P (F3.prog.rounds.length + 3) (fun d msg h => ?_) _ d (fun s hs => ?_) hd
  · rw [main3Prog0K_zeros]
    exact mainZerosK_batch F3.prog d msg h
  · simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hs
    rcases hs with ⟨-, rfl⟩ | rfl <;> rfl

end Main

/-- **The Keccak verifier's code-level link at π1-rec3's shape, observationally**, for the program without the
counts' zero. -/
theorem link3_obs0K (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (hκ : D.shape.heights.getD opBlake2s 0 = κ) (np : ℕ) (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1)
    (input : Vector UInt8 32) (P : KeccakState → m KeccakState) :
    ObsEq3 (reduceWithK P D.shape (publicWordsOf input.toList) keccakRec3 .point)
      (readCounts D.shape.heights >>= fun rows => (main3Prog0K D F3 np input rows).run P) := by
  have hv : D.shape.validate true = true := D.valid.2
  have ht : (ClaimsMode.point == ClaimsMode.point) = true := rfl
  unfold reduceWithK
  simp only [hv, Bool.not_true, Bool.false_eq_true, ite_false, ht, ite_true, countBits_eq,
    bind_map_left, keccakRec3_fs, drawRun, OfNat.ofNat_ne_zero, batchK3_eq, tablePart_eq, hκ, F3.link]
  refine ObsEq3.bind_right _ fun rows => ?_
  simp only [ChainProg.run]
  rw [main3Prog0K_rounds, show (main3Prog0K D F3 np input rows).tail = 3 from rfl, runRounds_append,
    runRounds_append, runRounds_append, runRounds_cons, main3Prog0K_zeros]
  simp only [rootRead, ite_true, mainZerosK_nil, nextScalars_zero, ChainProg.requireZeros, pure_bind,
    bind_map_left, bind_assoc, ChainProg.runRounds, Nat.reduceAdd, samples_three]
  -- Round 0: `C1`'s root, `c, β, γ`.
  refine ObsEq3.bind_right _ fun root1 => ?_
  refine ObsEq3.bind_right _ fun c => ?_
  refine ObsEq3.bind_right _ fun beta => ?_
  refine ObsEq3.bind_right _ fun gamma => ?_
  -- Flock's rounds (`F3.link`).
  rw [F3.tail_eq, nextScalars_zero, main3Prog0K_flock, runRounds_fix F3.prog P F3.prog.rounds []]
  simp only [pure_bind, bind_map_left, List.nil_append, List.length_nil, List.drop_zero, main3Prog0K_zeros]
  refine ObsEq3.bind_right _ fun fd => ?_
  -- `C2`'s root (Flock's tail zeros moved past it), `t`.
  refine ObsEq3.trans (ObsEq.obsEq3 (obsEq_requireZeros_nextRoot _ _)) ?_
  refine ObsEq3.bind_right _ fun root2 => ?_
  rw [mainZerosK_c2 F3.prog _ _ (length_fixDone _ _)]
  refine ObsEq3.bind_right _ fun _ => ?_
  rw [UniSound.samples_one]
  simp only [bind_map_left]
  refine ObsEq3.bind_right _ fun t => ?_
  -- The values at `t`.
  rw [forIn_reads_of tableReads (tablesStep D.shape.heights (eqKernel (squares c 4)) beta
    (digits t (max D.shape.heap.h (D.shape.constraintVars + 4) + 2)))]
  swap
  · intro table s
    simp [map_eq_bind_pure_comp, tablesStep]
  simp only [Bool.false_eq_true, ite_false, bind_assoc, pure_bind, samples_two]
  simp only [mainZerosK_vals F3.prog _ _ _ (length_fixDone _ _)]
  rw [show valsCountK = (tablesKeccak.map tableReads).sum + 7 from rfl,
    nextScalars_add, nextScalars_seven, nextScalars_fix (tablesKeccak.map tableReads).sum]
  simp only [ChainProg.requireZeros, bind_assoc, pure_bind, bind_map_left]
  refine ObsEq3.bind_right _ fun vt => ?_
  refine ObsEq3.bind_right _ fun a1 => ?_
  refine ObsEq3.bind_right _ fun a2 => ?_
  refine ObsEq3.bind_right _ fun a3 => ?_
  refine ObsEq3.bind_right _ fun a4 => ?_
  refine ObsEq3.bind_right _ fun a5 => ?_
  refine ObsEq3.bind_right _ fun a6 => ?_
  refine ObsEq3.bind_right _ fun a7 => ?_
  simp only [fixLen_fixLen]
  rcases hE : (F3.prog.out (fixDone F3.prog.rounds.length fd) []).2 with ⟨map, target⟩ | ⟨ws, value⟩
  all_goals
    simp only []
    refine ObsEq3.bind_right _ fun rho => ?_
    refine ObsEq3.bind_right _ fun lam => ?_
    rw [main3Prog0K_batch D F3 np input rows P _ (by simp)]
    simp only [bind_map_left]
    have hc2 := mainRelsK_c2 D.shape D.valid.1 (publicWordsOf input.toList) (countsBits D.shape.heights rows)
      (squares c 4) beta gamma t (fixLen (tablesKeccak.map tableReads).sum vt ++ [a1, a2, a3, a4, a5, a6, a7])
    simp only [mainRelsK, tablesReadsK, getD_fixLen_append, getD_fixLen_append_zero, List.getD_cons_zero,
      List.getD_cons_succ, List.take_left', length_fixLen] at hc2
    have hlen := mainCombinedK_length D.shape (publicWordsOf input.toList) (countsBits D.shape.heights rows)
      (squares c 4) beta gamma t (fixLen (tablesKeccak.map tableReads).sum vt ++ [a1, a2, a3, a4, a5, a6, a7])
      (F3.prog.out (fixDone F3.prog.rounds.length fd) []) rho
    simp only [mainRelsK, flockClaimK, hE, tablesReadsK, getD_fixLen_append, getD_fixLen_append_zero,
      List.getD_cons_zero, List.getD_cons_succ, List.take_left', length_fixLen] at hlen
    rw [hlen]
    refine ObsEq3.bind_chEq (φ := List.map narrowRec) ?_ (fun brs => ChEq.of_eq ?_ ?_)
      (fun _ => chObl_bind (chObl_nextScalars _) fun _ => chObl_bind (chObl_requireZeros _) fun _ =>
        chObl_pure _)
      (fun _ => chObl_bind (chObl_nextScalars _) fun _ => chObl_bind (chObl_requireZeros _) fun _ =>
        chObl_pure _)
      (chObl_readRounds P _)
    · rw [hc2, show layoutsK D.shape (Shape.c2ColumnsK D.shape) = layoutsOfK D.shape from rfl, hV, batchNvs_odd]
      exact chEq_batchRounds P np
    · refine bind_congr fun tl => ?_
      simp only [batchPureWK_narrow]
      simp only [main3Prog0K, decode_r0, decode_fd _ _ _ _ _ _ (length_fixDone _ _),
        decode_r2 _ _ _ _ _ _ (length_fixDone _ _), decode_r3 _ _ _ _ _ _ (length_fixDone _ _),
        decode_brs _ _ _ _ _ _ (length_fixDone _ _)]
      simp only [main3OutK, mainRelsK, flockClaimK, hE, tablesReadsK, getD_fixLen_append,
        getD_fixLen_append_zero, List.getD_cons_zero, List.getD_cons_succ, List.headD_cons, Option.getD_some,
        List.take_left', length_fixLen]
    · exact chObl_bind (chObl_nextScalars _) fun _ => chObl_bind (chObl_requireZeros _) fun _ => chObl_pure _

/-- **The counts' zero is invisible** (as `link_countsK`). -/
theorem link3_countsK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (np : ℕ) (input : Vector UInt8 32) (P : KeccakState → m KeccakState) :
    ObsEq (readCounts D.shape.heights >>= fun rows => (main3Prog0K D F3 np input rows).run P)
      (readCounts D.shape.heights >>= fun rows => (main3ProgK D F3 np input rows).run P) := by
  intro c
  have h1 : ObsEq (readCounts (m := m) D.shape.heights >>= fun rows => (main3ProgK D F3 np input rows).run P)
      (readCounts (m := m) D.shape.heights >>= fun rows =>
        ChainProg.requireZeros [countsZeroK D.shape.heights rows] >>= fun _ =>
          (main3Prog0K D F3 np input rows).run P) :=
    ObsEq.bind_right _ fun rows => obsEq_withHead (main3Prog0K D F3 np input rows)
      [countsZeroK D.shape.heights rows] P 2 _ rfl (funext fun msg => mainZerosK_nil F3.prog msg)
  rw [h1 c]
  obtain ⟨q, hq, hspec⟩ := readCounts_spec (m := m) D.shape.heights c
  rw [run_bind_of _ _ c q hq, run_bind_of _ _ c q hq]
  rcases q with ⟨r, c1⟩
  cases r with
  | error e => rfl
  | ok rows =>
    dsimp only
    refine (obsOf_requireZeros_of _ _ (obl_run _ P) c1 fun hz => ?_).symm
    obtain ⟨hl, hb⟩ := hspec rows rfl
    have h6 := D.valid.1
    have hfit : CountsInRange D.shape.heights rows :=
      ⟨by rw [hl, h6], fun j hj => (hb hz).2 j (by rw [h6]; exact hj)⟩
    simp [countsZeroK, hfit]

/-- **The Keccak verifier's code-level link at π1-rec3's shape, observationally.** -/
theorem link3_obsK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (hκ : D.shape.heights.getD opBlake2s 0 = κ) (np : ℕ) (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1)
    (input : Vector UInt8 32) (P : KeccakState → m KeccakState) :
    ObsEq3 (reduceWithK P D.shape (publicWordsOf input.toList) keccakRec3 .point)
      (readCounts D.shape.heights >>= fun rows => (main3ProgK D F3 np input rows).run P) :=
  (link3_obs0K D F3 hκ np hV input P).trans (link3_countsK D F3 np input P).obsEq3

end Monad

/-! ## The code-level link -/

/-- **The Keccak verifier's code-level link at π1-rec3's shape** (`UniCodeK3`), for every deployment whose `SHA3`
height is Flock's `κ` and whose batch has `2 np + 1` variables: after the row counts, `reduceWithK … keccakRec3`
is `main3ProgK` on `rec3Rounds F3.prog.rounds valsCountK np`, with a tail of three, up to `obsOf3`. -/
def uniCodeK3 (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (hκ : D.shape.heights.getD opBlake2s 0 = κ) (np : ℕ) (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1) :
    UniCodeK3 D F3 valsCountK np where
  prog := main3ProgK D F3 np
  rounds_eq _ _ := rfl
  tail_eq _ _ := rfl
  link := fun input {_} _ _ P c₀ => link3_obsK D F3 hκ np hV input P c₀

/-- `uniCodeK3` at any number of values `nV = valsCountK` (an identity model's). -/
def uniCodeK3At (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (hκ : D.shape.heights.getD opBlake2s 0 = κ) (nV np : ℕ) (hnV : nV = valsCountK)
    (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1) : UniCodeK3 D F3 nV np where
  prog := main3ProgK D F3 np
  rounds_eq _ _ := by rw [hnV]; rfl
  tail_eq _ _ := rfl
  link := (uniCodeK3 D F3 hκ np hV).link

theorem uniCodeK3At_prog (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (hκ : D.shape.heights.getD opBlake2s 0 = κ) (nV np : ℕ)
    (hnV : nV = valsCountK) (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1) :
    (uniCodeK3At D F3 hκ nV np hnV hV).prog = main3ProgK D F3 np := rfl

/-- **`np` as a function of the shape**: `np = varsOf (layoutsOfK D.shape) / 2`, for a shape whose batch has an odd
number of variables (the only ones `rec3Rounds` can describe). -/
theorem twice_half_add_one {V : ℕ} (hodd : V % 2 = 1) : V = 2 * (V / 2) + 1 := by omega

/-- `uniCodeK3` at `np = varsOf (layoutsOfK D.shape) / 2`. -/
def uniCodeK3Odd (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (hκ : D.shape.heights.getD opBlake2s 0 = κ) (hodd : varsOf (layoutsOfK D.shape) % 2 = 1) :
    UniCodeK3 D F3 valsCountK (varsOf (layoutsOfK D.shape) / 2) :=
  uniCodeK3 D F3 hκ _ (twice_half_add_one hodd)

/-! ## Facts of the link the Fiat–Shamir layer reads -/

/-- **The chain program's result names the roots the transcript carries** at rounds `0` (`C1`) and `nF + 1`
(`C2`), at π1-rec3's shape (as `UniOutRootsK`), for every transcript and tail. -/
def UniOutRootsK3 (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    {nV np : ℕ} (C : UniCodeK3 D F3 nV np) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (done : Done) (tl : List E),
    ((C.prog input rows).out done tl).roots =
      ((done.getD 0 default).1.1.getD default,
        (done.getD (F3.prog.rounds.length + 1) default).1.1.getD default)

/-- The chain program at π1-rec3's shape names them (`main3OutK`). -/
theorem uniOutRootsK3_uniCodeK3At (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (hκ : D.shape.heights.getD opBlake2s 0 = κ) (nV np : ℕ)
    (hnV : nV = valsCountK) (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1) :
    UniOutRootsK3 D F3 (uniCodeK3At D F3 hκ nV np hnV hV) := fun _ _ _ _ => rfl

theorem uniOutRootsK3_uniCodeK3 (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (hκ : D.shape.heights.getD opBlake2s 0 = κ) (np : ℕ)
    (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1) :
    UniOutRootsK3 D F3 (uniCodeK3 D F3 hκ np hV) := fun _ _ _ _ => rfl

/-- **The chain program's checks give the counts in range** at π1-rec3's shape: round `0`'s zero is the counts'. -/
theorem countsZeroK3_holds (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (np : ℕ) (input : Vector UInt8 32) (rows : List ℕ) (done : Done)
    (tl : List E) (hd : done ≠ []) (hz : (main3ProgK D F3 np input rows).ZerosVanish done tl) :
    CountsInRange D.shape.heights rows := by
  have hlen : 0 < done.length := List.length_pos_iff.mpr hd
  have h0 := hz.1 0 hlen
  rw [List.take_zero, main3ProgK_zeros_nil] at h0
  have h1 := h0 _ (List.mem_singleton_self _)
  by_contra hc
  simp [countsZeroK, hc] at h1

/-- On a completed transcript of π1-rec3's rounds. -/
theorem countsZeroK3_of_fits (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (np : ℕ) (input : Vector UInt8 32) (rows : List ℕ) (done : Done)
    (tl : List E) (hd : DoneFits (rec3Rounds F3.prog.rounds valsCountK np) done)
    (hz : (main3ProgK D F3 np input rows).ZerosVanish done tl) :
    CountsInRange D.shape.heights rows := by
  refine countsZeroK3_holds D F3 np input rows done tl ?_ hz
  rintro rfl
  have := hd.length_eq
  rw [length_rec3Rounds] at this
  simp only [List.length_nil] at this
  omega

end UniKeccakSound

/-- info: 'UniKeccakSound.uniCodeK3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniCodeK3

/-- info: 'UniKeccakSound.uniCodeK3At' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniCodeK3At

/-- info: 'UniKeccakSound.uniOutRootsK3_uniCodeK3At' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniOutRootsK3_uniCodeK3At

/-- info: 'UniKeccakSound.countsZeroK3_of_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.countsZeroK3_of_fits
