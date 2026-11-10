-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The program is `formal/UniKeccak`'s `reduceWithK`
-- (`Verifier.lean`); Flock's phase is cited through `KFlockSound.link`. The proof is
-- `formal/UniSound/UniSound/CodeLink.lean`'s (`uniCode`) on the Keccak verifier.
import UniKeccakSound.Code.Batch

/-!
# The Keccak verifier's code-level link: `reduceWithK` on the main line is a chain program (`UniCodeK`)

**`uniCodeK D Fl hκ : UniCodeK D Fl valsCountK (varsOf (layoutsOfK D.shape))`**, for every deployment `D` and every
Flock phase `Fl : KFlockSound F κ keccakMain` with `D.shape.heights.getD opSha3 0 = κ`: after the row counts,
`reduceWithK` at the deployment's shape, `keccakMain`, point claims, is the chain program `mainProgK` on
`uniRounds Fl.prog.rounds valsCountK V 1`, `V` the batch's variables at the shape (`varsOf (layoutsOfK D.shape)`), with a
tail of three, up to `obsOf`. Its rounds:

* `C1`'s root and `α ∈ E^4, β, γ` (`drawRun .main 4` is four draws);
* Flock's rounds on the Keccak-f block (`Fl.link`: `verifyWalkedK` is Flock's chain program; its zeros, the
  structured terminal among them, are the main line's there, its tail zeros the `C2` round's);
* `C2`'s root and `t`;
* the `valsCountK` values at `t` (`tableReads` of each Keccak table, then the memory's three, the bytecode's two,
  `T(t)`, `Q_W(t)`) and `ρ, λ`;
* the batch's `V` rounds (`batchK_eq`);

then the three stacks' values, the batch's terminal collected (`batchPureK`), and the result (`mainOutK`). Each is a
function of the transcript (`mainRelsK`, `flockClaimK`, `batchPureK`). Round `0` also carries the counts' zero
(`countsZeroK`, `readCounts`' range checks repeated, invisible to the verdict: `link_countsK`).

Also, for the Fiat–Shamir layer: **`uniOutRootsK_uniCodeKAt`** (the chain program's result names the roots of
rounds `0` and `nF + 1`, `UniOutRootsK`) and **`countsZeroK_holds`** (the chain program's zeros vanishing put the row
counts in range).

The numbers: `nV = valsCountK = Σ_{T ∈ tablesKeccak} tableReads T + 7`, `V = varsOf (layoutsOfK D.shape)`.
-/

namespace UniKeccakSound

open UniStatement UniSound UniKeccak LeanVM.Parameters LeanVM.Semantics FlockSound.Uni

/-! ## The main line's program -/

/-- **The main line's result** from its rounds' records (`C1`'s round `r0`, Flock's `fd`, `C2`'s `r2`, the values'
`r3`, the batch's `brs`) and the tail `tl` (the three stacks' values): the batch's zero and the `Reduced`. -/
def mainOutK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (input : Vector UInt8 32) (rows : List ℕ) (r0 : UMsg × List E) (fd : Done) (r2 r3 : UMsg × List E)
    (brs : Done) (tl : List E) : List E × Reduced :=
  let fl := Fl.prog.out fd []
  let mr := mainRelsK D.shape (publicWordsOf input.toList) (countsBits D.shape.heights rows) (r0.2.take 4)
    (r0.2.getD 4 0) (r0.2.getD 5 0) (r2.2.headD 0) r3.1.2
  let fc := flockClaimK mr.1 fl
  let combined := commitments.filterMap fun c => (combine fc.1.toList c (r3.2.headD 0)).map fun x => (c, x)
  let stackLayouts := layoutsK D.shape mr.2
  let bp := batchPureK combined stackLayouts fc.2 (r3.2.getD 1 0) brs tl
  (bp.1, ⟨(r0.1.1.getD default, r2.1.1.getD default), bp.2, none, fc.1.size,
    stackLayouts.map fun x => (x.1, x.2.vars), stackLayouts, (r0.1.2.headD 0, r2.1.2.headD 0)⟩)

/-- The main line's zeros after a round, for Flock's program `FP`: Flock's in its rounds, its tail zeros in `C2`'s
round. -/
def mainZerosK {β : Type} (FP : ChainProg β) (done : Done) (msg : UMsg) : List E :=
  if 1 ≤ done.length ∧ done.length ≤ FP.rounds.length then FP.zeros (done.drop 1) msg
  else if done.length = FP.rounds.length + 1 then FP.tailZeros (done.drop 1) []
  else []

/-- **The main line's chain program without the counts' zero** (`reduceWithK` after `readCounts`, its zeros as
`reduceWithK` collects them). -/
def mainProg0K (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (input : Vector UInt8 32) (rows : List ℕ) : ChainProg Reduced where
  rounds := uniRounds Fl.prog.rounds valsCountK (varsOf (layoutsOfK D.shape)) 1
  zeros := mainZerosK Fl.prog
  tail := 3
  tailZeros done tl := (mainOutK D Fl input rows (done.getD 0 default)
    ((done.drop 1).take Fl.prog.rounds.length) (done.getD (Fl.prog.rounds.length + 1) default)
    (done.getD (Fl.prog.rounds.length + 2) default) (done.drop (Fl.prog.rounds.length + 3)) tl).1
  out done tl := (mainOutK D Fl input rows (done.getD 0 default)
    ((done.drop 1).take Fl.prog.rounds.length) (done.getD (Fl.prog.rounds.length + 1) default)
    (done.getD (Fl.prog.rounds.length + 2) default) (done.drop (Fl.prog.rounds.length + 3)) tl).2

/-- **The counts' zero**: `0` if the row counts are in range (`readCounts`' checks), else `1`. -/
def countsZeroK (heights rows : List ℕ) : E := if CountsInRange heights rows then 0 else 1

/-- **The Keccak verifier's main line as a chain program** for a public input and the row counts: `mainProg0K` with
the counts' zero in round `0` (`readCounts`' range checks, repeated inside the chain, so that the chain program's
zeros vanishing puts the counts in range; observationally the same run, `link_countsK`). -/
def mainProgK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (input : Vector UInt8 32) (rows : List ℕ) : ChainProg Reduced :=
  (mainProg0K D Fl input rows).withHead [countsZeroK D.shape.heights rows]

section Defs

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
  (input : Vector UInt8 32) (rows : List ℕ)

theorem mainProgK_rounds :
    (mainProgK D Fl input rows).rounds = uniRounds Fl.prog.rounds valsCountK (varsOf (layoutsOfK D.shape)) 1 :=
  rfl

theorem mainProgK_tail : (mainProgK D Fl input rows).tail = 3 := rfl

/-- The main line's zeros in round `0`: the counts' zero. -/
theorem mainProgK_zeros_nil (msg : UMsg) :
    (mainProgK D Fl input rows).zeros [] msg = [countsZeroK D.shape.heights rows] := by
  simp [mainProgK, ChainProg.withHead]

theorem mainProg0K_rounds : (mainProg0K D Fl input rows).rounds = [⟨true, 1, 5⟩] ++ Fl.prog.rounds ++
    [⟨true, 1, 0⟩, ⟨false, valsCountK, 1⟩] ++ List.replicate (varsOf (layoutsOfK D.shape)) ⟨false, 2, 0⟩ :=
  rfl

theorem mainProg0K_zeros : (mainProg0K D Fl input rows).zeros = mainZerosK Fl.prog := rfl

/-- After round `0`, the main line's zeros are Flock's (in its rounds) and its tail zeros (in `C2`'s round). -/
theorem mainProgK_zeros_ne {done : Done} (hd : done ≠ []) :
    (mainProgK D Fl input rows).zeros done = mainZerosK Fl.prog done :=
  withHead_zeros_ne _ _ hd

/-- The tail's zeros: the batch's terminal `sum + last` (`mainOutK`'s first component). -/
theorem mainProgK_tailZeros (done : Done) (tl : List E) :
    (mainProgK D Fl input rows).tailZeros done tl = (mainOutK D Fl input rows (done.getD 0 default)
      ((done.drop 1).take Fl.prog.rounds.length) (done.getD (Fl.prog.rounds.length + 1) default)
      (done.getD (Fl.prog.rounds.length + 2) default) (done.drop (Fl.prog.rounds.length + 3)) tl).1 := rfl

/-- The result: `mainOutK`'s second component. -/
theorem mainProgK_out (done : Done) (tl : List E) :
    (mainProgK D Fl input rows).out done tl = (mainOutK D Fl input rows (done.getD 0 default)
      ((done.drop 1).take Fl.prog.rounds.length) (done.getD (Fl.prog.rounds.length + 1) default)
      (done.getD (Fl.prog.rounds.length + 2) default) (done.drop (Fl.prog.rounds.length + 3)) tl).2 := rfl

end Defs

theorem mainZerosK_nil {β : Type} (FP : ChainProg β) (msg : UMsg) : mainZerosK FP [] msg = [] := by
  simp [mainZerosK]

theorem mainZerosK_flock {β : Type} (FP : ChainProg β) (x : UMsg × List E) (e : Done) (msg : UMsg)
    (h : e.length < FP.rounds.length) : mainZerosK FP ([] ++ [x] ++ e) msg = FP.zeros e msg := by
  simp only [mainZerosK, List.nil_append, List.length_cons, List.singleton_append]
  rw [ite_eq_left ⟨by omega, by omega⟩]
  simp

theorem mainZerosK_c2 {β : Type} (FP : ChainProg β) (x : UMsg × List E) (G : Done)
    (hG : G.length = FP.rounds.length) (msg : UMsg) :
    mainZerosK FP ([x] ++ G) msg = FP.tailZeros G [] := by
  have h1 : ([x] ++ G).length = FP.rounds.length + 1 := by simp [hG]
  unfold mainZerosK
  rw [ite_eq_right (by omega), ite_eq_left h1]
  simp

theorem mainZerosK_vals {β : Type} (FP : ChainProg β) (x x2 : UMsg × List E) (G : Done)
    (hG : G.length = FP.rounds.length) (msg : UMsg) :
    mainZerosK FP ([x] ++ G ++ [x2]) msg = [] := by
  have h1 : ([x] ++ G ++ [x2]).length = FP.rounds.length + 2 := by simp [hG]
  unfold mainZerosK
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem keccakMain_fs : keccakMain.fs = .main := rfl

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

omit [LawfulMonad m] in
theorem drawRun_main (P : KeccakState → m KeccakState) (n : ℕ) : drawRun P .main n = samples P n := rfl

section Main

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
  (input : Vector UInt8 32) (rows : List ℕ)

theorem mainProg0K_flock (P : KeccakState → m KeccakState) (x : UMsg × List E) :
    (mainProg0K D Fl input rows).runRounds P Fl.prog.rounds ([] ++ [x]) =
      (fun d' => [] ++ [x] ++ d') <$> Fl.prog.runRounds P Fl.prog.rounds [] := by
  have h := runRounds_shift (mainProg0K D Fl input rows) Fl.prog P ([] ++ [x]) Fl.prog.rounds.length
    (fun e msg he => by rw [mainProg0K_zeros]; exact mainZerosK_flock Fl.prog x e msg he) Fl.prog.rounds []
    (by simp)
  rw [List.append_nil] at h
  exact h

theorem mainProg0K_batch (P : KeccakState → m KeccakState) (d : Done)
    (hd : Fl.prog.rounds.length + 3 ≤ d.length) :
    (mainProg0K D Fl input rows).runRounds P
        (List.replicate (varsOf (layoutsOfK D.shape)) ⟨false, 2, 0⟩) d =
      (fun e => d ++ e) <$> readRounds P (List.replicate (varsOf (layoutsOfK D.shape)) ⟨false, 2, 0⟩) := by
  refine runRounds_noZeros _ P (Fl.prog.rounds.length + 3) (fun d msg h => ?_) _ d
    (fun s hs => by rw [(List.mem_replicate.mp hs).2]) hd
  rw [mainProg0K_zeros]
  simp only [mainZerosK]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

end Main

/-- **The code-level link, observationally**, for the program without the counts' zero. -/
theorem link_obs0K (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (hκ : D.shape.heights.getD opSha3 0 = κ) (input : Vector UInt8 32)
    (P : KeccakState → m KeccakState) :
    ObsEq (reduceWithK P D.shape (publicWordsOf input.toList) keccakMain .point)
      (readCounts D.shape.heights >>= fun rows => (mainProg0K D Fl input rows).run P) := by
  have hv : D.shape.validate true = true := D.valid.2
  have ht : (ClaimsMode.point == ClaimsMode.point) = true := rfl
  unfold reduceWithK
  simp only [hv, Bool.not_true, Bool.false_eq_true, ite_false, ht, ite_true, countBits_eq,
    bind_map_left, keccakMain_fs, drawRun_main, batchK_eq, tablePart_eq, hκ, Fl.link]
  refine ObsEq.bind_right _ fun rows => ?_
  simp only [ChainProg.run]
  rw [mainProg0K_rounds, show (mainProg0K D Fl input rows).tail = 3 from rfl, runRounds_append,
    runRounds_append, runRounds_append, runRounds_cons, mainProg0K_zeros]
  rw [samples_fix P 4]
  simp only [rootRead, ite_true, mainZerosK_nil, nextScalars_one, ChainProg.requireZeros, pure_bind,
    bind_map_left, bind_assoc, ChainProg.runRounds, Nat.reduceAdd, samples_six]
  -- Round 0: `C1`'s root and out-of-domain answer, `α, β, γ`.
  refine ObsEq.bind_right _ fun root1 => ?_
  refine ObsEq.bind_right _ fun ood1 => ?_
  refine ObsEq.bind_right _ fun alphas => ?_
  refine ObsEq.bind_right _ fun beta => ?_
  refine ObsEq.bind_right _ fun gamma => ?_
  -- Flock's rounds (`Fl.link`).
  rw [Fl.tail_eq, nextScalars_zero, mainProg0K_flock, runRounds_fix Fl.prog P Fl.prog.rounds []]
  simp only [pure_bind, bind_map_left, List.nil_append, List.length_nil, List.drop_zero, mainProg0K_zeros]
  refine ObsEq.bind_right _ fun fd => ?_
  -- `C2`'s root (Flock's tail zeros moved past it), `t`.
  refine ObsEq.trans (obsEq_requireZeros_nextRoot _ _) ?_
  refine ObsEq.bind_right _ fun root2 => ?_
  refine ObsEq.trans (obsEq_requireZeros_nextScalar _ _) ?_
  try simp only [nextScalars_one, bind_map_left]
  refine ObsEq.bind_right _ fun ood2 => ?_
  rw [mainZerosK_c2 Fl.prog _ _ (length_fixDone _ _)]
  refine ObsEq.bind_right _ fun _ => ?_
  rw [UniSound.samples_one]
  simp only [bind_map_left]
  refine ObsEq.bind_right _ fun t => ?_
  -- The values at `t`.
  rw [forIn_reads_of tableReads (tablesStep D.shape.heights (eqKernel (fixLen 4 alphas)) beta
    (digits t (max D.shape.heap.h (D.shape.constraintVars + 4) + 2)))]
  swap
  · intro table s
    simp [map_eq_bind_pure_comp, tablesStep]
  simp only [Bool.false_eq_true, ite_false, bind_assoc, pure_bind, samples_two]
  simp only [mainZerosK_vals Fl.prog _ _ _ (length_fixDone _ _)]
  rw [show valsCountK = (tablesKeccak.map tableReads).sum + 7 from rfl,
    nextScalars_add, nextScalars_seven, nextScalars_fix (tablesKeccak.map tableReads).sum]
  simp only [ChainProg.requireZeros, bind_assoc, pure_bind, bind_map_left]
  refine ObsEq.bind_right _ fun vt => ?_
  refine ObsEq.bind_right _ fun a1 => ?_
  refine ObsEq.bind_right _ fun a2 => ?_
  refine ObsEq.bind_right _ fun a3 => ?_
  refine ObsEq.bind_right _ fun a4 => ?_
  refine ObsEq.bind_right _ fun a5 => ?_
  refine ObsEq.bind_right _ fun a6 => ?_
  refine ObsEq.bind_right _ fun a7 => ?_
  simp only [fixLen_fixLen]
  rcases hE : (Fl.prog.out (fixDone Fl.prog.rounds.length fd) []).2 with ⟨map, target⟩ | ⟨ws, value⟩
  all_goals
    simp only []
    refine ObsEq.bind_right _ fun rho => ?_
    refine ObsEq.bind_right _ fun lam => ?_
    rw [mainProg0K_batch D Fl input rows P _ (by simp)]
    simp only [bind_map_left]
    refine ObsEq.bind_eq (by
      have h := mainRelsK_c2 D.shape D.valid.1 (publicWordsOf input.toList) (countsBits D.shape.heights rows)
        (fixLen 4 alphas) beta gamma t (fixLen (tablesKeccak.map tableReads).sum vt ++ [a1, a2, a3, a4, a5, a6, a7])
      simp only [mainRelsK, tablesReadsK, getD_fixLen_append, getD_fixLen_append_zero, List.getD_cons_zero,
        List.getD_cons_succ, List.take_left', length_fixLen] at h
      rw [h]
      rfl) fun brs => ?_
    refine ObsEq.bind_eq (by
      have h := mainCombinedK_length D.shape (publicWordsOf input.toList) (countsBits D.shape.heights rows)
        (fixLen 4 alphas) beta gamma t (fixLen (tablesKeccak.map tableReads).sum vt ++ [a1, a2, a3, a4, a5, a6, a7])
        (Fl.prog.out (fixDone Fl.prog.rounds.length fd) []) rho
      simp only [mainRelsK, flockClaimK, hE, tablesReadsK, getD_fixLen_append, getD_fixLen_append_zero,
        List.getD_cons_zero, List.getD_cons_succ, List.take_left', length_fixLen] at h
      rw [h]) fun tl => ?_
    refine ObsEq.of_eq ?_
    simp only [mainProg0K, decode_r0, decode_fd _ _ _ _ _ _ (length_fixDone _ _),
      decode_r2 _ _ _ _ _ _ (length_fixDone _ _), decode_r3 _ _ _ _ _ _ (length_fixDone _ _),
      decode_brs _ _ _ _ _ _ (length_fixDone _ _)]
    simp only [mainOutK, mainRelsK, flockClaimK, hE, tablesReadsK, getD_fixLen_append,
      getD_fixLen_append_zero, getD_five, List.getD_cons_zero, List.getD_cons_succ, List.headD_cons,
      Option.getD_some, List.take_left', length_fixLen]

/-- **The counts' zero is invisible**: after `readCounts`, whose zeros vanish only if the counts are in range
(`readCounts_spec`), the counts' zero in round `0` changes no verdict. -/
theorem link_countsK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (input : Vector UInt8 32) (P : KeccakState → m KeccakState) :
    ObsEq (readCounts D.shape.heights >>= fun rows => (mainProg0K D Fl input rows).run P)
      (readCounts D.shape.heights >>= fun rows => (mainProgK D Fl input rows).run P) := by
  intro c
  have h1 : ObsEq (readCounts (m := m) D.shape.heights >>= fun rows => (mainProgK D Fl input rows).run P)
      (readCounts (m := m) D.shape.heights >>= fun rows =>
        ChainProg.requireZeros [countsZeroK D.shape.heights rows] >>= fun _ =>
          (mainProg0K D Fl input rows).run P) :=
    ObsEq.bind_right _ fun rows => obsEq_withHead1 (mainProg0K D Fl input rows)
      [countsZeroK D.shape.heights rows] P 5 _ rfl (funext fun msg => mainZerosK_nil Fl.prog msg)
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

/-- **The Keccak verifier's code-level link, observationally.** -/
theorem link_obsK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (hκ : D.shape.heights.getD opSha3 0 = κ) (input : Vector UInt8 32)
    (P : KeccakState → m KeccakState) :
    ObsEq (reduceWithK P D.shape (publicWordsOf input.toList) keccakMain .point)
      (readCounts D.shape.heights >>= fun rows => (mainProgK D Fl input rows).run P) :=
  (link_obs0K D Fl hκ input P).trans (link_countsK D Fl input P)

end Monad

/-! ## The code-level link -/

/-- **The Keccak verifier's code-level link** (`UniCodeK`) at the main line, for every deployment whose `SHA3`
height is Flock's `κ`: after the row counts, `reduceWithK` is `mainProgK` on
`uniRounds Fl.prog.rounds valsCountK (varsOf (layoutsOfK D.shape)) 1`, with a tail of three, up to `obsOf`. -/
def uniCodeK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (hκ : D.shape.heights.getD opSha3 0 = κ) :
    UniCodeK D Fl valsCountK (varsOf (layoutsOfK D.shape)) where
  prog := mainProgK D Fl
  rounds_eq _ _ := rfl
  tail_eq _ _ := rfl
  link := fun input {_} _ _ P c₀ => link_obsK D Fl hκ input P c₀

/-- `uniCodeK` at given numbers `nV = valsCountK`, `V = varsOf (layoutsOfK D.shape)` (an identity model's). -/
def uniCodeKAt (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (hκ : D.shape.heights.getD opSha3 0 = κ) (nV V : ℕ) (hnV : nV = valsCountK)
    (hV : V = varsOf (layoutsOfK D.shape)) : UniCodeK D Fl nV V where
  prog := mainProgK D Fl
  rounds_eq i r := by
    rw [hnV, hV, mainProgK_rounds]
  tail_eq _ _ := rfl
  link := (uniCodeK D Fl hκ).link

theorem uniCodeKAt_prog (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (Fl : KFlockSound F κ keccakMain) (hκ : D.shape.heights.getD opSha3 0 = κ) (nV V : ℕ)
    (hnV : nV = valsCountK) (hV : V = varsOf (layoutsOfK D.shape)) :
    (uniCodeKAt D Fl hκ nV V hnV hV).prog = mainProgK D Fl := rfl

/-! ## Facts of the link the Fiat–Shamir layer reads -/

/-- **The chain program's result names the roots the transcript carries** at rounds `0` (`C1`) and `nF + 1`
(`C2`): `UniSound.UniOutRoots` for the Keccak code-level link, stated for every transcript and tail (so in
particular for the stream's, `uDone`, and its tail). -/
def UniOutRootsK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    {nV V : ℕ} (C : UniCodeK D Fl nV V) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (done : Done) (tl : List E),
    ((C.prog input rows).out done tl).roots =
      ((done.getD 0 default).1.1.getD default,
        (done.getD (Fl.prog.rounds.length + 1) default).1.1.getD default)

/-- The main line's chain program names them (`mainOutK`). -/
theorem uniOutRootsK_uniCodeKAt (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (Fl : KFlockSound F κ keccakMain) (hκ : D.shape.heights.getD opSha3 0 = κ) (nV V : ℕ)
    (hnV : nV = valsCountK) (hV : V = varsOf (layoutsOfK D.shape)) :
    UniOutRootsK D Fl (uniCodeKAt D Fl hκ nV V hnV hV) := fun _ _ _ _ => rfl

theorem uniOutRootsK_uniCodeK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (Fl : KFlockSound F κ keccakMain) (hκ : D.shape.heights.getD opSha3 0 = κ) :
    UniOutRootsK D Fl (uniCodeK D Fl hκ) := fun _ _ _ _ => rfl

/-- **The chain program's checks give the counts in range**: round `0`'s zero is the counts' (`countsZeroK`, `1`
out of range). -/
theorem countsZeroK_holds (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (Fl : KFlockSound F κ keccakMain) (input : Vector UInt8 32) (rows : List ℕ) (done : Done) (tl : List E)
    (hd : done ≠ []) (hz : (mainProgK D Fl input rows).ZerosVanish done tl) :
    CountsInRange D.shape.heights rows := by
  have hlen : 0 < done.length := List.length_pos_iff.mpr hd
  have h0 := hz.1 0 hlen
  rw [List.take_zero, mainProgK_zeros_nil] at h0
  have h1 := h0 _ (List.mem_singleton_self _)
  by_contra hc
  simp [countsZeroK, hc] at h1

/-- On a completed transcript of the main line's rounds. -/
theorem countsZeroK_of_fits (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (Fl : KFlockSound F κ keccakMain) (input : Vector UInt8 32) (rows : List ℕ) (done : Done) (tl : List E)
    (hd : DoneFits (uniRounds Fl.prog.rounds valsCountK (varsOf (layoutsOfK D.shape)) 1) done)
    (hz : (mainProgK D Fl input rows).ZerosVanish done tl) :
    CountsInRange D.shape.heights rows := by
  refine countsZeroK_holds D Fl input rows done tl ?_ hz
  rintro rfl
  have := hd.length_eq
  rw [length_uniRounds] at this
  simp only [List.length_nil] at this
  omega

end UniKeccakSound

/-- info: 'UniKeccakSound.uniCodeK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniCodeK

/-- info: 'UniKeccakSound.uniCodeKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniCodeKAt

/-- info: 'UniKeccakSound.uniOutRootsK_uniCodeKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniOutRootsK_uniCodeKAt
