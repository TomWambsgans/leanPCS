-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The program is `formal/UniKeccak`'s `reduceWithK4`
-- (`Verifier4.lean`: `sampleWide`, `verifyWalkedK4`, `batchK4`); the proof follows `Code/Link3.lean`'s (`uniCodeK3`),
-- Flock's front cited through `Rec4/Flock4.lean` (`KF.kflock_link4`).
import UniKeccakSound.Rec4.Link4Base
import UniKeccakSound.Rec4.Flock4

/-!
# The Keccak verifier's code-level link at π1-rec4 (`UniCodeK4`)

**`uniCodeK4 D F3 hF3 hκ np hV : UniCodeK4 D κ valsCountK np`** (and `uniCodeK4At` at any `nV = valsCountK`), for every
deployment `D` whose `SHA3` height is `κ` (`hκ`) and whose batch has `2 np + 1` variables (`hV`), and π1-rec3's Flock
phase `F3` with `F3.prog = KF.kProg3 κ` (`hF3`; `KF.kFlockSoundRec3`'s by definition): after the row counts,
`reduceWithK4` at the deployment's shape, `keccakRec4`, point claims, is the wide chain program `main4ProgK D F3 np`
on `rec4Rounds κ valsCountK np`, up to `obsOf3`, for every lawful monad and permutation. The proof:

* `main4Prog0K` (`main4ProgK` without the counts' zero) runs as its rounds written out (`main4Prog0K_runW`): `C1`'s
  root and answer and a wide draw of four; Flock's rounds between (`kRoundsMid κ`, one `sample` each:
  `sampleWide_one`); the slices, `C2`'s root and answer, Flock's structured terminal, a wide draw of five; the values
  and a wide draw of four; the batch's rounds; the tail;
* the verifier's Flock front is those rounds and the slices (`KF.kflock_link4`), its structured terminal moved past
  `C2`'s root and answer (`obsEq_requireZeros_nextRoot`, `obsEq_requireZeros_nextScalar`); the batch is
  `batchK4_eq` (`λ` given, the narrow draws read through `narrowRec`, as π1-rec3's); the result is `main3OutK` on the
  transcript read as π1-rec3's (`toRec3`: `main4Prog0K_out`, `main4Prog0K_tailZeros`), Flock's end the ring switch
  at the map `f_0 … f_5` drawn in two parts (`prog_out_fd4`);
* the counts' zero in round `0` is invisible (`link4_countsK`, by `obsEq_headW` and `obl_runW`).

Also **`uniOutRootsK4_uniCodeK4At`** (`UniOutRootsK4`: the result names the roots of rounds `0` and `28 + κ`, for every
transcript) and **`countsZeroK4_of_fits`** (the chain program's zeros vanishing on a completed transcript of
`rec4Rounds` put the row counts in range).
-/

namespace UniKeccakSound

open UniStatement UniSound UniKeccak LeanVM.Parameters LeanVM.Semantics FlockSound.Uni

/-! ## The batch at π1-rec4 -/

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- A bind on a triple whose continuation does not read the middle reads the pair of its ends. -/
theorem bind_triple {β : Type} (x : ChanM m (List E × List E × E)) (K : List E × List E × E → ChanM m β)
    (hK : ∀ y, K y = K (y.1, [], y.2.2)) :
    x >>= K = ((fun y => (y.1, y.2.2)) <$> x) >>= fun p => K (p.1, [], p.2) := by
  rw [bind_map_left]
  exact bind_congr hK

/-- **The Keccak batch at π1-rec4** (`batchK4 P λ`): the rounds `batchNvs vars`, the stacks' values, the terminal
zero, the result (`batchPureWK id`), `λ` given. -/
theorem batchK4_eq (P : KeccakState → m KeccakState) (lambda : E) (combined : List (Commitment × Combined))
    (layouts : List (Commitment × StackLayout)) (ringMap : Option (List E)) :
    batchK4 P lambda combined layouts ringMap = (do
      let brs ← readRoundsN P (batchNvs (varsOf layouts))
      let tl ← nextScalars (m := m) combined.length
      ChainProg.requireZeros (batchPureWK id combined layouts ringMap lambda brs tl).1
      pure (batchPureWK id combined layouts ringMap lambda brs tl).2) := by
  unfold batchK4
  have hv : (layouts.map (·.2.vars)).foldl max 0 = varsOf layouts := rfl
  simp only [hv]
  rw [bind_triple _ _ fun _ => rfl, sumcheckPairsDrawn_eq, bind_map_left]
  refine bind_congr fun brs => ?_
  refine bind_congr fun values => ?_
  simp [batchPureWK, batchFoldK, batchTarget, layoutOf, varsOf, ChainProg.requireZeros]

end Monad

/-! ## The program without the counts' zero -/

/-- **π1-rec4's zeros without the counts'**: Flock's structured terminal in `C2`'s round. -/
def zeros4K0 (κ : ℕ) (done : Done) (msg : UMsg) : List E :=
  if done.length = 28 + κ then [KF.kTerm κ (KF.sampRec3 κ) (vFront4 κ done) (msg.2.take 64)] else []

/-- **`main4ProgK` without the counts' zero.** -/
def main4Prog0K (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (np : ℕ) (input : Vector UInt8 32) (rows : List ℕ) : ChainProgW Reduced :=
  { main4ProgK D F3 np input rows with zeros := zeros4K0 κ }

theorem rec4Rounds_eq (κ nV np : ℕ) : rec4Rounds κ nV np = ⟨true, 1, 3⟩ :: (kRoundsMid κ ++
    ⟨true, 65, 4⟩ :: ⟨false, nV, 3⟩ :: (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩])) := by
  simp only [rec4Rounds, List.append_assoc, List.cons_append, List.nil_append]

theorem pv4_ne {κ j : ℕ} (h : j ≠ 28 + κ) : pv4 κ j = 0 := by
  unfold pv4
  rw [ite_eq_right h]

theorem zeros4K0_ne {κ : ℕ} {d : Done} (h : d.length ≠ 28 + κ) (msg : UMsg) : zeros4K0 κ d msg = [] := by
  unfold zeros4K0
  rw [ite_eq_right h]

section Prog

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3) (np : ℕ)
  (input : Vector UInt8 32) (rows : List ℕ)

theorem main4Prog0K_rounds : (main4Prog0K D F3 np input rows).rounds = rec4Rounds κ valsCountK np := rfl

theorem main4Prog0K_pv : (main4Prog0K D F3 np input rows).pv = pv4 κ := rfl

theorem main4Prog0K_zeros : (main4Prog0K D F3 np input rows).zeros = zeros4K0 κ := rfl

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Round `0`: `C1`'s root and answer, one wide draw of four. -/
theorem main4Prog0K_r0 (P : KeccakState → m KeccakState) (rs : List Compose.RoundSpec) :
    (main4Prog0K D F3 np input rows).runRoundsW P (⟨true, 1, 3⟩ :: rs) [] = (do
      let root1 ← nextRoot (m := m)
      let ood1 ← nextScalar (m := m)
      let bus ← sampleWide P 4
      (main4Prog0K D F3 np input rows).runRoundsW P rs [((some root1, [ood1]), bus)]) := by
  have h0 : ∀ msg, zeros4K0 κ [] msg = [] := zeros4K0_ne (by simp only [List.length_nil]; omega)
  have hp : pv4 κ 0 = 0 := pv4_ne (by omega)
  rw [runRoundsW_cons]
  simp only [main4Prog0K_pv, main4Prog0K_zeros, h0, List.length_nil, hp, UniSound.nextScalars_zero, pure_bind,
    rootRead, ite_true, Nat.sub_zero, nextScalars_one, bind_map_left, ChainProg.requireZeros, List.nil_append]

/-- Flock's rounds between: their reads and draws. -/
theorem main4Prog0K_mid (P : KeccakState → m KeccakState) (x : UMsg × List E) :
    (main4Prog0K D F3 np input rows).runRoundsW P (kRoundsMid κ) [x] =
      (fun e => [x] ++ fitN (27 + κ) e) <$> readRounds P (kRoundsMid κ) := by
  have hz : ∀ (d : Done) (msg : UMsg), 1 ≤ d.length → d.length < 28 + κ →
      (main4Prog0K D F3 np input rows).zeros d msg = [] := fun d msg _ h1 => zeros4K0_ne (by omega) msg
  have hp : ∀ j, 1 ≤ j → j < 28 + κ → (main4Prog0K D F3 np input rows).pv j = 0 := fun j _ h1 =>
    pv4_ne (by omega)
  have hr : ∀ s ∈ kRoundsMid κ, s.root = false ∧ s.ns = 0 := by
    intro s hs
    simp only [kRoundsMid, List.mem_append, List.mem_singleton, List.mem_replicate] at hs
    rcases hs with ((rfl | ⟨-, rfl⟩) | rfl) | ⟨-, rfl⟩ <;> exact ⟨rfl, rfl⟩
  rw [runRoundsW_read _ P 1 (28 + κ) hz hp (kRoundsMid κ) [x] hr (by simp)
    (by simp only [List.length_singleton, length_kRoundsMid]; omega)]
  conv_lhs => rw [readRounds_fit P (kRoundsMid κ)]
  simp only [Functor.map_map, length_kRoundsMid]

/-- `C2`'s round (the slices, the root, the answer, Flock's structured terminal, one wide draw of five) and the
values' round (one wide draw of four). -/
theorem main4Prog0K_c2v (P : KeccakState → m KeccakState) (rs : List Compose.RoundSpec) (x : UMsg × List E)
    (e : Done) :
    (main4Prog0K D F3 np input rows).runRoundsW P (⟨true, 65, 4⟩ :: ⟨false, valsCountK, 3⟩ :: rs)
        ([x] ++ fitN (27 + κ) e) = (do
      let slices ← nextScalars (m := m) 64
      let root2 ← nextRoot (m := m)
      let ood2 ← nextScalar (m := m)
      ChainProg.requireZeros
        [KF.kTerm κ (KF.sampRec3 κ) (((none, []), [x.2.getD 3 0]) :: fitN (27 + κ) e) (fixLen 64 slices)]
      let pd ← sampleWide P 5
      let vals ← nextScalars (m := m) valsCountK
      let late ← sampleWide P 4
      (main4Prog0K D F3 np input rows).runRoundsW P rs
        ([x] ++ fitN (27 + κ) e ++ [((some root2, fixLen 64 slices ++ [ood2]), pd), ((none, vals), late)])) := by
  have hd : ([x] ++ fitN (27 + κ) e).length = 28 + κ := by
    simp only [List.length_append, List.length_singleton, length_fitN]
    omega
  have hz0 : ∀ msg : UMsg, zeros4K0 κ ([x] ++ fitN (27 + κ) e) msg =
      [KF.kTerm κ (KF.sampRec3 κ) (((none, []), [x.2.getD 3 0]) :: fitN (27 + κ) e) (msg.2.take 64)] := by
    intro msg
    rw [zeros4K0, ite_eq_left hd]
    simp [vFront4, List.take_of_length_le]
  have hz1 : ∀ (y : UMsg × List E) (msg : UMsg), zeros4K0 κ ([x] ++ fitN (27 + κ) e ++ [y]) msg = [] :=
    fun y msg => zeros4K0_ne (by simp only [List.length_append, List.length_singleton, length_fitN]; omega) msg
  have hp0 : pv4 κ ([x] ++ fitN (27 + κ) e).length = 64 := by
    rw [hd, pv4, ite_eq_left rfl]
  have hp1 : ∀ y : UMsg × List E, pv4 κ ([x] ++ fitN (27 + κ) e ++ [y]).length = 0 := fun y =>
    pv4_ne (by simp only [List.length_append, List.length_singleton, length_fitN]; omega)
  have hn : ChainProg.requireZeros (m := m) [] = pure () := rfl
  simp only [runRoundsW_cons, main4Prog0K_pv, main4Prog0K_zeros, hp0, hp1, hz0, hz1, rootRead, ite_true,
    Bool.false_eq_true, ite_false, pure_bind, nextScalars_one, UniSound.nextScalars_zero, bind_map_left,
    Nat.sub_zero, List.nil_append, Nat.reduceSub, Nat.reduceAdd, hn]
  rw [nextScalars_fix 64]
  simp only [bind_map_left, fixLen_fixLen, List.take_left' (length_fixLen _ _), List.append_assoc,
    List.singleton_append]

/-- The batch's rounds: their reads and draws. -/
theorem main4Prog0K_batch (P : KeccakState → m KeccakState) (d : Done) (hd : 30 + κ ≤ d.length) :
    (main4Prog0K D F3 np input rows).runRoundsW P (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩]) d =
      (fun e => d ++ e) <$> readRounds P (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩]) := by
  refine runRoundsW_read _ P (30 + κ) (d.length + (np + 1)) (fun d' msg h0 _ => zeros4K0_ne (by omega) msg)
    (fun j h0 _ => pv4_ne (by omega)) _ d (fun s hs => ?_) hd (by simp)
  simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hs
  rcases hs with ⟨-, rfl⟩ | rfl <;> exact ⟨rfl, rfl⟩

/-- **`main4Prog0K`'s run**, its rounds written out. -/
theorem main4Prog0K_runW (P : KeccakState → m KeccakState) :
    (main4Prog0K D F3 np input rows).runW P = (do
      let root1 ← nextRoot (m := m)
      let ood1 ← nextScalar (m := m)
      let bus ← sampleWide P 4
      let d ← readRounds P (kRoundsMid κ)
      let slices ← nextScalars (m := m) 64
      let root2 ← nextRoot (m := m)
      let ood2 ← nextScalar (m := m)
      ChainProg.requireZeros
        [KF.kTerm κ (KF.sampRec3 κ) (((none, []), [bus.getD 3 0]) :: fitN (27 + κ) d) (fixLen 64 slices)]
      let pd ← sampleWide P 5
      let vals ← nextScalars (m := m) valsCountK
      let late ← sampleWide P 4
      let brs ← readRounds P (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩])
      let tl ← nextScalars (m := m) 3
      ChainProg.requireZeros ((main4Prog0K D F3 np input rows).tailZeros
        ([((some root1, [ood1]), bus)] ++ fitN (27 + κ) d ++
          [((some root2, fixLen 64 slices ++ [ood2]), pd), ((none, vals), late)] ++ brs) tl)
      pure ((main4Prog0K D F3 np input rows).out
        ([((some root1, [ood1]), bus)] ++ fitN (27 + κ) d ++
          [((some root2, fixLen 64 slices ++ [ood2]), pd), ((none, vals), late)] ++ brs) tl)) := by
  unfold ChainProgW.runW
  rw [main4Prog0K_rounds, rec4Rounds_eq, main4Prog0K_r0]
  simp only [bind_assoc]
  refine bind_congr fun root1 => bind_congr fun ood1 => bind_congr fun bus => ?_
  rw [runRoundsW_append, main4Prog0K_mid]
  simp only [bind_map_left, bind_assoc]
  refine bind_congr fun d => ?_
  rw [main4Prog0K_c2v]
  simp only [bind_assoc]
  refine bind_congr fun slices => ?_
  refine bind_congr fun root2 => ?_
  refine bind_congr fun ood2 => ?_
  refine bind_congr fun _ => ?_
  refine bind_congr fun pd => ?_
  refine bind_congr fun vals => ?_
  refine bind_congr fun late => ?_
  rw [main4Prog0K_batch _ _ _ _ _ P _ (by simp; omega)]
  simp only [bind_map_left]
  rfl

end Monad

end Prog

/-! ## The result through π1-rec3's -/

theorem toRec3_eq (κ : ℕ) (r0 c2 v : UMsg × List E) (mid brs : Done) (hm : mid.length = 27 + κ) :
    toRec3 κ ([r0] ++ mid ++ [c2, v] ++ brs) = [(r0.1, r0.2.take 3)] ++
      ((((none, []), [r0.2.getD 3 0]) :: mid) ++ [((none, c2.1.2.take 64), c2.2.drop 1 ++ v.2.drop 2)]) ++
      [((c2.1.1, c2.1.2.drop 64), c2.2.take 1)] ++ [(v.1, v.2.take 2)] ++ brs := by
  have e2 : 28 + κ = 27 + κ + 1 := by omega
  have e3 : 29 + κ = 27 + κ + 2 := by omega
  have e4 : 30 + κ = 27 + κ + 3 := by omega
  have e : [r0] ++ mid ++ [c2, v] ++ brs = [r0] ++ mid ++ [c2] ++ [v] ++ brs := by simp
  unfold toRec3 vFront4
  rw [e, e2, e3, e4, decode_r0, decode_fd _ _ _ _ _ _ hm,
    decode_r2 _ _ _ _ _ _ hm, decode_r3 _ _ _ _ _ _ hm, decode_brs _ _ _ _ _ _ hm]
  simp only [List.cons_append, List.append_assoc, List.nil_append]

section Out

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
  (hF3 : F3.prog = KF.kProg3 κ) (np : ℕ) (input : Vector UInt8 32) (rows : List ℕ)
include hF3

theorem length_fd4 (r0 c2 v : UMsg × List E) (mid : Done) (hm : mid.length = 27 + κ) :
    ((((none, []), [r0.2.getD 3 0]) :: mid) ++ [((none, c2.1.2.take 64), c2.2.drop 1 ++ v.2.drop 2)]).length =
      F3.prog.rounds.length := by
  rw [hF3, show (KF.kProg3 κ).rounds = KF.kRounds κ KF.r0Rec3 from rfl, KF.length_kRounds]
  simp only [List.length_append, List.length_cons, List.length_nil, hm]
  omega

/-- **The result** of `main4Prog0K` on a transcript of π1-rec4's shape: `main3OutK` on its π1-rec3 reading. -/
theorem main4Prog0K_out (r0 c2 v : UMsg × List E) (mid brs : Done) (hm : mid.length = 27 + κ) (tl : List E) :
    (main4Prog0K D F3 np input rows).out ([r0] ++ mid ++ [c2, v] ++ brs) tl =
      (main3OutK D F3 input rows (r0.1, r0.2.take 3)
        ((((none, []), [r0.2.getD 3 0]) :: mid) ++ [((none, c2.1.2.take 64), c2.2.drop 1 ++ v.2.drop 2)])
        ((c2.1.1, c2.1.2.drop 64), c2.2.take 1) (v.1, v.2.take 2) brs tl).2 := by
  show (main3ProgK D F3 np input rows).out (toRec3 κ _) tl = _
  rw [toRec3_eq κ r0 c2 v mid brs hm, main3ProgK_out, decode_r0,
    decode_fd _ _ _ _ _ _ (length_fd4 F3 hF3 r0 c2 v mid hm), decode_r2 _ _ _ _ _ _ (length_fd4 F3 hF3 r0 c2 v mid hm),
    decode_r3 _ _ _ _ _ _ (length_fd4 F3 hF3 r0 c2 v mid hm), decode_brs _ _ _ _ _ _ (length_fd4 F3 hF3 r0 c2 v mid hm)]

/-- **The tail's zeros** of `main4Prog0K`: `main3OutK`'s on its π1-rec3 reading. -/
theorem main4Prog0K_tailZeros (r0 c2 v : UMsg × List E) (mid brs : Done) (hm : mid.length = 27 + κ)
    (tl : List E) :
    (main4Prog0K D F3 np input rows).tailZeros ([r0] ++ mid ++ [c2, v] ++ brs) tl =
      (main3OutK D F3 input rows (r0.1, r0.2.take 3)
        ((((none, []), [r0.2.getD 3 0]) :: mid) ++ [((none, c2.1.2.take 64), c2.2.drop 1 ++ v.2.drop 2)])
        ((c2.1.1, c2.1.2.drop 64), c2.2.take 1) (v.1, v.2.take 2) brs tl).1 := by
  show (main3ProgK D F3 np input rows).tailZeros (toRec3 κ _) tl = _
  rw [toRec3_eq κ r0 c2 v mid brs hm, main3ProgK_tailZeros, decode_r0,
    decode_fd _ _ _ _ _ _ (length_fd4 F3 hF3 r0 c2 v mid hm), decode_r2 _ _ _ _ _ _ (length_fd4 F3 hF3 r0 c2 v mid hm),
    decode_r3 _ _ _ _ _ _ (length_fd4 F3 hF3 r0 c2 v mid hm), decode_brs _ _ _ _ _ _ (length_fd4 F3 hF3 r0 c2 v mid hm)]

/-- Flock's result in `main3OutK` on π1-rec4's reading: the point from Flock's front, the ring switch at the map. -/
theorem prog_out_fd4 (c : E) (mid : Done) (hm : mid.length = 27 + κ) (s mp : List E) :
    F3.prog.out ((((none, []), [c]) :: mid) ++ [((none, s), mp)]) [] =
      ((KF.kOutT κ (KF.sampRec3 κ) ((((none, []), [c]) :: mid) ++ [((none, s), [])])).1,
        .ring mp (Flock.towerTarget s mp)) := by
  rw [hF3]
  exact KF.kOutT_rec3_append κ _ (by simp only [List.length_cons, hm]; omega) s mp

end Out

theorem fixLen_four (l : List E) : fixLen 4 l = [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0] := by
  simp [fixLen, List.range_succ]

theorem headD_take_one (l : List E) : (l.take 1).headD 0 = l.getD 0 0 := by
  cases l <;> rfl

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **The code-level link at π1-rec4, observationally**, for the program without the counts' zero. -/
theorem link4_obs0K (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (hF3 : F3.prog = KF.kProg3 κ) (hκ : D.shape.heights.getD opSha3 0 = κ) (np : ℕ)
    (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1) (input : Vector UInt8 32) (P : KeccakState → m KeccakState) :
    ObsEq3 (reduceWithK4 P D.shape (publicWordsOf input.toList) keccakRec4 .point)
      (readCounts D.shape.heights >>= fun rows => (main4Prog0K D F3 np input rows).runW P) := by
  have hv : D.shape.validate true = true := D.valid.2
  have ht : (ClaimsMode.point == ClaimsMode.point) = true := rfl
  unfold reduceWithK4
  simp only [hv, Bool.not_true, Bool.false_eq_true, ite_false, ht, ite_true, countBits_eq,
    bind_map_left, batchK4_eq, tablePart_eq, hκ, KF.kflock_link4]
  refine ObsEq3.bind_right _ fun rows => ?_
  rw [main4Prog0K_runW]
  simp only [bind_assoc, pure_bind]
  -- Round 0: `C1`'s root and answer, `c, β, γ, c'`.
  refine ObsEq3.bind_right _ fun root1 => ?_
  refine ObsEq3.bind_right _ fun ood1 => ?_
  rw [sampleWide_fix P 4]
  simp only [bind_map_left, fixLen_four, List.getD_cons_zero, List.getD_cons_succ]
  refine ObsEq3.bind_right _ fun bus => ?_
  -- Flock's rounds between, the slices.
  refine ObsEq3.bind_right _ fun d => ?_
  rw [nextScalars_fix 64]
  simp only [bind_map_left, fixLen_fixLen]
  refine ObsEq3.bind_right _ fun slices => ?_
  -- `C2`'s root and answer (Flock's structured terminal moved past them), `t, f_0 … f_3`.
  refine ObsEq3.trans (ObsEq.obsEq3 (obsEq_requireZeros_nextRoot _ _)) ?_
  refine ObsEq3.bind_right _ fun root2 => ?_
  refine ObsEq3.trans (ObsEq.obsEq3 (obsEq_requireZeros_nextScalar _ _)) ?_
  refine ObsEq3.bind_right _ fun ood2 => ?_
  refine ObsEq3.bind_right _ fun _ => ?_
  refine ObsEq3.bind_right _ fun pd => ?_
  -- The values at `t`.
  rw [forIn_reads_of tableReads (tablesStep D.shape.heights (eqKernel (squares (bus.getD 0 0) 4)) (bus.getD 1 0)
    (digits (pd.getD 0 0) (max D.shape.heap.h (D.shape.constraintVars + 4) + 2)))]
  swap
  · intro table s
    simp [map_eq_bind_pure_comp, tablesStep]
  rw [show valsCountK = (tablesKeccak.map tableReads).sum + 7 from rfl, nextScalars_add, nextScalars_seven,
    nextScalars_fix (tablesKeccak.map tableReads).sum]
  simp only [bind_assoc, pure_bind, bind_map_left]
  refine ObsEq3.bind_right _ fun vt => ?_
  refine ObsEq3.bind_right _ fun a1 => ?_
  refine ObsEq3.bind_right _ fun a2 => ?_
  refine ObsEq3.bind_right _ fun a3 => ?_
  refine ObsEq3.bind_right _ fun a4 => ?_
  refine ObsEq3.bind_right _ fun a5 => ?_
  refine ObsEq3.bind_right _ fun a6 => ?_
  refine ObsEq3.bind_right _ fun a7 => ?_
  simp only [fixLen_fixLen]
  -- `ρ, λ, f_4, f_5`.
  refine ObsEq3.bind_right _ fun late => ?_
  -- The batch.
  have hc2 := mainRelsK_c2 D.shape D.valid.1 (publicWordsOf input.toList) (countsBits D.shape.heights rows)
    (squares (bus.getD 0 0) 4) (bus.getD 1 0) (bus.getD 2 0) (pd.getD 0 0)
    (fixLen (tablesKeccak.map tableReads).sum vt ++ [a1, a2, a3, a4, a5, a6, a7])
  simp only [mainRelsK, tablesReadsK, getD_fixLen_append, getD_fixLen_append_zero, List.getD_cons_zero,
    List.getD_cons_succ, List.take_left', length_fixLen] at hc2
  have hlen := mainCombinedK_length D.shape (publicWordsOf input.toList) (countsBits D.shape.heights rows)
    (squares (bus.getD 0 0) 4) (bus.getD 1 0) (bus.getD 2 0) (pd.getD 0 0)
    (fixLen (tablesKeccak.map tableReads).sum vt ++ [a1, a2, a3, a4, a5, a6, a7])
    ((KF.kOutT κ (KF.sampRec3 κ) ((((none, []), [bus.getD 3 0]) :: fitN (27 + κ) d) ++
      [((none, fixLen 64 slices), [])])).1,
      .ring (pd.drop 1 ++ [late.getD 2 0, late.getD 3 0])
        (Flock.towerTarget (fixLen 64 slices) (pd.drop 1 ++ [late.getD 2 0, late.getD 3 0]))) (late.getD 0 0)
  simp only [mainRelsK, flockClaimK, tablesReadsK, getD_fixLen_append, getD_fixLen_append_zero,
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
    rw [main4Prog0K_tailZeros D F3 hF3 np input rows _ _ _ _ _ (length_fitN _ _),
      main4Prog0K_out D F3 hF3 np input rows _ _ _ _ _ (length_fitN _ _)]
    simp only [batchPureWK_narrow, main3OutK, mainRelsK, flockClaimK, tablesReadsK, getD_fixLen_append,
      getD_fixLen_append_zero, List.getD_cons_zero, List.getD_cons_succ, List.headD_cons, Option.getD_some,
      List.take_left', length_fixLen, List.drop_left', prog_out_fd4 F3 hF3 _ _ (length_fitN _ _), headD_take_one,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero]
  · exact chObl_bind (chObl_nextScalars _) fun _ => chObl_bind (chObl_requireZeros _) fun _ => chObl_pure _

/-- **The counts' zero is invisible** (as `link3_countsK`). -/
theorem link4_countsK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (np : ℕ) (input : Vector UInt8 32) (P : KeccakState → m KeccakState) :
    ObsEq (readCounts D.shape.heights >>= fun rows => (main4Prog0K D F3 np input rows).runW P)
      (readCounts D.shape.heights >>= fun rows => (main4ProgK D F3 np input rows).runW P) := by
  intro c
  have h1 : ObsEq (readCounts (m := m) D.shape.heights >>= fun rows => (main4ProgK D F3 np input rows).runW P)
      (readCounts (m := m) D.shape.heights >>= fun rows =>
        ChainProg.requireZeros [countsZeroK D.shape.heights rows] >>= fun _ =>
          (main4Prog0K D F3 np input rows).runW P) := by
    refine ObsEq.bind_right _ fun rows => obsEq_headW (main4ProgK D F3 np input rows)
      (main4Prog0K D F3 np input rows) [countsZeroK D.shape.heights rows] P 3 _ (rec4Rounds_eq κ valsCountK np)
      (rec4Rounds_eq κ valsCountK np) rfl (pv4_ne (by omega)) (funext fun msg => ?_)
      (funext fun msg => zeros4K0_ne (by simp only [List.length_nil]; omega) msg)
      (fun d hd => funext fun msg => ?_) rfl rfl rfl
    · show zeros4K _ _ κ [] msg = _
      rw [zeros4K, ite_eq_left (show ([] : Done).length = 0 from rfl)]
    · show zeros4K _ _ κ d msg = zeros4K0 κ d msg
      unfold zeros4K zeros4K0
      rw [ite_eq_right (by simpa using hd)]
  rw [h1 c]
  obtain ⟨q, hq, hspec⟩ := readCounts_spec (m := m) D.shape.heights c
  rw [run_bind_of _ _ c q hq, run_bind_of _ _ c q hq]
  rcases q with ⟨r, c1⟩
  cases r with
  | error e => rfl
  | ok rows =>
    dsimp only
    refine (obsOf_requireZeros_of _ _ (obl_runW _ P) c1 fun hz => ?_).symm
    obtain ⟨hl, hb⟩ := hspec rows rfl
    have h6 := D.valid.1
    have hfit : CountsInRange D.shape.heights rows :=
      ⟨by rw [hl, h6], fun j hj => (hb hz).2 j (by rw [h6]; exact hj)⟩
    simp [countsZeroK, hfit]

/-- **The Keccak verifier's code-level link at π1-rec4, observationally.** -/
theorem link4_obsK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (hF3 : F3.prog = KF.kProg3 κ) (hκ : D.shape.heights.getD opSha3 0 = κ) (np : ℕ)
    (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1) (input : Vector UInt8 32) (P : KeccakState → m KeccakState) :
    ObsEq3 (reduceWithK4 P D.shape (publicWordsOf input.toList) keccakRec4 .point)
      (readCounts D.shape.heights >>= fun rows => (main4ProgK D F3 np input rows).runW P) :=
  (link4_obs0K D F3 hF3 hκ np hV input P).trans (link4_countsK D F3 np input P).obsEq3

end Monad

/-! ## The code-level link -/

/-- **The Keccak verifier's code-level link at π1-rec4** (`UniCodeK4`), for every deployment whose `SHA3` height is
`κ` and whose batch has `2 np + 1` variables, and π1-rec3's Flock phase `F3` (its program `KF.kProg3 κ`): after the
row counts, `reduceWithK4 … keccakRec4` is `main4ProgK` on `rec4Rounds κ valsCountK np`, `C2`'s slices before its
root, with a tail of three, up to `obsOf3`. -/
def uniCodeK4 (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (hF3 : F3.prog = KF.kProg3 κ) (hκ : D.shape.heights.getD opSha3 0 = κ) (np : ℕ)
    (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1) : UniCodeK4 D κ valsCountK np where
  prog := main4ProgK D F3 np
  rounds_eq _ _ := rfl
  tail_eq _ _ := rfl
  pv_eq _ _ := rfl
  link := fun input {_} _ _ P c₀ => link4_obsK D F3 hF3 hκ np hV input P c₀

/-- `uniCodeK4` at any number of values `nV = valsCountK` (an identity model's). -/
def uniCodeK4At (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (hF3 : F3.prog = KF.kProg3 κ) (hκ : D.shape.heights.getD opSha3 0 = κ) (nV np : ℕ) (hnV : nV = valsCountK)
    (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1) : UniCodeK4 D κ nV np where
  prog := main4ProgK D F3 np
  rounds_eq _ _ := by rw [hnV]; rfl
  tail_eq _ _ := rfl
  pv_eq _ _ := rfl
  link := (uniCodeK4 D F3 hF3 hκ np hV).link

/-- π1-rec3's Flock phase on the Keccak-f block has `KF.kProg3 κ` as its program (`uniCodeK4`'s `hF3`). -/
theorem kFlockSoundRec3_prog (F : KeccakVm.KeccakFlockSpec) (hT : KF.TerminalSpecK F) (κ : ℕ) :
    (KF.kFlockSoundRec3 F hT κ).prog = KF.kProg3 κ := rfl

theorem uniCodeK4At_prog (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (hF3 : F3.prog = KF.kProg3 κ) (hκ : D.shape.heights.getD opSha3 0 = κ)
    (nV np : ℕ) (hnV : nV = valsCountK) (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1) :
    (uniCodeK4At D F3 hF3 hκ nV np hnV hV).prog = main4ProgK D F3 np := rfl

/-! ## Facts of the link the Fiat–Shamir layer reads -/

theorem getD_of_length_le {l : Done} {n : ℕ} (h : l.length ≤ n) : l.getD n default = default := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

theorem getD_three_mid (A R : Done) (x y z : UMsg × List E) (i : ℕ) (h : A.length + 1 = i) :
    (A ++ [x, y, z] ++ R).getD i default = y := by
  subst h
  rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp

theorem getD_three_past (A : Done) (x y z : UMsg × List E) (i : ℕ) (h : A.length + 1 ≤ i)
    (hy : y.1.1 = none) (hz : z.1.1 = none) : ((A ++ [x, y, z] ++ []).getD i default).1.1 = none := by
  rw [List.append_nil, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  obtain ⟨k, hk⟩ : ∃ k, i - A.length = k + 1 := ⟨i - A.length - 1, by omega⟩
  rw [hk]
  rcases k with _ | _ | k
  · simpa using hy
  · simpa using hz
  · simp
    rfl

/-- **`C2`'s root in π1-rec4's transcript read as π1-rec3's**: π1-rec3's `C2` round (index `30 + κ`) carries the root
of π1-rec4's (index `28 + κ`), for every transcript. -/
theorem toRec3_root2 (κ : ℕ) (done : Done) :
    ((toRec3 κ done).getD (30 + κ) default).1.1 = (done.getD (28 + κ) default).1.1 := by
  simp only [toRec3]
  by_cases h : 28 + κ < done.length
  · have hv : (vFront4 κ done).length = 28 + κ := by
      simp only [vFront4, List.length_cons, List.length_take, List.length_drop]
      omega
    rw [getD_three_mid _ _ _ _ _ _ (by simp only [List.length_append, List.length_singleton, hv]; omega)]
  · have hv : (vFront4 κ done).length ≤ 28 + κ := by
      simp only [vFront4, List.length_cons, List.length_take]
      omega
    rw [getD_of_length_le (show done.length ≤ 28 + κ by omega),
      getD_of_length_le (show done.length ≤ 29 + κ by omega),
      List.drop_eq_nil_of_le (show done.length ≤ 30 + κ by omega)]
    exact getD_three_past _ _ _ _ _ (by simp only [List.length_append, List.length_singleton]; omega) rfl rfl

/-- **The chain program's result names the roots the transcript carries** at rounds `0` (`C1`) and `28 + κ` (`C2`),
at π1-rec4's shape (as `UniOutRootsK3`), for every transcript and tail. -/
def UniOutRootsK4 (D : KDeployment) {κ nV np : ℕ} (C : UniCodeK4 D κ nV np) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (done : Done) (tl : List E),
    ((C.prog input rows).out done tl).roots =
      ((done.getD 0 default).1.1.getD default, (done.getD (28 + κ) default).1.1.getD default)

/-- `main4ProgK`'s result names them (`main3OutK` on `toRec3`). -/
theorem uniOutRootsK4_main4ProgK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (hF3 : F3.prog = KF.kProg3 κ) (np : ℕ) (input : Vector UInt8 32)
    (rows : List ℕ) (done : Done) (tl : List E) :
    ((main4ProgK D F3 np input rows).out done tl).roots =
      ((done.getD 0 default).1.1.getD default, (done.getD (28 + κ) default).1.1.getD default) := by
  have hn : F3.prog.rounds.length + 1 = 30 + κ := by
    rw [hF3, show (KF.kProg3 κ).rounds = KF.kRounds κ KF.r0Rec3 from rfl, KF.length_kRounds]
    omega
  show ((main3ProgK D F3 np input rows).out (toRec3 κ done) tl).roots = _
  rw [main3ProgK_out]
  show (((toRec3 κ done).getD 0 default).1.1.getD default,
    ((toRec3 κ done).getD (F3.prog.rounds.length + 1) default).1.1.getD default) = _
  rw [hn, toRec3_root2]
  rfl

theorem uniOutRootsK4_uniCodeK4At (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (hF3 : F3.prog = KF.kProg3 κ) (hκ : D.shape.heights.getD opSha3 0 = κ)
    (nV np : ℕ) (hnV : nV = valsCountK) (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1) :
    UniOutRootsK4 D (uniCodeK4At D F3 hF3 hκ nV np hnV hV) := fun input rows done tl =>
  uniOutRootsK4_main4ProgK D F3 hF3 np input rows done tl

theorem uniOutRootsK4_uniCodeK4 (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (hF3 : F3.prog = KF.kProg3 κ) (hκ : D.shape.heights.getD opSha3 0 = κ)
    (np : ℕ) (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1) :
    UniOutRootsK4 D (uniCodeK4 D F3 hF3 hκ np hV) := fun input rows done tl =>
  uniOutRootsK4_main4ProgK D F3 hF3 np input rows done tl

/-- **The chain program's checks give the counts in range** at π1-rec4's shape: round `0`'s zero is the counts'. -/
theorem countsZeroK4_holds (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (np : ℕ) (input : Vector UInt8 32) (rows : List ℕ) (done : Done)
    (tl : List E) (hd : done ≠ []) (hz : (main4ProgK D F3 np input rows).ZerosVanish done tl) :
    CountsInRange D.shape.heights rows := by
  have hlen : 0 < done.length := List.length_pos_iff.mpr hd
  have h0 := hz.1 0 hlen
  have hz0 : (main4ProgK D F3 np input rows).zeros [] = fun _ => [countsZeroK D.shape.heights rows] := by
    funext msg
    show zeros4K _ _ κ [] msg = _
    rw [zeros4K, ite_eq_left (show ([] : Done).length = 0 from rfl)]
  rw [List.take_zero, hz0] at h0
  have h1 := h0 _ (List.mem_singleton_self _)
  by_contra hc
  simp [countsZeroK, hc] at h1

/-- On a completed transcript of π1-rec4's rounds: round `0`'s zero is `countsZeroK`. -/
theorem countsZeroK4_of_fits (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (nV np : ℕ) (input : Vector UInt8 32) (rows : List ℕ) (done : Done)
    (tl : List E) (hd : DoneFits (rec4Rounds κ nV np) done)
    (hz : (main4ProgK D F3 np input rows).ZerosVanish done tl) :
    CountsInRange D.shape.heights rows := by
  refine countsZeroK4_holds D F3 np input rows done tl ?_ hz
  rintro rfl
  have := hd.length_eq
  rw [length_rec4Rounds] at this
  simp only [List.length_nil] at this
  omega

end UniKeccakSound

/-- info: 'UniKeccakSound.uniCodeK4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniCodeK4

/-- info: 'UniKeccakSound.uniCodeK4At' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniCodeK4At

/-- info: 'UniKeccakSound.uniOutRootsK4_uniCodeK4At' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniOutRootsK4_uniCodeK4At

/-- info: 'UniKeccakSound.countsZeroK4_of_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.countsZeroK4_of_fits

/-- info: 'UniKeccakSound.KF.kflock_link4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.kflock_link4
