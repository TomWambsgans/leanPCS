-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The last link is π1-rec3's (`Ids3/Final3.lean`'s
-- `uniFinalK3_uniCodeK3At`, through `FinalK3.lean`'s `hlink_uniPiopK3`) on π1-rec4's transcript read as π1-rec3's
-- (`Prog4.lean`'s `toRec3`, `Piop4.lean`'s `opT`).
import UniKeccakSound.Rec4.PiopSound4
import UniKeccakSound.Ids3.Final3
import UniKeccakSound.FinalK3

/-!
# The last link of π1-rec4

On a completed transcript of π1-rec4's rounds (`rec4Rounds κ valsCountK np`) whose zeros (`main4ProgK`'s) vanish and
whose three claims are true, the transcript read as π1-rec3's (`toRec3 κ`) is a completed transcript of π1-rec3's
rounds (`doneFits_toRec3`) whose zeros (`main3ProgK`'s) vanish (`zerosVanish_toRec3`: the counts' in round `0`, Flock's
structured terminal, the batch's terminal, which `main4ProgK` requires where π1-rec4 reads them) and whose claims are
the same (`main4ProgK`'s result is `main3ProgK`'s on `toRec3`). π1-rec3's last link (`uniFinalK3_uniCodeK3At`) gives
π1-rec3's last state on its opened transcript, which is π1-rec4's read as π1-rec3's (`opT_openedOf`), that is,
π1-rec4's last state (`uniSK4`).

* **`hzb_uniIdsK3`**, **`hpolys_uniIdsK3`**: the identity model `uniIdsK3`'s merge polynomial and identities read
  Flock's point only, which Flock's last round (the slices, the map) does not change (`kOutT_fst_append`);
* **`uniFinalK4`**: the last link of `uniPiopK4` for `uniIdsK3`, the paired batch and `main4ProgK`, under π1-rec3's
  hypotheses (`FlockGoodDoneK`, `WeightMleK`, `LayoutVarsSmall3K`).
-/

namespace UniKeccakSound.Rec4

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniKeccak UniKeccakSound.Ids Finset
open scoped ENNReal

/-! ## Completed transcripts -/

theorem doneFits_append : ∀ (a b : List Compose.RoundSpec) (d1 d2 : Done), DoneFits a d1 → DoneFits b d2 →
    DoneFits (a ++ b) (d1 ++ d2)
  | [], _, [], _, _, h => h
  | _ :: a, b, (_, _) :: d1, d2, h1, h2 => ⟨h1.1, h1.2.1, doneFits_append a b d1 d2 h1.2.2 h2⟩
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim

section Cut

variable {κ : ℕ}

/-- **A completed transcript of π1-rec4's rounds, cut**: round `0`, Flock's rounds between, `C2`'s, the values', the
batch's. -/
theorem rec4_cut {nV np : ℕ} (done : Done) (hd : DoneFits (rec4Rounds κ nV np) done) :
    ∃ x0 M y v B, done = x0 :: (M ++ y :: v :: B) ∧ M.length = 27 + κ ∧
      x0.1.Fits ⟨true, 1, 3⟩ ∧ x0.2.length = 4 ∧ DoneFits (kRoundsMid κ) M ∧
      y.1.Fits ⟨true, 65, 4⟩ ∧ y.2.length = 5 ∧ v.1.Fits ⟨false, nV, 3⟩ ∧ v.2.length = 4 ∧
      DoneFits (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩]) B := by
  have e : rec4Rounds κ nV np = ⟨true, 1, 3⟩ :: (kRoundsMid κ ++
      (⟨true, 65, 4⟩ :: ⟨false, nV, 3⟩ :: (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩]))) := by
    simp [rec4Rounds]
  rw [e] at hd
  rcases done with _ | ⟨⟨m0, c0⟩, rest⟩
  · exact hd.elim
  obtain ⟨h0, h0c, hr⟩ := hd
  obtain ⟨M, R, rfl, hM, hR⟩ := doneFits_append_split _ _ _ hr
  rcases R with _ | ⟨⟨my, cy⟩, _ | ⟨⟨mv, cv⟩, B⟩⟩
  · exact hR.elim
  · exact hR.2.2.elim
  obtain ⟨hy, hyc, hv, hvc, hB⟩ := hR
  refine ⟨(m0, c0), M, (my, cy), (mv, cv), B, rfl, ?_, h0, h0c, hM, hy, hyc, hv, hvc, hB⟩
  rw [doneFits_length _ _ hM, length_kRoundsMid]

/-- **π1-rec4's transcript as π1-rec3's, on the cut.** -/
theorem toRec3_cut (x0 : UMsg × List E) (M : Done) (y v : UMsg × List E) (B : Done) (hM : M.length = 27 + κ) :
    toRec3 κ (x0 :: (M ++ y :: v :: B)) = (x0.1, x0.2.take 3) :: ((((none, []), [x0.2.getD 3 0]) :: M) ++
      ((none, y.1.2.take 64), y.2.drop 1 ++ v.2.drop 2) :: ((y.1.1, y.1.2.drop 64), y.2.take 1) ::
        (v.1, v.2.take 2) :: B) := by
  have hy : (x0 :: (M ++ y :: v :: B)).getD (28 + κ) default = y := by
    rw [show 28 + κ = (27 + κ) + 1 by omega, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_append_right (by omega), hM, Nat.sub_self]
    rfl
  have hv : (x0 :: (M ++ y :: v :: B)).getD (29 + κ) default = v := by
    rw [show 29 + κ = (27 + κ) + 1 + 1 by omega, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_append_right (by omega), hM, show 27 + κ + 1 - (27 + κ) = 1 by omega]
    rfl
  have hB : (x0 :: (M ++ y :: v :: B)).drop (30 + κ) = B := by
    rw [show 30 + κ = (M.length + 2) + 1 by omega, List.drop_succ_cons, List.drop_append,
      List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]
    rfl
  have hMt : ((x0 :: (M ++ y :: v :: B)).drop 1).take (27 + κ) = M := by
    rw [List.drop_one, List.tail_cons, List.take_left' hM]
  unfold toRec3 vFront4
  simp only [hy, hv, hB, hMt, List.getD_cons_zero, List.cons_append, List.append_assoc,
    List.nil_append]

/-- Flock's rounds of an opened transcript: no root. -/
def strip (x : UMsg × List E) : (Option Stk × List E) × List E := ((none, x.1.2), x.2)

theorem map_zipIdx_strip (nF : ℕ) (c1 c2 : Stk) : ∀ (l : Done) (k : ℕ), 0 < k →
    (nF + 1 < k ∨ k + l.length ≤ nF + 1) →
    (l.zipIdx k).map (fun x : (UMsg × List E) × ℕ =>
        ((if x.2 = 0 then some c1 else if x.2 = nF + 1 then some c2 else none, x.1.1.2), x.1.2)) = l.map strip
  | [], _, _, _ => rfl
  | x :: l, k, hk, h => by
    simp only [List.zipIdx_cons, List.map_cons, List.cons.injEq]
    refine ⟨?_, map_zipIdx_strip nF c1 c2 l (k + 1) (by omega) ?_⟩
    · rw [ite_eq_right (by omega), ite_eq_right (by simp at h; omega)]
      rfl
    · simp only [List.length_cons] at h
      omega

/-- **An opened transcript, on a cut**: `c1` at round `0`, `c2` at round `nF + 1`, no root elsewhere. -/
theorem openedOf_cut (nF : ℕ) (c1 c2 : Stk) (x0 : UMsg × List E) (M : Done) (y : UMsg × List E) (B : Done)
    (hM : M.length = nF) :
    openedOf nF c1 c2 (x0 :: (M ++ y :: B)) =
      ((some c1, x0.1.2), x0.2) :: (M.map strip ++ ((some c2, y.1.2), y.2) :: B.map strip) := by
  unfold openedOf
  rw [List.zipIdx_cons, List.map_cons, List.zipIdx_append, List.map_append, List.zipIdx_cons, List.map_cons,
    map_zipIdx_strip nF c1 c2 M 1 (by omega) (Or.inr (by omega)),
    map_zipIdx_strip nF c1 c2 B _ (by omega) (Or.inl (by omega))]
  simp only [ite_true, hM]
  rw [ite_eq_right (by omega), show 0 + 1 + nF = nF + 1 by omega, ite_eq_left rfl]

/-- **`opT` on a cut.** -/
theorem opT_cut (a : (Option Stk × List E) × List E) (M : Op Stk) (y v : (Option Stk × List E) × List E)
    (B : Op Stk) (hM : M.length = 27 + κ) :
    opT κ (a :: (M ++ y :: v :: B)) = [(a.1, a.2.take 3), ((none, []), [a.2.getD 3 0])] ++ M ++
      [((none, y.1.2.take 64), y.2.drop 1 ++ v.2.drop 2), ((y.1.1, y.1.2.drop 64), y.2.take 1),
        (v.1, v.2.take 2)] ++ B := by
  have hy : rd (a :: (M ++ y :: v :: B)) (28 + κ) = y := by
    unfold rd
    rw [show 28 + κ = (27 + κ) + 1 by omega, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_append_right (by omega), hM, Nat.sub_self]
    rfl
  have hv : rd (a :: (M ++ y :: v :: B)) (29 + κ) = v := by
    unfold rd
    rw [show 29 + κ = (27 + κ) + 1 + 1 by omega, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_append_right (by omega), hM, show 27 + κ + 1 - (27 + κ) = 1 by omega]
    rfl
  have hB : (a :: (M ++ y :: v :: B)).drop (30 + κ) = B := by
    rw [show 30 + κ = (M.length + 2) + 1 by omega, List.drop_succ_cons, List.drop_append,
      List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]
    rfl
  have hMt : ((a :: (M ++ y :: v :: B)).drop 1).take (27 + κ) = M := by
    rw [List.drop_one, List.tail_cons, List.take_left' hM]
  have h0 : rd (a :: (M ++ y :: v :: B)) 0 = a := rfl
  rw [opT, ite_eq_right (by simp; omega)]
  simp only [r0Op, vr0Op, lastOp, hy, hv, hB, hMt, h0]

/-- **π1-rec4's opened transcript read as π1-rec3's is π1-rec3's opened transcript of `toRec3`.** -/
theorem opT_openedOf {nV np : ℕ} (c1 c2 : Stk) (done : Done) (hd : DoneFits (rec4Rounds κ nV np) done) :
    opT κ (openedOf (27 + κ) c1 c2 done) = openedOf (29 + κ) c1 c2 (toRec3 κ done) := by
  obtain ⟨x0, M, y, v, B, rfl, hM, -⟩ := rec4_cut done hd
  rw [toRec3_cut x0 M y v B hM, openedOf_cut _ c1 c2 x0 M y (v :: B) hM,
    show (((none, []), [x0.2.getD 3 0]) :: M) ++ ((none, y.1.2.take 64), y.2.drop 1 ++ v.2.drop 2) ::
        ((y.1.1, y.1.2.drop 64), y.2.take 1) :: (v.1, v.2.take 2) :: B =
      ((((none, []), [x0.2.getD 3 0]) :: M) ++ [((none, y.1.2.take 64), y.2.drop 1 ++ v.2.drop 2)]) ++
        ((y.1.1, y.1.2.drop 64), y.2.take 1) :: (v.1, v.2.take 2) :: B by simp,
    openedOf_cut _ c1 c2 _ _ _ _ (by simp [hM]; omega), List.map_cons,
    opT_cut _ _ _ _ _ (by simp [hM])]
  simp [strip]

/-- **π1-rec4's completed transcripts read as π1-rec3's are π1-rec3's**, Flock's rounds `kRounds κ r0Rec3`. -/
theorem doneFits_toRec3 {nV np : ℕ} (done : Done) (hd : DoneFits (rec4Rounds κ nV np) done) :
    DoneFits (rec3Rounds (KF.kRounds κ KF.r0Rec3) nV np 1) (toRec3 κ done) := by
  obtain ⟨x0, M, y, v, B, rfl, hM, ⟨h01, h02⟩, h0c, hMf, ⟨hy1, hy2⟩, hyc, ⟨hv1, hv2⟩, hvc, hB⟩ := rec4_cut done hd
  rw [toRec3_cut x0 M y v B hM]
  have e : rec3Rounds (KF.kRounds κ KF.r0Rec3) nV np 1 = ⟨true, 1, 2⟩ :: ((KF.r0Rec3 :: kRoundsMid κ) ++
      ⟨false, 64, 5⟩ :: ⟨true, 1, 0⟩ :: ⟨false, nV, 1⟩ :: (List.replicate np ⟨false, 8, 0⟩ ++
        [⟨false, 2, 0⟩])) := by
    simp [rec3Rounds, KF.kRounds, kRoundsPre_eq]
  rw [e]
  refine ⟨⟨h01, h02⟩, by simp [h0c], doneFits_append _ _ _ _ ⟨⟨rfl, rfl⟩, rfl, hMf⟩
    ⟨⟨rfl, by simp [hy2]⟩, by simp [hyc, hvc], ⟨hy1, by simp [hy2]⟩, by simp [hyc], ⟨hv1, hv2⟩, by simp [hvc], hB⟩⟩

end Cut

/-! ## The zeros and the claims -/

section Zeros

theorem cut_take_drop {α : Type} {x : α} (P : List α) {L : α} {R : List α} {n : ℕ} (hn : P.length + 1 = n) :
    ((x :: (P ++ L :: R)).take n).drop 1 = P := by
  subst hn
  rw [List.take_succ_cons, List.drop_one, List.tail_cons, List.take_left' rfl]

theorem cut_getElem {α : Type} {x : α} (P : List α) {L : α} {R : List α} {n : ℕ} (hn : P.length + 1 = n)
    (h : n < (x :: (P ++ L :: R)).length) : (x :: (P ++ L :: R))[n]'h = L := by
  subst hn
  rw [List.getElem_cons_succ, List.getElem_append_right (le_refl _)]
  simp

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (hT : KF.TerminalSpecK F) (np : ℕ)
  (input : Vector UInt8 32) (rows : List ℕ)

theorem kFlockSoundRec3_zeros (d : Done) (msg : UMsg) :
    (KF.kFlockSoundRec3 F hT κ).prog.zeros d msg =
      if d.length = 28 + κ then [KF.kTerm κ (KF.sampRec3 κ) d msg.2] else [] := rfl

theorem kFlockSoundRec3_tailZeros (d : Done) (tl : List E) :
    (KF.kFlockSoundRec3 F hT κ).prog.tailZeros d tl = [] := rfl

/-- **π1-rec4's zeros vanishing make π1-rec3's vanish on `toRec3`**: the counts' (round `0` of both), Flock's
structured terminal (π1-rec3's Flock's last round, π1-rec4's `C2`'s round, on the same front and slices), the
batch's terminal (the same). -/
theorem zerosVanish_toRec3 (done : Done) (tl : List E) (hd : DoneFits (rec4Rounds κ valsCountK np) done)
    (hz : (main4ProgK D (KF.kFlockSoundRec3 F hT κ) np input rows).ZerosVanish done tl) :
    (main3ProgK D (KF.kFlockSoundRec3 F hT κ) np input rows).ZerosVanish (toRec3 κ done) tl := by
  obtain ⟨x0, M, y, v, B, rfl, hM, -⟩ := rec4_cut done hd
  have h2 : ∀ z ∈ (main3ProgK D (KF.kFlockSoundRec3 F hT κ) np input rows).tailZeros
      (toRec3 κ (x0 :: (M ++ y :: v :: B))) tl, z = 0 := hz.2
  rw [toRec3_cut x0 M y v B hM] at h2 ⊢
  refine ⟨fun j hj z hzj => ?_, h2⟩
  by_cases h0 : j = 0
  · subst h0
    rw [List.take_zero, main3ProgK_zeros_nil] at hzj
    have h := hz.1 0 (by simp)
    rw [List.take_zero] at h
    exact h z (by simpa [main4ProgK, zeros4K] using hzj)
  rw [main3ProgK_zeros_ne _ _ _ _ _ (by
    intro he
    rw [List.take_eq_nil_iff] at he
    rcases he with he | he
    · exact h0 he
    · simp at he)] at hzj
  have hlen : (((none, []), [x0.2.getD 3 0]) :: M : Done).length = 28 + κ := by simp [hM]; omega
  have hjl := min_eq_left hj.le
  unfold mainZerosK at hzj
  rw [List.length_take, hjl, nF3 (κ := κ) hT] at hzj
  by_cases h1 : j ≤ 29 + κ
  · rw [ite_eq_left ⟨by omega, h1⟩, kFlockSoundRec3_zeros] at hzj
    by_cases h2 : j = 29 + κ
    · subst h2
      rw [List.length_drop, List.length_take, hjl, ite_eq_left (by omega)] at hzj
      rw [cut_take_drop (((none, []), [x0.2.getD 3 0]) :: M) (by rw [hlen]; omega),
        cut_getElem (((none, []), [x0.2.getD 3 0]) :: M) (by rw [hlen]; omega), List.mem_singleton] at hzj
      have h := hz.1 (28 + κ) (by simp; omega)
      have hx : (x0 :: (M ++ y :: v :: B)).take (28 + κ) = x0 :: M := by
        rw [show 28 + κ = (27 + κ) + 1 by omega, List.take_succ_cons, List.take_left' hM]
      have hy : ((x0 :: (M ++ y :: v :: B))[28 + κ]'(by simp; omega)) = y := by
        simp only [show 28 + κ = (27 + κ) + 1 by omega, List.getElem_cons_succ]
        rw [List.getElem_append_right (by omega)]
        simp [hM]
      have hvf : vFront4 κ (x0 :: M) = ((none, []), [x0.2.getD 3 0]) :: M := by
        simp only [vFront4, List.getD_cons_zero, List.drop_one, List.tail_cons]
        rw [List.take_of_length_le (by omega)]
      simp only [hx, hy] at h
      refine h z ?_
      show z ∈ zeros4K D.shape.heights rows κ (x0 :: M) y.1
      rw [zeros4K, ite_eq_right (by simp), ite_eq_left (by simp; omega), hvf]
      rw [hzj]
      exact List.mem_singleton_self _
    · rw [List.length_drop, List.length_take, hjl, ite_eq_right (by omega)] at hzj
      exact absurd hzj List.not_mem_nil
  · rw [ite_eq_right (by omega)] at hzj
    by_cases h2 : j = 29 + κ + 1
    · rw [ite_eq_left h2, kFlockSoundRec3_tailZeros] at hzj
      exact absurd hzj List.not_mem_nil
    · rw [ite_eq_right h2] at hzj
      exact absurd hzj List.not_mem_nil

end Zeros

/-! ## The identity model reads Flock's point only -/

section Model

theorem kOutT_fst_append (κ : ℕ) (d : Done) (hd : d.length = 28 + κ) (x y : UMsg × List E) :
    (KF.kOutT κ (KF.sampRec3 κ) (d ++ [x])).1 = (KF.kOutT κ (KF.sampRec3 κ) (d ++ [y])).1 := by
  have e0 : ∀ x : UMsg × List E, KF.sampRec3 κ (d ++ [x]) =
      squares ((FlockSound.Uni.rd d 0).2.headD 0) (7 + κ) := fun x => by
    rw [KF.sampRec3, FlockSound.Uni.rd_append_left (by omega)]
  have e1 : ∀ x : UMsg × List E, FlockSound.Uni.rd (d ++ [x]) 1 = FlockSound.Uni.rd d 1 := fun x =>
    FlockSound.Uni.rd_append_left (by omega)
  have e2 : ∀ x : UMsg × List E, ((d ++ [x]).drop 2).take (14 + κ) = (d.drop 2).take (14 + κ) := fun x => by
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  have e3 : ∀ x : UMsg × List E, FlockSound.Uni.rd ((d ++ [x]).drop (16 + κ)) 0 =
      FlockSound.Uni.rd (d.drop (16 + κ)) 0 := fun x => by
    rw [FlockSound.Uni.rd_drop, FlockSound.Uni.rd_drop, FlockSound.Uni.rd_append_left (by omega)]
  have e4 : ∀ x : UMsg × List E, ((d ++ [x]).drop (17 + κ)).take 11 = (d.drop (17 + κ)).take 11 := fun x => by
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  simp only [KF.kOutT, KF.kOutOf, e0, e1, e2, e3, e4]

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (hT : KF.TerminalSpecK F) (N : ℕ)
  (h : IdsHypsK F D κ N) (d n : ℕ) (g : IdsGapsK D (KF.kFlockSoundRec3 F hT κ) d n) (np : ℕ)
  (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1)

/-- **The merge polynomial reads Flock's point only.** -/
theorem hzb_uniIdsK3 (fd : Done) (x y : UMsg × List E) (hfd : fd.length = 28 + κ) :
    (uniIdsK3 D (KF.kFlockSoundRec3 F hT κ) N h d n g np hV).zb (fd ++ [x]) =
      (uniIdsK3 D (KF.kFlockSoundRec3 F hT κ) N h d n g np hV).zb (fd ++ [y]) := by
  show zBad D.shape ((KF.kOutT κ (KF.sampRec3 κ) (fd ++ [x])).1.getD 0 0) =
    zBad D.shape ((KF.kOutT κ (KF.sampRec3 κ) (fd ++ [y])).1.getD 0 0)
  rw [kOutT_fst_append κ fd hfd x y]

/-- **The identities read Flock's point only.** -/
theorem hpolys_uniIdsK3 (s : USt) (c1 : Stk) (ch : List E) (fd : Done) (x y : UMsg × List E) (c2 : Stk)
    (hfd : fd.length = 28 + κ) :
    (uniIdsK3 D (KF.kFlockSoundRec3 F hT κ) N h d n g np hV).polys s c1 ch (fd ++ [x]) c2 =
      (uniIdsK3 D (KF.kFlockSoundRec3 F hT κ) N h d n g np hV).polys s c1 ch (fd ++ [y]) c2 := by
  show polysK D (KF.kFlockSoundRec3 F hT κ) s c1 (expandCh ch) (fd ++ [x]) c2 =
    polysK D (KF.kFlockSoundRec3 F hT κ) s c1 (expandCh ch) (fd ++ [y]) c2
  have e : ((KF.kFlockSoundRec3 F hT κ).prog.out (fd ++ [x]) []).1 =
      ((KF.kFlockSoundRec3 F hT κ).prog.out (fd ++ [y]) []).1 := kOutT_fst_append κ fd hfd x y
  unfold polysK
  rw [e]

end Model

/-! ## The last link -/

/-- **The last link of π1-rec4** (`uniPiopK4`'s, for the identity model `uniIdsK3`, the paired batch
`pairBatchRec3 np` and the program `main4ProgK`): on a completed transcript of π1-rec4's rounds whose zeros vanish and
whose three claims are true, the opened transcript is π1-rec4's last state, under π1-rec3's hypotheses (Flock's result
the main line's, the weights multilinear off `Z_bad`'s roots, the stacks' variables below `256`). -/
theorem uniFinalK4 (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (hT : KF.TerminalSpecK F)
    (hκ : D.shape.heights.getD opSha3 0 = κ) (N : ℕ) (h : IdsHypsK F D κ N) (d n : ℕ)
    (g : IdsGapsK D (KF.kFlockSoundRec3 F hT κ) d n) (np : ℕ) (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1)
    (hgood : FlockGoodDoneK (KF.kFlockSoundRec3 F hT κ)) (hW : WeightMleK D (KF.kFlockSoundRec3 F hT κ))
    (hsmall : LayoutVarsSmall3K D) (s : USt) (done : Done) (tl : List E) (c1 c2 : Stk)
    (hd : DoneFits (rec4Rounds κ valsCountK np) done) (htl : tl.length = 3)
    (hz : (main4ProgK D (KF.kFlockSoundRec3 F hT κ) np s.1 s.2).ZerosVanish done tl)
    (hc : ClaimsHoldK D ((main4ProgK D (KF.kFlockSoundRec3 F hT κ) np s.1 s.2).out done tl) c1 c2) :
    ∃ p m ch, openedOf (27 + κ) c1 c2 done = p ++ [(m, ch)] ∧
      (uniPiopK4 hT (uniIdsK3 D (KF.kFlockSoundRec3 F hT κ) N h d n g np hV) (pairBatchRec3 np)
        (fun fd x y hfd => hzb_uniIdsK3 D hT N h d n g np hV fd x y hfd)
        (fun s c1 ch fd x y c2 hfd => hpolys_uniIdsK3 D hT N h d n g np hV s c1 ch fd x y c2 hfd)).post s p m ch := by
  have h3 := hlink_uniPiopK3 (KF.kFlockSoundRec3 F hT κ) (uniIdsK3 D (KF.kFlockSoundRec3 F hT κ) N h d n g np hV)
    (pairBatchRec3 np) (uniCodeK3At D (KF.kFlockSoundRec3 F hT κ) hκ valsCountK np rfl hV)
    (uniFinalK3_uniCodeK3At D (KF.kFlockSoundRec3 F hT κ) hκ N h d n g np hV hgood hW hsmall) s (toRec3 κ done) tl
    c1 c2 (doneFits_toRec3 done hd) htl (zerosVanish_toRec3 D hT np s.1 s.2 done tl hd hz) hc
  obtain ⟨p, m, ch, hpq, hpost⟩ := h3
  have hS3 : uniSK3 (KF.kFlockSoundRec3 F hT κ) (uniIdsK3 D (KF.kFlockSoundRec3 F hT κ) N h d n g np hV)
      (pairBatchRec3 np) s (openedOf (29 + κ) c1 c2 (toRec3 κ done)) := by
    have e := nF3 (κ := κ) hT
    rw [e] at hpq
    rw [hpq]
    exact hpost
  have hlen : (openedOf (27 + κ) c1 c2 done).length = 31 + κ + np := by
    rw [length_openedOf, hd.length_eq, length_rec4Rounds]
  have hne : openedOf (27 + κ) c1 c2 done ≠ [] := by
    intro he
    rw [he, List.length_nil] at hlen
    omega
  refine ⟨(openedOf (27 + κ) c1 c2 done).dropLast, ((openedOf (27 + κ) c1 c2 done).getLast hne).1,
    ((openedOf (27 + κ) c1 c2 done).getLast hne).2, (List.dropLast_append_getLast hne).symm, ?_⟩
  change uniSK4 hT _ _ s ((openedOf (27 + κ) c1 c2 done).dropLast ++
    [(((openedOf (27 + κ) c1 c2 done).getLast hne).1, ((openedOf (27 + κ) c1 c2 done).getLast hne).2)])
  rw [show (openedOf (27 + κ) c1 c2 done).dropLast ++
      [(((openedOf (27 + κ) c1 c2 done).getLast hne).1, ((openedOf (27 + κ) c1 c2 done).getLast hne).2)] =
      openedOf (27 + κ) c1 c2 done from List.dropLast_append_getLast hne]
  unfold uniSK4
  rw [ite_eq_right (by omega), opT_openedOf c1 c2 done hd]
  exact hS3

end UniKeccakSound.Rec4

/-- info: 'UniKeccakSound.Rec4.uniFinalK4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Rec4.uniFinalK4
