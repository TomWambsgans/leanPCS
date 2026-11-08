-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The links' form and the composition are
-- `UniSound/Rec3/Fs3.lean`'s, `Fs128_3.lean`'s and `Final3.lean`'s, for the Keccak verifier at `keccakRec3`.
import UniSound.Rec3.Final3
import UniSound.Rec3.Fs128_3
import UniKeccakSound.PiopSoundK3
import UniKeccakSound.FinalK

/-!
# Knowledge soundness of the Keccak verifier at π1-rec3's shape (`keccakRec3`), from its links

The links are π1-rec3's (`UniSound.UniCode3`, `UniFinal3`, `FsLayer128_3`) for the Keccak verifier:

* **`UniCodeK3`**: `reduceWithK … keccakRec3 .point` after the row counts is a chain program on `rec3Rounds`, tail
  three, up to `obsOf3` (π1-rec3's batch records its narrow challenges, `UniSound/Rec3/Fs3.lean`);
* **`UniFinalK3`**: the checks with the three point claims true make Flock's zeros vanish and the batch's last state
  hold, unless `t` is a root of the merge polynomial;
* **`FsLayer128K3`**: the Fiat–Shamir layer at `≥ 128` bits for `keccakRec3`, three openings.

**`uniKnowledgeSoundnessK3`**: `UniKnowledgeSoundnessKeccakRec3 F D (uniBound128 e)` from Flock on the Keccak-f block
(`KFlockSound F κ keccakRec3`), the identity model `UniIdsK3`, the batch `PairBatch`, the links, and every round's
error at most `e`; **`uniKnowledgeSoundnessK3_bits`** at `e = 2^35 / |E|`: at most `2^-64` for `Q ≤ 2^64`
(`UniSound.uniBound128_le_bits35`).
-/

namespace UniKeccakSound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement UniSound UniKeccak Finset WhirBridge
open scoped ENNReal

/-- **The Keccak verifier at π1-rec3's shape as a chain program** (code-level link), for its Flock phase `F3`, with
`nV` values at `t` and `np` pair rounds: after the row counts, the chain program `prog input rows` on
`rec3Rounds F3.prog.rounds nV np`, with a tail of three, runs as `reduceWithK` at the deployment's shape,
`keccakRec3`, point claims, up to `obsOf3`. -/
structure UniCodeK3 {F : KeccakVm.KeccakFlockSpec} (D : KDeployment) {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (nV np : ℕ) where
  prog : Vector UInt8 32 → List ℕ → ChainProg Reduced
  rounds_eq : ∀ input rows, (prog input rows).rounds = rec3Rounds F3.prog.rounds nV np
  tail_eq : ∀ input rows, (prog input rows).tail = 3
  link : ∀ (input : Vector UInt8 32) {m : Type → Type} [Monad m] [LawfulMonad m]
    (P : KeccakState → m KeccakState) (c₀ : Chan),
    obsOf3 <$> ((reduceWithK P D.shape (publicWordsOf input.toList) keccakRec3 .point).run.run c₀) =
      obsOf3 <$> ((readCounts D.shape.heights >>= fun rows => (prog input rows).run P).run.run c₀)

/-- **The last link at π1-rec3's shape**: the checks with the three point claims true make Flock's zeros vanish on
its transcript and the batch's last state hold at its point, unless `t` is a root of the merge polynomial. -/
def UniFinalK3 {F : KeccakVm.KeccakFlockSpec} (D : KDeployment) {κ : ℕ} (F3 : KFlockSound F κ keccakRec3) {np : ℕ}
    (I : UniIdsK3 F D F3 np) (BR : PairBatch np) (C : UniCodeK3 D F3 I.nV np) : Prop :=
  ∀ (s : USt) done tl c1 c2, DoneFits (rec3Rounds F3.prog.rounds I.nV np) done → tl.length = 3 →
    (C.prog s.1 s.2).ZerosVanish done tl → ClaimsHoldK D ((C.prog s.1 s.2).out done tl) c1 c2 →
      F3.prog.ZerosVanish (fdOf F3.prog.rounds.length (openedOf F3.prog.rounds.length c1 c2 done)) [] ∧
      ((I.zb (fdOf F3.prog.rounds.length (openedOf F3.prog.rounds.length c1 c2 done))).eval
          ((rd (openedOf F3.prog.rounds.length c1 c2 done) (F3.prog.rounds.length + 1)).2.headD 0) = 0 ∨
      BR.St (I.prod s c1 (rd (openedOf F3.prog.rounds.length c1 c2 done) 0).2
          (fdOf F3.prog.rounds.length (openedOf F3.prog.rounds.length c1 c2 done)) c2
          ((rd (openedOf F3.prog.rounds.length c1 c2 done) (F3.prog.rounds.length + 1)).2.headD 0)
          (rd (openedOf F3.prog.rounds.length c1 c2 done) (F3.prog.rounds.length + 2)).1.2
          ((rd (openedOf F3.prog.rounds.length c1 c2 done) (F3.prog.rounds.length + 2)).2.headD 0)
          ((rd (openedOf F3.prog.rounds.length c1 c2 done) (F3.prog.rounds.length + 2)).2.getD 1 0))
        (I.target s c1 (rd (openedOf F3.prog.rounds.length c1 c2 done) 0).2
          (fdOf F3.prog.rounds.length (openedOf F3.prog.rounds.length c1 c2 done)) c2
          ((rd (openedOf F3.prog.rounds.length c1 c2 done) (F3.prog.rounds.length + 1)).2.headD 0)
          (rd (openedOf F3.prog.rounds.length c1 c2 done) (F3.prog.rounds.length + 2)).1.2
          ((rd (openedOf F3.prog.rounds.length c1 c2 done) (F3.prog.rounds.length + 2)).2.headD 0)
          ((rd (openedOf F3.prog.rounds.length c1 c2 done) (F3.prog.rounds.length + 2)).2.getD 1 0))
        (brOf F3.prog.rounds.length (openedOf F3.prog.rounds.length c1 c2 done)))

/-- **The Fiat–Shamir layer at `≥ 128` bits at π1-rec3's shape**: every round-by-round sound protocol on its rounds,
errors at most `e`, first state the Keccak VM's relation, last state from the checks with true claims, makes the
deployed Keccak verifier at `keccakRec3` knowledge sound for `uniExtractorK F D` with the bound `uniBound128 e`. -/
def FsLayer128K3 (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (nV np : ℕ) (C : UniCodeK3 D F3 nV np) : Prop :=
  ∀ (R : RbrPiop (rec3Rounds F3.prog.rounds nV np) USt Stk) (e : ℝ≥0∞), (∀ j, R.err j ≤ e) →
    (∀ s c m, R.pre s [] (some c, m) → RelK F D s c) →
    (∀ (s : USt) done tl c1 c2, DoneFits (rec3Rounds F3.prog.rounds nV np) done → tl.length = 3 →
      (C.prog s.1 s.2).ZerosVanish done tl → ClaimsHoldK D ((C.prog s.1 s.2).out done tl) c1 c2 →
        ∃ p m ch, openedOf F3.prog.rounds.length c1 c2 done = p ++ [(m, ch)] ∧ R.post s p m ch) →
    UniKnowledgeSoundnessKeccakRec3 F D (uniBound128 e)

variable {F : KeccakVm.KeccakFlockSpec} {D : KDeployment} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3) {np : ℕ}
  (I : UniIdsK3 F D F3 np) (BR : PairBatch np)

theorem hlink_uniPiopK3 (C : UniCodeK3 D F3 I.nV np) (hFin : UniFinalK3 D F3 I BR C) (s : USt)
    (done : Done) (tl : List E) (c1 c2 : Stk)
    (hd : DoneFits (rec3Rounds F3.prog.rounds I.nV np) done) (htl : tl.length = 3)
    (hz : (C.prog s.1 s.2).ZerosVanish done tl)
    (hc : ClaimsHoldK D ((C.prog s.1 s.2).out done tl) c1 c2) :
    ∃ p m ch, openedOf F3.prog.rounds.length c1 c2 done = p ++ [(m, ch)] ∧
      (uniPiopK3 F3 I BR).post s p m ch := by
  set nF := F3.prog.rounds.length
  set q := openedOf nF c1 c2 done with hq
  have hlen : done.length = nF + 4 + np := by
    rw [hd.length_eq, length_rec3Rounds]
  have hql : q.length = nF + 4 + np := by rw [hq, length_openedOf, hlen]
  have hne : q ≠ [] := by
    intro h
    rw [h] at hql
    simp only [List.length_nil] at hql
    omega
  refine ⟨q.dropLast, (q.getLast hne).1, (q.getLast hne).2, ?_, ?_⟩
  · exact (List.dropLast_append_getLast hne).symm
  change uniSK3 F3 I BR s (q.dropLast ++ [((q.getLast hne).1, (q.getLast hne).2)])
  rw [show q.dropLast ++ [((q.getLast hne).1, (q.getLast hne).2)] = q from
    List.dropLast_append_getLast hne]
  obtain ⟨hPend, hFin'⟩ := hFin s done tl c1 c2 hd htl hz hc
  unfold uniSK3
  refine ⟨c1, ?_, ?_⟩
  · rw [hq, rd_openedOf _ _ _ _ 0 (by omega)]
    simp
  rw [ite_eq_right (by omega)]
  refine ⟨c2, ?_, ?_, hPend, ?_⟩
  · rw [hq, rd_openedOf _ _ _ _ (nF + 1) (by omega)]
    simp
  · -- Flock's rounds completed.
    show DoneFits F3.prog.rounds (fdOf nF q)
    rw [hq, fdOf_openedOf]
    refine doneFits_map_noRoot _ _ F3.rounds_root ?_
    rcases done with _ | ⟨x, d⟩
    · simp only [List.length_nil] at hlen
      omega
    · have h1 : DoneFits (F3.prog.rounds ++ ([⟨true, 0, 0⟩, ⟨false, I.nV, 1⟩] ++
          (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩]))) d := by
        have := hd
        rw [rec3Rounds_eq] at this
        simp only [List.singleton_append] at this
        exact this.2.2
      simpa using doneFits_append_take _ _ d h1
  · rw [ite_eq_right (by omega)]
    exact hFin'

/-- **Every round's error is at most `e`**, given the identity model's, Flock's and the batch's numbers. -/
theorem uniErrK3_le (e : ℝ≥0∞)
    (hMain : I.errMain ≤ e) (hFl : ∀ j, F3.err j ≤ e)
    (hdeg : ((I.degSum + I.degBad : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) ≤ e)
    (hrel : ((I.nRel - 1 + (3 - 1) : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) ≤ e)
    (hP : BR.errPair ≤ e) (hL : BR.errLast ≤ e) (j : ℕ) : uniErrK3 F3 I BR j ≤ e := by
  unfold uniErrK3
  split_ifs
  · exact hMain
  · exact hFl _
  · exact hdeg
  · exact hrel
  · exact hP
  · exact hL

/-- **Knowledge soundness of the Keccak verifier at π1-rec3's shape** for the explicit extractor `uniExtractorK F D`,
with error `uniBound128 e Q`, every round's error at most `e`; from Flock on the Keccak-f block `F3`, the identity
model `I`, the batch `BR`, the links `C`, `hFin` and the Fiat–Shamir layer `hFs`. -/
theorem uniKnowledgeSoundnessK3 (C : UniCodeK3 D F3 I.nV np) (hFin : UniFinalK3 D F3 I BR C)
    (hFs : FsLayer128K3 F D F3 I.nV np C) (e : ℝ≥0∞)
    (hMain : I.errMain ≤ e) (hFl : ∀ j, F3.err j ≤ e)
    (hdeg : ((I.degSum + I.degBad : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) ≤ e)
    (hrel : ((I.nRel - 1 + (3 - 1) : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) ≤ e)
    (hP : BR.errPair ≤ e) (hL : BR.errLast ≤ e) :
    UniKnowledgeSoundnessKeccakRec3 F D (uniBound128 e) :=
  hFs (uniPiopK3 F3 I BR) e (uniErrK3_le F3 I BR e hMain hFl hdeg hrel hP hL) (hpre_uniPiopK3 F3 I BR)
    (hlink_uniPiopK3 F3 I BR C hFin)

/-- **With the bound in bits** at `e = 2^35 / |E|`: at most `2^-64` for every adversary of at most `2^64` calls. -/
theorem uniKnowledgeSoundnessK3_bits (C : UniCodeK3 D F3 I.nV np) (hFin : UniFinalK3 D F3 I BR C)
    (hFs : FsLayer128K3 F D F3 I.nV np C)
    (hMain : I.errMain ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hFl : ∀ j, F3.err j ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hdeg : I.degSum + I.degBad ≤ 2 ^ 35) (hrel : I.nRel + 2 ≤ 2 ^ 35)
    (hP : BR.errPair ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hL : BR.errLast ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) :
    UniKnowledgeSoundnessKeccakRec3 F D (uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  ⟨uniKnowledgeSoundnessK3 F3 I BR C hFin hFs _ hMain hFl
    (ENNReal.div_le_div_right (Nat.cast_le.mpr hdeg) _)
    (ENNReal.div_le_div_right (Nat.cast_le.mpr (by omega)) _) hP hL, uniBound128_le_bits35⟩

end UniKeccakSound
