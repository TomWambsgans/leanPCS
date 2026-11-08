-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The composition is `UniSound/Final.lean`'s and
-- `UniSound/Closed128.lean`'s `uniKnowledgeSoundness128`, for the Keccak verifier's main line.
import UniSound.Final
import UniKeccakSound.PiopSoundK
import UniKeccakSound.FsK

/-!
# Knowledge soundness of the Keccak verifier (main line), from its links

**`uniKnowledgeSoundnessK`**: `UniKnowledgeSoundnessKeccak F D (uniBound128 (2^32/|E|))` from

* `Fl : KFlockSound F κ keccakMain` — Flock on the Keccak-f block (`FlockInterfaceK.lean`);
* `I : UniIdsK F D Fl` — the identity model (`PiopK.lean`);
* `C : UniCodeK D Fl I.nV I.V`, `hFin : UniFinalK D Fl I C` — the code-level links (`FsK.lean`);
* `hFs : FsLayer128K F D Fl I.nV I.V C` — the Fiat–Shamir layer (`FsK.lean`);
* the numbers: `errMain`, Flock's rounds' errors at most `2^32 / |E|`, the identities' degrees and the merge
  polynomial's at most `2^32` in all, at most `2^32 − 2` relations on a commitment.

The protocol is `uniPiopK Fl I` (`PiopSoundK.lean`, proved): its first state is the relation (`hpre_uniPiopK`), its
last follows from the checks with true claims (`hlink_uniPiopK`, from `hFin`), every round errs at most
`2^32 / |E|` (`uniErrK_le`). The bound is at most `2^-64` for `Q ≤ 2^64` (`UniSound.uniBound128_le_bits`).
-/

namespace UniKeccakSound

open LeanVM.Parameters UniStatement UniSound UniKeccak Finset WhirBridge
open scoped ENNReal

variable {F : KeccakVm.KeccakFlockSpec} {D : KDeployment} {κ : ℕ}

variable (Fl : KFlockSound F κ keccakMain) (I : UniIdsK F D Fl)

theorem hpre_uniPiopK (s : USt) (c : Stk) (m : List E) :
    (uniPiopK Fl I).pre s [] (some c, m) → RelK F D s c := by
  intro h
  change uniPreK Fl I s [] (some c, m) at h
  unfold uniPreK at h
  rw [ite_eq_left (List.length_nil : ([] : Op Stk).length = 0)] at h
  obtain ⟨c', hc', hr⟩ := h
  cases hc'
  exact hr

theorem hlink_uniPiopK (C : UniCodeK D Fl I.nV I.V) (hFin : UniFinalK D Fl I C) (s : USt)
    (done : Done) (tl : List E) (c1 c2 : Stk)
    (hd : DoneFits (uniRounds Fl.prog.rounds I.nV I.V) done) (htl : tl.length = 3)
    (hz : (C.prog s.1 s.2).ZerosVanish done tl)
    (hc : ClaimsHoldK D ((C.prog s.1 s.2).out done tl) c1 c2) :
    ∃ p m ch, openedOf Fl.prog.rounds.length c1 c2 done = p ++ [(m, ch)] ∧
      (uniPiopK Fl I).post s p m ch := by
  set nF := Fl.prog.rounds.length
  set q := openedOf nF c1 c2 done with hq
  have hlen : done.length = nF + 3 + I.V := by
    rw [hd.length_eq, length_uniRounds]
  have hql : q.length = nF + 3 + I.V := by rw [hq, length_openedOf, hlen]
  have hne : q ≠ [] := by
    intro h
    rw [h] at hql
    simp only [List.length_nil] at hql
    omega
  obtain ⟨hzF, hFin'⟩ := hFin s done tl c1 c2 hd htl hz hc
  refine ⟨q.dropLast, (q.getLast hne).1, (q.getLast hne).2, ?_, ?_⟩
  · exact (List.dropLast_append_getLast hne).symm
  change uniSK Fl I s (q.dropLast ++ [((q.getLast hne).1, (q.getLast hne).2)])
  rw [show q.dropLast ++ [((q.getLast hne).1, (q.getLast hne).2)] = q from
    List.dropLast_append_getLast hne]
  unfold uniSK
  refine ⟨c1, ?_, ?_⟩
  · rw [hq, rd_openedOf _ _ _ _ 0 (by omega)]
    simp
  rw [ite_eq_right (by omega)]
  refine ⟨c2, ?_, ⟨?_, hzF⟩, ?_⟩
  · rw [hq, rd_openedOf _ _ _ _ (nF + 1) (by omega)]
    simp
  · -- Flock's rounds completed.
    show DoneFits Fl.prog.rounds (fdOf nF q)
    rw [hq, fdOf_openedOf]
    refine doneFits_map_noRoot _ _ Fl.rounds_root ?_
    rcases done with _ | ⟨x, d⟩
    · simp only [List.length_nil] at hlen
      omega
    · have h1 : DoneFits (Fl.prog.rounds ++ ([⟨true, 0, 0⟩, ⟨false, I.nV, 1⟩] ++
          List.replicate I.V ⟨false, 2, 0⟩)) d := by
        have := hd
        simp only [uniRounds, List.append_assoc, List.singleton_append] at this
        exact this.2.2
      simpa using doneFits_append_take _ _ d h1
  · rw [ite_eq_right (by omega)]
    exact hFin'

/-- **Every round's error is at most `2^32 / |E|`**, given the identity model's and Flock's numbers. -/
theorem uniErrK_le (hMain : I.errMain ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hFl : ∀ j, Fl.err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hdeg : I.degSum + I.degBad ≤ 2 ^ 32) (hrel : I.nRel + 2 ≤ 2 ^ 32) (j : ℕ) :
    uniErrK Fl I j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  unfold uniErrK
  split_ifs
  · exact hMain
  · exact hFl _
  · exact ENNReal.div_le_div_right (Nat.cast_le.mpr hdeg) _
  · exact ENNReal.div_le_div_right (Nat.cast_le.mpr (by omega)) _
  · exact ENNReal.div_le_div_right (Nat.cast_le.mpr (by norm_num)) _

/-- **Knowledge soundness of the Keccak verifier (main line)** for the explicit extractor `uniExtractorK F D`, with
error `uniBound128 (2^32 / |E|) Q` at `Q` calls of `π` and `π⁻¹`, from Flock on the Keccak-f block `Fl`, the identity
model `I`, the code-level links `C`, `hFin`, the Fiat–Shamir layer `hFs`, and the numbers. -/
theorem uniKnowledgeSoundnessK (C : UniCodeK D Fl I.nV I.V) (hFin : UniFinalK D Fl I C)
    (hFs : FsLayer128K F D Fl I.nV I.V C)
    (hMain : I.errMain ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hFl : ∀ j, Fl.err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hdeg : I.degSum + I.degBad ≤ 2 ^ 32) (hrel : I.nRel + 2 ≤ 2 ^ 32) :
    UniKnowledgeSoundnessKeccak F D (uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) :=
  hFs (uniPiopK Fl I) _ (uniErrK_le Fl I hMain hFl hdeg hrel) (hpre_uniPiopK Fl I)
    (hlink_uniPiopK Fl I C hFin)

/-- **With the bound in bits**: at most `2^-64` for every adversary of at most `2^64` calls of `π` and `π⁻¹`. -/
theorem uniKnowledgeSoundnessK_bits (C : UniCodeK D Fl I.nV I.V) (hFin : UniFinalK D Fl I C)
    (hFs : FsLayer128K F D Fl I.nV I.V C)
    (hMain : I.errMain ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hFl : ∀ j, Fl.err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hdeg : I.degSum + I.degBad ≤ 2 ^ 32) (hrel : I.nRel + 2 ≤ 2 ^ 32) :
    UniKnowledgeSoundnessKeccak F D (uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  ⟨uniKnowledgeSoundnessK Fl I C hFin hFs hMain hFl hdeg hrel, uniBound128_le_bits⟩

end UniKeccakSound
