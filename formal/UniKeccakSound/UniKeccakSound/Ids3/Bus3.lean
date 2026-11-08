-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Round `0` with squares is `UniSound/Rec3/BusSq.lean`'s
-- `BusModel.mainSoundSq` for the Keccak VM's bus model (`Ids/Bus.lean`).
import UniSound.Rec3.BusSq
import UniKeccakSound.Ids.Bus

/-!
# Round `0` of π1-rec3 on the Keccak VM: the bus with `α = (c, c², c⁴, c⁸)`

**`BusModelK.mainSoundSq`**: round `0` of π1-rec3 (`c, β, γ`, the bus read at `α = (c, c², c⁴, c⁸)`,
`UniSound.expandCh`) is sound on the Keccak VM, error `errMainSq = 16 N / |E| + (ncv − 1) / |E|`
(`UniSound.card_sat_not_balanced_le_sq`, generic in the instance, on the Keccak VM's); at most `2^35 / |E|` when
`16 N + ncv ≤ 2^35` (`errMainSq_le`). (Kept apart from the model: `Ids/Build.lean`'s imports bring `Completeness`'s
instance of `SampleableType E`, and the PIOP's statements are at `LeanVM.Protocol`'s.)
-/

namespace UniKeccakSound.Ids

open LeanVM.Parameters UniStatement UniSound UniKeccak Finset
open scoped ENNReal

/-! ## Round `0` with squares -/

namespace BusModelK

variable {D : KDeployment} (B : BusModelK D)

/-- **Round `0`'s error with squares**: the bus (`16 N / |E|`) and the constraints' batching. -/
noncomputable def errMainSq : ℝ≥0∞ :=
  ((16 * B.N : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) +
    ((B.ncv - 1 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)

/-- **Round `0` with squares is sound** on the Keccak VM: three challenges `[c, β, γ]`, read as the main line's six
(`expandCh`), turn `¬ MainHolds` into `MainOK` with probability at most `errMainSq`. -/
theorem mainSoundSq (s : USt) (c : Stk) :
    Pr{let ch ← Compose.draws E 3}[¬ B.MainHolds s c ∧ B.MainOK s c (expandCh ch)] ≤ B.errMainSq := by
  classical
  unfold errMainSq
  by_cases hall : ∀ x < B.nrows, ∀ v ∈ B.cvec s c x, v = 0
  · obtain ⟨hcv, hcn, hpl, hcp⟩ := B.cvec_ok s c hall
    have hR := B.realizes s c hcp
    have hev : ∀ ch : List E, (¬ B.MainHolds s c ∧ B.MainOK s c (expandCh ch)) →
        ((B.hd s c).Sat (FlockSound.sqPt 4 ((ch.take 2).getD 0 0)) ((ch.take 2).getD 1 0) ∧
          ¬ (D.inst s.2).Balanced (kvStack D.prog (D.sizes s.2) D.shape c)) ∨ False := by
      intro ch ⟨hn, hok⟩
      refine Or.inl ⟨?_, fun hb => hn ⟨hcv, hb, hcn, hpl, hcp⟩⟩
      have h1 : (ch.take 2).getD 0 0 = ch.getD 0 0 := by
        simp [List.getD_eq_getElem?_getD]
      have h2 : (ch.take 2).getD 1 0 = ch.getD 1 0 := by
        simp [List.getD_eq_getElem?_getD]
      rw [h1, h2, ← expandCh_alpha, ← expandCh_beta]
      exact hok.1
    have hb := prEvent_draws_append_le 2 1 (fun l => (B.hd s c).Sat
      (FlockSound.sqPt 4 (l.getD 0 0)) (l.getD 1 0) ∧
        ¬ (D.inst s.2).Balanced (kvStack D.prog (D.sizes s.2) D.shape c))
      (fun _ => False)
    refine (prEvent_mono _ _ _ hev).trans (hb.trans ?_)
    rw [prEvent_eq_zero_of_forall_not _ _ (fun _ h => h), add_zero]
    refine le_trans ?_ le_self_add
    have hc := card_sat_not_balanced_le_sq (I := D.inst s.2) (B.wf s c) hR (B.hpush s c hcp)
      (B.hpull s c hcp)
    refine prEvent_draws_le_of_card 1 _ (16 * B.N) ?_
    rw [pow_one]
    have h2 := BusModel.card_fin_two_pair (fun a b => (B.hd s c).Sat (FlockSound.sqPt 4 a) b ∧
      ¬ (D.inst s.2).Balanced (kvStack D.prog (D.sizes s.2) D.shape c))
    exact (le_of_eq h2).trans hc
  · obtain ⟨x₀, hx₀, v, hv, hv0⟩ : ∃ x < B.nrows, ∃ v ∈ B.cvec s c x, v ≠ 0 := by
      by_contra hne
      exact hall fun x hx v hv => by
        by_contra h0
        exact hne ⟨x, hx, v, hv, h0⟩
    have hev : ∀ ch : List E, (¬ B.MainHolds s c ∧ B.MainOK s c (expandCh ch)) →
        False ∨ powComb (B.cvec s c x₀) ((ch.drop 2).headD 0) = 0 := by
      intro ch ⟨_, hok⟩
      refine Or.inr ?_
      have h1 : (ch.drop 2).headD 0 = (expandCh ch).getD 5 0 := by
        rw [expandCh_gamma]
        simp [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]
      rw [h1]
      exact hok.2 x₀ hx₀
    have hb := prEvent_draws_append_le 2 1 (fun _ => False)
      (fun l => powComb (B.cvec s c x₀) (l.headD 0) = 0)
    refine (prEvent_mono _ _ _ hev).trans (hb.trans ?_)
    rw [prEvent_eq_zero_of_forall_not _ _ (fun _ h => h), zero_add]
    refine le_trans ?_ le_add_self
    refine prEvent_draws_le_of_card 0 _ _ ?_
    rw [pow_zero, mul_one]
    convert (card_powComb_le _ ⟨v, hv, hv0⟩).trans (Nat.sub_le_sub_right (B.cvec_len s c x₀) 1)
      using 1
    convert card_filter_fin_one (fun ρ => powComb (B.cvec s c x₀) ρ = 0) using 2

/-- Round `0`'s error with squares is at most `2^35 / |E|` when `16 N + ncv ≤ 2^35`. -/
theorem errMainSq_le (h : 16 * B.N + B.ncv ≤ 2 ^ 35) :
    B.errMainSq ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  unfold errMainSq
  rw [ENNReal.div_add_div_same, ← Nat.cast_add]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (by omega)) _

end BusModelK

end UniKeccakSound.Ids

/-- info: 'UniKeccakSound.Ids.BusModelK.mainSoundSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.BusModelK.mainSoundSq
