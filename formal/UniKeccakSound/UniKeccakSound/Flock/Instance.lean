-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows `formal/FlockSound/FlockSoundUni/Instance.lean`
-- and `Rec3Instance.lean` (BLAKE2s's) for the Keccak verifier's Flock phase.
import UniKeccakSound.Flock.Rec3

/-!
# Flock's interface on the Keccak-f block, from the terminal

For a block `F` whose structured terminal is its matrices' product sum plus the known terms (`TerminalSpecK F`):

* **`kFlockSoundMain F hT κ : KFlockSound F κ keccakMain`**: the chain program `kProg κ`, its link `kflock_link`,
  the bad family `kBad F κ` of sizes `dBoundK κ` (catching: `catchesK`); every round's error at most
  `max(7 + κ, 90)/|E|` (`kFlockSoundMain_err_le`), so at most `2^32/|E|` when `7 + κ ≤ 2^32`;
* **`kFlockSoundRec3 F hT κ : KFlockSound F κ keccakRec3`**: the chain program `kProg3 κ`, its link `kflock_link3`,
  the bad family `kBad3 F κ` of sizes `dBound3K κ` (Kronecker for the squares' challenge: `2^(7 + κ) − 1`); every
  round's error at most `(2^(7 + κ) + 90)/|E|`, so at most `2^35/|E|` when `κ ≤ 28` (`kFlockSoundRec3_err_le`).

`Terminal.lean` gives `TerminalSpecK` for `KeccakFlock.keccakFlockSpec`.
-/

namespace UniKeccakSound.KF

open UniSound hiding rd
open UniStatement UniKeccak LeanVM.Parameters Finset
open scoped ENNReal

variable (F : KeccakVm.KeccakFlockSpec)

/-- **Flock's interface on the block `F`, main line**, from its terminal. -/
noncomputable def kFlockSoundMain (hT : TerminalSpecK F) (κ : ℕ) : KFlockSound F κ keccakMain :=
  ofFamilyK F keccakMain (kProg κ) (kProgWith_root κ _ rfl _) (kProgWith_tail κ _ _) (fun P ↦ kflock_link κ P)
    (kBad F κ) (dBoundK κ) (card_kBad F κ) (catchesK F hT)

/-- **Flock's interface on the block `F`, π1-rec3**, from its terminal. -/
noncomputable def kFlockSoundRec3 (hT : TerminalSpecK F) (κ : ℕ) : KFlockSound F κ keccakRec3 :=
  ofFamilyK F keccakRec3 (kProg3 κ) (kProgWith_root κ _ rfl _) (kProgWith_tail κ _ _) (fun P ↦ kflock_link3 κ P)
    (kBad3 F κ) (dBound3K κ) (card_kBad3 F κ) (catches3K F hT)

/-! ## The rounds' errors -/

theorem kRounds_getElem?_zero (κ : ℕ) (r0 : Compose.RoundSpec) : (kRounds κ r0)[0]? = some r0 := rfl

theorem kRounds_ns_succ_le (κ : ℕ) (r0 : Compose.RoundSpec) (j : ℕ) :
    (((kRounds κ r0)[j + 1]?).map (·.ns)).getD 0 ≤ 5 := by
  cases h : (kRounds κ r0)[j + 1]? with
  | none => simp
  | some s =>
    have hj : j + 1 < (kRounds κ r0).length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at h
      exact absurd h (by simp)
    have hs : s = (kRounds κ r0)[j + 1] := by
      rw [List.getElem?_eq_getElem hj] at h
      exact (Option.some.inj h).symm
    show s.ns ≤ 5
    rw [hs]
    have hl : (kRounds κ r0).length = 29 + κ := length_kRounds κ r0
    simp only [kRounds, kRoundsPre, List.getElem_append, List.length_append, List.length_cons,
      List.length_replicate, List.length_nil, List.getElem_replicate, List.getElem_cons]
    split_ifs <;> first | decide | (exfalso; omega)

theorem dBoundK_le (κ j i : ℕ) : dBoundK κ j i ≤ 15 := by
  unfold dBoundK
  split_ifs <;> omega

/-- **Round `j`'s error, times `|E|`, main line**: `7 + κ` for `τ`, at most `90` after. -/
theorem sum_dBoundK_le (κ j : ℕ) :
    ∑ i ∈ range ((((kRounds κ (r0Main κ))[j]?).map (·.ns)).getD 0 + 1), dBoundK κ j i ≤ max (7 + κ) 90 := by
  rcases j with _ | j
  · rw [kRounds_getElem?_zero]
    simp only [Option.map_some, Option.getD_some]
    have h : ∀ i ∈ range (6 + κ + 1), dBoundK κ 0 i = 1 := fun i _ ↦ by unfold dBoundK; rw [ite_eq_left rfl]
    rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    omega
  · have hns := kRounds_ns_succ_le κ (r0Main κ) j
    generalize (((kRounds κ (r0Main κ))[j + 1]?).map (·.ns)).getD 0 = n at hns ⊢
    calc ∑ i ∈ range (n + 1), dBoundK κ (j + 1) i
        ≤ ∑ _i ∈ range (n + 1), 15 := Finset.sum_le_sum fun i _ ↦ dBoundK_le κ (j + 1) i
      _ ≤ max (7 + κ) 90 := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
          exact le_trans (by omega : (n + 1) * 15 ≤ 90) (le_max_right _ _)

/-- **Round `j`'s error, times `|E|`, π1-rec3**: `2^(7 + κ) − 1` for the squares' challenge, at most `90` after. -/
theorem sum_dBound3K_le (κ j : ℕ) :
    ∑ i ∈ range ((((kRounds κ r0Rec3)[j]?).map (·.ns)).getD 0 + 1), dBound3K κ j i ≤ 2 ^ (7 + κ) + 90 := by
  rcases j with _ | j
  · rw [kRounds_getElem?_zero]
    simp [dBound3K]
    omega
  · have hns := kRounds_ns_succ_le κ r0Rec3 j
    generalize (((kRounds κ r0Rec3)[j + 1]?).map (·.ns)).getD 0 = n at hns ⊢
    calc ∑ i ∈ range (n + 1), dBound3K κ (j + 1) i
        ≤ ∑ _i ∈ range (n + 1), 15 :=
          Finset.sum_le_sum fun i _ ↦ by unfold dBound3K; rw [ite_eq_right (by omega)]; exact dBoundK_le κ _ i
      _ ≤ 2 ^ (7 + κ) + 90 := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
          exact le_trans (by omega : (n + 1) * 15 ≤ 90) (Nat.le_add_left 90 _)

/-- **Every round's error, main line**, at most `max(7 + κ, 90)/|E|`. -/
theorem kFlockSoundMain_err_le' (hT : TerminalSpecK F) (κ j : ℕ) :
    (kFlockSoundMain F hT κ).err j ≤ ((max (7 + κ) 90 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) :=
  ENNReal.div_le_div_right (Nat.cast_le.mpr (sum_dBoundK_le κ j)) _

/-- **Every round's error, main line**, at most `2^32/|E|` (for `7 + κ ≤ 2^32`). -/
theorem kFlockSoundMain_err_le (hT : TerminalSpecK F) (κ : ℕ) (hκ : 7 + κ ≤ 2 ^ 32) (j : ℕ) :
    (kFlockSoundMain F hT κ).err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) :=
  (kFlockSoundMain_err_le' F hT κ j).trans
    (ENNReal.div_le_div_right (Nat.cast_le.mpr (max_le hκ (by norm_num))) _)

/-- **Every round's error, π1-rec3**, at most `(2^(7 + κ) + 90)/|E|`. -/
theorem kFlockSoundRec3_err_le' (hT : TerminalSpecK F) (κ j : ℕ) :
    (kFlockSoundRec3 F hT κ).err j ≤ ((2 ^ (7 + κ) + 90 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) :=
  ENNReal.div_le_div_right (Nat.cast_le.mpr (sum_dBound3K_le κ j)) _

/-- **Every round's error, π1-rec3**, at most `2^35/|E|` (for `κ ≤ 28`). -/
theorem kFlockSoundRec3_err_le (hT : TerminalSpecK F) (κ : ℕ) (hκ : κ ≤ 28) (j : ℕ) :
    (kFlockSoundRec3 F hT κ).err j ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  show ∑ i ∈ range ((((kRounds κ r0Rec3)[j]?).map (·.ns)).getD 0 + 1), dBound3K κ j i ≤ 2 ^ 35
  rcases j with _ | j
  · rw [kRounds_getElem?_zero]
    have : 2 ^ (7 + κ) ≤ 2 ^ 35 := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [dBound3K]
    omega
  · have hns := kRounds_ns_succ_le κ r0Rec3 j
    generalize (((kRounds κ r0Rec3)[j + 1]?).map (·.ns)).getD 0 = n at hns ⊢
    calc ∑ i ∈ range (n + 1), dBound3K κ (j + 1) i
        ≤ ∑ _i ∈ range (n + 1), 15 :=
          Finset.sum_le_sum fun i _ ↦ by unfold dBound3K; rw [ite_eq_right (by omega)]; exact dBoundK_le κ _ i
      _ ≤ 2 ^ 35 := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
          omega

/-! ## Flock's result, and the Fiat–Shamir layer's sizes -/

/-- **Flock's result is the main line's** (the identity model's `FlockGoodDoneK`, unfolded): on every completed
transcript, a ring end and a point of `q_flock`'s `11 + κ` coordinates. -/
theorem kFlockSoundMain_good (hT : TerminalSpecK F) (κ : ℕ) : ∀ fd, DoneFits (kFlockSoundMain F hT κ).prog.rounds fd →
    (∃ map target, ((kFlockSoundMain F hT κ).prog.out fd []).2 = .ring map target) ∧
      ((kFlockSoundMain F hT κ).prog.out fd []).1.length = KeccakVm.kWords + κ := by
  intro fd hfit
  have hF := fitsK_of_doneFits (κ := κ) hfit
  show (∃ map target, (kOutT κ sampMain fd).2 = .ring map target) ∧ (kOutT κ sampMain fd).1.length = _
  rw [kOutT_parse F hF]
  exact ⟨⟨_, _, rfl⟩, List.length_ofFn⟩

/-- **Flock's result is the main line's**, π1-rec3. -/
theorem kFlockSoundRec3_good (hT : TerminalSpecK F) (κ : ℕ) : ∀ fd, DoneFits (kFlockSoundRec3 F hT κ).prog.rounds fd →
    (∃ map target, ((kFlockSoundRec3 F hT κ).prog.out fd []).2 = .ring map target) ∧
      ((kFlockSoundRec3 F hT κ).prog.out fd []).1.length = KeccakVm.kWords + κ := by
  intro fd hfit
  have hfit' : DoneFits (kRounds κ r0Rec3) fd := hfit
  have hF := fitsK_of_doneFits (doneFits_expandK hfit')
  have hd : fd ≠ [] := by
    rintro rfl
    exact hfit'
  show (∃ map target, (kOutT κ (sampRec3 κ) fd).2 = .ring map target) ∧ (kOutT κ (sampRec3 κ) fd).1.length = _
  rw [kOutT_expandK fd hd, kOutT_parse F hF]
  exact ⟨⟨_, _, rfl⟩, List.length_ofFn⟩

/-- **The rounds' scalars**: at most `64` each, so at most `2^30`. -/
theorem kFlockSoundMain_nv (hT : TerminalSpecK F) (κ : ℕ) : ∀ r ∈ (kFlockSoundMain F hT κ).prog.rounds, r.nv ≤ 2 ^ 30 := by
  intro r hr
  have hr' : r ∈ kRounds κ (r0Main κ) := hr
  simp only [kRounds, kRoundsPre, List.mem_append, List.mem_cons, List.mem_replicate, List.not_mem_nil,
    or_false] at hr'
  rcases hr' with ((((h | h) | ⟨-, h⟩) | h) | ⟨-, h⟩) | h <;> subst h <;> norm_num

theorem kFlockSoundRec3_nv (hT : TerminalSpecK F) (κ : ℕ) : ∀ r ∈ (kFlockSoundRec3 F hT κ).prog.rounds, r.nv ≤ 2 ^ 30 := by
  intro r hr
  have hr' : r ∈ kRounds κ r0Rec3 := hr
  simp only [kRounds, kRoundsPre, List.mem_append, List.mem_cons, List.mem_replicate, List.not_mem_nil,
    or_false] at hr'
  rcases hr' with ((((h | h) | ⟨-, h⟩) | h) | ⟨-, h⟩) | h <;> subst h <;> norm_num

/-- **The rounds' challenges at the reference shape** (`κ = 15`): `70`, with the batch's `27` within `1014`. -/
theorem kFlockSoundMain_nSteps (hT : TerminalSpecK F) : Compose.nSteps (kFlockSoundMain F hT 15).prog.rounds + 27 ≤ 1014 := by
  show Compose.nSteps (kRounds 15 (r0Main 15)) + 27 ≤ 1014
  decide

theorem kFlockSoundRec3_nSteps (hT : TerminalSpecK F) : Compose.nSteps (kFlockSoundRec3 F hT 15).prog.rounds + 27 ≤ 1014 := by
  show Compose.nSteps (kRounds 15 r0Rec3) + 27 ≤ 1014
  decide

end UniKeccakSound.KF

/-- info: 'UniKeccakSound.KF.kFlockSoundMain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.kFlockSoundMain

/-- info: 'UniKeccakSound.KF.kFlockSoundRec3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.kFlockSoundRec3

/-- info: 'UniKeccakSound.KF.kFlockSoundMain_err_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.kFlockSoundMain_err_le

/-- info: 'UniKeccakSound.KF.kFlockSoundRec3_err_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.kFlockSoundRec3_err_le
