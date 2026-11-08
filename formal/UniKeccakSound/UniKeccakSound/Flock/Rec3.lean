-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Follows `formal/FlockSound/FlockSoundUni/Rec3Catch.lean`
-- (BLAKE2s's π1-rec3) at the Keccak verifier's sizes, with `FlockSound.FlockSq`'s `flock_front_sq`.
import UniKeccakSound.Flock.Catch

/-!
# π1-rec3's Flock bad family on the Keccak-f block catches

π1-rec3's Flock transcript `done` (rounds `kRounds κ r0Rec3`) is read as the main line's (`expandK κ done`: the
first round's one challenge `c` written out as `squares c (7 + κ)`), whose parse (`parseK κ`) is `FlockSound`'s run
with `τs = sqPt (7 + κ) c` (`parseK_expandK_τs`). Its zero and result are the main line's on the expanded transcript
(`kTerm_expandK`, `kOutT_expandK`).

**The bad family** (`kBad3 F κ`): round `0`'s one challenge is bad when the residual's sampled tables vanish at its
squares (`kronBad (7 + κ)`, at most `2^(7 + κ) − 1` values: Kronecker); every later challenge is bad as the main
line's (`kBad F κ`) on the expanded transcript. Sizes `dBound3K`: `2^(7 + κ) − 1` for `c`, the main line's after.

**`catches3K`**: given the terminal (`TerminalSpecK F`), the bad family catches (`flock_front_sq` at `kSetup F κ`
on the expanded parse, each event of `Front.BadSq` a hit of `kBad3`).
-/

namespace UniKeccakSound.KF

open UniSound hiding rd
open UniStatement LeanVM.Parameters LeanVM.Semantics Finset Polynomial FlockSound FlockSound.Uni
open LeanVM.Protocol (Column)

variable {κ : ℕ}

/-- **`squares` is the point of squares.** -/
theorem squares_eq_ofFnK : ∀ (c : E) (n : ℕ), squares c n = List.ofFn (FlockSound.sqPt n c)
  | _, 0 => by simp [squares]
  | c, n + 1 => by
    rw [squares, FlockSound.sqPt_succ, List.ofFn_succ, squares_eq_ofFnK (c * c) n]
    simp [sq]

/-! ## The expanded transcript -/

/-- **The transcript as the main line's**: the first round's challenge written out as its `7 + κ` squares. -/
def expandK (κ : ℕ) : Done → Done
  | [] => []
  | (m, c) :: d => (m, squares (c.headD 0) (7 + κ)) :: d

theorem length_expandK (κ : ℕ) (d : Done) : (expandK κ d).length = d.length := by
  cases d <;> rfl

theorem rd_expandK_succ (κ : ℕ) (d : Done) (a : ℕ) : rd (expandK κ d) (a + 1) = rd d (a + 1) := by
  cases d <;> rfl

theorem drop_expandK (κ : ℕ) (d : Done) (a : ℕ) : (expandK κ d).drop (a + 1) = d.drop (a + 1) := by
  cases d <;> rfl

theorem rd_expandK_zero (κ : ℕ) (d : Done) (h : d ≠ []) :
    (rd (expandK κ d) 0).2 = squares ((rd d 0).2.headD 0) (7 + κ) := by
  cases d with
  | nil => exact absurd rfl h
  | cons x d => rfl

theorem expandK_take (κ : ℕ) (d : Done) (j : ℕ) (hj : 1 ≤ j) : expandK κ (d.take j) = (expandK κ d).take j := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  cases d <;> rfl

theorem doneFits_expandK {d : Done} (h : DoneFits (kRounds κ r0Rec3) d) :
    DoneFits (kRounds κ (r0Main κ)) (expandK κ d) := by
  rcases d with _ | ⟨⟨msg, c⟩, d⟩
  · exact h.elim
  · obtain ⟨hm, hc, hd⟩ := h
    refine ⟨hm, ?_, ?_⟩
    · show (squares (c.headD 0) (7 + κ)).length = 6 + κ + 1
      rw [length_squares]
      omega
    · exact hd

theorem sampMain_expandK (d : Done) (h : d ≠ []) : sampMain (expandK κ d) = sampRec3 κ d :=
  rd_expandK_zero κ d h

/-- **The zero reads as the main line's** on the expanded transcript. -/
theorem kTerm_expandK (d : Done) (h : d ≠ []) (s : List E) :
    kTerm κ (sampRec3 κ) d s = kTerm κ sampMain (expandK κ d) s := by
  unfold kTerm
  rw [sampMain_expandK d h, rd_expandK_succ, drop_expandK, show 16 + κ = (15 + κ) + 1 by omega, drop_expandK,
    show 17 + κ = (16 + κ) + 1 by omega, drop_expandK]

/-- **The result reads as the main line's** on the expanded transcript. -/
theorem kOutT_expandK (d : Done) (h : d ≠ []) : kOutT κ (sampRec3 κ) d = kOutT κ sampMain (expandK κ d) := by
  unfold kOutT
  rw [sampMain_expandK d h, rd_expandK_succ, drop_expandK, show 16 + κ = (15 + κ) + 1 by omega, drop_expandK,
    show 17 + κ = (16 + κ) + 1 by omega, drop_expandK, show 28 + κ = (27 + κ) + 1 by omega, drop_expandK]

/-- **The zero of a completed transcript vanishes**, π1-rec3. -/
theorem kTerm_zero3 {done : Done} (hl : done.length = 29 + κ) (hz : (kProg3 κ).ZerosVanish done []) :
    kTerm κ (sampRec3 κ) done (rd done (28 + κ)).1.2 = 0 := by
  have hlt : 28 + κ < done.length := by omega
  have h := hz.1 (28 + κ) hlt
  have hlen : (done.take (28 + κ)).length = 28 + κ := by rw [List.length_take]; omega
  rw [show (kProg3 κ) = kProgWith κ r0Rec3 (sampRec3 κ) from rfl, kProgWith_zeros _ _ _ _ hlen] at h
  have h' := h _ (List.mem_singleton_self _)
  have hd : done ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hdt : done.take (28 + κ) ≠ [] := List.ne_nil_of_length_pos (by omega)
  rw [kTerm_expandK _ hdt, expandK_take κ _ _ (by omega), kTerm_take, ← kTerm_expandK _ hd,
    ← rd_eq_getElem hlt] at h'
  exact h'

theorem getD_ofFn_sqK (n : ℕ) (c : E) (a : ℕ) (ha : a < n) :
    (List.ofFn (FlockSound.sqPt n c)).getD a 0 = FlockSound.sqPt n c ⟨a, ha⟩ := by
  simp [List.getD_eq_getElem?_getD, ha]

/-- **The expanded parse's sampled coordinates are the squares of the first challenge.** -/
theorem parseK_expandK_τs (d : Done) (hd : d ≠ []) :
    (parseK κ (expandK κ d)).τs = FlockSound.sqPt (7 + κ) ((rd d 0).2.headD 0) := by
  funext a
  show (rd (expandK κ d) 0).2.getD a 0 = _
  rw [rd_expandK_zero κ d hd, squares_eq_ofFnK, getD_ofFn_sqK _ _ _ a.isLt]

/-! ## The bad family -/

variable (F : KeccakVm.KeccakFlockSpec)

/-- **π1-rec3's Flock bad family on the Keccak-f block**: round `0`'s challenge the Kronecker bad set of the
residual's sampled tables; the later ones the main line's on the expanded transcript. -/
noncomputable def kBad3 (κ : ℕ) : KBadFamily κ := fun qf done msg pre ↦
  if done.length = 0 then
    FlockSound.kronBad (7 + κ) (FlockSound.sampledTables (kSetup F κ).hsize (kSetup F κ).fixed
      (FlockSound.Front.zRes (kSetup F κ) (zOfK qf)))
  else kBad F κ qf (expandK κ done) msg pre

/-- **The bad sets' sizes**: `2^(7 + κ) − 1` for the squares' challenge, the main line's after. -/
def dBound3K (κ : ℕ) (j i : ℕ) : ℕ := if j = 0 then 2 ^ (7 + κ) - 1 else dBoundK κ j i

theorem card_kBad3 (κ : ℕ) : ∀ qf done msg pre,
    (kBad3 F κ qf done msg pre).card ≤ dBound3K κ done.length pre.length := by
  intro qf done msg pre
  unfold kBad3 dBound3K
  by_cases h : done.length = 0
  · rw [ite_eq_left h, ite_eq_left h]
    exact FlockSound.card_kronBad_le _ _
  · rw [ite_eq_right h, ite_eq_right h, ← length_expandK κ done]
    exact card_kBad F κ qf _ msg pre

/-- **A later challenge in the expanded parse's bad set is a hit of `kBad3`.** -/
theorem hitIn3K_of_mem (qf : Column (KeccakVm.kWords + κ)) {done : Done} {j i : ℕ} (h1 : 1 ≤ j)
    (hj : j < done.length) (hi : i < (rd (expandK κ done) j).2.length)
    (hmem : (rd (expandK κ done) j).2.getD i 0 ∈ badAtK F qf (parseK κ (expandK κ done)) j i) :
    HitInK (kBad3 F κ) qf done := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hrd : rd (expandK κ done) (j' + 1) = rd done (j' + 1) := rd_expandK_succ κ done j'
  rw [hrd] at hi hmem
  obtain ⟨r, ds, rfl⟩ : ∃ r ds, done = r :: ds :=
    List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (by omega))
  have hr := rd_eq_getElem hj
  refine ⟨j' + 1, hj, i, by rw [← hr]; exact hi, ?_⟩
  show _ ∈ kBad3 F κ qf ((r :: ds).take (j' + 1)) ((r :: ds)[j' + 1]).1 (((r :: ds)[j' + 1]).2.take i)
  rw [← hr]
  unfold kBad3
  rw [ite_eq_right (by simp), expandK_take κ _ _ (by omega)]
  unfold kBad
  have hA := agree_pfx (done := expandK κ (r :: ds)) (j := j' + 1) (by rw [length_expandK]; exact hj) i
  rw [hrd] at hA
  rw [List.length_take, length_expandK, min_eq_left hj.le, List.length_take, min_eq_left hi.le,
    badAtK_congr F qf hA]
  exact hmem

/-- **Each of `Front.BadSq`'s events on the expanded parse is a hit of `kBad3`.** -/
theorem hitK_of_badSq (qf : Column (KeccakVm.kWords + κ)) {done : Done} (hd : done ≠ [])
    (h0 : (rd done 0).2.length = 1) (hF : FitsK κ (expandK κ done))
    (hbad : FlockSound.Front.BadSq (kSetup F κ) (parseK κ (expandK κ done)) (zOfK qf) ((rd done 0).2.headD 0)) :
    HitInK (kBad3 F κ) qf done := by
  have hl : done.length = 29 + κ := by rw [← length_expandK κ done]; exact hF.len
  rcases hbad with hk | hz | ⟨t, ht⟩ | hα | ⟨t, ht⟩ | ⟨a, ha⟩
  · obtain ⟨r, ds, rfl⟩ := List.exists_cons_of_ne_nil hd
    refine ⟨0, by simp, 0, ?_, ?_⟩
    · show 0 < r.2.length
      have h0' : r.2.length = 1 := h0
      omega
    · show r.2.getD 0 0 ∈ kBad3 F κ qf ((r :: ds).take 0) (r :: ds)[0].1 ((r :: ds)[0].2.take 0)
      unfold kBad3
      rw [ite_eq_left (by simp), ← headD_eq_getD']
      exact hk
  · refine hitIn3K_of_mem F qf (j := 1) (i := 0) le_rfl (by omega) (by rw [hF.r1c]; omega) ?_
    rw [badAtK_z, ← headD_eq_getD']
    exact hz
  · have ht2 := t.isLt
    refine hitIn3K_of_mem F qf (j := 2 + t) (i := 0) (by omega) (by omega)
      (by rw [(hF.mid _ (by omega) (by omega)).2]; omega) ?_
    rw [badAtK_zc, ← headD_eq_getD', ← rd_drop]
    exact ht
  · refine hitIn3K_of_mem F qf (j := 16 + κ) (i := 0) (by omega) (by omega)
      (by rw [(hF.mid _ (by omega) (by omega)).2]; omega) ?_
    rw [badAtK_α, ← headD_eq_getD']
    exact hα
  · have ht11 := t.isLt
    refine hitIn3K_of_mem F qf (j := 17 + κ + t) (i := 0) (by omega) (by omega)
      (by rw [(hF.mid _ (by omega) (by omega)).2]; omega) ?_
    rw [badAtK_lin, ← headD_eq_getD', ← rd_drop]
    exact ht
  · refine hitIn3K_of_mem F qf (j := 28 + κ) (i := a) (by omega) (by omega)
      (by rw [hF.r6c]; exact (show (a : ℕ) < 6 from a.isLt)) ?_
    rw [badAtK_ring]
    exact ha

/-! ## The catch -/

/-- **π1-rec3's bad family on the Keccak-f block catches**, given the terminal: on a completed transcript whose
structured terminal vanishes and whose ring claim holds of the column, the block's relation holds or a challenge is
in its bad set (`flock_front_sq` at `kSetup F κ` on the expanded parse). -/
theorem catches3K (hT : TerminalSpecK F) : CatchesK F (kProg3 κ) (kBad3 F κ) := by
  intro qf done hfit hz hend
  have hF := fitsK_of_doneFits (doneFits_expandK hfit)
  have hd : done ≠ [] := by
    rintro rfl
    exact hfit
  have hl : done.length = 29 + κ := by rw [← length_expandK κ done]; exact hF.len
  have h0 : (rd done 0).2.length = 1 := by
    have := ((doneFits_rd hfit).2 0 (by
      rw [show (kProg3 κ).rounds = kRounds κ r0Rec3 from rfl, length_kRounds]; omega)).2
    simpa [kProg3, kProgWith, kRounds, kRoundsPre] using this
  by_cases hold : KFlockHolds F κ qf
  · exact Or.inl hold
  right
  have hend' : FlockEndHoldsK qf (kOutT κ (sampRec3 κ) done) := hend
  rw [kOutT_expandK done hd, kOutT_parse F hF] at hend'
  have hnot : ¬ R1CSHolds (kSetup F κ).A (kSetup F κ).B (zOfK qf) (kSetup F κ).cpos :=
    fun h ↦ hold ((kFlockHolds_iff F κ qf).mp h)
  have h0' := kTerm_zero3 hl hz
  rw [kTerm_expandK done hd, show (rd done (28 + κ)).1.2 = (rd (expandK κ done) (28 + κ)).1.2 by
    rw [show 28 + κ = (27 + κ) + 1 by omega, rd_expandK_succ], kTerm_parse F hF] at h0'
  rcases flock_front_sq (kSetup F κ) (kSetup_valid F κ) (zOfK qf) (colBitsM_bool rfl qf)
      (colWordM (m := 11) qf) (colPackM rfl qf) (parseK κ (expandK κ done)) ((rd done 0).2.headD 0)
      (parseK_expandK_τs done hd) (zcK_consistent F hF).2 (linK_consistent F hF).2 (hringK F qf _ hend')
      hnot with hbad | hfalse
  · exact hitK_of_badSq F qf hd h0 hF hbad
  · exact absurd (matClaim_of_zero F hT _ h0') hfalse

end UniKeccakSound.KF

/-- info: 'UniKeccakSound.KF.catches3K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.catches3K
