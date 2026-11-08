-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The proof is `UniSound/Ids/FlockEnd.lean`'s
-- (`diffsFlock`) for the Keccak verifier (`weightAtK`'s ring term, `q_flock` of `11 + κ` variables).
import UniSound.Ids.FlockEnd
import UniSound.Ids.Facts
import UniSound.FinalLink
import UniKeccakSound.Ids.FlockReg

/-!
# `DiffsFlockK`: the ring-switch relation gives Flock's claim on `q_flock`

**`diffsFlockK`**: on the Keccak VM, the main line's ring-switch relation `⟨[q_flock at p, twist ringTwist],
target⟩` is one of `C1`'s relations (`flockClaimK`); `combine` may merge its point into a longer one, which changes
nothing (`termWExtend`: the ring term reads `11 + κ = |p|` coordinates); a ring term's `weightAtK` is `weightAt`'s
(`termWK_ring`), its weight on the cube the tower weight (`ringInner`), which is `Σ_k d_k eq(φ^k(p), ·)`
(`towerWeight`), so its difference is `Σ_k d_k q̂(φ^k(p)) + target` (`FlockEndHoldsK`).
-/

namespace UniKeccakSound.Ids

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniKeccak Finset

/-- **A ring term's `weightAtK` is `weightAt`'s** (the slot bits play no part). -/
theorem termWK_ring (L : StackLayout) (rm : Option (List E)) (V : ℕ) (col : Column) (pt : List E) (u : ℕ) :
    termWK L rm V col pt ringTwist u = termW L rm V col pt ringTwist u := by
  rw [termWK_eq, Weights.termW_eq]
  simp only [wSumK, Weights.wSum, ite_true]

theorem layoutOfK_c1 (S : Shape) : layoutOfK S .c1 = c1LayoutK S := rfl

/-- **The ring-switch relation gives Flock's claim** (`DiffsFlockK`), for `κ = h_SHA3`. -/
theorem diffsFlockK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) (hκ : D.shape.heights.getD opBlake2s 0 = κ) : DiffsFlockK D Fl := by
  intro s c1 ch fd c2 t vals hz
  unfold diffsK at hz
  split_ifs at hz with hg
  swap
  · exact absurd (hz [1] (List.mem_singleton_self _) 1 (List.mem_singleton_self _)) one_ne_zero
  obtain ⟨⟨map, target, hend⟩, hlen⟩ := hg.2
  set fl := Fl.prog.out fd []
  set rels := relsAtK D Fl s ch fd t vals
  -- The ring relation is one of C1's.
  have hmem : (⟨[⟨.qflock, fl.1, ringTwist, 1⟩], target⟩ : Relation) ∈ mine rels .c1 := by
    refine List.mem_filter.mpr ⟨?_, rfl⟩
    show (⟨[⟨.qflock, fl.1, ringTwist, 1⟩], target⟩ : Relation) ∈ (flockClaimK _ fl).1.toList
    unfold flockClaimK
    rw [hend]
    simp
  have hrm : ringMapAtK Fl fd = some map := by
    unfold ringMapAtK flockClaimK
    rw [show (Fl.prog.out fd []).2 = .ring map target from hend]
  have h0 := hz _ (List.mem_map.mpr ⟨.c1, List.mem_cons_self .., rfl⟩) _ (List.mem_map_of_mem hmem)
  unfold relDiffK at h0
  rw [hrm] at h0
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul] at h0
  simp only [termWK_ring] at h0
  -- The merged point changes nothing.
  obtain ⟨off, hl⟩ := c1LayoutK_qflock D.shape
  rw [← layoutOfK_c1] at hl
  have hq11 : D.shape.heights.getD opBlake2s 0 + qflockRowBits = KeccakVm.kWords + κ := by
    rw [hκ]; show κ + 11 = 11 + κ; ring
  rw [hq11] at hl
  have hext : ∀ u, termW (layoutOfK D.shape .c1) (some map) (batchVarsK D.shape) .qflock
      (mergedPoint (mine rels .c1) fl.1) ringTwist u =
      termW (layoutOfK D.shape .c1) (some map) (batchVarsK D.shape) .qflock fl.1 ringTwist u := by
    intro u
    refine termWExtend (layoutOfK D.shape .c1) (some map) (batchVarsK D.shape) .qflock fl.1 _ ringTwist u
      (fun j h ↦ by cases h) ?_ ?_
    · intro b hb
      rw [hl] at hb
      rw [List.mem_singleton.mp hb, hlen]
    · exact (mergedPrefix (mine rels .c1) fl.1 ⟨(⟨[⟨.qflock, fl.1, ringTwist, 1⟩], target⟩ : Relation), hmem, _,
        List.mem_singleton_self _, rfl⟩).1
  rw [show stackForK D c1 c2 .c1 = c1 from rfl] at h0
  simp only [hext] at h0
  have hbl := layoutAligned_new _ _ (limbs_mem_blocks (L := layoutOfK D.shape .c1)
    (b := (0, KeccakVm.kWords + κ, off)) (by rw [hl]; exact List.mem_singleton_self _))
  have hb1 : 2 ^ (KeccakVm.kWords + κ) ∣ off := hbl.1
  have hb2 : off + 2 ^ (KeccakVm.kWords + κ) ≤ 2 ^ (layoutOfK D.shape .c1).vars := hbl.2
  have hvars : (layoutOfK D.shape .c1).vars ≤ batchVarsK D.shape := UniSound.layoutOf_vars_le _ _
  have hvV : KeccakVm.kWords + κ ≤ batchVarsK D.shape := by
    have h1 := hb2
    have h2 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hvars
    have h3 : 2 ^ (KeccakVm.kWords + κ) ≤ 2 ^ (batchVarsK D.shape) := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h3
  rw [ringInner (layoutOfK D.shape .c1) map (batchVarsK D.shape) c1 fl.1
    (fun b hb ↦ by rw [hl] at hb; rw [List.mem_singleton.mp hb]; exact hvV), hl] at h0
  have hoff : off < 2 ^ (batchVarsK D.shape) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hvars
    have := Nat.two_pow_pos (KeccakVm.kWords + κ)
    omega
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, limbScale, ite_true, one_mul,
    blockBase_of_aligned hb1 hoff] at h0
  have hqf : qfOffK D = off := by
    unfold qfOffK
    rw [← layoutOfK_c1, hl]
    rfl
  -- The tower weight.
  have htw : ∀ x ∈ range (2 ^ (KeccakVm.kWords + κ)), Flock.towerWeightAt (fl.1.take (KeccakVm.kWords + κ))
      ((bitsE x (KeccakVm.kWords + κ)).map (1 + ·)) map *
      stE c1 (layoutOfK D.shape .c1).vars (off + x) =
      ∑ k ∈ range 64, (Flock.towerCoefficients map).getD k 0 *
        (cubeEq (twist fl.1 k) (KeccakVm.kWords + κ) x * ofK (c1 (qfOffK D + x))) := by
    intro x hx
    rw [Finset.mem_range] at hx
    rw [towerWeight _ _ map (by simp [bitsE, hlen]), Finset.sum_mul]
    have hst : stE c1 (layoutOfK D.shape .c1).vars (off + x) = ofK (c1 (qfOffK D + x)) := by
      rw [hqf]
      unfold stE
      rw [ite_eq_left (by omega)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hst, mul_assoc]
    refine congrArg (_ * ·) (congrArg (· * ofK (c1 (qfOffK D + x))) ?_)
    unfold cubeEq
    rw [show (List.take (KeccakVm.kWords + κ) fl.1).length = KeccakVm.kWords + κ by simp [hlen]]
    refine Finset.prod_congr rfl fun n hn ↦ ?_
    rw [Finset.mem_range] at hn
    rw [bitsE_getD x _ n hn, twist_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
      ite_eq_left hn, ← List.getD_eq_getElem?_getD]
    ring
  rw [Finset.sum_congr rfl htw, Finset.sum_comm] at h0
  have hmle : ∀ k ∈ range 64, ∑ x ∈ range (2 ^ (KeccakVm.kWords + κ)), (Flock.towerCoefficients map).getD k 0 *
        (cubeEq (twist fl.1 k) (KeccakVm.kWords + κ) x * ofK (c1 (qfOffK D + x))) =
      (Flock.towerCoefficients map).getD k 0 * mleE (qfK D c1 κ) (twist fl.1 k) := by
    intro k _
    rw [← Finset.mul_sum]
    refine congrArg ((Flock.towerCoefficients map).getD k 0 * ·) ?_
    unfold mleE qfK
    simp only [Vector.get_ofFn]
    exact (Fin.sum_univ_eq_sum_range (fun x ↦ cubeEq (twist fl.1 k) (KeccakVm.kWords + κ) x *
      ofK (c1 (qfOffK D + x))) _).symm
  rw [Finset.sum_congr rfl hmle] at h0
  show FlockEndHoldsK (qfK D c1 κ) fl
  unfold FlockEndHoldsK
  rw [hend]
  exact CharTwo.add_eq_zero.mp h0

end UniKeccakSound.Ids

/-- info: 'UniKeccakSound.Ids.diffsFlockK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.diffsFlockK
