-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Follows `formal/FlockSound/FlockSoundUni/Catch.lean`
-- at the Keccak verifier's sizes; the structured terminal's zero replaces the pending claim.
import UniKeccakSound.Flock.Parse
import FlockSoundUni.Catch
import FlockSoundUni.Transcription

/-!
# The Keccak verifier's Flock bad family catches

`CatchesK F (kProg κ) (kBad F κ)` is `FlockSound`'s deterministic theorem (`flock_front`, at `kSetup F κ`) on the
transcript: a completed transcript whose zeros vanish (the structured terminal's) and whose ring claim holds of the
column has a satisfied relation, or one of its challenges is in its bad set.

* the transcript's shape (`FitsK`, from `DoneFits`), the decoded rounds' consistency (`zcK_consistent`,
  `linK_consistent`), the code's result as the run's (`kOutT_parse`: the point, the map, the slices) and the
  structured terminal's zero as the run's (`kTerm_parse`);
* the ring claim on `q_flock` at `11 + κ` variables is `hring`'s left side (`ringK`, `Tower.lean`'s at `m = 11`);
* each bad event of `Front.Bad` a hit of `kBad` (`hitK_of_bad`, by the prefix property);
* **the terminal** (`TerminalSpecK F`): the structured terminal at the run's skip point, row point, lincheck points,
  `α` and slices is the matrices' product sum `Σ_cy matPart … s(cy)` plus the two known terms (`Front.known`): its
  zero is then the product sum's claim `matClaim` (`matClaim_of_zero`). `Terminal.lean` proves it for
  `KeccakFlock.keccakFlockSpec`.

**`catchesK`** proves `CatchesK` from `TerminalSpecK F`.
-/

namespace UniKeccakSound.KF

open UniSound hiding rd
open UniStatement LeanVM.Parameters LeanVM.Semantics Finset Polynomial FlockSound FlockSound.Uni
open LeanVM.Protocol (Column)

variable {κ : ℕ}

/-! ## The transcript's shape -/

theorem kRounds_getElem (κ a : ℕ) (h : a < (kRounds κ (r0Main κ)).length) :
    (kRounds κ (r0Main κ))[a] = if a = 0 then ⟨false, 0, 6 + κ⟩ else if a = 1 then ⟨false, 8, 0⟩
      else if a < 28 + κ then ⟨false, 2, 0⟩ else ⟨false, 64, 5⟩ := by
  have h' : a < 29 + κ := length_kRounds κ _ ▸ h
  simp only [kRounds, kRoundsPre, List.getElem_append, List.length_append, List.length_cons,
    List.length_replicate, List.length_nil, List.getElem_replicate, List.getElem_cons]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- **The transcript's shape**: `29 + κ` rounds, each of its round's reads and draws. -/
structure FitsK (κ : ℕ) (done : Done) : Prop where
  len : done.length = 29 + κ
  r0 : (rd done 0).2.length = 7 + κ
  r1v : (rd done 1).1.2.length = 8
  r1c : (rd done 1).2.length = 1
  mid : ∀ a, 2 ≤ a → a < 28 + κ → (rd done a).1.2.length = 2 ∧ (rd done a).2.length = 1
  r6v : (rd done (28 + κ)).1.2.length = 64
  r6c : (rd done (28 + κ)).2.length = 6

theorem fitsK_of_doneFits {done : Done} (h : DoneFits (kRounds κ (r0Main κ)) done) : FitsK κ done := by
  obtain ⟨hl, hr⟩ := doneFits_rd h
  have hL := length_kRounds κ (r0Main κ)
  have at_ : ∀ a (ha : a < 29 + κ), (rd done a).1.2.length = ((kRounds κ (r0Main κ))[a]'(by omega)).nv ∧
      (rd done a).2.length = ((kRounds κ (r0Main κ))[a]'(by omega)).ns + 1 :=
    fun a ha ↦ hr a (by omega)
  refine ⟨by omega, ?_, ?_, ?_, fun a h2 h28 ↦ ?_, ?_, ?_⟩
  · have := (at_ 0 (by omega)).2
    rw [kRounds_getElem] at this
    simp only [ite_true] at this
    omega
  · have := (at_ 1 (by omega)).1
    rw [kRounds_getElem] at this
    simpa using this
  · have := (at_ 1 (by omega)).2
    rw [kRounds_getElem] at this
    simpa using this
  · have := at_ a (by omega)
    rw [kRounds_getElem, ite_eq_right (by omega : ¬a = 0), ite_eq_right (by omega : ¬a = 1),
      ite_eq_left h28] at this
    exact this
  · have := (at_ (28 + κ) (by omega)).1
    rw [kRounds_getElem, ite_eq_right (by omega : ¬28 + κ = 0), ite_eq_right (by omega : ¬28 + κ = 1),
      ite_eq_right (by omega : ¬28 + κ < 28 + κ)] at this
    exact this
  · have := (at_ (28 + κ) (by omega)).2
    rw [kRounds_getElem, ite_eq_right (by omega : ¬28 + κ = 0), ite_eq_right (by omega : ¬28 + κ = 1),
      ite_eq_right (by omega : ¬28 + κ < 28 + κ)] at this
    exact this

/-! ## The ring claim at `11 + κ` variables -/

theorem wordFinM_eq (m κ : ℕ) (u : Cube (m + κ)) : wordFinM m κ (lowPart u, highPart u) = cubeFin (m + κ) u := by
  apply Fin.ext
  simp only [wordFinM, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, LeanVM.Protocol.cubeSplit_apply,
    LeanVM.Protocol.cubeIndex]
  rw [← cubeFin_append_val, append_lowPart_highPart]

/-- **The ring claim the verifier pushes on `q_flock`** (`FlockEndHoldsK`: the 64 twisted terms) **is `hring`'s left
side**, `Σ_u Φ_tower(eq(p, u)) q(u)`, at `11 + κ` variables (`Tower.lean`'s `ringClaim_code`). -/
theorem ringClaim_codeK (κ : ℕ) (qf : Column (11 + κ)) (p map : List E) :
    ∑ k ∈ range 64, (Flock.towerCoefficients map).getD k 0 * mleE qf (twist p k) =
      ∑ u, stagedMap [1, 2, 4, 8, 16, 32] (fun i ↦ map.getD i.val 0) (eqP (ptOf p (11 + κ)) u) *
        colWordM (m := 11) qf u := by
  simp only [mleE, cubeEq_twist, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← (cubeFin (11 + κ)).sum_comp]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [stagedMap_tower_list, phiT_expand, show (2 : ℕ) ^ 6 = 64 by norm_num, Finset.sum_mul, cubeEq_cubeFin,
    colWordM, wordFinM_eq]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [towerCoefficients_getD map k (mem_range.mp hk)]
  ring

theorem ringK (κ : ℕ) (qf : Column (11 + κ)) (p : Fin (11 + κ) → E) (f : Fin 6 → E) :
    ∑ k ∈ range 64, (Flock.towerCoefficients (List.ofFn f)).getD k 0 * mleE qf (twist (List.ofFn p) k) =
      ∑ u, stagedMap [1, 2, 4, 8, 16, 32] f (eqP p u) * colWordM (m := 11) qf u := by
  rw [ringClaim_codeK, ptOf_ofFn]
  simp only [ofFn_challenges]

/-! ## The decoded rounds and the code's result -/

theorem getD_replicate_none11 (t : Fin 11) : (List.replicate 11 (none : Option E)).getD t none = none := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, t.isLt, ite_true, Option.getD_some]

section Run

variable (F : KeccakVm.KeccakFlockSpec) {done : Done} (hF : FitsK κ done)
include hF

/-- The parsed run's zerocheck point is the code's `eq` factors. -/
theorem kEs_getD (t : Fin (3 + 11 + κ)) :
    (kEs done).getD t none = some (Front.τ (kSetup F κ) (parseK κ done) t) := by
  have hlen : (Flock.fixedChallenges ++ kSampled done).length = 3 + 11 + κ := by
    simp only [List.length_append, length_fixedChallenges, kSampled, hF.r0]
    omega
  have ht := t.isLt
  have e1 : (kEs done).getD t none = some ((Flock.fixedChallenges ++ kSampled done).getD t 0) := by
    simp only [kEs, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (show t.val < (Flock.fixedChallenges ++ kSampled done).length by omega),
      Option.map_some, Option.getD_some]
  rw [e1]
  congr 1
  show _ = Fin.append fixedPt (parseK κ done).τs (Fin.cast _ t)
  rw [fin_append_cast]
  split_ifs with h7
  · rw [← tx_fixedChallenges_getD]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left
      (show t.val < Flock.fixedChallenges.length by rw [length_fixedChallenges]; exact h7)]
  · show _ = (kSampled done).getD (t - 7) 0
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right
      (show Flock.fixedChallenges.length ≤ t.val by rw [length_fixedChallenges]; omega),
      length_fixedChallenges]

/-- **The zerocheck is consistent**, and its claims are the code's. -/
theorem zcK_consistent :
    (∀ t : Fin (3 + 11 + κ + 1), claimAt (Front.c₀ (kSetup F κ) (parseK κ done)) (parseK κ done).zq
      (parseK κ done).zχ t = scClaim (kC0 done) (kEs done) (done.drop 2) t) ∧
    Consistent 2 (fun i ↦ some (Front.τ (kSetup F κ) (parseK κ done) i))
      (Front.c₀ (kSetup F κ) (parseK κ done)) (parseK κ done).zq (parseK κ done).zχ := by
  refine sc_consistent (kC0 done) _ ?_ (kEs done) (done.drop 2) _ _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)
    (kEs_getD F hF) fun t ↦ ?_
  · have hc : kCoset done = List.ofFn fun i : Fin 8 ↦ (parseK κ done).cv ((cubeFin 3).symm i) := by
      show (rd done 1).1.2 = _
      conv_lhs => rw [eq_ofFn_getD hF.r1v 0]
      congr 1
      funext i
      show _ = (kCoset done).getD (cubeFin 3 ((cubeFin 3).symm i)) 0
      rw [Equiv.apply_symm_apply]
      rfl
    show Flock.lagrangeInterpolate 16 (List.replicate 8 0 ++ kCoset done) (kZ done) = _
    rw [hc, tx_interp]
    rfl
  · rw [rd_drop]
    exact (hF.mid _ (by omega) (by have := t.isLt; omega)).1

theorem runningK_eq : Front.running (kSetup F κ) (parseK κ done) = kRunning κ done :=
  (zcK_consistent F hF).1 (Fin.last _)

/-- **The lincheck is consistent**, and its claims are the code's. -/
theorem linK_consistent :
    (∀ t : Fin (11 + 1), claimAt (Front.linC₀ (kSetup F κ) (parseK κ done)) (parseK κ done).lq
      (parseK κ done).lχ t = scClaim (kLc0 κ done) (List.replicate 11 none) (done.drop (17 + κ)) t) ∧
    Consistent 2 (fun _ ↦ none) (Front.linC₀ (kSetup F κ) (parseK κ done)) (parseK κ done).lq
      (parseK κ done).lχ := by
  refine sc_consistent (kLc0 κ done) _ ?_ (List.replicate 11 none) (done.drop (17 + κ)) _ _ _
    (fun t ↦ ?_) (fun _ ↦ rfl) (fun t ↦ getD_replicate_none11 t) fun t ↦ ?_
  · show _ = (parseK κ done).va + (parseK κ done).α * (parseK κ done).vb +
      (parseK κ done).α ^ 2 * (Front.running (kSetup F κ) (parseK κ done) + (parseK κ done).va *
        (parseK κ done).vb) + (parseK κ done).α ^ 3
    rw [runningK_eq F hF, ← epow_eq, ← epow_eq]
    rfl
  · show msgPoly (decodeMsg _ none _) = msgPoly (decodeMsg _ _ _)
    rw [getD_replicate_none11]
  · rw [rd_drop]
    exact (hF.mid _ (by omega) (by have := t.isLt; omega)).1

omit F in
theorem decodeK_zc :
    decodeSC (Flock.lagrangeInterpolate 16 (List.replicate 8 0 ++ kCoset done) (kZ done))
        ((Flock.fixedChallenges ++ kSampled done).map some) ((done.drop 2).take (14 + κ)) =
      (List.ofFn (parseK κ done).zχ, kRunning κ done) := by
  have hl : ((done.drop 2).take (14 + κ)).length = 14 + κ := by
    simp only [List.length_take, List.length_drop, hF.len]
    omega
  have hes : ((Flock.fixedChallenges ++ kSampled done).map some).length = 14 + κ := by
    simp only [List.length_map, List.length_append, length_fixedChallenges, kSampled, hF.r0]
    omega
  rw [decodeSC_eq _ _ _ (hl.trans hes.symm), hes, map_eq_ofFn hl noRound]
  congr 1
  · congr 1
    funext t
    show (rd ((done.drop 2).take (14 + κ)) t).2.headD 0 = (rd (done.drop 2) t).2.headD 0
    rw [rd_take t.isLt]
  · exact scClaim_congr _ _ _ fun v hv ↦ rd_take hv

theorem decodeK_lin :
    decodeSC (kVa κ done + kAlpha κ done * kVb κ done +
        epow (kAlpha κ done) 2 * (kRunning κ done + kVa κ done * kVb κ done) + epow (kAlpha κ done) 3)
        (List.replicate 11 none) ((done.drop (17 + κ)).take 11) =
      (List.ofFn (parseK κ done).lχ, Front.rlc (kSetup F κ) (parseK κ done)) := by
  have hl : ((done.drop (17 + κ)).take 11).length = 11 := by
    simp only [List.length_take, List.length_drop, hF.len]
    omega
  rw [decodeSC_eq _ _ _ (hl.trans (List.length_replicate ..).symm), List.length_replicate,
    map_eq_ofFn hl noRound]
  congr 1
  · congr 1
    funext t
    show (rd ((done.drop (17 + κ)).take 11) t).2.headD 0 = (rd (done.drop (17 + κ)) t).2.headD 0
    rw [rd_take t.isLt]
  · rw [scClaim_congr _ _ _ fun v hv ↦ rd_take hv]
    exact ((linK_consistent F hF).1 (Fin.last 11)).symm

omit hF in
theorem kOutT_eq (d : Done) :
    kOutT κ sampMain d = kOutOf (kSampled d) (kCoset d) (kZ d) ((d.drop 2).take (14 + κ)) (kVa κ d)
      (kVb κ d) (kAlpha κ d) ((d.drop (17 + κ)).take 11) (rd d (28 + κ)).1.2 (rd d (28 + κ)).2 := by
  simp only [kOutT, rd_drop, Nat.add_zero]
  rfl

omit hF in
theorem kTerm_eq (d : Done) (s : List E) :
    kTerm κ sampMain d s = kTermOf (kSampled d) (kCoset d) (kZ d) ((d.drop 2).take (14 + κ)) (kVa κ d)
      (kVb κ d) (kAlpha κ d) ((d.drop (17 + κ)).take 11) s := by
  simp only [kTerm, rd_drop, Nat.add_zero]
  rfl

/-- **The code's result is the run's**: the point of the words, the ring map and the target of the sent slices. -/
theorem kOutT_parse :
    kOutT κ sampMain done =
      (List.ofFn (Front.p (kSetup F κ) (parseK κ done)),
        .ring (List.ofFn (parseK κ done).f)
          (Flock.towerTarget (sliceList (parseK κ done).s) (List.ofFn (parseK κ done).f))) := by
  obtain ⟨-, -, h11'⟩ := ofFn_three_parts (a := 3) (b := 11) (c := κ) (parseK κ done).zχ
  have hmap : (rd done (28 + κ)).2 = List.ofFn (parseK κ done).f := eq_ofFn_getD hF.r6c 0
  have hsl : (rd done (28 + κ)).1.2 = sliceList (parseK κ done).s := eq_sliceList hF.r6v
  rw [kOutT_eq, kOutOf]
  simp only [decodeK_zc hF, decodeK_lin F hF]
  rw [h11', reverse_ofFn, hmap, hsl, ← List.ofFn_fin_append]
  rfl

/-- **The structured terminal's zero is the run's**: at the run's skip point, row point, lincheck points (the
lincheck's challenges reversed), slices and `α`, plus `r_lc`. -/
theorem kTerm_parse :
    kTerm κ sampMain done (rd done (28 + κ)).1.2 =
      UniKeccak.structuredTerminal (some (parseK κ done).z) (List.ofFn (Front.rl (kSetup F κ) (parseK κ done)))
        (List.ofFn (Front.rh (kSetup F κ) (parseK κ done))) (List.ofFn (Front.χ' (kSetup F κ) (parseK κ done)))
        (sliceList (parseK κ done).s) (parseK κ done).α + Front.rlc (kSetup F κ) (parseK κ done) := by
  obtain ⟨h3, h11, -⟩ := ofFn_three_parts (a := 3) (b := 11) (c := κ) (parseK κ done).zχ
  have hsl : (rd done (28 + κ)).1.2 = sliceList (parseK κ done).s := eq_sliceList hF.r6v
  rw [kTerm_eq, kTermOf]
  simp only [decodeK_zc hF, decodeK_lin F hF]
  rw [h3, h11, reverse_ofFn, hsl]
  rfl

end Run

/-- **The structured terminal reads the rounds before the slices only.** -/
theorem kTerm_take (d : Done) (s : List E) : kTerm κ sampMain (d.take (28 + κ)) s = kTerm κ sampMain d s := by
  unfold kTerm
  have h0 : sampMain (d.take (28 + κ)) = sampMain d := by
    unfold sampMain
    rw [rd_take (by omega)]
  have h1 : rd (d.take (28 + κ)) 1 = rd d 1 := rd_take (by omega)
  have h2 : ((d.take (28 + κ)).drop 2).take (14 + κ) = (d.drop 2).take (14 + κ) := by
    rw [List.drop_take, List.take_take]
    congr 1
    omega
  have h16 : rd ((d.take (28 + κ)).drop (16 + κ)) 0 = rd (d.drop (16 + κ)) 0 := by
    rw [rd_drop, rd_drop, rd_take (by omega)]
  have h17 : ((d.take (28 + κ)).drop (17 + κ)).take 11 = (d.drop (17 + κ)).take 11 := by
    rw [List.drop_take, List.take_take]
    congr 1
    omega
  rw [h0, h1, h2, h16, h17]

theorem kProgWith_zeros (r0 : Compose.RoundSpec) (samp : Done → List E) (d : Done) (msg : UMsg)
    (h : d.length = 28 + κ) : (kProgWith κ r0 samp).zeros d msg = [kTerm κ samp d msg.2] := by
  show (if d.length = 28 + κ then [kTerm κ samp d msg.2] else []) = _
  rw [ite_eq_left h]

/-- **The zero of a completed transcript vanishes**: the structured terminal at its slices. -/
theorem kTerm_zero {done : Done} (hl : done.length = 29 + κ) (hz : (kProg κ).ZerosVanish done []) :
    kTerm κ sampMain done (rd done (28 + κ)).1.2 = 0 := by
  have hlt : 28 + κ < done.length := by omega
  have h := hz.1 (28 + κ) hlt
  have hlen : (done.take (28 + κ)).length = 28 + κ := by rw [List.length_take]; omega
  rw [show (kProg κ) = kProgWith κ (r0Main κ) sampMain from rfl, kProgWith_zeros _ _ _ _ hlen] at h
  have h' := h _ (List.mem_singleton_self _)
  rw [kTerm_take, ← rd_eq_getElem hlt] at h'
  exact h'

/-! ## The terminal -/

/-- **The structured terminal is the matrices' product sum plus the known terms**, at the main line's shape (skip
point `z`, row point of `3`, lincheck points of `11`, `64` slices `s` on the cube): `Σ_cy matPart … s(cy)` (the
block `F`'s matrices `A`, `B` on the cube) plus `α² eq(χ_in, χ') Σ_cy e(cy) s(cy) + α³ eq(χ', cpos.2) s(cpos.1)`
(`Front.known`). For `KeccakFlock.keccakFlockSpec` this is `KeccakFlock.Core.structuredTerminal_eq_bilinear` read on
the cube (`Terminal.lean`). -/
def TerminalSpecK (F : KeccakVm.KeccakFlockSpec) : Prop :=
  ∀ (z α : E) (rl : Fin 3 → E) (rh χ' : Fin 11 → E) (s : Cube (3 + 3) → E),
    UniKeccak.structuredTerminal (some z) (List.ofFn rl) (List.ofFn rh) (List.ofFn χ') (sliceList s) α =
      ∑ cy, matPart (cubeMatM (k := 3) (l := 3) rfl F.r1cs.A) (cubeMatM (k := 3) (l := 3) rfl F.r1cs.B)
          (skipNodes 3 (by decide)) z rl rh χ' α cy * s cy +
        (α ^ 2 * FlockSound.eqEval rh χ' * ∑ cy, lowW (skipNodes 3 (by decide)) z rl cy * s cy +
          α ^ 3 * eqP χ' ((posFinM (k := 3) (l := 3) 11 rfl).symm F.constPos).2 *
            s ((posFinM (k := 3) (l := 3) 11 rfl).symm F.constPos).1)

/-- **The terminal's zero is the product sum's claim** (characteristic two). -/
theorem matClaim_of_zero (F : KeccakVm.KeccakFlockSpec) (hT : TerminalSpecK F) (R : Front E 3 3 11 κ (7 + κ) 6)
    (h0 : UniKeccak.structuredTerminal (some R.z) (List.ofFn (Front.rl (kSetup F κ) R))
        (List.ofFn (Front.rh (kSetup F κ) R)) (List.ofFn (Front.χ' (kSetup F κ) R)) (sliceList R.s) R.α +
        Front.rlc (kSetup F κ) R = 0) :
    Front.matClaim (kSetup F κ) R = ∑ cy, matPart (cubeMatM (k := 3) (l := 3) rfl F.r1cs.A)
      (cubeMatM (k := 3) (l := 3) rfl F.r1cs.B) (skipNodes 3 (by decide)) R.z (Front.rl (kSetup F κ) R)
      (Front.rh (kSetup F κ) R) (Front.χ' (kSetup F κ) R) R.α cy * R.s cy := by
  rw [hT] at h0
  have e : Front.matClaim (kSetup F κ) R = Front.rlc (kSetup F κ) R +
      (R.α ^ 2 * FlockSound.eqEval (Front.rh (kSetup F κ) R) (Front.χ' (kSetup F κ) R) *
        ∑ cy, lowW (skipNodes 3 (by decide)) R.z (Front.rl (kSetup F κ) R) cy * R.s cy +
        R.α ^ 3 * eqP (Front.χ' (kSetup F κ) R) ((posFinM (k := 3) (l := 3) 11 rfl).symm F.constPos).2 *
          R.s ((posFinM (k := 3) (l := 3) 11 rfl).symm F.constPos).1) := rfl
  rw [e]
  exact CharTwo.add_eq_zero.mp (by linear_combination h0)

/-! ## Each bad event is a hit -/

section Hit

variable (F : KeccakVm.KeccakFlockSpec) (qf : Column (KeccakVm.kWords + κ)) (R : Front E 3 3 11 κ (7 + κ) 6)

theorem badAtK_τ (a : Fin (7 + κ)) :
    badAtK F qf R 0 a = pointBad (7 + κ) (sampledTables (kSetup F κ).hsize (kSetup F κ).fixed
      (Front.zRes (kSetup F κ) (zOfK qf))) R.τs a := by
  unfold badAtK
  rw [ite_eq_left rfl, dite_eq_left a.isLt]

theorem badAtK_z :
    badAtK F qf R 1 0 = skipBad (kSetup F κ).node (Front.zA (kSetup F κ) (zOfK qf))
      (Front.zB (kSetup F κ) (zOfK qf)) (Front.zZ (zOfK qf)) (Front.τ (kSetup F κ) R) R.cv := by
  unfold badAtK
  rw [ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left rfl]

theorem badAtK_zc (t : Fin (3 + 11 + κ)) :
    badAtK F qf R (2 + t) 0 = zcBad (kSetup F κ).node (Front.zA (kSetup F κ) (zOfK qf))
      (Front.zB (kSetup F κ) (zOfK qf)) (Front.zZ (zOfK qf)) (pinTab (zOfK qf) (kSetup F κ).cpos)
      (Front.τ (kSetup F κ) R) R.z (Front.c₀ (kSetup F κ) R) R.zq R.zχ t := by
  have := t.isLt
  unfold badAtK
  rw [ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_left (by omega), ite_eq_left rfl]
  congr 1
  ext
  simp

theorem badAtK_α :
    badAtK F qf R (16 + κ) 0 = alphaBad R.va R.vb (Front.vc (kSetup F κ) R)
      (skipVal (kSetup F κ).node (Front.zA (kSetup F κ) (zOfK qf)) R.z R.zχ)
      (skipVal (kSetup F κ).node (Front.zB (kSetup F κ) (zOfK qf)) R.z R.zχ)
      (skipVal (kSetup F κ).node (Front.zZ (zOfK qf)) R.z R.zχ)
      (zhat (zOfK qf) (Front.rt (kSetup F κ) R) (kSetup F κ).cpos) := by
  unfold badAtK
  rw [ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right (by omega), ite_eq_left rfl,
    ite_eq_left rfl]

theorem badAtK_lin (t : Fin 11) :
    badAtK F qf R (17 + κ + t) 0 = sumBad 2 11 (fun _ ↦ none)
      (linRev (linFun (kSetup F κ).A (kSetup F κ).B (zOfK qf) (kSetup F κ).cpos (kSetup F κ).node
        R.z (Front.rl (kSetup F κ) R) (Front.rh (kSetup F κ) R) (Front.rt (kSetup F κ) R) R.α))
      R.lq R.lχ t := by
  have := t.isLt
  unfold badAtK
  rw [ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right (by omega),
    ite_eq_right (by omega), dite_eq_left (by omega), ite_eq_left rfl]
  congr 1
  ext
  simp

theorem badAtK_ring (a : Fin (kSetup F κ).sh.length) :
    badAtK F qf R (28 + κ) a = ringBad univ (kSetup F κ).w (kSetup F κ).sh
      (fun cy ↦ R.s cy - strue (zOfK qf) (Front.rt (kSetup F κ) R) (Front.χ' (kSetup F κ) R) cy) R.f
      a := by
  unfold badAtK
  rw [ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right (by omega),
    ite_eq_right (by omega), dite_eq_right (by omega), ite_eq_left rfl,
    dite_eq_left (show (a : ℕ) < 6 from a.isLt)]

/-- **Each of `Front.Bad`'s events on the transcript's parse is a hit of `kBad`.** -/
theorem hitK_of_bad {done : Done} (hF : FitsK κ done)
    (hbad : Front.Bad (kSetup F κ) (parseK κ done) (zOfK qf)) : HitInK (kBad F κ) qf done := by
  have hl := hF.len
  unfold Front.Bad at hbad
  rcases hbad with ⟨a, ha⟩ | hz | ⟨t, ht⟩ | hα | ⟨t, ht⟩ | ⟨a, ha⟩
  · refine hitInK_of_mem F qf (j := 0) (i := a) (by omega) (by rw [hF.r0]; exact a.isLt) ?_
    rw [badAtK_τ]
    exact ha
  · refine hitInK_of_mem F qf (j := 1) (i := 0) (by omega) (by rw [hF.r1c]; omega) ?_
    rw [badAtK_z, ← headD_eq_getD']
    exact hz
  · have ht2 := t.isLt
    refine hitInK_of_mem F qf (j := 2 + t) (i := 0) (by omega)
      (by rw [(hF.mid _ (by omega) (by omega)).2]; omega) ?_
    rw [badAtK_zc, ← headD_eq_getD', ← rd_drop]
    exact ht
  · refine hitInK_of_mem F qf (j := 16 + κ) (i := 0) (by omega)
      (by rw [(hF.mid _ (by omega) (by omega)).2]; omega) ?_
    rw [badAtK_α, ← headD_eq_getD']
    exact hα
  · have ht11 := t.isLt
    refine hitInK_of_mem F qf (j := 17 + κ + t) (i := 0) (by omega)
      (by rw [(hF.mid _ (by omega) (by omega)).2]; omega) ?_
    rw [badAtK_lin, ← headD_eq_getD', ← rd_drop]
    exact ht
  · refine hitInK_of_mem F qf (j := 28 + κ) (i := a) (by omega)
      (by rw [hF.r6c]; exact (show (a : ℕ) < 6 from a.isLt)) ?_
    rw [badAtK_ring]
    exact ha

end Hit

/-! ## The catch -/

/-- **The ring claim on the column is `flock_front`'s.** -/
theorem hringK (F : KeccakVm.KeccakFlockSpec) (qf : Column (KeccakVm.kWords + κ)) (R : Front E 3 3 11 κ (7 + κ) 6)
    (h : FlockEndHoldsK qf (List.ofFn (Front.p (kSetup F κ) R),
      UniStatement.Flock.End.ring (List.ofFn R.f) (Flock.towerTarget (sliceList R.s) (List.ofFn R.f)))) :
    ∑ u, stagedMap (kSetup F κ).sh R.f (eqP (Front.p (kSetup F κ) R) u) * colWordM (m := 11) qf u =
      Front.target (kSetup F κ) R := by
  simp only [FlockEndHoldsK] at h
  rw [ringK κ qf, show sliceList R.s = List.ofFn fun i : Fin 64 ↦ R.s ((cubeFin (3 + 3)).symm i) from rfl,
    tower_tx_target] at h
  exact h

/-- **The Keccak verifier's Flock bad family catches**, given the terminal: on a completed transcript whose
structured terminal vanishes and whose ring claim holds of the column, the block's relation holds or a challenge is
in its bad set (`flock_front` at `kSetup F κ` on the parse). -/
theorem catchesK (F : KeccakVm.KeccakFlockSpec) (hT : TerminalSpecK F) :
    CatchesK F (kProg κ) (kBad F κ) := by
  intro qf done hfit hz hend
  have hF := fitsK_of_doneFits hfit
  by_cases hold : KFlockHolds F κ qf
  · exact Or.inl hold
  right
  have hend' : FlockEndHoldsK qf (kOutT κ sampMain done) := hend
  rw [kOutT_parse F hF] at hend'
  have hnot : ¬ R1CSHolds (kSetup F κ).A (kSetup F κ).B (zOfK qf) (kSetup F κ).cpos :=
    fun h ↦ hold ((kFlockHolds_iff F κ qf).mp h)
  have h0 := kTerm_zero hF.len hz
  rw [kTerm_parse F hF] at h0
  rcases flock_front (kSetup F κ) (kSetup_valid F κ) (zOfK qf) (colBitsM_bool rfl qf) (colWordM (m := 11) qf)
      (colPackM rfl qf) (parseK κ done) (zcK_consistent F hF).2 (linK_consistent F hF).2
      (hringK F qf _ hend') hnot with hbad | hfalse
  · exact hitK_of_bad F qf hF hbad
  · exact absurd (matClaim_of_zero F hT _ h0) hfalse

end UniKeccakSound.KF

/-- info: 'UniKeccakSound.KF.catchesK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.catchesK
