-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `E2ECompleteness/ProverConstants.lean`, `E2ECompleteness/ProverFacts.lean` and
-- `Bridge/Claims/Constants.lean` (the previous protocol's constants, unchanged by the PCS claims).
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the fields `K`, `E`.
import E2ECompleteness.PcsDefs
import E2ECompleteness.PcsNtt
import Bridge.Claims.Tau
import Completeness
import Compose.Reduce

/-!
# The Statement's constants are the proof layers'

`Constants` (`PcsDefs.lean`) holds (**`constants`**: `beta()` a Cantor basis and `coordinates(11)` by kernel
evaluation, `row_vanishing(24)` from its kernel-checked words `tauWords`); from it, `beta()`'s first `24`
vectors are F1's `deployedBasis` (`betaAt_eq_deployed`), and F1's deployed instance matches `reduce` at the
Statement's constants (**`matches_deployed`**).
-/

open LeanVM LeanVM.Parameters PcsQuotient PcsQuotient.Domain Finset
open QuotientSecurity

set_option autoImplicit false

namespace E2ECompleteness.Pcs

/-! ## Words (`Bridge/Claims/Constants.lean`) -/

/-- An entry of a list of `K` given by its words. -/
theorem getD_of_words {l : List K} {ws : List UInt64} (h : l.map K.lane = ws) (i : ℕ) :
    l.getD i 0 = K.ofLane (ws.getD i 0) := by
  subst h
  by_cases hi : i < l.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none,
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega), Option.getD_none]
    rfl

/-! ## The Cantor basis -/

/-- **The statement's Cantor basis, as words**: F0c's `betaWords` (the first `24`, which the
instance reads), then four more (by kernel evaluation of the statement's pivots and solves). -/
theorem beta_lanes : PcsQuotient.Domain.beta.toList.map K.lane =
    betaWords ++ [0xf89578714bd28f96, 0x564dda59237a3352, 0xad33bc6cc75aed38, 0x57a3104fcd0e5f34] := by
  decide +kernel

theorem betaAt_eq_getD (k : ℕ) : betaAt k = PcsQuotient.Domain.beta.toList.getD k 0 := by
  simp [betaAt, List.getD_eq_getElem?_getD]

/-- **`β_k`, `k < 24`, is the deployed basis's** (`QuotientSecurity.deployedBasis`, `beta()`'s
words). -/
theorem betaAt_eq_deployedBasis (k : ℕ) (hk : k < 22 + 2) : betaAt k = deployedBasis.β k := by
  rw [betaAt_eq_getD, getD_of_words beta_lanes,
    List.getD_append _ _ _ _ (show k < betaWords.length by rw [show betaWords.length = 24 from rfl]; omega)]
  rfl


/-! ## The rows' polynomial -/

/-- `row_vanishing(24)`'s words (the Rust's, which F5's graph carries as `tau`). -/
def tauWords : List UInt64 :=
  [5246327309480240592, 462416703093199623, 5836061695391999385, 17933131952861334950,
    18372946041939442404, 12828942987611060278, 13588355210333287157, 1205146552516504875,
    981042065287506825, 5923339044450209179, 951408172292342183, 12676167449202766892,
    13719231351162120800, 12661900118541078806, 12449589984762772511, 11682037014426230835,
    1012368888076811759, 18272804218237563919, 5328687504910262779, 18383142605220007825,
    802269026382174146, 1506959928840120550, 1]

/-- **`rowVanishing 24`, as words** (`Tau.lean`: `22` kernel-checked elimination steps). -/
theorem rowVanishing_24_words : (rowVanishing 24).map K.lane = tauWords :=
  Bridge.Claims.rowVanishing_24_lanes


theorem sum_range_eq_list (f : ℕ → K) :
    ∀ n, ∑ k ∈ Finset.range n, f k = ((List.range n).map f).sum
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_range_eq_list f n, List.range_succ, List.map_append,
      List.sum_append]
    simp

/-- `row_vanishing(24)`'s system, in `K`, by kernel evaluation (`22` equations of `23` products). -/
theorem tau_system : ∀ j < 22 + 2, 2 ≤ j →
    ((List.range (22 + 1)).map fun k ↦
      (if k ≤ j then betaF64 (j - k) else 0) * K.ofLane (tauWords.getD k 0)).sum = 0 := by
  decide +kernel


/-! ## `beta()` -/

/-- Every vector `beta()` pushes is a `solve`'s. -/
theorem foldl_push_solve : ∀ (n : ℕ) (init : Array K),
    ∀ k, init.size ≤ k → k < ((List.range n).foldl (fun b _ ↦ b.push (solve (b.back?.getD 1)))
      init).size → ∃ x, ((List.range n).foldl (fun b _ ↦ b.push (solve (b.back?.getD 1))) init)[k]?
        = some (solve x)
  | 0, init, k, h1, h2 => by simp at h2; omega
  | n + 1, init, k, h1, h2 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at h2 ⊢
    set b := (List.range n).foldl (fun b _ ↦ b.push (solve (b.back?.getD 1))) init
    rw [Array.size_push] at h2
    by_cases hk : k < b.size
    · obtain ⟨x, hx⟩ := foldl_push_solve n init k h1 hk
      refine ⟨x, ?_⟩
      rw [Array.getElem?_push_lt hk]
      rwa [Array.getElem?_eq_getElem hk] at hx
    · have : k = b.size := by omega
      subst this
      exact ⟨_, Array.getElem?_push_size⟩

theorem size_foldl_push : ∀ (n : ℕ) (init : Array K),
    ((List.range n).foldl (fun b _ ↦ b.push (solve (b.back?.getD 1))) init).size = init.size + n
  | 0, _ => rfl
  | n + 1, init => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Array.size_push,
      size_foldl_push n init]
    rfl

theorem beta_size : beta.size = basisSize := by
  unfold beta
  rw [size_foldl_push]
  rfl

/-- `solve` clears the low bit. -/
theorem lowBit_solve (x : K) : lowBit (solve x) = false := by
  unfold lowBit solve
  simp only [Primitives.F64.toU64, K.ofLane]
  rw [show (UInt64.ofBitVec (BF64.ofBitVec (UInt64.toBitVec
      (solveLoop 64 x.lane 0 &&& ~~~(1 : UInt64)))).toBitVec) =
      solveLoop 64 x.lane 0 &&& ~~~(1 : UInt64) from rfl]
  rw [UInt64.toNat_and, Nat.testBit_and]
  simp

/-- **`beta()`'s vectors past the first have their low bit clear.** -/
theorem lowBit_betaAt {k : ℕ} (h0 : 0 < k) (hk : k < basisSize) : lowBit (betaAt k) = false := by
  have hs : k < beta.size := by rw [beta_size]; exact hk
  obtain ⟨x, hx⟩ := foldl_push_solve (basisSize - 1) #[1] k (by simp; omega) (by
    rw [size_foldl_push]; simp [basisSize] at hk ⊢; omega)
  have hb : betaAt k = solve x := by
    unfold betaAt
    rw [Array.getD_eq_getD_getElem?]
    show (beta[k]?).getD 0 = solve x
    rw [show beta = (List.range (basisSize - 1)).foldl
      (fun b _ ↦ b.push (solve (b.back?.getD 1))) #[1] from rfl, hx]
    rfl
  rw [hb]
  exact lowBit_solve x

/-- The Statement's basis as F1's, its first `24` vectors. -/
def stmtBasis (hK : Constants) : CantorBasis K (22 + 2) :=
  Bridge.Ntt.cantorOf (E2ECompleteness.Pcs.Ntt.cantorUpTo_of_isCantorBasis hK.cantor (by decide))

/-- **`beta()`'s first `24` vectors are `deployedBasis`'s.** -/
theorem betaAt_eq_deployed (hK : Constants) {k : ℕ} (hk : k < 22 + 2) :
    betaAt k = deployedBasis.β k :=
  deployedBasis_unique (stmtBasis hK) (fun k h0 hk ↦ lowBit_betaAt h0 (by
    unfold basisSize; omega)) k hk

/-! ## The constants of `reduce` -/

/-- **The Statement's constants** as `reduce`'s: `beta()` and `row_vanishing(24)`. -/
def stmtConsts : Compose.Reduce.Consts := ⟨betaAt, fun k ↦ (rowVanishing (22 + 2)).getD k 0⟩

theorem length_rowVanishing (m : ℕ) : (rowVanishing m).length = m - 2 + 1 := by
  simp [rowVanishing]

/-- `rowPolyAt` as a sum. -/
theorem rowPolyAt_eq_sum (x : K) :
    rowPolyAt (22 + 2) x = ∑ k ∈ range (22 + 1), (rowVanishing (22 + 2)).getD k 0 *
      (chain x (22 + 2 - 1)).getD k 0 := by
  unfold rowPolyAt
  have hl1 : (chain x (22 + 2 - 1)).length = 22 + 1 := by
    rw [chain, Bridge.Ntt.chain_foldl]
    simp
  have hl2 : (rowVanishing (22 + 2)).length = 22 + 1 := length_rowVanishing _
  generalize hc : chain x (22 + 2 - 1) = ws at hl1 ⊢
  generalize hr : rowVanishing (22 + 2) = ts at hl2 ⊢
  -- A fold of `acc + t · w` over a zip of two lists of length `n`.
  have key : ∀ (ws ts : List K) (n : ℕ), ws.length = n → ts.length = n → ∀ a : K,
      (ws.zip ts).foldl (fun acc (p : K × K) ↦ acc + p.2 * p.1) a =
        a + ∑ k ∈ range n, ts.getD k 0 * ws.getD k 0 := by
    intro ws
    induction ws with
    | nil => intro ts n h1 _ a; subst h1; simp
    | cons w ws ih =>
      intro ts n h1 h2 a
      rcases ts with _ | ⟨t, ts⟩
      · simp at h1 h2; omega
      · rcases n with _ | n
        · simp at h1
        simp only [List.zip_cons_cons, List.foldl_cons]
        rw [ih ts n (by simpa using h1) (by simpa using h2), sum_range_succ', add_assoc]
        simp [add_comm]
  rw [key ws ts (22 + 1) hl1 hl2 0, zero_add]

/-- **`row_vanishing(24)` solves its system.** -/
theorem rowVanishing_stmt (hK : Constants) : Compose.Reduce.RowVanishing stmtConsts 22 := by
  obtain ⟨hlast, hzero, -, -, -⟩ := hK.rows
  have hl : (rowVanishing (22 + 2)).length = 22 + 1 := length_rowVanishing _
  have hB := E2ECompleteness.Pcs.Ntt.cantorUpTo_of_isCantorBasis hK.cantor (N := basisSize) le_rfl
  refine ⟨?_, fun j hj2 hj ↦ ?_⟩
  · simp only [stmtConsts]
    rw [List.getLast?_eq_getElem?, hl] at hlast
    rw [List.getD_eq_getElem?_getD, show (22 : ℕ) = 22 + 1 - 1 from rfl, hlast]
    rfl
  · simp only [stmtConsts]
    have h := hzero ⟨j, hj⟩ hj2
    rw [rowPolyAt_eq_sum] at h
    refine Eq.trans (sum_congr rfl fun k hk ↦ ?_) h
    have hk' := mem_range.mp hk
    rw [Bridge.Ntt.chain_getD _ (by omega), Bridge.Ntt.iterate_betaAt hB (by unfold basisSize; omega),
      mul_comm]

/-! ## The weights -/

theorem ofBits_shiftLeft (j : ℕ) (hj : j < 64) :
    K.ofBits (1 <<< j) = Primitives.F64.ofU64 ((1 : UInt64) <<< j.toUInt64) := by
  rw [one_shiftLeft_toUInt64 j hj]
  rfl

/-- `bit_weight`, transcribed twice. -/
theorem bitWeight_eq (j : ℕ) (hj : j < 128) : Compose.Reduce.bitWeight j = rustBitWeight j := by
  unfold Compose.Reduce.bitWeight rustBitWeight
  by_cases h : j < 64
  · rw [if_pos h, if_pos h, ofBits_shiftLeft j h]
    rfl
  · rw [if_neg h, if_neg h, ofBits_shiftLeft (j - 64) (by omega)]
    rfl

/-- **`coordinate_weight` is the deployed instance's weights** below `8`. -/
theorem coordinateWeight_deployed (k : ℕ) (hk : k < 8) :
    Compose.Reduce.coordinateWeight k = some (Completeness.deployedInstanceE.c k) := by
  rw [show Completeness.deployedInstanceE.c k = coordWeight Primitives.F192.G Primitives.F192.Y k
    from rfl, ← rustCoordinateWeight_eq k hk]
  unfold Compose.Reduce.coordinateWeight rustCoordinateWeight
  by_cases h0 : k = 0
  · rw [if_pos h0, if_pos h0, bitWeight_eq 1 (by norm_num)]
  by_cases h1 : k = 1
  · rw [if_neg h0, if_neg h0, if_pos h1, if_pos h1]
  rw [if_neg h0, if_neg h0, if_neg h1, if_neg h1, if_pos hk, if_pos hk, bitWeight_eq _ ?_]
  rw [Nat.shiftLeft_eq, one_mul]
  calc 2 ^ (k - 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ < 128 := by norm_num

/-- **F1's deployed instance matches `reduce` at the Statement's constants.** -/
theorem matches_deployed (hK : Constants) :
    Compose.Reduce.Matches Completeness.deployedInstanceE.params stmtConsts 22 :=
  Compose.Reduce.matches_params Completeness.deployedInstanceE stmtConsts
    (fun k hk ↦ by
      show algebraMap K E (deployedBasis.β k) = ofK (betaAt k)
      rw [betaAt_eq_deployed hK hk]
      rfl)
    coordinateWeight_deployed (rowVanishing_stmt hK)


/-! ## The constants hold -/

/-- **`beta()` is a Cantor basis** (its `28` vectors), by kernel evaluation. -/
theorem isCantorBasis : IsCantorBasis := by decide +kernel

/-- **`coordinates(11)` reads the region's coordinates**, by kernel evaluation. -/
theorem coordinatesRead : CoordinatesRead 11 := by decide +kernel

/-- The rows' polynomial at `x`, from `τ`'s words. -/
theorem rowPolyAt_words (x : K) :
    rowPolyAt (22 + 2) x = ((List.range (22 + 1)).map fun k ↦
      K.ofLane (tauWords.getD k 0) * S^[k] x).sum := by
  rw [rowPolyAt_eq_sum, sum_range_eq_list]
  refine congrArg List.sum (List.map_congr_left fun k hk ↦ ?_)
  rw [getD_of_words rowVanishing_24_words,
    Bridge.Ntt.chain_getD _ (by simp at hk; omega)]

/-- The three values the rows' polynomial must not vanish at, by kernel evaluation. -/
theorem rowPoly_words_ne :
    ((List.range (22 + 1)).map fun k ↦ K.ofLane (tauWords.getD k 0) * S^[k] 1).sum ≠ 0 ∧
      ((List.range (22 + 1)).map fun k ↦
        K.ofLane (tauWords.getD k 0) * S^[k] (betaF64 1)).sum ≠ 0 ∧
      ((List.range (22 + 1)).map fun k ↦
        K.ofLane (tauWords.getD k 0) * S^[k] (1 + betaF64 1)).sum ≠ 0 := by
  decide +kernel

/-- **`row_vanishing(24)` vanishes exactly on the `X` cells** (`RowVanishingProperty 24`). -/
theorem rowVanishingProperty : RowVanishingProperty 24 := by
  have hB := E2ECompleteness.Pcs.Ntt.cantorUpTo_of_isCantorBasis isCantorBasis (N := basisSize) le_rfl
  have hb1 : betaAt 1 = betaF64 1 := betaAt_eq_deployedBasis 1 (by norm_num)
  obtain ⟨n1, n2, n3⟩ := rowPoly_words_ne
  refine ⟨?_, fun j hj2 ↦ ?_, ?_, ?_, ?_⟩
  · have hl : (rowVanishing 24).length = 22 + 1 := length_rowVanishing _
    rw [List.getLast?_eq_getElem?, hl]
    have h := getD_of_words rowVanishing_24_words 22
    rw [List.getD_eq_getElem?_getD] at h
    rcases he : (rowVanishing 24)[22]? with _ | x
    · rw [List.getElem?_eq_none_iff] at he
      omega
    · rw [he, Option.getD_some] at h
      rw [h]
      rfl
  · show rowPolyAt (22 + 2) (betaAt j) = 0
    rw [rowPolyAt_eq_sum, sum_range_eq_list]
    refine Eq.trans (congrArg List.sum (List.map_congr_left fun k hk ↦ ?_))
      (tau_system j j.isLt hj2)
    have hk' : k < 22 + 1 := by simp at hk; omega
    rw [getD_of_words rowVanishing_24_words, Bridge.Ntt.chain_getD _ (by omega),
      Bridge.Ntt.iterate_betaAt hB (by have := j.isLt; unfold basisSize; omega), mul_comm]
    by_cases hkj : k ≤ (j : ℕ)
    · rw [if_pos hkj, if_pos hkj, betaAt_eq_deployedBasis _ (by have := j.isLt; omega)]
      rfl
    · rw [if_neg hkj, if_neg hkj]
  · rw [show (24 : ℕ) = 22 + 2 from rfl, rowPolyAt_words]
    exact n1
  · rw [show (24 : ℕ) = 22 + 2 from rfl, rowPolyAt_words, hb1]
    exact n2
  · rw [show (24 : ℕ) = 22 + 2 from rfl, rowPolyAt_words, hb1]
    exact n3

/-- **The Statement's computed constants have their defining properties.** -/
theorem constants : Constants := ⟨isCantorBasis, coordinatesRead, rowVanishingProperty⟩

end E2ECompleteness.Pcs

/-- info: 'E2ECompleteness.Pcs.constants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.constants

/-- info: 'E2ECompleteness.Pcs.matches_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.matches_deployed
