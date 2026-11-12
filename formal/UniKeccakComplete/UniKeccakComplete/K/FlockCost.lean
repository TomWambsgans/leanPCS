-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the two calls `KeccakCalls`, the block cost `hashBlocks`, the weight calculus `Common.QueryCostAtMost`; VCVio's
-- `support` of an `OracleComp`.
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/FlockCost.lean` (its cost half) and `Prob.lean`'s
-- `totalCost_le`.
import UniKeccakComplete.K.FlockCommutes
import UniKeccakComplete.K.ProverCost

/-!
# Flock's honest prover's cost, the main line's prover hypotheses, and the total

The probability layer takes Flock's prover as a parameter (`FlockProverH`) and names the facts it uses of it. Here
the cost facts are proved of the honest one, **`flockProveH`** (`FlockCommutes.lean`; its commutation is there):

1. **`flockCost_flockProveH : Cost.FlockCost flockProveH flockBlocks flockBytes`** (`ProverCost.lean`'s writer
   calculus `WC`): at `log_n` and a Keccak variant of skip `k`,
   * `flockBlocks`: the run of the `log_n − k − 7` sampled coordinates (`drawBlocks`: one each on the main line,
     one at π1-rec3, the squares of one challenge), the skip's `z`, one challenge per zerocheck round
     (`7 + (log_n − k − 7)` rounds), `α`, the lincheck's `11`, the ring map's `6`;
   * `flockBytes`: the `2^k` coset values, two scalars per zerocheck round, `v_a`, `v_b`, two per lincheck round,
     the `64` slices (always sent; `24` bytes a scalar).

   At the reference (`log_n = 32`, skip `3`): `70` blocks on the main line, `49` at π1-rec3, `3696` bytes
   (`flockBlocks_main_reference`, `flockBlocks_rec3_reference`, `flockBytes_reference`).
2. **The probability layer's hypotheses** (`ProbHyp.lean`) at every deployment of the reference shape
   (`keccakRefShape`) with a program IV of at most `2^16` bytes:
   * **`Prob.proverCost_flockProveH : ProverCost flockProveH D (2 ^ 47)`** (`cost_uniProverWith`,
     `proverBlocks_reference`);
   * **`Prob.proverStreamSize_flockProveH : ProverStreamSize flockProveH D (2 ^ 14)`** (`costP_uniProverWith` read on
     the support, `CostP.mem_support`; `proverStream_reference`: `5656 + 3696` bytes).
3. **The total** (`totalCostK_le`): the setup (one tree of `2^23` words), the prover's `2^47`, the verifier on `2^14`
   bytes: at most `2^48` block calls (as the original `Prob.lean`'s `totalCost_le`).

Decision (recorded): the cost lemmas carry only what the budget needs: the runs' lengths (the rounds' count) and the
slices' count (`2^17 / 2^11 = 64`); the coset values are bounded by `24 · 2^k` bytes and one challenge (`z`) also
without a skip (`k = 0` sends and draws nothing).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open UniStatement

set_option autoImplicit false

namespace UniKeccakComplete.FlockP

open UniComplete

open UniStatement.Flock

/-! ## Flock's prover's cost -/

section Cost

open UniKeccakComplete.Cost (WC wc_seq wc_mono wc_pure wc_sampleW wc_sendScalar wc_sendScalars wc_samplesW)

/-- `count` challenges, and as many. -/
theorem wc_samplesW_len : ∀ count : ℕ,
    WC (samplesW callKeccak256 count) count 0 fun l _ ↦ l.length = count
  | 0 => wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ by subst hb; rfl
  | count + 1 => by
    unfold samplesW
    refine wc_seq wc_sampleW (fun _ _ _ ↦ ?_) (by omega) (Nat.zero_le _)
    refine wc_seq (wc_samplesW_len count) (fun _ _ hl ↦ ?_) (by omega) (by omega)
    exact wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ by rw [hb, List.length_cons, hl]

/-- `squares c n` has `n` terms. -/
theorem length_squares : ∀ (c : E) (n : ℕ), (squares c n).length = n
  | _, 0 => rfl
  | c, n + 1 => by rw [squares, List.length_cons, length_squares (c * c) n]

/-- The blocks of a run of `count` challenges beyond its bytes: one each drawn one by one (`main`), one for the
first and its squares (the others). -/
def drawBlocks : FsShape → ℕ → ℕ
  | .main, count => count
  | .rec1, _ | .rec2, _ | .rec3, _ | .rec4, _ => 1

/-- **A run of draws**: `drawBlocks` challenges, `count` terms. -/
theorem wc_drawW (fs : FsShape) (count : ℕ) :
    WC (drawW callKeccak256 fs count) (drawBlocks fs count) 0 fun l _ ↦ l.length = count := by
  cases fs
  · exact wc_samplesW_len count
  all_goals
    dsimp only [drawW, drawBlocks]
    split
    · next h => exact wc_mono (wc_pure _) (Nat.zero_le _) le_rfl fun b _ hb ↦ by rw [hb, List.length_nil, h]
    · refine wc_seq wc_sampleW (fun c _ _ ↦ ?_) le_rfl le_rfl
      exact wc_mono (wc_pure _) le_rfl le_rfl fun b _ hb ↦ by rw [hb, length_squares]

/-- **The zerocheck's rounds**: one challenge and two scalars each. -/
theorem wc_zcRounds : ∀ (r : List E) (claim : E) (a b c : Array E),
    WC (zcRounds callKeccak256 r claim a b c) r.length (48 * r.length) fun _ _ ↦ True
  | [], _, _, _, _ => wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial
  | _ :: rest, _, _, _, _ => by
    simp only [zcRounds, List.length_cons]
    refine wc_seq (wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
    refine wc_seq (wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
    refine wc_seq wc_sampleW (fun _ _ _ ↦ ?_) (by omega) (Nat.zero_le _)
    refine wc_seq (wc_zcRounds rest _ _ _ _) (fun _ _ _ ↦ ?_) (by omega) (by omega)
    exact wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial

theorem length_cosetValues (k : ℕ) (r : List E) (wit : Wit) : (cosetValues k r wit).length = 2 ^ k := by
  simp [cosetValues]

/-- **The skip**: the `2^k` coset values and `z` (nothing without a skip). -/
theorem wc_skipW (k : ℕ) (r : List E) (wit : Wit) :
    WC (skipW callKeccak256 k r wit) 1 (24 * 2 ^ k) fun _ _ ↦ True := by
  unfold skipW
  split
  · refine wc_seq (wc_sendScalars _) (fun _ _ _ ↦ ?_) (Nat.zero_le _)
      (le_of_eq (by rw [length_cosetValues]))
    refine wc_seq wc_sampleW (fun _ _ _ ↦ ?_) (by omega) (Nat.zero_le _)
    exact wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial
  · exact wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial

theorem length_fixedChallenges : fixedChallenges.length = nFixed := rfl

/-- **The zerocheck**: the run of sampled coordinates, the skip, `7 + (log_n − k − 7)` rounds, `v_a`, `v_b`. -/
theorem wc_zerocheckW (logN k : ℕ) (fs : FsShape) (wit : Wit) :
    WC (zerocheckW callKeccak256 logN k fs wit)
      (drawBlocks fs (logN - k - nFixed) + 1 + (nFixed + (logN - k - nFixed)))
      (24 * 2 ^ k + 48 * (nFixed + (logN - k - nFixed)) + 48) fun _ _ ↦ True := by
  unfold zerocheckW
  refine wc_seq (wc_drawW _ _) (fun sampled _ hs ↦ ?_) (by omega) (Nat.zero_le _)
  have hr : (fixedChallenges ++ sampled).length = nFixed + (logN - k - nFixed) := by
    rw [List.length_append, hs, length_fixedChallenges]
  refine wc_seq (wc_skipW _ _ _) (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_zcRounds _ _ _ _ _) (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
  refine wc_seq (wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
  exact wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial

theorem size_foldHigh (v : Array E) (x : E) : (foldHigh v x).size = v.size / 2 := by
  simp [foldHigh]

/-- **The lincheck's rounds**: one challenge and two scalars each; the witness halved `n` times. -/
theorem wc_lcRounds : ∀ (n : ℕ) (claim : E) (w z : Array E),
    WC (lcRounds callKeccak256 n claim w z) n (48 * n) fun out _ ↦ out.z.size = z.size / 2 ^ n
  | 0, _, _, _ => wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ by subst hb; simp
  | n + 1, _, _, z => by
    simp only [lcRounds]
    refine wc_seq (wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
    refine wc_seq (wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
    refine wc_seq wc_sampleW (fun x _ _ ↦ ?_) (by omega) (Nat.zero_le _)
    refine wc_seq (wc_lcRounds n _ _ _) (fun out _ hout ↦ ?_) (by omega) (by omega)
    refine wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ ?_
    subst hb
    dsimp only
    rw [hout, size_foldHigh, Nat.div_div_eq_div_mul, ← pow_succ']

theorem size_lcWitnessOf (k : ℕ) (q : Array K) (zc : Option E × List E × E × E × E) :
    (lcWitnessOf k q zc).size = 2 ^ keccakR1csLogSize := by
  simp [lcWitnessOf, lincheckWitness]

/-- `2^17 / 2^11 = 64` slices. -/
theorem slices_count : 2 ^ keccakR1csLogSize / 2 ^ UniKeccak.lincheckRoundsK = kBits := by decide +kernel

/-- **The front**: the zerocheck, `α`, the lincheck's `11` rounds, the `64` slices. -/
theorem wc_frontW (logN : ℕ) (v : UniKeccak.KeccakVariant) (q : Array K) :
    WC (frontW callKeccak256 logN v q)
      (drawBlocks v.fs (logN - v.skip - nFixed) + 1 + (nFixed + (logN - v.skip - nFixed)) + 1 +
        UniKeccak.lincheckRoundsK)
      (24 * 2 ^ v.skip + 48 * (nFixed + (logN - v.skip - nFixed)) + 48 + 48 * UniKeccak.lincheckRoundsK +
        24 * kBits)
      fun _ _ ↦ True := by
  unfold frontW
  refine wc_seq (wc_zerocheckW _ _ _ _) (fun zc _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun alpha _ _ ↦ ?_) (by omega) (Nat.zero_le _)
  refine wc_seq (wc_lcRounds _ _ _ _) (fun lc _ hlc ↦ ?_) (by omega) (by omega)
  have hz : lc.z.toList.length = kBits := by
    rw [Array.length_toList, hlc, size_lcWitnessOf, slices_count]
  refine wc_seq (wc_sendScalars _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by rw [hz]; omega)
  exact wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial

/-- **The ring map's `6` challenges.** -/
theorem wc_ringEndW (s : List E) : WC (ringEndW callKeccak256 s) ringMapShifts.length 0 fun _ _ ↦ True := by
  unfold ringEndW
  exact wc_seq (wc_samplesW _) (fun _ _ _ ↦ wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _)
    fun _ _ _ ↦ trivial) le_rfl le_rfl

end Cost

end UniKeccakComplete.FlockP

namespace UniKeccakComplete

open UniComplete

open UniStatement.Flock UniKeccak
open UniKeccakSound (keccakRefShape)

/-! ## Flock's honest prover's cost -/

/-- **Flock's blocks beyond its bytes**: the run of the `log_n − k − 7` sampled coordinates, the skip's `z`, the
zerocheck's `7 + (log_n − k − 7)` round challenges, `α`, the lincheck's `11`, the ring map's `6`. -/
def flockBlocks (logN : ℕ) (v : KeccakVariant) : ℕ :=
  FlockP.drawBlocks v.fs (logN - v.skip - nFixed) + 1 + (nFixed + (logN - v.skip - nFixed)) + 1 + lincheckRoundsK +
    ringMapShifts.length

/-- **Flock's bytes**: the `2^k` coset values, the zerocheck's rounds' two scalars, `v_a`, `v_b`, the lincheck's
rounds' two, the `64` slices; `24` bytes a scalar. -/
def flockBytes (logN : ℕ) (v : KeccakVariant) : ℕ :=
  24 * 2 ^ v.skip + 48 * (nFixed + (logN - v.skip - nFixed)) + 48 + 48 * lincheckRoundsK + 24 * kBits

/-- **Flock's honest prover's cost** (`ProverCost.lean`'s `FlockCost`): at most `flockBlocks` blocks beyond one per
byte it writes, at most `flockBytes` bytes, at both variants. -/
theorem flockCost_flockProveH : Cost.FlockCost flockProveH flockBlocks flockBytes := by
  intro logN v words
  show Cost.WC (FlockP.flockProve callKeccak256 logN v words) _ _ _
  unfold FlockP.flockProve flockBlocks flockBytes
  refine Cost.wc_seq (FlockP.wc_frontW _ _ _) (fun frs _ _ ↦ ?_) (by omega) (by omega)
  refine Cost.wc_seq (FlockP.wc_ringEndW _) (fun e _ _ ↦ ?_) (by omega) (Nat.zero_le _)
  exact Cost.wc_mono (Cost.wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial

theorem flockBlocks_main_reference : flockBlocks 32 keccakMain = 70 := by decide +kernel

theorem flockBlocks_rec3_reference : flockBlocks 32 keccakRec3 = 49 := by decide +kernel

theorem flockBytes_reference : flockBytes 32 keccakMain = 3696 := by decide +kernel

theorem flockBytes_rec3_reference : flockBytes 32 keccakRec3 = 3696 := by decide +kernel

/-! ## The probability layer's hypotheses on the main line's prover -/

namespace Prob

/-- **The honest prover with Flock's honest prover makes at most `2^47` block calls** at the reference shape (a
program IV of at most `2^16` bytes). -/
theorem proverCost_flockProveH (D : KDeployment) (hD : D.shape = keccakRefShape) (hIv : D.programIv.length ≤ 2 ^ 16) :
    ProverCost flockProveH D (2 ^ 47) := by
  intro input rows q hfit _
  have h := Cost.cost_uniProverWith flockProveH flockBlocks flockBytes flockCost_flockProveH D input rows q
  rw [hfit.1] at h
  exact h.mono (Cost.proverBlocks_reference D hD hIv flockBlocks flockBytes
    (by rw [flockBlocks_main_reference]; norm_num) (by rw [flockBytes_reference]; norm_num))

/-- **Every proof the honest prover can output has a stream of at most `2^14` bytes** at the reference shape (at
most `5656 + 3696`). -/
theorem proverStreamSize_flockProveH (D : KDeployment) (hD : D.shape = keccakRefShape) :
    ProverStreamSize flockProveH D (2 ^ 14) := by
  intro input rows q hfit _ π hπ
  have h := Cost.CostP.mem_support (Cost.costP_uniProverWith flockProveH flockBlocks flockBytes
    flockCost_flockProveH D input rows q) _ hπ π rfl
  rw [hfit.1, Cost.proverStream_reference D hD, flockBytes_reference] at h
  exact h.trans (by norm_num)

end Prob

/-! ## The total -/

/-- **The block count of the main line's run at the reference shape**: the setup (one tree, `5 · 2^18`), the
prover's `2^47`, the verifier on streams of `2^14` bytes: at most `2^48` (for a program IV of at most `2^16`
bytes). -/
theorem totalCostK_le (D : KDeployment) (hD : D.shape = keccakRefShape) (hiv : D.programIv.length ≤ 2 ^ 16) :
    Cost.setupCost D + (2 ^ 47 + Cost.verifierCost D keccakMain (2 ^ 14)) ≤ 2 ^ 48 := by
  have h3 := Cost.reference_stackVars.2.2.1
  have ho := Cost.openCost_le
  have hivc : (163 + D.programIv.length) / 136 ≤ 163 + 2 ^ 16 := (Nat.div_le_self _ _).trans (by omega)
  unfold Cost.setupCost Cost.verifierCost Cost.ivCost
  rw [Cost.walkCost_main, hD, h3, Cost.reference_sha3Height]
  norm_num
  omega

end UniKeccakComplete

/-! ## Axioms -/

/-- info: 'UniKeccakComplete.flockCost_flockProveH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.flockCost_flockProveH

/-- info: 'UniKeccakComplete.Prob.proverCost_flockProveH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Prob.proverCost_flockProveH

/-- info: 'UniKeccakComplete.Prob.proverStreamSize_flockProveH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Prob.proverStreamSize_flockProveH

/-- info: 'UniKeccakComplete.totalCostK_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.totalCostK_le
