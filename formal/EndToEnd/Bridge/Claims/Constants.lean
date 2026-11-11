-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import PcsQuotient.Reduction
import Compose.Reduce
import Compose.Claims
import Bridge.Opening
import Field.F192
import QuotientSecurity.DeployedBasis

/-!
# The statement's constants and its Cantor basis

`Compose.Reduce.reduce`'s constants as the statement computes them (`statementConsts`: the Cantor basis
`Domain.betaAt` and the rows' polynomial `statementTau`, the coefficients of `rowVanishing 24`), and the basis
checked by kernel evaluation (`decide +kernel`, no `native_decide`):

* `beta_lanes`: the statement's `28` basis words, the first `24` F0c's `betaWords` (about 4 s);
  so `betaAt_eq_deployedBasis`: `β_k` is `QuotientSecurity.deployedBasis`'s, `k < 24`, and
  **`isCantor_statementConsts`** follows from `deployedBasis`'s kernel-checked `S(β_{k+1}) = β_k`.

The constants were in `Reduce.lean` and the rows' polynomial's check (`rowVanishing_statementConsts`) here; they
are swapped so that the leanVM line (`Heap`, `UniSound`), which imports this module, does not import the
previous protocol's reduction (`Reduce.lean`).
-/

namespace Bridge

open LeanVM.Parameters PcsQuotient PcsQuotient.Domain QuotientSecurity

/-! ## The constants -/

/-- The statement's rows' polynomial at `2^22` rows, its `k`-th coefficient. -/
def statementTau (k : ℕ) : K := (rowVanishing 24).getD k 0

/-- **`reduce`'s constants as the statement computes them**: its Cantor basis and its rows'
polynomial at `2^22` rows (`m = 24` cell variables). -/
def statementConsts : Compose.Reduce.Consts :=
  ⟨betaAt, statementTau⟩

@[simp] theorem statementConsts_beta : statementConsts.beta = betaAt := rfl

@[simp] theorem statementConsts_tau : statementConsts.tau = statementTau := rfl

/-! ## Words -/

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

/-- **The statement's basis is a Cantor basis** (`Compose.IsCantor`, what `Compose`'s claims theorems
ask of `beta()`). -/
theorem isCantor_statementConsts : Compose.IsCantor statementConsts.beta := by
  refine ⟨?_, fun k hk ↦ ?_⟩
  · rw [statementConsts_beta, betaAt_eq_deployedBasis 0 (by norm_num)]
    exact deployedBasis.zero
  · rw [statementConsts_beta, betaAt_eq_deployedBasis (k + 1) hk,
      betaAt_eq_deployedBasis k (by omega)]
    exact deployedBasis.succ k hk

end Bridge

/-- info: 'Bridge.isCantor_statementConsts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.isCantor_statementConsts
