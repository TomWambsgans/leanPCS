-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0), `lean_vm/LeanVM/Protocol/Compile/Rom/Complete.lean`: the honest
-- prover fails only at a proof of work (`proveFromM_eq_some_none`, here for the script runner
-- `runFromWithHash`), and a failed search puts the potential at `1` (the end of `one_le_powPot`,
-- here `one_le_powPot_of_findNonceM`). Uses, from the same commit: the proof-of-work potential
-- `powPot` and its step (`powPot_stepF`, `powPot_append_inl`, `Compile/Rom/Complete.lean`), the logged
-- random oracle and its potential engine (`ToVCVio/Rom/LoggedOracle.lean`,
-- `prEvent_run_loggedRO_le_of_freshStepBound`, `prEvent_run_randomOracle_eq_loggedRO`), the bridge
-- from a logged run to the run at the log's answers (`simulateQ_look_of_mem_support`,
-- `Compile/Rom/Bridge.lean`; `simulateQ_id_of_look`, `Compile/Rom/Prover.lean`), and WHIR's proofs
-- of work (`movesOK_verifyStackedOpening`, `EndToEnd/Sound/Moves.lean`).
import E2ECompleteness.Duplex
import E2ECompleteness.ProverOpening
import Compose.Claims
import Compose.Rpm
import LeanVM.Protocol.Compile.Rom.Bridge
import LeanVM.Protocol.EndToEnd.Sound.Moves
import LeanVM.Protocol.LeanVMRpm
import LeanVM.Protocol.Rpm.Duplex
import LeanVM.Protocol.WithHashBridge
import LeanVM.Prover.Refine
import LeanVM.Prover.Whir
import PcsQuotient.Security

/-!
# The opening's grinding fails rarely

The prover run at a state (`runAt`), a run that returns `none` (`runFromWithHash_eq_some_none`,
`proveOpeningWithH_eq_some_none`), the prover's sponge (`proverSp_openingSpongeWithH`), the query bound from the
cost (`isTotalQueryBound_of_queryCostAtMost`), and the grinding bound (`grinding_le`).

Pruned to what the leanVM line uses (`formal/Uni*`, `formal/Rec*`); the previous membership protocol's declarations
that were here are in the git history.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom
open LeanVM.Prover (Tree findNonceM powStepM Script)
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript
open scoped ENNReal

set_option autoImplicit false

namespace E2ECompleteness

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## Runs at a log and at a hash function and a permutation -/

/-- **The pure run** of a two-call computation at a hash function `H` and a permutation `F`. -/
abbrev runAt {α : Type} (H : Bytes → Digest) (F : KeccakState → KeccakState)
    (oa : OracleComp KeccakCalls α) : α :=
  simulateQ (totalImpl H F) oa

section Failure

variable {H : Bytes → Option Digest} {F : KeccakState → Option KeccakState}

/-- **The script runner fails only at a proof of work** (mumbai's `proveFromM_eq_some_none`, for
`runFromWithHash`): if it fails, with the queries answered in `Option`, along a program whose proofs
of work all have `b` bits, then a `b`-bit search fails at a sponge the honest prover keeps. -/
theorem runFromWithHash_eq_some_none (b fuel : ℕ) {α β : Type} (P : Prog α) :
    ∀ (S : Option (Script β)) (sp : Sponge) (cs : List Tree),
      EndToEnd.Sound.MovesOK (· = b) True P → ProverSp sp →
      LeanVM.Prover.runFromWithHash H F fuel P S sp cs = some none →
      ∃ sp', ProverSp sp' ∧ findNonceM F b sp' fuel = some none := by
  induction P with
  | ret a => intro S sp cs _ _ hp; cases hp
  | fail => intro S sp cs _ _ hp; cases hp
  | read k ih =>
    intro S sp cs hm hsp hp
    simp only [LeanVM.Prover.runFromWithHash] at hp
    obtain ⟨sp', hsp', hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
    rcases r with _ | _
    · exact ih _ _ _ _ (hm _) (proverSp_absorb hsp hsp') hr
    · cases hp
  | sample k ih =>
    intro S sp cs hm hsp hp
    simp only [LeanVM.Prover.runFromWithHash] at hp
    obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨u, -, rfl⟩ := (squeeze_option _ _ _).mp hr
    exact ih _ _ _ _ (hm _) ⟨by simp, by simp⟩ hp
  | grind bits k ih =>
    intro S sp cs hm hsp hp
    have hb : bits = b := hm.1
    simp only [LeanVM.Prover.runFromWithHash] at hp
    obtain ⟨o, ho, hp⟩ := Option.bind_eq_some_iff.mp hp
    rcases o with _ | n
    · subst hb
      exact ⟨sp, hsp, ho⟩
    · obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
      obtain ⟨t, ht, hp⟩ := Option.bind_eq_some_iff.mp hp
      have hsp' : ProverSp r.2 := by
        simp only [powStepM, bind, Option.bind_eq_some_iff] at hr
        obtain ⟨sp', -, hs⟩ := hr
        obtain ⟨u, -, rfl⟩ := (squeeze_option _ _ _).mp hs
        exact ⟨by simp, by simp⟩
      rcases t with _ | _
      · exact ih _ _ _ hm.2 hsp' ht
      · cases hp
  | commit ht w k ih =>
    intro S sp cs hm hsp hp
    simp only [LeanVM.Prover.runFromWithHash] at hp
    obtain ⟨tree, -, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨sp0, h0, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨sp1, h1, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
    rcases r with _ | _
    · exact ih _ _ _ hm.2 (proverSp_absorb (proverSp_absorb hsp h0) h1) hr
    · cases hp
  | query i ps k ih =>
    intro S sp cs hm hsp hp
    simp only [LeanVM.Prover.runFromWithHash] at hp
    split at hp
    · cases hp
    · obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
      rcases r with _ | _
      · exact ih _ _ _ _ (hm _) hsp hr
      · cases hp

/-- The opening's sponge waits for nothing. -/
theorem proverSp_openingSpongeWithH {L : PcsQuotient.Layout} {claims : List PcsQuotient.Claim}
    {sp : Sponge} (h : openingSpongeWithH H F L claims = some sp) : ProverSp sp := by
  simp only [openingSpongeWithH] at h
  obtain ⟨iv, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨s, -, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact ⟨by simp, by simp⟩

/-- **An opening fails only at a `17`-bit proof of work.** -/
theorem proveOpeningWithH_eq_some_none {fuel : ℕ} {L : PcsQuotient.Layout} {tree : Tree}
    {stack : Array K} {claims : List PcsQuotient.Claim}
    (h : proveOpeningWithH H F fuel L tree stack claims = some none) :
    ∃ sp', ProverSp sp' ∧ findNonceM F Whir.queryGrindingBits sp' fuel = some none := by
  simp only [proveOpeningWithH] at h
  obtain ⟨sp₀, h₀, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨sp₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨sp₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
  rcases r with _ | _
  · exact runFromWithHash_eq_some_none _ fuel _ _ _ _
      (EndToEnd.Sound.movesOK_verifyStackedOpening _ _ _)
      (proverSp_absorb (proverSp_absorb (proverSp_openingSpongeWithH h₀) h₁) h₂) hr
  · cases h

end Failure

/-! ## The deployed instance -/

/-- **At most `N` blocks is at most `N` queries**: every query costs at least one block. -/
theorem isTotalQueryBound_of_queryCostAtMost {α : Type} {oa : OracleComp KeccakCalls α} {N : ℕ}
    (h : Common.QueryCostAtMost oa hashBlocks N) : IsTotalQueryBound oa N := by
  induction oa using OracleComp.inductionOn generalizing N with
  | pure x => trivial
  | query_bind t mx ih =>
    obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).1 h
    have ht' : hashBlocks t ≤ N := ht
    have h1 : 1 ≤ hashBlocks t := by rcases t with x | s <;> simp [hashBlocks]
    exact isTotalQueryBound_query_bind_iff.2 ⟨by omega, fun u ↦ (ih u (hk u)).mono (by omega)⟩

/-- **The numbers**: `2^48` queries, each completing a `17`-bit proof of work whose `2^25` nonces all
failed with probability `(1 - 2^-17)^(2^25) ≤ (3/8)^(2^8)` (mumbai's
`one_sub_pow_le_three_eighths`): below `2^-304`. -/
theorem grinding_le : ((2 ^ 48 : ℕ) : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ nonceFuel ≤
    (2 : ℝ≥0∞)⁻¹ ^ 304 := by
  have hb : Whir.queryGrindingBits = 17 := rfl
  have hf : nonceFuel = 2 ^ 17 * 2 ^ 8 := by norm_num [nonceFuel]
  have hy : (0 : ℝ) ≤ 1 - (1 / 2 : ℝ) ^ 17 := by norm_num
  have h38 : (1 - (1 / 2 : ℝ) ^ 17) ^ (2 ^ 17) ≤ 3 / 8 := one_sub_pow_le_three_eighths 17
  have hreal : (2 : ℝ) ^ 48 * ((1 - (1 / 2 : ℝ) ^ 17) ^ (2 ^ 17)) ^ (2 ^ 8) ≤ (1 / 2) ^ 304 := by
    calc (2 : ℝ) ^ 48 * ((1 - (1 / 2 : ℝ) ^ 17) ^ (2 ^ 17)) ^ (2 ^ 8)
        ≤ (2 : ℝ) ^ 48 * (3 / 8) ^ (2 ^ 8) := by gcongr
      _ ≤ ((1 / 2) ^ 152) ^ 2 := by norm_num
      _ = (1 / 2) ^ 304 := by rw [← pow_mul]
  rw [hb, hf, pow_mul, missProb_eq_ofReal, ← ENNReal.ofReal_pow hy,
    ← ENNReal.ofReal_pow (pow_nonneg hy _)]
  calc ((2 ^ 48 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (((1 - (1 / 2 : ℝ) ^ 17) ^ 2 ^ 17) ^ 2 ^ 8)
      = ENNReal.ofReal ((2 : ℝ) ^ 48 * ((1 - (1 / 2 : ℝ) ^ 17) ^ 2 ^ 17) ^ 2 ^ 8) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        norm_num
    _ ≤ ENNReal.ofReal ((1 / 2) ^ 304) := ENNReal.ofReal_le_ofReal hreal
    _ = (2 : ℝ≥0∞)⁻¹ ^ 304 := by
        rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num

end E2ECompleteness
