-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `E2ECompleteness/End.lean` (the previous protocol's staged experiment) to the PCS claims'
-- four challenges. Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0): the two calls and their random-permutation model, `rpmError`, the duplex
-- discipline `DuplexVm` and the block cost `hashBlocks`.
import E2ECompleteness.PcsChain
import E2ECompleteness.Transfer
import E2ECompleteness.Regular
import E2ECompleteness.End
import PcsQuotient.Security

/-!
# `PcsQuotient.Completeness`, from the staged two-call experiment (the PCS claims)

**`completeness_of_staged4`**: if the completeness experiment is, in distribution, the coins then a
two-call computation of the chain's shape (`Staged4`, `Staged4.Holds`), with degenerate quadruples
(`bad`) of density at most `εbad`, then `PcsQuotient.Completeness (εbad + εpow + rpmError N)`:

* `rpmError N = N² / 2^508`: the random permutation is two random oracles to an honest computation of
  at most `N` block calls following the duplex discipline (`rpm_le_rom`);
* `εbad`: the chain's challenges `(α, β, t, ρ)` are degenerate with probability at most their density
  (`prEvent_staged4_le`: every challenge query is fresh by its length);
* `εpow`: the honest proof is rejected at non-degenerate challenges (the proofs of work).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open LeanVM.Protocol.KeccakHash
open E2ECompleteness (ro HashOK)
open scoped ENNReal

set_option autoImplicit false

namespace E2ECompleteness.Pcs

/-- **The experiment's stages**: the coins, and for each draw the honest run as a two-call computation
of the chain's shape, with the degenerate quadruples of the draw. -/
structure Staged4 where
  Coins : Type
  α : Type
  β : Type
  γ : Type
  coins : ProbComp Coins
  bad : Coins → Finset (E × E × E × E)
  A : Coins → OracleComp KeccakCalls (α × Digest × PcsQuotient.CommitmentScalars)
  B : Coins → α → Digest → Digest → Digest → OracleComp KeccakCalls (β × Scalars9)
  C : Coins → α → β → Digest → Digest → Digest → Digest →
    OracleComp KeccakCalls (γ × Digest × (Vector E 4 × E))
  D : Coins → α → β → γ → Digest → Digest → Digest → Digest → Digest → OracleComp KeccakCalls Bool

/-- The two-call run of a draw. -/
def Staged4.run (S : Staged4) (c : S.Coins) : OracleComp KeccakCalls (Bool × (E × E × E × E)) :=
  staged4 PcsQuotient.Transcript.challengeOf (S.A c) (S.B c) (S.C c) (S.D c)

/-- **The code-level bridge** of the Statement's experiment for `(stmt, w)`. -/
structure Staged4.Holds (S : Staged4) (stmt : PcsQuotient.Statement) (w : PcsQuotient.Secret)
    (N : ℕ) (εbad εpow : ℝ≥0∞) : Prop where
  experiment : PcsQuotient.completenessExperiment stmt w =ᵈ
    (S.coins >>= fun c ↦ (fun z ↦ z.1) <$>
      (simulateQ keccakCallsOverRandomPermutation (S.run c)).run' [])
  duplex : ∀ c, DuplexVm (S.run c) []
  cost : ∀ c, Common.QueryCostAtMost (S.run c) hashBlocks N
  hashA : ∀ c, HashOK Good4 (S.A c)
  hashB : ∀ c a s₁ s₂ s₃, HashOK Good4 (S.B c a s₁ s₂ s₃)
  hashC : ∀ c a b s₁ s₂ s₃ s₄, HashOK GoodC (S.C c a b s₁ s₂ s₃ s₄)
  density : ∀ c, ((S.bad c).card : ℝ≥0∞) / 2 ^ 768 ≤ εbad
  rejectGood : ∀ c,
    Pr{let z ← (simulateQ ro (S.run c)).run' ∅}[z.1 = false ∧ z.2 ∉ S.bad c] ≤ εpow

theorem prEvent_run4_false_le (S : Staged4) {stmt : PcsQuotient.Statement} {w : PcsQuotient.Secret}
    {N : ℕ} {εbad εpow : ℝ≥0∞} (h : S.Holds stmt w N εbad εpow) (c : S.Coins) :
    Pr{let z ← (simulateQ keccakCallsOverRandomPermutation (S.run c)).run' []}[z.1 = false] ≤
      (εbad + εpow) + rpmError N := by
  refine E2ECompleteness.rpm_le_rom (S.run c) (h.duplex c) (h.cost c) (fun z ↦ z.1 = false) ?_
  refine (prEvent_le_prEvent_add_prEvent_and_not _ _
    (fun z : Bool × (E × E × E × E) ↦ z.2 ∈ S.bad c)).trans ?_
  refine add_le_add ?_ (h.rejectGood c)
  have hc : Pr{let z ← (simulateQ ro (S.run c)).run' ∅}[z.2 ∈ S.bad c] =
      Pr{let z ← (simulateQ ro (S.run c)).run ∅}[z.1.2 ∈ S.bad c] := by
    rw [StateT.run'_eq, prEvent_map]
  rw [hc]
  exact (prEvent_staged4_le _ E2ECompleteness.challengeOf_regular _ _ _ _ _ (h.hashA c) (h.hashB c)
    (h.hashC c) ∅ fun m hm ↦ absurd rfl hm).trans (h.density c)

/-- **Completeness in the random-permutation model, from the staged experiment.** -/
theorem completeness_of_staged4 {N : ℕ} {εbad εpow : ℝ≥0∞}
    (hS : ∀ stmt w, PcsQuotient.Relation stmt w → ∃ S : Staged4, S.Holds stmt w N εbad εpow) :
    PcsQuotient.Completeness (εbad + εpow + rpmError N) := by
  intro stmt w hrel
  obtain ⟨S, h⟩ := hS stmt w hrel
  rw [h.experiment.prEvent_eq]
  refine prEvent_bind_le_of_forall_le _ _ _ fun c ↦ ?_
  rw [prEvent_map]
  exact prEvent_run4_false_le S h c

/-! ## The numbers -/

/-- **The deployed bound**: degenerate challenges `(19 · 2^24 + 31) / 2^192`, the proofs of work `2^-304`,
the transfer at `2^48` block calls. -/
noncomputable def deltaPcs : ℝ≥0∞ :=
  (19 * 2 ^ 24 + 31 : ℝ≥0∞) / 2 ^ 192 + (2 : ℝ≥0∞)⁻¹ ^ 304 + rpmError (2 ^ 48)

theorem deltaPcs_lt : deltaPcs < (2 : ℝ≥0∞)⁻¹ ^ 163 := by
  have h1 : (19 * 2 ^ 24 + 31 : ℝ≥0∞) / 2 ^ 192 ≤ 5 * (2 : ℝ≥0∞)⁻¹ ^ 166 := by
    calc (19 * 2 ^ 24 + 31 : ℝ≥0∞) / 2 ^ 192 ≤ (5 * 2 ^ 26) / 2 ^ 192 := by
          gcongr; norm_num
      _ = 5 * (2 ^ 26 * (2 : ℝ≥0∞)⁻¹ ^ (166 + 26)) := by
          rw [← ENNReal.inv_pow, mul_div_assoc, div_eq_mul_inv]
      _ = 5 * (2 : ℝ≥0∞)⁻¹ ^ 166 := by rw [E2ECompleteness.two_pow_mul_inv_pow]
  have h2 : (2 : ℝ≥0∞)⁻¹ ^ 304 ≤ (2 : ℝ≥0∞)⁻¹ ^ 166 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
  have h3 : rpmError (2 ^ 48) ≤ (2 : ℝ≥0∞)⁻¹ ^ 166 := by
    calc rpmError (2 ^ 48) = 2 ^ (48 * 2) * (2 : ℝ≥0∞)⁻¹ ^ (412 + 48 * 2) := by
          rw [rpmError, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ENNReal.div_eq_inv_mul,
            ← ENNReal.inv_pow, mul_comm]
      _ = (2 : ℝ≥0∞)⁻¹ ^ 412 := E2ECompleteness.two_pow_mul_inv_pow _ 412
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 166 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
  have hsum : deltaPcs ≤ 7 * (2 : ℝ≥0∞)⁻¹ ^ 166 := by
    unfold deltaPcs
    calc _ ≤ 5 * (2 : ℝ≥0∞)⁻¹ ^ 166 + (2 : ℝ≥0∞)⁻¹ ^ 166 + (2 : ℝ≥0∞)⁻¹ ^ 166 :=
          add_le_add (add_le_add h1 h2) h3
      _ = 7 * (2 : ℝ≥0∞)⁻¹ ^ 166 := by ring
  refine lt_of_le_of_lt hsum ?_
  calc 7 * (2 : ℝ≥0∞)⁻¹ ^ 166 < 2 ^ 3 * (2 : ℝ≥0∞)⁻¹ ^ (163 + 3) := by
        rw [mul_comm 7, mul_comm ((2 : ℝ≥0∞) ^ 3)]
        exact ENNReal.mul_lt_mul_right (by simp) (by simp) (by norm_num)
    _ = (2 : ℝ≥0∞)⁻¹ ^ 163 := E2ECompleteness.two_pow_mul_inv_pow 3 163

end E2ECompleteness.Pcs
