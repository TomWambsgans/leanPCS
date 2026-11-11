-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here.
import ZK.PcsBadPhase
import ZK.PcsEnd

/-!
# The Fiat–Shamir hypothesis, proved

**`fiatShamirUniform_closed`**: `FiatShamirUniform εfs₀`, `εfs₀ = 58 · δq L ≤ 2^-163` (`εfs₀_le`): the challenge
phase run for real is within its tracked queries' cost of the ideal run (`close`, on every observation with values
in `[0, 1]`), whose challenges and revealed scalars are independent and uniform (`ideal_joint`), and that cost is at
most `εfs₀` (`phase_bound`).

**`zeroKnowledge_pcs_closed`**: zero knowledge from the PCS hypothesis and `RevealedUniform` alone.
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open FProg

/-- The Fiat–Shamir term: `58` tracked queries, each at most `δq L`. -/
noncomputable def εfs₀ : ℝ≥0∞ := 58 * δq phaseL

theorem εfs₀_le : εfs₀ ≤ ((2 : ℝ≥0∞) ^ 163)⁻¹ := by
  have hL : (phaseL : ℝ≥0∞) ≤ 2 ^ 22 := by unfold phaseL; norm_num
  calc εfs₀ = 58 * (phaseL * pmax + phaseL * nInv) := rfl
    _ ≤ 58 * (2 ^ 22 * pmax + 2 ^ 22 * pmax) := by gcongr; exact nInv_le_pmax
    _ ≤ 2 ^ 29 * pmax := by
        rw [← two_mul, ← mul_assoc, ← mul_assoc]
        gcongr
        norm_num
    _ = ((2 : ℝ≥0∞) ^ 163)⁻¹ := by
        rw [pmax_eq, show (2 : ℝ≥0∞) ^ 192 = 2 ^ 29 * 2 ^ 163 by rw [← pow_add],
          ENNReal.mul_inv (by simp) (by simp), ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

/-- **The simulator's Fiat–Shamir challenges and revealed scalars are within `εfs₀` of uniform**, on every
observation with values in `[0, 1]`. -/
theorem fiatShamirUniform_closed : FiatShamirUniform εfs₀ := by
  intro A a₀ stmt h hh
  have hrun : ∀ X : StateT (Edges × A) ProbComp (Challenges × PhaseOut),
      ∑' x, Pr{let y ← X.run' ([], a₀)}[y = x] * h x.1 (answersOf x.2) =
        ∑' o, Pr{let y ← X.run ([], a₀)}[y = o] * h o.1.1 (answersOf o.1.2) := fun X ↦ by
    rw [show X.run' ([], a₀) = Prod.fst <$> X.run ([], a₀) from rfl, tsum_map]
  rw [hrun, ← interpR_phaseF]
  refine ((close (phaseF (A := A) (membership logRows) stmt) ([], a₀)) (fun o ↦ h o.1.1 (answersOf o.1.2))
    fun o ↦ hh _ _).trans ?_
  rw [ideal_joint]
  exact add_le_add le_rfl (phase_bound stmt ([], a₀) rfl)

/-- **Zero knowledge of the membership proof, assuming a zero-knowledge PCS**, with the Fiat–Shamir term proved:
for every PCS simulator `sim` within `εpcs` (`PcsZeroKnowledge`), if the revealed scalars are within `δr` of uniform
at all but `εr` of the challenges (`RevealedUniform`), the simulator `zkSimulator sim` is within
`εpcs Q + εr + δr + εfs₀` of the honest prover, `εfs₀ ≤ 2^-163` (`εfs₀_le`). -/
theorem zeroKnowledge_pcs_closed (sim : PcsSimulator) (εpcs : ℕ → ℝ≥0∞) (εr δr : ℝ≥0∞)
    (hpcs : PcsZeroKnowledge sim εpcs) (hrev : RevealedUniform εr δr) :
    ZeroKnowledgeWith sim.s₀ (zkSimulator sim) sim.oracle (fun Q ↦ εpcs Q + εr + δr + εfs₀) :=
  zeroKnowledge_pcs sim εpcs εr δr εfs₀ hpcs hrev fiatShamirUniform_closed

end PcsQuotient.EndToEnd
