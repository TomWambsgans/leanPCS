-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `formal/Compose/Compose/Openings.lean` and `formal/Compose/Compose/ComposedKC.lean` of
-- this repository (the verifier, the extractor, the doomed openings, the composition) to the four
-- commitments of the EIP's PCS claims; the claims (`Compose.witnessClaim`, `wiringClaim`,
-- `reductionCheck`, `quotientClaims`, `accepts_iff`) are reused as they are.
import ComposePcs.TwoOracle4

/-!
# The four-root reduction composed with the openings

The verifier of the EIP's PCS claims runs the reduction's chain on the proof's four commitments and
five values, checks what the reduction checks itself (`Compose.reductionCheck`: the product it
inverts is not zero), and hands its claims to the openings (six one-point PCS claims: on `W`, on the
circuit's wiring table, two on `H`, one on `Q`, one on `G`). Here the openings are **any**
computation `post` after the chain, returning any verdict `b : β`, and `ok : β → Prop` says when it
accepts (six booleans all true, say). **The verifier accepts** (`Accepted4`) when its own check holds
and `ok` does.

**The extractor** (`extractor4`) returns the candidates of the witness table's root read off the
transcript; knowledge soundness is broken (`Breaks4`) when the verifier accepts while no candidate's
cells satisfy the relation.

**The openings' guarantees**, each an event of the same experiment, each on an accepted run:

* `WitnessDoomed4`: no candidate of `W`'s root satisfies F1's witness claim;
* `WiringDoomed4`: F1's wiring claim fails;
* `QuotientDoomed4`: no triple of candidates of `H`'s, `Q`'s and `G`'s roots, assembled by `asm`,
  satisfies F1's two quotient claims (what the openings of the three parts, with the parts' values,
  must give together).

`breaks4_imp`: a broken run has a doomed opening, or wins `ListChain4.lean`'s list game.
**`knowledgeSoundness_composed4`** (the hash a random oracle `bytes → 32 bytes`) and
**`knowledgeSoundness_composed_kc4`** (mumbai's two-oracle model): the probability that the verifier
accepts while the extracted list holds no witness of the statement is at most the three doomed
events' bounds plus `(Q + 6 + QV) (listFactor4 · roundError + 7 (Q + 6 + QV) / 2^256)`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace ComposePcs

open Compose QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {O β : Type} (ok : β → Prop)
variable {P : Params F} {B : P.Bounds} (W : Wire P B) {MH MQ MG : Type} (K : Commits4 B MH MQ MG)

/-- **The verifier accepts** a run: its own check holds and the openings accept. -/
def Accepted4 (z : Run4 F O β × Transcript) : Prop :=
  Compose.reductionCheck P z.1.chals.α z.1.chals.β z.1.chals.t z.1.proof.v.1 z.1.proof.v.2 ∧
    ok z.1.out

/-- **The extractor**: the candidates of the witness table's root, read off the transcript. It is
as computable as the list commitment's `cands`. -/
def extractor4 (z : Run4 F O β × Transcript) : List B.Msg₁ :=
  K.CW.cands (histOfTr z.2) (tableOfTr z.2) z.1.proof.rW

/-- **Knowledge soundness is broken**: the verifier accepts while no extracted candidate's cells
satisfy the relation for the statement the proof's bytes stand for. -/
def Breaks4 (z : Run4 F O β × Transcript) : Prop :=
  Accepted4 (P := P) ok z ∧ ∀ g ∈ extractor4 K z, ¬ P.Sat (W.decode z.1.proof.stmt) (P.cells g.1)

/-- The verifier accepts while every candidate of `W`'s root violates F1's witness claim. -/
def WitnessDoomed4 (z : Run4 F O β × Transcript) : Prop :=
  Accepted4 (P := P) ok z ∧ ∀ g ∈ extractor4 K z,
    ¬ Compose.witnessClaim g.1 z.1.chals.t z.1.chals.ρ z.1.proof.v.1

/-- The verifier accepts while F1's wiring claim is false. -/
def WiringDoomed4 (z : Run4 F O β × Transcript) : Prop :=
  Accepted4 (P := P) ok z ∧ ¬ Compose.wiringClaim P z.1.chals.t z.1.proof.v.2

/-- The verifier accepts while no triple of candidates of the parts' roots, assembled, satisfies
F1's two quotient claims. -/
def QuotientDoomed4 (z : Run4 F O β × Transcript) : Prop :=
  Accepted4 (P := P) ok z ∧
    ∀ h ∈ K.CH.cands (histOfTr z.2) (tableOfTr z.2) z.1.proof.rH,
      ∀ q ∈ K.CQ.cands (histOfTr z.2) (tableOfTr z.2) z.1.proof.rQ,
        ∀ gg ∈ K.CG.cands (histOfTr z.2) (tableOfTr z.2) z.1.proof.rG,
          ¬ Compose.quotientClaims P (W.decode z.1.proof.stmt) (K.asm h q gg).1 z.1.chals.α
            z.1.chals.β z.1.chals.γ z.1.chals.t z.1.proof.v.1 z.1.proof.v.2 z.1.chals.ρ

/-- **A broken run has a doomed opening, or wins the list game.** -/
theorem breaks4_imp (z : Run4 F O β × Transcript) (hb : Breaks4 ok W K z) :
    WitnessDoomed4 ok K z ∨ WiringDoomed4 (P := P) ok z ∨ QuotientDoomed4 ok W K z ∨
      ListWins4 W K z := by
  obtain ⟨hA, hsat⟩ := hb
  by_contra hno
  simp only [not_or] at hno
  obtain ⟨hW, hσ, hQ, hL⟩ := hno
  have hW' : ∃ g ∈ extractor4 K z,
      Compose.witnessClaim g.1 z.1.chals.t z.1.chals.ρ z.1.proof.v.1 := by
    by_contra hc
    push Not at hc
    exact hW ⟨hA, hc⟩
  have hσ' : Compose.wiringClaim P z.1.chals.t z.1.proof.v.2 := by
    by_contra hc
    exact hσ ⟨hA, hc⟩
  have hQ' : ∃ h ∈ K.CH.cands (histOfTr z.2) (tableOfTr z.2) z.1.proof.rH,
      ∃ q ∈ K.CQ.cands (histOfTr z.2) (tableOfTr z.2) z.1.proof.rQ,
        ∃ gg ∈ K.CG.cands (histOfTr z.2) (tableOfTr z.2) z.1.proof.rG,
          Compose.quotientClaims P (W.decode z.1.proof.stmt) (K.asm h q gg).1 z.1.chals.α
            z.1.chals.β z.1.chals.γ z.1.chals.t z.1.proof.v.1 z.1.proof.v.2 z.1.chals.ρ := by
    by_contra hc
    push Not at hc
    exact hQ ⟨hA, hc⟩
  obtain ⟨g, hg, hgc⟩ := hW'
  obtain ⟨h, hh, q, hq, gg, hgg, hRc⟩ := hQ'
  exact hL ⟨g, hg, h, hh, q, hq, gg, hgg,
    (Compose.accepts_iff _ _ _ _ _ _ _ _ _ _).mpr ⟨hgc, hσ', hA.1, hRc⟩, hsat g hg⟩

/-- Three doomed events and the list game bound a broken run. -/
theorem prEvent_breaks4_le {mx : ProbComp (Run4 F O β × Transcript)} (εW εσ εQ εL : ℝ≥0∞)
    (hW : Pr{let z ← mx}[WitnessDoomed4 ok K z] ≤ εW)
    (hσ : Pr{let z ← mx}[WiringDoomed4 (P := P) ok z] ≤ εσ)
    (hQd : Pr{let z ← mx}[QuotientDoomed4 ok W K z] ≤ εQ)
    (hL : Pr{let z ← mx}[ListWins4 W K z] ≤ εL) :
    Pr{let z ← mx}[Breaks4 ok W K z] ≤ εW + εσ + εQ + εL := by
  refine (prEvent_mono mx _ _ (breaks4_imp ok W K)).trans ?_
  refine (prEvent_or_le _ _ _).trans ?_
  refine (add_le_add hW ((prEvent_or_le _ _ _).trans (add_le_add hσ
    ((prEvent_or_le _ _ _).trans (add_le_add hQd hL))))).trans ?_
  simp only [add_assoc, le_refl]

/-- **Knowledge soundness of the four-root reduction composed with the openings, in the
random-oracle model.** For every adversary making at most `Q` queries of the random oracle
`H : bytes → 32 bytes` that outputs a statement, four commitments, five values and the rest (the
parts' values, the openings), and every openings' verifier `openings` of at most `QV` queries: if
the three doomed events have probabilities at most `εW`, `εσ`, `εQ`, the verifier accepts while the
extractor's list holds no witness of the statement with probability at most `εW + εσ + εQ +
(Q + 6 + QV) (listFactor4 · roundError + 7 (Q + 6 + QV) / 2^256)`. -/
theorem knowledgeSoundness_composed4 (A : OracleComp HashSpec (RootProof4 F × O))
    (openings : RootProof4 F × O → Chals F → OracleComp HashSpec β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (openings p ch) QV)
    (εW εσ εQ : ℝ≥0∞)
    (hW : Pr{let z ← (simulateQ randomOracle (rootExperiment4 W A openings)).run' ∅}[
      WitnessDoomed4 ok K z] ≤ εW)
    (hσ : Pr{let z ← (simulateQ randomOracle (rootExperiment4 W A openings)).run' ∅}[
      WiringDoomed4 (P := P) ok z] ≤ εσ)
    (hQd : Pr{let z ← (simulateQ randomOracle (rootExperiment4 W A openings)).run' ∅}[
      QuotientDoomed4 ok W K z] ≤ εQ) :
    Pr{let z ← (simulateQ randomOracle (rootExperiment4 W A openings)).run' ∅}[
        Breaks4 ok W K z] ≤
      εW + εσ + εQ + ((Q + 6 + QV : ℕ) : ℝ≥0∞) *
        ((listFactor4 K.CW.bound K.CH.bound K.CQ.bound K.CG.bound : ℝ≥0∞) *
          (roundError P B : ℝ≥0∞) + 7 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) :=
  prEvent_breaks4_le ok W K εW εσ εQ _ hW hσ hQd
    (knowledgeSoundness_list4 W K A openings Q QV hQ hV)

/-- **Knowledge soundness of the four-root reduction composed with the openings, in mumbai's
two-oracle model** (Keccak-256 and Keccak-f[1600], F2's model): the bound of
`knowledgeSoundness_composed4`, the openings any computation of both oracles. -/
theorem knowledgeSoundness_composed_kc4 (A : OracleComp KeccakCalls (RootProof4 F × O))
    (openings : RootProof4 F × O → Chals F → OracleComp KeccakCalls β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (openings p ch) QV)
    (εW εσ εQ : ℝ≥0∞)
    (hW : Pr{let z ← (simulateQ randomOracle (kcExperiment4 W A openings)).run' ∅}[
      WitnessDoomed4 ok K z] ≤ εW)
    (hσ : Pr{let z ← (simulateQ randomOracle (kcExperiment4 W A openings)).run' ∅}[
      WiringDoomed4 (P := P) ok z] ≤ εσ)
    (hQd : Pr{let z ← (simulateQ randomOracle (kcExperiment4 W A openings)).run' ∅}[
      QuotientDoomed4 ok W K z] ≤ εQ) :
    Pr{let z ← (simulateQ randomOracle (kcExperiment4 W A openings)).run' ∅}[
        Breaks4 ok W K z] ≤
      εW + εσ + εQ + ((Q + 6 + QV : ℕ) : ℝ≥0∞) *
        ((listFactor4 K.CW.bound K.CH.bound K.CQ.bound K.CG.bound : ℝ≥0∞) *
          (roundError P B : ℝ≥0∞) + 7 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) :=
  prEvent_breaks4_le ok W K εW εσ εQ _ hW hσ hQd
    (knowledgeSoundness_list_kc4 W K A openings Q QV hQ hV)

end ComposePcs
