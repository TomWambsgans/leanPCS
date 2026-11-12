-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π1-rec4's analogue of `Rec3ProbStaged.lean`'s
-- `uniCompletenessKeccakRec3_of_staged3`: the random permutation to the rate's two random oracles (`Rec4Rate.lean`),
-- then to leanerVM's two random oracles (`Rec4Couple.lean`), then the staged run (`Rec4Staged.lean`); uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): `rpmError`.
import UniKeccakComplete.K.Rec4Staged

/-!
# `UniCompletenessKeccakRec4`, from the staged experiment

**`uniCompletenessKeccakRec4_of_staged4`**: if, for every honest witness, π1-rec4's experiment over its calls
(`expW4 hashW callRate callFW`, `KeccakCallsW`) makes at most `N ≤ 2^52` block calls and follows the duplex
discipline, and its five-digest reading (`expW4 hash5 rate5 callKeccakF1600`, `KeccakCalls`) is the verdict of a
staged run (`KStaged4`) with these probability conditions, then π1-rec4's honest prover (`uniProverRec4RP`) is rejected
with probability at most

  `Nbad / 2^192 + (ct / 2^192 + εt) + εpow + rpmError N`:

the completeness experiment is the run over `KeccakCallsW` against the random permutation (`experiment4_eq`); against
the rate's two random oracles within `rpmError N` (`rpm_le_romW`); which is its five-digest reading against leanerVM's
(`prEvent_romW_eq`, every hash input short, `< 136 · 2^52 ≤ 2^60` bytes, by the block count); which is the staged run
(`prEvent_run_false_le4`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open UniStatement UniKeccak
open E2ECompleteness (ro)
open scoped ENNReal

set_option autoImplicit false

namespace UniKeccakComplete.Rec4

/-- **A block count of at most `2^52` keeps every hash input short.** -/
theorem hashOKW_short_of_cost {α : Type} {X : OracleComp KeccakCallsW α} {N : ℕ}
    (h : Common.QueryCostAtMost X hashBlocksW N) (hN : N ≤ 2 ^ 52) : HashOKW Short X :=
  HashOKW.mono (fun m hm ↦ by unfold Short lenB; omega) (hashOKW_of_cost h)

/-- **`UniCompletenessKeccakRec4` in the random-permutation model, from the staged experiment.** -/
theorem uniCompletenessKeccakRec4_of_staged4 {F : KeccakVm.KeccakFlockSpec} {D : KDeployment} {Nbad ct N : ℕ}
    {εt εpow : ℝ≥0∞} (hN : N ≤ 2 ^ 52)
    (hcost : ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
      D.HonestRelation F rows input q →
      Common.QueryCostAtMost (expW4 hashW callRate callFW D input rows q) hashBlocksW N)
    (hdup : ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
      D.HonestRelation F rows input q → DuplexW (expW4 hashW callRate callFW D input rows q) [])
    (hS : ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
      D.HonestRelation F rows input q → ∃ (S : KStaged4) (bad badT : List E → E → Prop),
        expW4 hash5 rate5 callKeccakF1600 D input rows q = (fun z ↦ z.1.1) <$> S.run ∧
          S.Good bad badT Nbad ct εt εpow) :
    UniCompletenessKeccakRec4 F D (uniProverRec4RP D)
      ((Nbad : ℝ≥0∞) / 2 ^ 192 + ((ct : ℝ≥0∞) / 2 ^ 192 + εt) + εpow + rpmError N) := by
  intro input rows q hfit hrel
  obtain ⟨S, bad, badT, hrun, hgood⟩ := hS input rows q hfit hrel
  rw [experiment4_eq]
  refine rpm_le_romW _ (hdup input rows q hfit hrel) (hcost input rows q hfit hrel) (fun b ↦ b = false) ?_
  rw [prEvent_romW_eq _ (hashOKW_short_of_cost (hcost input rows q hfit hrel) hN), simulateQ_tauW_expWW, hrun,
    simulateQ_map]
  have e : ((fun z : (Bool × (List E × E)) × (List E × E) ↦ z.1.1) <$> simulateQ ro S.run :
      StateT E2ECompleteness.Cache ProbComp Bool).run' ∅ =
      (fun z : (Bool × (List E × E)) × (List E × E) ↦ z.1.1) <$> (simulateQ ro S.run).run' ∅ := by
    simp only [StateT.run'_eq, StateT.run_map, Functor.map_map]
  rw [e, prEvent_map]
  exact prEvent_run_false_le4 S hgood

end UniKeccakComplete.Rec4

/-- info: 'UniKeccakComplete.Rec4.uniCompletenessKeccakRec4_of_staged4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.uniCompletenessKeccakRec4_of_staged4
