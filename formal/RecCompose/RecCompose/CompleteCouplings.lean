-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecCompose.Complete
import RecCompose.RpmC
import RecCompose.Pi1Decode
import RecCompose.Pi1Words
import RecCompose.RunShape

/-!
# The completeness couplings, proved; the end-to-end completeness under π2's

Both in the eager form of the random-permutation model (`RpmC.eager_eq`, `RpmC.eager_le_add`: per permutation the
game keeps no state).

* **`completenessAgree`**: `CompletenessAgree D P1 P2`, for every deployment and provers: π2's completeness
  experiment runs π1-rec4's graph's check between π1's prover and π2's; per permutation its result is unused by the
  rest and drops out (`OracleComp.prEvent_true_eq_one`, `prEvent_bind_eq_of_forall_eq`).
* **`completenessPi1Coupling`**: `CompletenessPi1Coupling D P1 P2`, at the reference shape (`keccak128`) and under
  one fact of the Keccak π1-rec4's verifier's code, **`Pi1RunShape`** (a run that returns a result has no matrices'
  claim; proved, `RunShape.lean`). Per permutation, setup and π1 proof: on the merge hazard the honest-hazard
  experiment's event holds; off it (`graph_le_verifier`) the graph at π1's setup commitment is the verifier there
  (`RecGraphKeccak.Sim.pi1GraphIsVerifierK4At`, no hypothesis), its checks the run's verdict, its claims
  `UniKeccak.pcsClaimWordsK`' words at the setup's commitment, which decode back to the verifier's three commitments,
  points and values (`decode_pcsClaimWordsK`), so the graph runs the same three openings (`pcsOpenK` at `stackVarsK`)
  as π1-rec4's verifier when the run has three point openings, and π1-rec4's verifier rejects surely otherwise
  (`support_forIn_false`).
* **`recCompleteness_of_couplings`**, **`recCompleteness_end`**, **`recCompleteness_end_fs`**: with them,
  `RecCompleteness D P1 P2 δ1 δh δ2` (and its form with `Pi1GraphIsVerifierK4` discharged by
  `RecGraphKeccak.Sim.pi1GraphIsVerifierK4`) from π2's completeness `RecCompleteness2 D P1 P2 δ2`, for any π1 prover.
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open PcsQuotient.EndToEnd.Eager
open scoped ENNReal

/-- **`CompletenessAgree`**: π2's experiment's second verdict is the end-to-end experiment's (per permutation the graph's
check, its answer unused by the rest, drops out). -/
theorem completenessAgree (D : RecDeployment) (P1 : Pi1Prover D) (P2 : Pi2Prover) : CompletenessAgree D P1 P2 := by
  intro input rows q
  unfold recCompletenessExperiment recCompletenessExperiment2
  refine RpmC.eager_eq _ _ _ _ fun π ↦ ?_
  rw [simulateQ_bind, simulateQ_bind]
  refine prEvent_bind_congr _ _ _ _ _ fun trees ↦ ?_
  unfold composeProver
  rw [bind_assoc, simulateQ_bind, simulateQ_bind]
  refine prEvent_bind_congr _ _ _ _ _ fun o1 ↦ ?_
  cases o1 with
  | none =>
    simp only [pure_bind, simulateQ_pure, prEvent_pure]
  | some p1 =>
    simp only
    conv_rhs => rw [simulateQ_bind]
    symm
    refine prEvent_bind_eq_of_forall_eq _ (OracleComp.prEvent_true_eq_one _) _ _ fun a1 ↦ ?_
    rw [simulateQ_bind, simulateQ_bind]
    refine prEvent_bind_congr _ _ _ _ _ fun o2 ↦ ?_
    cases o2 with
    | none => simp only [simulateQ_pure, prEvent_pure]
    | some p2 =>
      simp only [simulateQ_bind, simulateQ_pure]
      refine (prEvent_bind_congr _ _ (fun x ↦ pure x) _ (fun v ↦ v = false) fun x ↦ ?_).trans (by rw [bind_pure])
      simp only [prEvent_pure]

/-! ## π1-rec4's graph and its verifier, on one proof -/

/-- **A loop of verdicts that a `false` keeps `false`** (every step yields; from `false` every step yields `false`)
returns `false` if it starts at `false` or passes a step that always yields `false`. -/
theorem support_forIn_false {ι : Type} {spec : OracleSpec ι} {β : Type}
    (f : β → Bool → OracleComp spec (ForInStep Bool))
    (hstep : ∀ x s, ∀ y ∈ support (f x s), ∃ b, y = ForInStep.yield b)
    (hpres : ∀ x, ∀ y ∈ support (f x false), y = ForInStep.yield false) :
    ∀ (l : List β) (init : Bool), (init = false ∨ ∃ x ∈ l, ∀ s, ∀ y ∈ support (f x s), y = ForInStep.yield false) →
      ∀ y ∈ support (forIn l init f), y = false
  | [], init, h, y, hy => by
    simp only [List.forIn_nil, support_pure, Set.mem_singleton_iff] at hy
    rcases h with h | ⟨x, hx, -⟩
    · rw [hy, h]
    · simp at hx
  | a :: l, init, h, y, hy => by
    rw [List.forIn_cons, support_bind] at hy
    simp only [Set.mem_iUnion, exists_prop] at hy
    obtain ⟨step, hs, hy⟩ := hy
    obtain ⟨b, rfl⟩ := hstep a init step hs
    refine support_forIn_false f hstep hpres l b ?_ y hy
    rcases h with h | ⟨x, hx, hxf⟩
    · subst h
      have := hpres a _ hs
      simp only [ForInStep.yield.injEq] at this
      exact Or.inl this
    · rcases List.mem_cons.mp hx with rfl | hx
      · have := hxf init _ hs
        simp only [ForInStep.yield.injEq] at this
        exact Or.inl this
      · exact Or.inr ⟨x, hx, hxf⟩

/-- **Off the merge hazard, π1-rec4's graph with its openings rejects at most as often as π1-rec4's verifier** at
Keccak-f[1600] with the same openings, for every permutation. -/
theorem graph_le_verifier (D : RecDeployment) (hD : D.pi1.shape = RecGraphKeccak.Pi1.keccak128) (hS : Pi1RunShape)
    (π : Equiv.Perm St) (roots : UniKeccak.SetupRootsK)
    (input : Vector UInt8 32) (p1 : UniKeccak.KeccakProof)
    (hz : ¬ RecGraphKeccak.MergeHazardK4 LeanVM.Semantics.keccakF1600 (D.pi1IvAt roots) input.toList p1.stream) :
    Pr{let a ← simulateQ (permImpl π) (pi1GraphVerifierWith queryPermutation D roots input p1)}[a = false] ≤
      Pr{let a ← simulateQ (permImpl π) (pi1KeccakVerifierWith queryPermutation D.pi1 roots input p1)}[a = false] := by
  have hge := RecGraphKeccak.Sim.pi1GraphIsVerifierK4At roots LeanVM.Semantics.keccakF1600 (D.pi1IvAt roots) input
    p1.stream hz
  unfold pi1GraphVerifierWith pi1KeccakVerifierWith
  simp only [RecDeployment.pi1IvAt] at hge ⊢
  rw [hD] at hge ⊢
  set iv := pi1Iv RecGraphKeccak.Pi1.keccak128 D.pi1.programIv roots with hiv
  set o := UniKeccak.runK4 RecGraphKeccak.Pi1.keccak128 iv input.toList p1.stream pi1Variant .point with ho
  have hgo : RecGraph.evalGraphDeployed (pi1GraphAt roots) iv input.toList p1.stream =
      match o.result with
      | .ok r => some ⟨UniKeccak.pcsClaimWordsK roots r, o.chan.zeros.toList, []⟩
      | .error _ => none := hge
  rw [hgo]
  cases hres : o.result with
  | error e =>
    have hacc : o.accepts = false := by simp [UniStatement.Outcome.accepts, hres]
    simp only [hacc, Bool.not_false, ite_true]
    exact le_rfl
  | ok r =>
    obtain ⟨hmat, -⟩ := hS iv input.toList p1.stream r hres
    have hacc : o.accepts = o.chan.zeros.all (· == 0) := by simp [UniStatement.Outcome.accepts, hres]
    simp only [hacc, Array.all_toList, List.all_nil, Bool.and_true]
    by_cases hzs : o.chan.zeros.all (· == 0) = true
    swap
    · simp only [Bool.eq_false_iff.mpr hzs, Bool.not_false, ite_true]
      exact le_rfl
    simp only [hzs, Bool.not_true, Bool.false_eq_true, ite_false]
    by_cases hgood : ∃ pt1 v1 pt2 v2 pt3 v3, r.openings = [(.c1, .point pt1 v1 none), (.c2, .point pt2 v2 none),
        (.setup, .point pt3 v3 none)]
    · obtain ⟨pt1, v1, pt2, v2, pt3, v3, hro⟩ := hgood
      rw [decode_pcsClaimWordsK _ r pt1 pt2 pt3 v1 v2 v3 hro, hro]
      have hcm : (List.map (fun x ↦ x.1) [(UniStatement.Commitment.c1, UniStatement.Opening.point pt1 v1 none),
          (UniStatement.Commitment.c2, UniStatement.Opening.point pt2 v2 none),
          (UniStatement.Commitment.setup, UniStatement.Opening.point pt3 v3 none)] == UniStatement.commitments) = true :=
        rfl
      simp only [hmat, Option.isSome_none, List.length_cons, List.length_nil, List.zip_cons_cons,
        List.zip_nil_right, List.forIn_cons, List.forIn_nil, bind_assoc, pure_bind, ne_eq, not_true_eq_false,
        ite_false, zero_add, Nat.reduceAdd, UniStatement.commitments, UniKeccak.commitOfK,
        UniKeccak.KeccakProof.openingOf]
      exact le_rfl
    · refine le_of_le_of_eq (prEvent_le_one _) (RpmC.prEvent_perm_eq_one π _ _ ?_).symm
      intro y hy
      simp only [support_bind, Set.mem_iUnion, exists_prop] at hy
      obtain ⟨s, hs, hys⟩ := hy
      simp only [hmat, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, support_pure,
        Set.mem_singleton_iff] at hys
      rw [hys]
      refine support_forIn_false _ ?_ ?_ r.openings _ ?_ s hs
      · rintro ⟨c, op⟩ b y hy
        rcases op with _ | ⟨pt, v, _ | bs⟩
        all_goals simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hy
        · exact ⟨false, hy⟩
        · obtain ⟨i, -, hi⟩ := hy
          exact ⟨_, hi⟩
        · exact ⟨false, hy⟩
      · rintro ⟨c, op⟩ y hy
        rcases op with _ | ⟨pt, v, _ | bs⟩
        all_goals simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hy
        · exact hy
        · obtain ⟨i, -, hi⟩ := hy
          rw [hi, Bool.false_and]
        · exact hy
      · by_cases hm : r.openings.map (·.1) = UniStatement.commitments
        · right
          rcases hro : r.openings with _ | ⟨⟨c1', o1⟩, _ | ⟨⟨c2', o2⟩, _ | ⟨⟨c3', o3⟩, _ | ⟨x4, l⟩⟩⟩⟩
          all_goals rw [hro] at hm
          all_goals simp [UniStatement.commitments] at hm
          obtain ⟨rfl, rfl, rfl⟩ := hm
          by_cases g1 : ∃ pt v, o1 = .point pt v none
          · by_cases g2 : ∃ pt v, o2 = .point pt v none
            · by_cases g3 : ∃ pt v, o3 = .point pt v none
              · exfalso
                obtain ⟨q1, w1, rfl⟩ := g1
                obtain ⟨q2, w2, rfl⟩ := g2
                obtain ⟨q3, w3, rfl⟩ := g3
                exact hgood ⟨q1, w1, q2, w2, q3, w3, hro⟩
              · refine ⟨(.setup, o3), by simp, fun s y hy ↦ ?_⟩
                rcases o3 with _ | ⟨pt, v, _ | bs⟩ <;>
                  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hy
                · exact hy
                · exact absurd ⟨pt, v, rfl⟩ g3
                · exact hy
            · refine ⟨(.c2, o2), by simp, fun s y hy ↦ ?_⟩
              rcases o2 with _ | ⟨pt, v, _ | bs⟩ <;>
                simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hy
              · exact hy
              · exact absurd ⟨pt, v, rfl⟩ g2
              · exact hy
          · refine ⟨(.c1, o1), by simp, fun s y hy ↦ ?_⟩
            rcases o1 with _ | ⟨pt, v, _ | bs⟩ <;>
              simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hy
            · exact hy
            · exact absurd ⟨pt, v, rfl⟩ g1
            · exact hy
        · left
          simp [hm]

/-- **`CompletenessPi1Coupling`**, at the reference shape, π1-rec4's run's shape given: per permutation, setup and π1
proof, on the merge hazard the honest-hazard experiment's event holds, and off it the graph rejects at most as often as
π1-rec4's verifier at Keccak-f[1600] (`graph_le_verifier`); π2's prover and the contract after the graph's check change
nothing of its verdict. -/
theorem completenessPi1Coupling (D : RecDeployment) (hD : D.pi1.shape = RecGraphKeccak.Pi1.keccak128) (hS : Pi1RunShape)
    (P1 : Pi1Prover D) (P2 : Pi2Prover) : CompletenessPi1Coupling D P1 P2 := by
  intro _ input rows q
  unfold recCompletenessExperiment2 pi1KeccakCompletenessExperiment pi1HonestHazardExperiment
  refine RpmC.eager_le_add _ _ _ _ _ _ fun π ↦ ?_
  rw [simulateQ_bind, simulateQ_bind, simulateQ_bind]
  refine prEvent_bind_le_add_of_forall_le _ _ _ _ _ _ _ fun trees ↦ ?_
  rw [simulateQ_bind, simulateQ_bind, simulateQ_bind]
  refine prEvent_bind_le_add_of_forall_le _ _ _ _ _ _ _ fun o1 ↦ ?_
  cases o1 with
  | none =>
    simp only [simulateQ_pure, prEvent_pure, ite_true]
    exact le_add_right le_rfl
  | some p1 =>
    simp only
    rw [simulateQ_bind]
    refine (prEvent_bind_congr _ _ (fun a ↦ (pure a : ProbComp Bool)) _ (fun v ↦ v = false) fun a1 ↦ ?_).trans_le ?_
    · rw [simulateQ_bind]
      refine prEvent_bind_eq_of_forall_eq _ (OracleComp.prEvent_true_eq_one _) _ _ fun o2 ↦ ?_
      cases o2 with
      | none => simp only [simulateQ_pure, prEvent_pure]
      | some p2 =>
        simp only [simulateQ_bind, simulateQ_pure]
        exact prEvent_bind_eq_of_forall_eq _ (OracleComp.prEvent_true_eq_one _) _ _ fun v ↦ by
          simp only [prEvent_pure]
    · classical
      rw [bind_pure, simulateQ_pure, prEvent_pure]
      by_cases hz : RecGraphKeccak.MergeHazardK4 LeanVM.Semantics.keccakF1600 (D.pi1IvAt trees.roots.pi1) input.toList
        p1.stream
      · rw [ite_eq_left ⟨_, _, rfl, hz⟩]
        exact (prEvent_le_one _).trans le_add_self
      · rw [ite_eq_right fun ⟨iv, s, he, hs⟩ ↦ by
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact hz hs, add_zero]
        exact graph_le_verifier D hD hS π trees.roots.pi1 input p1 hz

/-! ## The end-to-end completeness from π2's -/

/-- **The recursive verifier is complete end to end**, for a π1 prover then π2's: `RecCompleteness D P1 P2 δ1 δh δ2`
for every `δ1`, `δh`, i.e. under `Pi1GraphIsVerifierK4`, `Pi1CompletenessKeccak δ1` and `Pi1HazardKeccakHonest δh`,
error `δ1 + δh + δ2`, from π2's completeness `RecCompleteness2 D P1 P2 δ2` and the couplings. -/
theorem recCompleteness_of_couplings (D : RecDeployment) (P1 : Pi1Prover D) (P2 : Pi2Prover) (δ2 : ℝ≥0∞)
    (h2 : RecCompleteness2 D P1 P2 δ2) (hA : CompletenessAgree D P1 P2) (hC : CompletenessPi1Coupling D P1 P2)
    (δ1 δh : ℝ≥0∞) : RecCompleteness D P1 P2 δ1 δh δ2 :=
  recCompleteness_of_part1 h2 hA hC δ1 δh

/-- **The recursive verifier is complete end to end, at the real deployment's shape**: the couplings proved
(`completenessAgree`, `completenessPi1Coupling` at the reference shape, `pi1RunShape`), under π2's completeness
`RecCompleteness2 D P1 P2 δ2`. -/
theorem recCompleteness_end (D : RecDeployment) (hD : D.Real) (P1 : Pi1Prover D) (P2 : Pi2Prover) (δ2 : ℝ≥0∞)
    (h2 : RecCompleteness2 D P1 P2 δ2) (δ1 δh : ℝ≥0∞) : RecCompleteness D P1 P2 δ1 δh δ2 :=
  recCompleteness_of_part1 h2 (completenessAgree D P1 P2) (completenessPi1Coupling D hD.2.2.1 pi1RunShape P1 P2)
    δ1 δh

/-- **The recursive verifier is complete end to end, the graph being π1-rec4's verifier off the hazard proved**
(`RecGraphKeccak.Sim.pi1GraphIsVerifierK4`): for every `δ1`, `δh`, under π1-rec4's completeness at Keccak-f[1600]
(`Pi1CompletenessKeccak δ1`) and the honest proofs' hazard (`Pi1HazardKeccakHonest δh`) only, the composed prover's
proof is rejected with probability at most `δ1 + δh + δ2`. -/
theorem recCompleteness_end_fs (D : RecDeployment) (hD : D.Real) (P1 : Pi1Prover D) (P2 : Pi2Prover) (δ2 : ℝ≥0∞)
    (h2 : RecCompleteness2 D P1 P2 δ2) (δ1 δh : ℝ≥0∞) (h1 : Pi1CompletenessKeccak D P1 δ1)
    (hh : Pi1HazardKeccakHonest D P1 δh) :
    RecCompletenessWith D (composeProver D P1 P2) (δ1 + δh + δ2) :=
  recCompleteness_end D hD P1 P2 δ2 h2 δ1 δh RecGraphKeccak.Sim.pi1GraphIsVerifierK4 h1 hh

end RecCompose

/-- info: 'RecCompose.completenessAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.completenessAgree

/-- info: 'RecCompose.graph_le_verifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.graph_le_verifier

/-- info: 'RecCompose.completenessPi1Coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.completenessPi1Coupling

/-- info: 'RecCompose.recCompleteness_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recCompleteness_end

/-- info: 'RecCompose.recCompleteness_end_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recCompleteness_end_fs
