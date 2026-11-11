-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecCompose.Basic

/-!
# Part 1 ⇒ Part 2, knowledge soundness: the reduction `RecKnowledgeSoundnessReduction D ε2`, and the Prop-premise
corollary `RecKnowledgeSoundness D ε2 ε1 εh`, from `RecKnowledgeSoundness2 D ε2`

The end-to-end experiment (`recSoundnessExperiment`) is π2's (`recSoundnessExperiment2`) without the calls
(`recSoundnessExperiment_eq`). When the contract accepts and the end-to-end extractor (π2's, then π1-rec4's
`uniExtractorK D.flock`) finds no stack satisfying `KvHolds D.flock`, one of four events holds of π2's outcome:

1. **π2's**: π2's extractor outputs no π1 stream accepted with claims hashing to the declared ones
   (`RecBreaksKnowledgeSoundness2`, at most `ε2 Q` by Part 1);
2. **the hazard**: it outputs a stream π1-rec4's graph accepts on which π1-rec4's run at Keccak-f[1600] hits the merge
   hazard (at most the hazard experiment's probability for `hazardAdversary A`, `HazardCoupling`);
3. **a Keccak-256 collision**: it outputs an accepted stream on which a claim of π1-rec4's graph differs from the
   declared one (their encodings, `claimCollision`), their Keccak-256s being equal (at most the collision experiment's
   probability for `collisionAdversary A`, `CollisionCoupling`);
4. **π1-rec4's at Keccak-f[1600]**: it outputs an accepted stream off the hazard whose graph claims are the declared
   ones, and π1-rec4's own extractor finds no stack (at most the π1 experiment's probability for `pi1Adversary A` that
   π1-rec4 is broken, `Pi1Coupling`, which reads the graph as π1-rec4's verifier off the hazard,
   `Pi1GraphIsVerifierK4`).

That is the reduction (`recKnowledgeSoundnessReduction_of_part1`). The Prop-premise corollary bounds the π1 and hazard
terms by `ε1 Q` and `εh Q` under `Pi1FsKeccak`, `Pi1HazardKeccak`, and keeps the collision term. The derived adversaries
(`Reduction.lean`) run π2's adversary, its queries logged, then π2's extractor on its transcript and the setup's
evaluations: their queries are π2's adversary's, `Q` of them.
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open scoped ENNReal

/-! ## The three events -/

/-- The end-to-end outcome of π2's. -/
abbrev toOutcome (z : RecOutcome2) : RecOutcome := (z.1, z.2.1, z.2.2.1, z.2.2.2.1)

/-- **The hazard event**: π2's extractor outputs a stream π1-rec4's graph accepts at Keccak-f[1600] on which
π1-rec4's run draws `t` and hits the merge hazard (`Pi1HazardAccepted`). -/
def HazardEvent (D : RecDeployment) (z : RecOutcome2) : Prop :=
  ∃ s, recExtractor2 D (rts z) (inp z) (evs z) (lg z) (prf z) = some s ∧
    Pi1HazardAccepted (D.pi1IvAt (rts z).pi1) (inp z) s

/-- **The collision event**: π2's extractor outputs a stream on which a claim of π1-rec4's graph and the declared one
have different encodings of one Keccak-256 (`claimCollision`, `Keccak256Collision`). -/
def CollisionEvent (D : RecDeployment) (z : RecOutcome2) : Prop :=
  ∃ s, recExtractor2 D (rts z) (inp z) (evs z) (lg z) (prf z) = some s ∧
    Keccak256Collision (claimCollision (pi1GraphAt (rts z).pi1) (D.pi1IvAt (rts z).pi1) (inp z) s
      (prf z).pi1Claims).1
      (claimCollision (pi1GraphAt (rts z).pi1) (D.pi1IvAt (rts z).pi1) (inp z) s (prf z).pi1Claims).2

/-- **π1-rec4's event**: the contract accepts, π2's extractor outputs a stream accepted with claims hashing to the
declared ones, whose graph claims are the declared ones (no encoding differs: `claimCollision` empty), off the hazard,
and π1-rec4's own extractor (on that stream, the proof's π1 openings, the setup's evaluations and the transcript) finds
no stack satisfying `KvHolds D.flock`. -/
def Pi1Event (D : RecDeployment) (z : RecOutcome2) : Prop :=
  (acc z) = true ∧ ∃ s, recExtractor2 D (rts z) (inp z) (evs z) (lg z) (prf z) = some s ∧
    Pi1GraphAccepts (pi1GraphAt (rts z).pi1) (D.pi1IvAt (rts z).pi1) (inp z) s (prf z).pi1Claims ∧
    claimCollision (pi1GraphAt (rts z).pi1) (D.pi1IvAt (rts z).pi1) (inp z) s (prf z).pi1Claims = ([], []) ∧
    ¬ RecGraphKeccak.MergeHazardK4 LeanVM.Semantics.keccakF1600 (D.pi1IvAt (rts z).pi1) (inp z).toList s ∧
    ¬ ∃ q, UniKeccak.uniExtractorK D.flock D.pi1 (inp z) (evs z) (lg z) ((prf z).pi1Proof s) = some q ∧
      D.pi1.Relation D.flock ((prf z).pi1Proof s).rows (inp z) q

/-! ## The couplings (named; proved in `Couplings.lean`) -/

/-- **The end-to-end experiment is π2's, the calls dropped.** -/
def ExperimentsAgree (D : RecDeployment) : Prop :=
  ∀ A : RecAdversary, recSoundnessExperiment D A = toOutcome <$> recSoundnessExperiment2 D A

/-- **The hazard coupling**: the derived adversary makes `A`'s queries, and π2's hazard event is at most the hazard
experiment's for it. -/
def HazardCoupling (D : RecDeployment) : Prop :=
  ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    (∀ roots evals, QueryCostAtMost (hazardAdversary D A roots evals) permutationCallCost Q) ∧
    Pr{let z ← recSoundnessExperiment2 D A}[HazardEvent D z] ≤
      Pr{let z ← pi1HazardExperiment D (hazardAdversary D A)}[Pi1HazardAccepted z.1 z.2.1 z.2.2]

/-- **The collision coupling**: the derived adversary makes `A`'s queries, and π2's collision event is at most the
collision experiment's for it. -/
def CollisionCoupling (D : RecDeployment) : Prop :=
  ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    (∀ roots evals, QueryCostAtMost (collisionAdversary D A roots evals) permutationCallCost Q) ∧
    Pr{let z ← recSoundnessExperiment2 D A}[CollisionEvent D z] ≤
      Pr{let z ← collisionExperiment D (collisionAdversary D A)}[Keccak256Collision z.1 z.2]

/-- **π1-rec4's coupling**, the graph being π1-rec4's verifier off the hazard: the derived adversary makes `A`'s
queries, and π2's π1 event is at most the probability that it breaks π1-rec4 at Keccak-f[1600]. -/
def Pi1Coupling (D : RecDeployment) : Prop :=
  RecGraphKeccak.Pi1GraphIsVerifierK4 →
    ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
      (∀ roots evals, QueryCostAtMost (pi1Adversary D A roots evals) permutationCallCost Q) ∧
      Pr{let z ← recSoundnessExperiment2 D A}[Pi1Event D z] ≤
        Pr{let z ← pi1KeccakSoundnessExperiment D (pi1Adversary D A)}[
          UniKeccak.KBreaksKnowledgeSoundness D.flock D.pi1 (UniKeccak.uniExtractorK D.flock D.pi1) z]

/-- **The contract's π1 openings are the declared claims decoded**, on the outcome. -/
def CallsGood (z : RecOutcome2) : Prop :=
  acc z = true → ∃ ops, (prf z).pi1Claims.mapM claimOfWords = some ops ∧ contractPi1Openings (cls z) = some ops

/-- **On every accepted outcome, the contract's π1 openings are the declared claims decoded** (proved in
`CallsPure.lean`: the contract's claims are the declared ones followed by π2's four, and an accepted opening decodes). -/
def DeclaredGood (D : RecDeployment) : Prop :=
  ∀ (A : RecAdversary), ∀ z ∈ support (recSoundnessExperiment2 D A), CallsGood z

/-! ## The implication -/

/-- **The graph's acceptance includes its checks.** -/
theorem pi1GraphChecks_of_accepts {g : RecGraph.Graph} {iv1 : List UInt8} {input : Vector UInt8 32}
    {s : Array UInt8} {ds : List (List (List UInt8))} (h : Pi1GraphAccepts g iv1 input s ds) :
    pi1GraphChecks g iv1 input s = true := by
  obtain ⟨out, hout, hz, hnz, -⟩ := h
  unfold pi1GraphChecks
  rw [hout]
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  exact ⟨hz, hnz⟩

/-- `claimCollision`'s two strings agree or collide where the claims' Keccak-256s agree. -/
theorem collision_or_empty {g : RecGraph.Graph} {iv1 : List UInt8} {input : Vector UInt8 32} {s : Array UInt8}
    {ds : List (List (List UInt8))} (h : Pi1GraphAccepts g iv1 input s ds) :
    claimCollision g iv1 input s ds = ([], []) ∨
      Keccak256Collision (claimCollision g iv1 input s ds).1 (claimCollision g iv1 input s ds).2 := by
  obtain ⟨out, hout, -, -, -, hh⟩ := h
  unfold claimCollision
  rw [hout]
  simp only
  split
  · rename_i j hj
    right
    have hjr := List.mem_range.mp (List.mem_of_find?_eq_some hj)
    have hne := List.find?_some hj
    simp only [bne_iff_ne, ne_eq] at hne
    refine ⟨hne, ?_⟩
    have := hh j hjr
    unfold claimHash at this
    exact this
  · left; rfl

/-- **On π2's outcome, an end-to-end break is π2's, the hazard's, a collision or π1-rec4's.** -/
theorem breaks_cases (D : RecDeployment) (z : RecOutcome2)
    (h : RecBreaksKnowledgeSoundness D (recExtractor D) (toOutcome z)) :
    RecBreaksKnowledgeSoundness2 D (recExtractor2 D) z ∨ HazardEvent D z ∨ CollisionEvent D z ∨
      Pi1Event D z := by
  obtain ⟨hacc, hno⟩ := h
  change (acc z) = true at hacc
  change ¬ ∃ w, recExtractor D (rts z) (inp z) (evs z) (lg z) (prf z) = some w ∧
    D.pi1.Relation D.flock w.1 (inp z) w.2 at hno
  rcases Classical.em (RecBreaksKnowledgeSoundness2 D (recExtractor2 D) z) with h2 | h2
  · exact Or.inl h2
  refine Or.inr ?_
  have hex : ∃ s, recExtractor2 D (rts z) (inp z) (evs z) (lg z) (prf z) = some s ∧
      Pi1GraphAccepts (pi1GraphAt (rts z).pi1) (D.pi1IvAt (rts z).pi1) (inp z) s (prf z).pi1Claims :=
    Classical.byContradiction fun hc ↦ h2 ⟨hacc, hc⟩
  obtain ⟨s, hs, hga⟩ := hex
  rcases Classical.em
      (RecGraphKeccak.MergeHazardK4 LeanVM.Semantics.keccakF1600 (D.pi1IvAt (rts z).pi1) (inp z).toList s) with hz | hz
  · refine Or.inl ⟨s, hs, ?_, hz⟩
    rw [← pi1GraphChecks_graphAtSetup _ (rts z).pi1]
    exact pi1GraphChecks_of_accepts hga
  rcases collision_or_empty hga with hc | hc
  swap
  · exact Or.inr (Or.inl ⟨s, hs, hc⟩)
  refine Or.inr (Or.inr ⟨hacc, s, hs, hga, hc, hz, ?_⟩)
  rintro ⟨q, hq, hrel⟩
  refine hno ⟨⟨((prf z).pi1Proof s).rows, q⟩, ?_, hrel⟩
  have e : recExtractor D (rts z) (inp z) (evs z) (lg z) (prf z) =
      (recExtractor2 D (rts z) (inp z) (evs z) (lg z) (prf z)).bind (fun s ↦
        (UniKeccak.uniExtractorK D.flock D.pi1 (inp z) (evs z) (lg z) ((prf z).pi1Proof s)).map fun q ↦ ⟨_, q⟩) := rfl
  rw [e, hs, Option.bind_some, hq, Option.map_some]

/-- **Part 1 ⇒ Part 2 (knowledge soundness), as a reduction**: from π2's part `RecKnowledgeSoundness2 D ε2`, the
couplings and graph = verifier off the hazard, the end-to-end reduction `RecKnowledgeSoundnessReduction D ε2`. -/
theorem recKnowledgeSoundnessReduction_of_part1 {D : RecDeployment} {ε2 : ℕ → ℝ≥0∞}
    (h2 : RecKnowledgeSoundness2 D ε2) (hE : ExperimentsAgree D) (hH : HazardCoupling D) (hC : CollisionCoupling D)
    (hP : Pi1Coupling D) (hgv : RecGraphKeccak.Pi1GraphIsVerifierK4) : RecKnowledgeSoundnessReduction D ε2 := by
  intro A Q hQ
  obtain ⟨hHq, hHle⟩ := hH A Q hQ
  obtain ⟨hCq, hCle⟩ := hC A Q hQ
  obtain ⟨hPq, hPle⟩ := hP hgv A Q hQ
  refine ⟨hPq, hHq, hCq, ?_⟩
  rw [hE A, prEvent_map]
  calc Pr{let z ← recSoundnessExperiment2 D A}[RecBreaksKnowledgeSoundness D (recExtractor D) (toOutcome z)]
      ≤ Pr{let z ← recSoundnessExperiment2 D A}[RecBreaksKnowledgeSoundness2 D (recExtractor2 D) z ∨
          (HazardEvent D z ∨ (CollisionEvent D z ∨ Pi1Event D z))] :=
        prEvent_mono _ _ _ fun z hz ↦ breaks_cases D z hz
    _ ≤ Pr{let z ← recSoundnessExperiment2 D A}[RecBreaksKnowledgeSoundness2 D (recExtractor2 D) z] +
          (Pr{let z ← recSoundnessExperiment2 D A}[HazardEvent D z] +
            (Pr{let z ← recSoundnessExperiment2 D A}[CollisionEvent D z] +
              Pr{let z ← recSoundnessExperiment2 D A}[Pi1Event D z])) :=
        (prEvent_or_le _ _ _).trans (add_le_add le_rfl ((prEvent_or_le _ _ _).trans
          (add_le_add le_rfl (prEvent_or_le _ _ _))))
    _ ≤ ε2 Q + (Pr{let z ← pi1HazardExperiment D (hazardAdversary D A)}[Pi1HazardAccepted z.1 z.2.1 z.2.2] +
          (Pr{let z ← collisionExperiment D (collisionAdversary D A)}[Keccak256Collision z.1 z.2] +
            Pr{let z ← pi1KeccakSoundnessExperiment D (pi1Adversary D A)}[
              UniKeccak.KBreaksKnowledgeSoundness D.flock D.pi1 (UniKeccak.uniExtractorK D.flock D.pi1) z])) :=
        add_le_add (h2 A Q hQ) (add_le_add hHle (add_le_add hCle hPle))
    _ = _ := by ring

/-- **The Prop-premise corollary of a reduction**: under `Pi1FsKeccak ε1` and `Pi1HazardKeccak εh` (false as stated for
unbounded adversaries; the Fiat–Shamir heuristic for bounded ones), `RecKnowledgeSoundness D ε2 ε1 εh`. -/
theorem recKnowledgeSoundness_of_reduction {D : RecDeployment} {ε2 : ℕ → ℝ≥0∞}
    (hR : RecKnowledgeSoundnessReduction D ε2) (ε1 εh εc : ℕ → ℝ≥0∞) : RecKnowledgeSoundness D ε2 ε1 εh εc := by
  intro _ h1 hh hc A Q hQ
  obtain ⟨hPq, hHq, hCq, hle⟩ := hR A Q hQ
  exact hle.trans (add_le_add (add_le_add (add_le_add le_rfl (h1 _ Q hPq)) (hh _ Q hHq)) (hc _ Q hCq))

/-- **Part 1 ⇒ Part 2 (knowledge soundness)**: from π2's part `RecKnowledgeSoundness2 D ε2` and the couplings, the
end-to-end statement `RecKnowledgeSoundness D ε2 ε1 εh`, for every `ε1`, `εh`. -/
theorem recKnowledgeSoundness_of_part1 {D : RecDeployment} {ε2 : ℕ → ℝ≥0∞} (h2 : RecKnowledgeSoundness2 D ε2)
    (hE : ExperimentsAgree D) (hH : HazardCoupling D) (hC : CollisionCoupling D) (hP : Pi1Coupling D)
    (ε1 εh εc : ℕ → ℝ≥0∞) : RecKnowledgeSoundness D ε2 ε1 εh εc := by
  intro hgv
  exact recKnowledgeSoundness_of_reduction (recKnowledgeSoundnessReduction_of_part1 h2 hE hH hC hP hgv) ε1 εh εc hgv

end RecCompose

/-- info: 'RecCompose.recKnowledgeSoundnessReduction_of_part1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundnessReduction_of_part1

/-- info: 'RecCompose.recKnowledgeSoundness_of_part1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_of_part1
