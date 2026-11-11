-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: `PcsQuotient.challengePhase` (`formal/Statement/PcsQuotient/Zk.lean`) as a program with reveal queries.
import ZK.PcsTrace

/-!
# The challenge phase as a program with reveal queries

`phaseProg stmt`: `challengePhase stmt` (the Statement's) with its ten reveals as reveal queries (`RProg.rev`)
and its other steps as black boxes. **`interp_phaseProg`**: run with the answers `rv`, it is
`challengePhase stmt rv`. **`log_phaseProg`**: the logged run's queries are `revealQueries` of the challenges it
returns.
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open PcsQuotient.Transcript PcsQuotient.Domain
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open RProg

/-- **The challenge phase as a program**: `challengePhase`'s steps, its reveals as queries. -/
noncomputable def phaseProg {A : Type} (circuit : Circuit) (stmt : Statement) :
    RProg (Edges × A) Reveal E (Challenges × PhaseOut) :=
  let mv := cellVars circuit.logRows
  .step (commitmentWith edgePerm mv circuit.wiringTable) fun (indexTree, index) ↦
  .step (simulateQ edgeOracle sampleDigest) fun rW ↦
  .step (oodPointWith edgePerm (mv + 1) rW) fun zW ↦
  .step (Chain.startWith edgePerm (label index stmt)) fun c ↦
  .rev (.oodW zW) fun oW ↦
  let wCom : Commitment := ⟨rW, oW⟩
  let wS := CommitmentScalars.of wCom
  let c := c.absorbCommitment wS
  .step (c.squeezeWith edgePerm) fun (α, c) ↦
  .step (c.squeezeWith edgePerm) fun (β, c) ↦
  .step (c.squeezeWith edgePerm) fun (γ, c) ↦
  .step (simulateQ edgeOracle sampleDigest) fun rH ↦
  .step (oodPointWith edgePerm (mv + 3) rH) fun zH ↦
  .step (simulateQ edgeOracle sampleDigest) fun rQ ↦
  .step (oodPointWith edgePerm (mv + 4) rQ) fun zQ ↦
  .step (simulateQ edgeOracle sampleDigest) fun rG ↦
  .step (oodPointWith edgePerm (mv + 1) rG) fun zG ↦
  .rev (.oodQ α β γ zQ) fun oQ ↦
  .rev (.oodG α β γ zG) fun oG ↦
  .rev (.oodH α β γ zH) fun oH ↦
  let hCom : Commitment := ⟨rH, oH⟩
  let qCom : Commitment := ⟨rQ, oQ⟩
  let gCom : Commitment := ⟨rG, oG⟩
  let hS := CommitmentScalars.of hCom
  let qS := CommitmentScalars.of qCom
  let gS := CommitmentScalars.of gCom
  let c := ((c.absorbCommitment hS).absorbCommitment qS).absorbCommitment gS
  .step (c.squeezeWith edgePerm) fun (t, c) ↦
  .rev (.value 1 t) fun a1 ↦
  .rev (.value 2 t) fun a2 ↦
  .rev (.value 3 t) fun a3 ↦
  .rev (.value 0 t) fun a0 ↦
  let a : Vector E 4 := #v[a0, a1, a2, a3]
  let next := wiringValue circuit t
  let c := (a.toList.foldl Chain.absorb c).absorb next
  .step (c.squeezeWith edgePerm) fun (ρ, _) ↦
  .rev (.qValue α β γ t ρ) fun vq ↦
  .rev (.gValue α β γ t ρ) fun vg ↦
  .ret (⟨zW, zH, zQ, zG, α, β, γ, t, ρ⟩,
    ⟨indexTree, index, ⟨wS, hS, qS, gS, a, next, vq, vg⟩,
      (claimsAt circuit.logRows stmt α β γ t ρ a next vq vg).map fun cl ↦ ⟨⟨wCom, hCom, qCom, gCom⟩, cl⟩⟩)

/-- **The program is the challenge phase**, its reveals answered by `rv`. -/
theorem interp_phaseProg {A : Type} (circuit : Circuit) (stmt : Statement)
    (rv : Reveal → StateT (Edges × A) ProbComp E) :
    interp rv (phaseProg circuit stmt) = challengePhase circuit stmt rv := by
  rfl

/-- **The logged run's queries are the challenges' reveal queries.** -/
theorem log_phaseProg {A : Type} (circuit : Circuit) (stmt : Statement) (ν : Reveal → ProbComp E)
    (s : Edges × A) (o : (Challenges × PhaseOut) × (Edges × A) × List (Reveal × E))
    (ho : o ∈ support (semL ν (phaseProg circuit stmt) s [])) : o.2.2.map Prod.fst = revealQueries o.1.1 := by
  simp only [phaseProg, semL, mem_support_bind_iff] at ho
  obtain ⟨⟨⟨indexTree, index⟩, s1⟩, -, ⟨rW, s2⟩, -, ⟨zW, s3⟩, -, ⟨c0, s4⟩, -, oW, -, ⟨⟨α, c1⟩, s5⟩, -,
    ⟨⟨β, c2⟩, s6⟩, -, ⟨⟨γ, c3⟩, s7⟩, -, ⟨rH, s8⟩, -, ⟨zH, s9⟩, -, ⟨rQ, s10⟩, -, ⟨zQ, s11⟩, -,
    ⟨rG, s12⟩, -, ⟨zG, s13⟩, -, oQ, -, oG, -, oH, -, ⟨⟨t, c4⟩, s14⟩, -, a1, -, a2, -, a3, -, a0, -,
    ⟨⟨ρ, c5⟩, s15⟩, -, vq, -, vg, -, ho⟩ := ho
  simp only [support_pure, Set.mem_singleton_iff] at ho
  subst ho
  simp [revealQueries]

end PcsQuotient.EndToEnd
