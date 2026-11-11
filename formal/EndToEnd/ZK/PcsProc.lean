-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: `PcsQuotient.challengePhase` (`formal/Statement/PcsQuotient/Zk.lean`) as a program with reveal queries.
import ZK.PcsTrace

/-!
# The challenge phase as a program with reveal queries

`phaseProg stmt`: `challengePhase stmt` (the Statement's) with its five reveals as reveal queries (`RProg.rev`)
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
  .step (oodPointWith edgePerm mv rW) fun zW ↦
  .step (Chain.startWith edgePerm (label index stmt)) fun c ↦
  .rev (.oodW zW) fun oW ↦
  let wCom : Commitment := ⟨rW, oW⟩
  let wS := CommitmentScalars.of wCom
  let c := c.absorbCommitment wS
  .step (c.squeezeWith edgePerm) fun (α, c) ↦
  .step (c.squeezeWith edgePerm) fun (β, c) ↦
  .step (c.squeezeWith edgePerm) fun (μ, c) ↦
  .step (simulateQ edgeOracle sampleDigest) fun rT ↦
  .step (oodPointWith edgePerm (mv + 4) rT) fun zT ↦
  .rev (.oodT α β μ zT) fun oT ↦
  let tCom : Commitment := ⟨rT, oT⟩
  let tS := CommitmentScalars.of tCom
  let c := c.absorbCommitment tS
  .step (c.squeezeWith edgePerm) fun (t, c) ↦
  .rev (.value 1 t) fun v1 ↦
  .rev (.value 2 t) fun v2 ↦
  .rev (.value 0 t) fun v0 ↦
  let vals : Vector E 3 := #v[v0, v1, v2]
  let next := wiringValue circuit t
  let c := (vals.toList.foldl Chain.absorb c).absorb next
  .step (c.squeezeWith edgePerm) fun (ρ, _) ↦
  .ret (⟨zW, zT, α, β, μ, t, ρ⟩,
    ⟨indexTree, index, ⟨wS, tS, vals, next⟩,
      (claimsAt circuit.logRows stmt α β μ t ρ vals next).map fun cl ↦ ⟨⟨wCom, tCom⟩, cl⟩⟩)

/-- **The program is the challenge phase**, its reveals answered by `rv`. -/
theorem interp_phaseProg {A : Type} (circuit : Circuit) (stmt : Statement)
    (rv : Reveal → StateT (Edges × A) ProbComp E) :
    interp rv (phaseProg circuit stmt) = challengePhase circuit stmt rv := by
  rfl

/-- **The logged run's queries are the challenges' reveal queries, its answers the output's revealed scalars.** -/
theorem log_phaseProg {A : Type} (circuit : Circuit) (stmt : Statement) (ν : Reveal → ProbComp E)
    (s : Edges × A) (o : (Challenges × PhaseOut) × (Edges × A) × List (Reveal × E))
    (ho : o ∈ support (semL ν (phaseProg circuit stmt) s [])) :
    o.2.2.map Prod.fst = revealQueries o.1.1 ∧ o.2.2.map Prod.snd = answersOf o.1.2 := by
  simp only [phaseProg, semL, mem_support_bind_iff] at ho
  obtain ⟨⟨⟨indexTree, index⟩, s1⟩, -, ⟨rW, s2⟩, -, ⟨zW, s3⟩, -, ⟨c0, s4⟩, -, oW, -, ⟨⟨α, c1⟩, s5⟩, -,
    ⟨⟨β, c2⟩, s6⟩, -, ⟨⟨μ, c3⟩, s7⟩, -, ⟨rT, s8⟩, -, ⟨zT, s9⟩, -, oT, -, ⟨⟨t, c4⟩, s10⟩, -, v1, -, v2, -,
    v0, -, ⟨⟨ρ, c5⟩, s11⟩, -, ho⟩ := ho
  simp only [support_pure, Set.mem_singleton_iff] at ho
  subst ho
  simp [revealQueries, answersOf, CommitmentScalars.of]

end PcsQuotient.EndToEnd
