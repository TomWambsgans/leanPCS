-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- The zero-knowledge statement of `docs/membership/HIDING.md` (zero knowledge assuming a zero-knowledge PCS), in
-- leanerVM's programmable random-permutation model (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0:
-- `Statement/RandomPermutation.lean`, whose lazily sampled permutation the simulator's model is).
module

public import PcsQuotient.Security

/-!
# Zero knowledge, assuming a zero-knowledge PCS

`docs/membership/HIDING.md`: the EIP's PCS is assumed zero-knowledge — a commitment's root and an opening reveal
nothing beyond the commitment's out-of-domain answer and the claim — and the protocol makes everything else it
reveals (the out-of-domain answers, the four `a_j`, `Q`'s and `G`'s values) uniform with its randomness (the
masks, the random rows, the blinding of `h`). The deployed openings are leanVM's WHIR, which is not
zero-knowledge: this is a statement about the protocol over an ideal PCS.

**The simulator's model** (`edgeOracle`): mumbai's lazily sampled permutation (`lazyRandomPermutation`) on the
edges component of a state `Edges × A`, coins forwarded; the extra component `A` is a PCS simulator's own.

* **A PCS simulator** (`PcsSimulator`): its own state (`Aux`, from `aux₀`) and its opening simulator `simOpen`,
  which sees only the commitment and the claim and may read and program the permutation's edges (it runs on the
  whole state). Its oracle (`oracle`) is the model's, `edgeOracle`: the permutation is lazily sampled, and
  programmed only where `simOpen` writes edges.
* **The ideal PCS** (`idealPcs`): a commitment's root is uniform and independent of the table, its out-of-domain
  answer the table's polynomial at the root's point (computed with the model's permutation); an opening is the
  opening simulator's.
* **The hybrid experiment** (`hybridExperiment`): the honest prover with the witness, its four secret tables
  committed and opened by the ideal PCS (`proveWithPcs`), the circuit's commitment and the wiring opening (public)
  real, then the distinguisher, every query answered by the simulator's oracle.
* **`PcsZeroKnowledge sim εpcs`**, the hypothesis on the PCS: the real experiment (`Security.lean`'s
  `realExperiment`) and the hybrid differ by at most `εpcs Q` for a distinguisher of `Q` calls.
* **The revealed scalars** (`revealed`): the answers `revealAnswer` gives to the ten queries `revealQueries c` of
  the challenges `c`: four out-of-domain answers, the four `a_j`, `Q`'s and `G`'s values.
* **`RevealedUniform εr`**, the protocol's own randomness: for every witness, outside a set of challenge tuples of
  probability at most `εr` (the out-of-domain points and `α, β, γ, t, ρ` uniform), the revealed scalars are
  uniform when the prover's randomness is (`HIDING.md`'s rank conditions).
* **The simulator** (`zkSimulator sim`): it reads no witness. Its challenge phase (`challengePhase`, with
  `uniformReveal`) commits to the circuit (real, public), draws each root uniformly and computes its out-of-domain
  point with the model's permutation, draws each revealed scalar uniformly (`coinE`) where the prover computes it,
  and runs the reduction's chain on them (`α, β, γ, t, ρ`), `next` the public wiring value; then (`finishOpenings`) it
  opens the wiring claim with the real WHIR prover (public table) and the five secret claims with `simOpen`.
* **`FiatShamirUniform εfs`**, the random-permutation model's Fiat–Shamir challenges: in the simulator's challenge
  phase (uniform roots and uniform revealed scalars, the lazily sampled permutation, after the circuit's
  commitment), the challenges are within `εfs` of `sampleChallenges` on every event. This is a property of the
  model and of the transcript's encoding (each challenge is a Keccak-256 of an input holding a fresh uniform root,
  a fresh uniform scalar or a fresh permutation answer), not of the PCS nor of the witness; it is proved at
  `εfs₀ ≤ 2^-162` (`formal/EndToEnd/ZK`, `fiatShamirUniform_closed`).

**What changed from the first draft** (orchestrator's), so that the theorem is true and provable:
1. `PcsSimulator.oracle` was arbitrary, so the chain's challenges in the hybrid need not be uniform. The simulator's
   oracle is now the lazily sampled permutation of the model on the edges component (`edgeOracle`), and a PCS
   simulator only adds its state and its opening simulator, which may read and program edges. (This restricts the
   PCS simulators `PcsZeroKnowledge` may be instantiated with to programming ones: a simulator with an oracle of its
   own, such as an indifferentiability simulator answering fresh queries specially, is not covered.)
2. `revealed` is the map of `revealAnswer` over `revealQueries` (the same ten scalars as before, in the same
   order), so that the simulator's queries and the prover's answers are named; `Q`'s and `G`'s values read the
   reduction's claim through `Option.map`/`getD` (zero if it rejects, as before), `next` through `wiringValue`
   (equal to `rowValues`' by definition). `revealAnswer`, `challengePhase` and `finishOpenings` take the circuit
   (the membership circuit's in `revealed`, `zkSimulator`, `FiatShamirUniform`), so that the end theorem's
   equations never unfold the `2^22`-row circuit.
3. The simulator is in the statement (`zkSimulator`), with its challenge phase separate (`challengePhase`), and a
   third proposition, `FiatShamirUniform`, about that phase. The adaptivity argument (the revealed scalars are
   uniform at every fixed good challenge tuple, while the challenges are hashes of inputs holding the revealed
   scalars) bounds the distance of the hybrid and the simulator by the probability that the simulator's own
   challenges are bad; `RevealedUniform` bounds it at uniform challenges, so the simulator's challenges must be
   near-uniform. That is a random-permutation-model freshness bound on the transcript, **proved** in
   `formal/EndToEnd/ZK` (`fiatShamirUniform_closed`: `FiatShamirUniform εfs₀`, `εfs₀ = 113 · δq L ≤ 2^-162`, every
   input of a challenge's permutation call injective in a value drawn just before it, among at most
   `5 · 2^19 + 140` edges).
4. The simulator draws each revealed scalar last before the Fiat–Shamir input it must make unpredictable (`W`'s
   answer after the chain's seed, `H`'s after `Q`'s and `G`'s, `a_0` after `a_1, a_2, a_3`); `revealQueries` lists
   them in that order and `sampleChallenges` draws in the reduction's order (the same distributions).

The end theorems (`formal/EndToEnd/ZK`): `PcsQuotient.EndToEnd.zeroKnowledge_pcs` states `ZeroKnowledgeWith` for
`zkSimulator sim` under `PcsZeroKnowledge`, `RevealedUniform` and `FiatShamirUniform`, with
`ζ Q = εpcs Q + εr + εfs`; `zeroKnowledge_pcs_closed` under the first two only, `ζ Q = εpcs Q + εr + εfs₀`,
`εfs₀ ≤ 2^-162`.
-/

@[expose] public section

namespace PcsQuotient

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open PcsQuotient.Transcript PcsQuotient.Domain
open OracleComp OracleSpec Common
open scoped ENNReal

/-! ### The simulator's model -/

/-- The edges of the lazily sampled permutation (mumbai's `PermutationEdges`). -/
abbrev Edges : Type := PermutationEdges KeccakState

/-- A computation on the permutation's edges, run on the edges component of a state with an extra component. -/
def onEdges {A α : Type} (x : StateT Edges ProbComp α) : StateT (Edges × A) ProbComp α :=
  fun s ↦ (fun p ↦ (p.1, (p.2, s.2))) <$> x.run s.1

/-- **The model's oracles on a state with an extra component**: coins forwarded, `π` and `π⁻¹` the lazily
sampled permutation (`lazyRandomPermutationOracles`) on the edges. -/
noncomputable def edgeOracle {A : Type} : QueryImpl RandomPermutationOracles (StateT (Edges × A) ProbComp) :=
  fun q ↦ onEdges (lazyRandomPermutationOracles q)

/-- The model's permutation `π` on a state with an extra component. -/
noncomputable def edgePerm {A : Type} (s : KeccakState) : StateT (Edges × A) ProbComp KeccakState :=
  simulateQ edgeOracle (queryPermutation s)

/-- A uniform digest from the model's coins (four uniform words). -/
def sampleDigest : OracleComp RandomPermutationOracles Digest := do
  let w ← (List.range 4).mapM fun _ ↦ coinWord
  return #v[w.getD 0 0, w.getD 1 0, w.getD 2 0, w.getD 3 0]

/-- A uniform element of `E` from the model's coins (three uniform words). -/
def coinE : OracleComp RandomPermutationOracles E := do
  return E.ofLimbs (K.ofLane (← coinWord)) (K.ofLane (← coinWord)) (K.ofLane (← coinWord))

/-- `n` uniform elements of `E`. -/
def coinEs (n : ℕ) : OracleComp RandomPermutationOracles (List E) := (List.range n).mapM fun _ ↦ coinE

/-! ### The ideal PCS -/

/-- **A simulator of the PCS** in the programmable random-permutation model: its own state and initial state, and
its opening simulator, which sees only the commitment and the claim; it runs on the whole state, so it may read
and program the permutation's edges. -/
structure PcsSimulator where
  Aux : Type
  aux₀ : Aux
  simOpen : Commitment → Claim → StateT (Edges × Aux) ProbComp (Option Compile.Proof)

namespace PcsSimulator

variable (sim : PcsSimulator)

/-- The simulator's state: the permutation's edges and its own. -/
abbrev S : Type := Edges × sim.Aux

/-- The initial state: no edge. -/
def s₀ : sim.S := ([], sim.aux₀)

/-- The simulator's oracle: the model's, on its state's edges (programmed where `simOpen` wrote them). -/
noncomputable def oracle : QueryImpl RandomPermutationOracles (StateT sim.S ProbComp) := edgeOracle

/-- The simulator's permutation `π`. -/
noncomputable def perm : KeccakState → StateT sim.S ProbComp KeccakState := edgePerm

/-- **The ideal PCS**: a commitment's root uniform, independent of the table, its out-of-domain answer the
table's polynomial at the root's point (`oodPointWith` over the simulator's permutation); an opening the opening
simulator's. -/
noncomputable def idealPcs : PcsOps (StateT sim.S ProbComp) Unit where
  commit μ table := do
    let root ← simulateQ sim.oracle sampleDigest
    let z ← oodPointWith sim.perm μ root
    return ((), ⟨root, tableEval table z⟩)
  openClaim _ c claim := sim.simOpen c claim

end PcsSimulator

/-! ### The hypothesis on the PCS -/

/-- **The hybrid experiment**: the honest prover's proof of `stmt` from `w` with uniform coins, its secret tables
committed and opened by the ideal PCS, then the distinguisher, every query answered by the simulator. -/
noncomputable def hybridExperiment (sim : PcsSimulator) (stmt : Statement) (w : Secret) (D : Distinguisher) :
    ProbComp Bool :=
  (do
    let coins ← simulateQ sim.oracle sampleCoins
    let circuit := membership logRows
    let proof ← proveWithPcs sim.perm sim.idealPcs nonceFuel circuit stmt
      (circuit.cells (membershipInputs w)) coins
    simulateQ sim.oracle (D proof)).run' sim.s₀

/-- **The PCS is zero-knowledge for the prover's use of it** (the hypothesis): the real experiment and the hybrid
of the simulator `sim` differ by at most `εpcs Q` for every statement and witness of the relation and every
distinguisher of at most `Q` calls of `π`, `π⁻¹`. -/
def PcsZeroKnowledge (sim : PcsSimulator) (εpcs : ℕ → ℝ≥0∞) : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w →
  ∀ (D : Distinguisher) (Q : ℕ), (∀ proof, QueryCostAtMost (D proof) permutationCallCost Q) →
    Pr{let b ← realExperiment stmt w D}[b = true] ≤ Pr{let b ← hybridExperiment sim stmt w D}[b = true] + εpcs Q ∧
      Pr{let b ← hybridExperiment sim stmt w D}[b = true] ≤ Pr{let b ← realExperiment stmt w D}[b = true] + εpcs Q

/-! ### The revealed scalars -/

/-- **The challenges a proof's revealed scalars depend on**: the out-of-domain points of `W`, `H`, `Q`, `G` and the
chain's five challenges. -/
structure Challenges where
  zW : List E
  zH : List E
  zQ : List E
  zG : List E
  α : E
  β : E
  γ : E
  t : E
  ρ : E

/-- The public wiring polynomial at `t` (`rowValues`' `next`). -/
def wiringValue (circuit : Circuit) (t : E) : E :=
  novelEval circuit.wiringTable 0 1 ((digitsOf t (cellVars circuit.logRows)).take (cellVars circuit.logRows))

/-- **A revealed scalar, as a query**: the out-of-domain answer of `W` at `z`; of `H`, `Q`, `G` (tables at
`α, β, γ`) at `z`; the row value `a_j` at `t`; `Q`'s and `G`'s values at the points of the reduction's claims at
`α, β, γ, t, ρ`. -/
inductive Reveal where
  | oodW (z : List E)
  | oodH (α β γ : E) (z : List E)
  | oodQ (α β γ : E) (z : List E)
  | oodG (α β γ : E) (z : List E)
  | value (j : Fin 4) (t : E)
  | qValue (α β γ t ρ : E)
  | gValue (α β γ t ρ : E)

/-- **The prover's answer to a reveal query**, for the circuit `circuit`, the statement `stmt`, the circuit's cells
`cells₀` and the randomness `coins`: the table's polynomial at the point (`Q`'s and `G`'s at the reduction's points,
the row values `a` the prover's at `t`, `next` the public `wiringValue`, `Q`'s and `G`'s values zero; zero if the
reduction rejects). -/
def revealAnswer (circuit : Circuit) (stmt : Statement) (cells₀ : Array K) (coins : Coins) : Reveal → E
  | .oodW z => tableEval (witnessTable circuit cells₀ coins) z
  | .oodH α β γ z => tableEval (quotientTables circuit cells₀ coins α β γ).1 z
  | .oodQ α β γ z => tableEval (quotientTables circuit cells₀ coins α β γ).2.1 z
  | .oodG α β γ z => tableEval (quotientTables circuit cells₀ coins α β γ).2.2 z
  | .value j t => (rowValues circuit cells₀ coins t).1[j]
  | .qValue α β γ t ρ =>
    ((claimsAt circuit.logRows stmt α β γ t ρ (rowValues circuit cells₀ coins t).1 (wiringValue circuit t) 0
        0).map fun cl ↦ tableEval (quotientTables circuit cells₀ coins α β γ).2.1 cl.q.point).getD 0
  | .gValue α β γ t ρ =>
    ((claimsAt circuit.logRows stmt α β γ t ρ (rowValues circuit cells₀ coins t).1 (wiringValue circuit t) 0
        0).map fun cl ↦ tableEval (quotientTables circuit cells₀ coins α β γ).2.2 cl.g.point).getD 0

/-- **The ten reveal queries of the challenges `c`**, in the order the simulator draws them (`challengePhase`): the
out-of-domain answers of `W`, `Q`, `G`, `H`, the row values `a_1, a_2, a_3, a_0`, `Q`'s and `G`'s values. (The
order is the simulator's: each scalar that a Fiat–Shamir input must be unpredictable in is drawn last before
that input.) -/
def revealQueries (c : Challenges) : List Reveal :=
  [.oodW c.zW, .oodQ c.α c.β c.γ c.zQ, .oodG c.α c.β c.γ c.zG, .oodH c.α c.β c.γ c.zH, .value 1 c.t,
    .value 2 c.t, .value 3 c.t, .value 0 c.t, .qValue c.α c.β c.γ c.t c.ρ, .gValue c.α c.β c.γ c.t c.ρ]

/-- **The scalars a proof reveals** besides the roots, `next` (the public wiring's) and `H`'s value (which the
others determine), for the membership circuit's cells `cells₀`, the randomness `coins` and the challenges `c`: the
four out-of-domain answers, the four `a_j`, then `Q`'s and `G`'s values at their points (the reduction's, after
`ρ`; zero if it rejects). -/
def revealed (stmt : Statement) (cells₀ : Array K) (coins : Coins) (c : Challenges) : List E :=
  (revealQueries c).map (revealAnswer (membership logRows) stmt cells₀ coins)

/-- Uniform challenges: the points of `m + 1`, `m + 3`, `m + 4`, `m + 1` uniform coordinates, and five uniform
elements, drawn in the order of the reduction (`W`'s point, `α, β, γ`, the parts' points, `t`, `ρ`). -/
noncomputable def sampleChallenges : ProbComp Challenges := runWithRandomPermutation do
  let m := cellVars logRows
  let zW ← coinEs (m + 1)
  let α ← coinE
  let β ← coinE
  let γ ← coinE
  let zH ← coinEs (m + 3)
  let zQ ← coinEs (m + 4)
  let zG ← coinEs (m + 1)
  let t ← coinE
  let ρ ← coinE
  return ⟨zW, zH, zQ, zG, α, β, γ, t, ρ⟩

/-- **The revealed scalars are uniform at the challenges `c`**: with uniform randomness they are ten uniform
elements of `E`. -/
def UniformAt (stmt : Statement) (cells₀ : Array K) (c : Challenges) : Prop :=
  ∀ r : List E, Pr{let x ← runWithRandomPermutation (do return revealed stmt cells₀ (← sampleCoins) c)}[x = r] =
    Pr{let x ← runWithRandomPermutation (coinEs 10)}[x = r]

/-- **The protocol's randomness hides the revealed scalars** (the hypothesis on the rank conditions of
`HIDING.md`): for every statement and witness of the relation, the revealed scalars are uniform at all but a set
of challenges of probability at most `εr`. -/
def RevealedUniform (εr : ℝ≥0∞) : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w →
    Pr{let c ← sampleChallenges}[¬ UniformAt stmt ((membership logRows).cells (membershipInputs w)) c] ≤ εr

/-! ### The simulator -/

/-- What the challenge phase leaves for the openings: the circuit's commitment and tree, the reduction's proof,
the commitments and claims (`none` if the reduction rejects). -/
structure PhaseOut where
  indexTree : LeanVM.Prover.Tree
  index : Commitment
  proof : ReductionProof
  reduced : Option Reduced

/-- **The challenge phase** of a prover whose revealed scalars come from `rv` (the honest prover's: `revealAnswer`;
the simulator's: uniform), over the model's permutation: the circuit's commitment (public); each secret table's
root uniform, its out-of-domain point from the root, its out-of-domain answer from `rv`; the reduction's chain
(`α, β, γ` after `W`, `t` after `H`, `Q`, `G`), the four `a_j` from `rv`, `next` public, `ρ`, then `Q`'s and `G`'s
values from `rv`; the challenges, and the proof, commitments and claims. -/
noncomputable def challengePhase {A : Type} (circuit : Circuit) (stmt : Statement)
    (rv : Reveal → StateT (Edges × A) ProbComp E) : StateT (Edges × A) ProbComp (Challenges × PhaseOut) := do
  let mv := cellVars circuit.logRows
  let (indexTree, index) ← commitmentWith edgePerm mv circuit.wiringTable
  let rW ← simulateQ edgeOracle sampleDigest
  let zW ← oodPointWith edgePerm (mv + 1) rW
  let c ← Chain.startWith edgePerm (label index stmt)
  let oW ← rv (.oodW zW)
  let wCom : Commitment := ⟨rW, oW⟩
  let wS := CommitmentScalars.of wCom
  let c := c.absorbCommitment wS
  let (α, c) ← c.squeezeWith edgePerm
  let (β, c) ← c.squeezeWith edgePerm
  let (γ, c) ← c.squeezeWith edgePerm
  let rH ← simulateQ edgeOracle sampleDigest
  let zH ← oodPointWith edgePerm (mv + 3) rH
  let rQ ← simulateQ edgeOracle sampleDigest
  let zQ ← oodPointWith edgePerm (mv + 4) rQ
  let rG ← simulateQ edgeOracle sampleDigest
  let zG ← oodPointWith edgePerm (mv + 1) rG
  let oQ ← rv (.oodQ α β γ zQ)
  let oG ← rv (.oodG α β γ zG)
  let oH ← rv (.oodH α β γ zH)
  let hCom : Commitment := ⟨rH, oH⟩
  let qCom : Commitment := ⟨rQ, oQ⟩
  let gCom : Commitment := ⟨rG, oG⟩
  let hS := CommitmentScalars.of hCom
  let qS := CommitmentScalars.of qCom
  let gS := CommitmentScalars.of gCom
  let c := ((c.absorbCommitment hS).absorbCommitment qS).absorbCommitment gS
  let (t, c) ← c.squeezeWith edgePerm
  let a1 ← rv (.value 1 t)
  let a2 ← rv (.value 2 t)
  let a3 ← rv (.value 3 t)
  let a0 ← rv (.value 0 t)
  let a : Vector E 4 := #v[a0, a1, a2, a3]
  let next := wiringValue circuit t
  let c := (a.toList.foldl Chain.absorb c).absorb next
  let (ρ, _) ← c.squeezeWith edgePerm
  let vq ← rv (.qValue α β γ t ρ)
  let vg ← rv (.gValue α β γ t ρ)
  return (⟨zW, zH, zQ, zG, α, β, γ, t, ρ⟩,
    ⟨indexTree, index, ⟨wS, hS, qS, gS, a, next, vq, vg⟩,
      (claimsAt circuit.logRows stmt α β γ t ρ a next vq vg).map fun cl ↦ ⟨⟨wCom, hCom, qCom, gCom⟩, cl⟩⟩)

/-- **The openings**: the wiring claim by the real WHIR prover (the public table and the circuit's tree), the five
secret claims by the opening simulator; `none` if the reduction rejected or an opening fails. -/
noncomputable def finishOpenings (sim : PcsSimulator) (circuit : Circuit) (out : PhaseOut) :
    StateT sim.S ProbComp (Option Proof) :=
  match out.reduced with
  | none => return none
  | some r => do
    let some oW ← sim.simOpen r.commitments.witness r.claims.witness | return none
    let some oσ ← proveClaimWith sim.perm nonceFuel out.indexTree circuit.wiringTable out.index r.claims.wiring
      | return none
    let some oH ← sim.simOpen r.commitments.h r.claims.h | return none
    let some oQ ← sim.simOpen r.commitments.q r.claims.q | return none
    let some oG ← sim.simOpen r.commitments.g r.claims.g | return none
    let some oS ← sim.simOpen r.commitments.h r.claims.sum | return none
    return some ⟨out.proof, ⟨oW, oσ, oH, oQ, oG, oS⟩⟩

/-- The simulator's revealed scalars: each uniform, from the model's coins. -/
noncomputable def uniformReveal {A : Type} (_ : Reveal) : StateT (Edges × A) ProbComp E :=
  simulateQ edgeOracle coinE

/-- **The simulator** of the PCS simulator `sim`: it reads the statement, never the witness. The challenge phase
with uniform revealed scalars (`challengePhase`, `uniformReveal`), then the openings (`finishOpenings`). -/
noncomputable def zkSimulator (sim : PcsSimulator) (stmt : Statement) : StateT sim.S ProbComp (Option Proof) := do
  let (_, out) ← challengePhase (membership logRows) stmt uniformReveal
  finishOpenings sim (membership logRows) out

/-! ### The hypothesis on the model's Fiat–Shamir challenges -/

/-- **The simulator's challenges are near-uniform** (the random-permutation model's freshness bound on the
transcript): from no edge, the challenges of the simulator's challenge phase satisfy every event with at most the
probability of uniform challenges plus `εfs`. The extra state component `A` is never read by the phase. -/
def FiatShamirUniform (εfs : ℝ≥0∞) : Prop :=
  ∀ (A : Type) (a₀ : A) (stmt : Statement) (B : Challenges → Prop),
    Pr{let x ← (challengePhase (A := A) (membership logRows) stmt uniformReveal).run' ([], a₀)}[B x.1] ≤
      Pr{let c ← sampleChallenges}[B c] + εfs

end PcsQuotient

end
