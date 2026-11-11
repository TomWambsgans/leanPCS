-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- The zero-knowledge statement of `docs/membership/PROTOCOL.md`, "Zero knowledge" (zero knowledge assuming a
-- zero-knowledge PCS), in leanerVM's programmable random-permutation model (branch `mumbai`, commit 6175f1a0, MIT OR
-- Apache-2.0: `Statement/RandomPermutation.lean`, whose lazily sampled permutation the simulator's model is).
module

public import PcsQuotient.Security

/-!
# Zero knowledge, assuming a zero-knowledge PCS

`docs/membership/PROTOCOL.md`, "Zero knowledge": the EIP's PCS is assumed zero-knowledge — a commitment's root and
an opening reveal nothing beyond the commitment's out-of-domain answer and the claim — and the protocol makes
everything else it reveals (the two out-of-domain answers and the three values `X`, `C`, `V + Y` at `t`) uniform with
its randomness (the random rows, the blinding of `h`). The deployed openings are leanVM's WHIR, which is not
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
* **The hybrid experiment** (`hybridExperiment`): the honest prover with the witness, its two secret tables
  committed and opened by the ideal PCS (`proveWithPcs`), the circuit's commitment and the wiring opening (public)
  real, then the distinguisher, every query answered by the simulator's oracle.
* **`PcsZeroKnowledge sim εpcs`**, the hypothesis on the PCS: the real experiment (`Security.lean`'s
  `realExperiment`) and the hybrid differ by at most `εpcs Q` for a distinguisher of `Q` calls.
* **The revealed scalars** (`revealed`): the answers `revealAnswer` gives to the five queries `revealQueries c` of
  the challenges `c`: the two out-of-domain answers and the three values at `t`.
* **`RevealedUniform εr`**, the protocol's own randomness: for every witness, outside a set of challenge tuples of
  probability at most `εr` (the out-of-domain points and `α, β, μ, t, ρ` uniform), the revealed scalars are
  uniform when the prover's randomness is (`PROTOCOL.md`'s two rank conditions).
* **The simulator** (`zkSimulator sim`): it reads no witness. Its challenge phase (`challengePhase`, with
  `uniformReveal`) commits to the circuit (real, public), draws each root uniformly and computes its out-of-domain
  point with the model's permutation, draws each revealed scalar uniformly (`coinE`) where the prover computes it,
  and runs the reduction's chain on them (`α, β, μ, t, ρ`), `next` the public wiring value; then (`finishOpenings`) it
  opens the wiring claim with the real WHIR prover (public table) and the two secret claims with `simOpen`.
* **`FiatShamirUniform εfs`**, the random-permutation model's Fiat–Shamir challenges: in the simulator's challenge
  phase (uniform roots and uniform revealed scalars, the lazily sampled permutation, after the circuit's
  commitment), the challenges are within `εfs` of `sampleChallenges` on every event. This is a property of the
  model and of the transcript's encoding (each challenge is a Keccak-256 of an input holding a fresh uniform root,
  a fresh uniform scalar or a fresh permutation answer), not of the PCS nor of the witness; it is proved
  (`formal/EndToEnd/ZK`, `fiatShamirUniform_closed`).

**The shape of the statement**, so that the theorem is true and provable:
1. The simulator's oracle is the lazily sampled permutation of the model on the edges component (`edgeOracle`),
   and a PCS simulator only adds its state and its opening simulator, which may read and program edges. (This
   restricts the PCS simulators `PcsZeroKnowledge` may be instantiated with to programming ones: a simulator with an
   oracle of its own, such as an indifferentiability simulator answering fresh queries specially, is not covered.)
2. `revealed` is the map of `revealAnswer` over `revealQueries`, so that the simulator's queries and the prover's
   answers are named; `next` is read through `wiringValue` (equal to `valuesAt`'s by definition). `revealAnswer`,
   `challengePhase` and `finishOpenings` take the circuit (the membership circuit's in `revealed`, `zkSimulator`,
   `FiatShamirUniform`), so that the end theorem's equations never unfold the `2^22`-row circuit.
3. The simulator is in the statement (`zkSimulator`), with its challenge phase separate (`challengePhase`), and a
   third proposition, `FiatShamirUniform`, about that phase. The adaptivity argument (the revealed scalars are
   uniform at every fixed good challenge tuple, while the challenges are hashes of inputs holding the revealed
   scalars) bounds the distance of the hybrid and the simulator by the probability that the simulator's own
   challenges are bad; `RevealedUniform` bounds it at uniform challenges, so the simulator's challenges must be
   near-uniform: a random-permutation-model freshness bound on the transcript, **proved** in `formal/EndToEnd/ZK`.
4. The simulator draws each revealed scalar last before the Fiat–Shamir input it must make unpredictable (`W`'s
   answer after the chain's seed, `T`'s after `α, β, μ`, `X` after `C` and `V + Y`); `revealQueries` lists them in
   that order and `sampleChallenges` draws in the reduction's order (the same distributions).

The end theorems (`formal/EndToEnd/ZK`): `PcsQuotient.EndToEnd.zeroKnowledge_pcs` states `ZeroKnowledgeWith` for
`zkSimulator sim` under `PcsZeroKnowledge`, `RevealedUniform` and `FiatShamirUniform`, with
`ζ Q = εpcs Q + εr + εfs`; `zeroKnowledge_pcs_closed` under the first two only, `ζ Q = εpcs Q + εr + εfs₀`.
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

/-- **The challenges a proof's revealed scalars depend on**: the out-of-domain points of `W` and `T` and the
chain's challenges. -/
structure Challenges where
  zW : List E
  zT : List E
  α : E
  β : E
  μ : E
  t : E
  ρ : E

/-- The public wiring polynomial at `t` (`valuesAt`' `next`). -/
def wiringValue (circuit : Circuit) (t : E) : E :=
  novelEval circuit.wiringTable 0 1 ((digitsOf t (cellVars circuit.logRows)).take (cellVars circuit.logRows))

/-- **A revealed scalar, as a query**: the out-of-domain answer of `W` at `z`; of `T` (its table at `α, β, μ`) at
`z`; the value `j` of `X`, `C`, `V + Y` at `t`. -/
inductive Reveal where
  | oodW (z : List E)
  | oodT (α β μ : E) (z : List E)
  | value (j : Fin 3) (t : E)

/-- **The prover's answer to a reveal query**, for the circuit `circuit`, the statement `stmt`, the circuit's cells
`cells₀` and the randomness `coins`: the table's polynomial at the point, or the prover's value at `t`. -/
def revealAnswer (circuit : Circuit) (stmt : Statement) (cells₀ : Array K) (coins : Coins) : Reveal → E
  | .oodW z => tableEval (witnessTable circuit cells₀ coins) z
  | .oodT α β μ z => tableEval (quotientTable circuit stmt cells₀ coins α β μ) z
  | .value j t => (valuesAt circuit cells₀ coins t).1[j]

/-- **The five reveal queries of the challenges `c`**, in the order the simulator draws them (`challengePhase`):
the out-of-domain answers of `W` and `T`, the values `C`, `V + Y`, then `X`. (Each scalar that a Fiat–Shamir input
must be unpredictable in is drawn last before that input.) -/
def revealQueries (c : Challenges) : List Reveal :=
  [.oodW c.zW, .oodT c.α c.β c.μ c.zT, .value 1 c.t, .value 2 c.t, .value 0 c.t]

/-- **The scalars a proof reveals** besides the roots and `next` (the public wiring's), for the membership
circuit's cells `cells₀`, the randomness `coins` and the challenges `c`: the two out-of-domain answers and the
three values at `t`. -/
def revealed (stmt : Statement) (cells₀ : Array K) (coins : Coins) (c : Challenges) : List E :=
  (revealQueries c).map (revealAnswer (membership logRows) stmt cells₀ coins)

/-- Uniform challenges: the points of `m` and `m + 4` uniform coordinates, and five uniform elements, drawn in the
order of the reduction (`W`'s point, `α, β, μ`, `T`'s point, `t`, `ρ`). -/
noncomputable def sampleChallenges : ProbComp Challenges := runWithRandomPermutation do
  let m := cellVars logRows
  let zW ← coinEs m
  let α ← coinE
  let β ← coinE
  let μ ← coinE
  let zT ← coinEs (m + 4)
  let t ← coinE
  let ρ ← coinE
  return ⟨zW, zT, α, β, μ, t, ρ⟩

/-- **The revealed scalars are uniform at the challenges `c`**: with uniform randomness they are five uniform
elements of `E`. -/
def UniformAt (stmt : Statement) (cells₀ : Array K) (c : Challenges) : Prop :=
  ∀ r : List E, Pr{let x ← runWithRandomPermutation (do return revealed stmt cells₀ (← sampleCoins) c)}[x = r] =
    Pr{let x ← runWithRandomPermutation (coinEs 5)}[x = r]

/-- **The protocol's randomness hides the revealed scalars** (`PROTOCOL.md`'s rank conditions): for every
statement and witness of the relation, the revealed scalars are uniform at all but a set of challenges of
probability at most `εr`. -/
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
(`α, β, μ` after `W`, `t` after `T`), the three values from `rv`, `next` public, `ρ`; the challenges, and the proof,
commitments and claims. -/
noncomputable def challengePhase {A : Type} (circuit : Circuit) (stmt : Statement)
    (rv : Reveal → StateT (Edges × A) ProbComp E) : StateT (Edges × A) ProbComp (Challenges × PhaseOut) := do
  let mv := cellVars circuit.logRows
  let (indexTree, index) ← commitmentWith edgePerm mv circuit.wiringTable
  let rW ← simulateQ edgeOracle sampleDigest
  let zW ← oodPointWith edgePerm mv rW
  let c ← Chain.startWith edgePerm (label index stmt)
  let oW ← rv (.oodW zW)
  let wCom : Commitment := ⟨rW, oW⟩
  let wS := CommitmentScalars.of wCom
  let c := c.absorbCommitment wS
  let (α, c) ← c.squeezeWith edgePerm
  let (β, c) ← c.squeezeWith edgePerm
  let (μ, c) ← c.squeezeWith edgePerm
  let rT ← simulateQ edgeOracle sampleDigest
  let zT ← oodPointWith edgePerm (mv + 4) rT
  let oT ← rv (.oodT α β μ zT)
  let tCom : Commitment := ⟨rT, oT⟩
  let tS := CommitmentScalars.of tCom
  let c := c.absorbCommitment tS
  let (t, c) ← c.squeezeWith edgePerm
  let v1 ← rv (.value 1 t)
  let v2 ← rv (.value 2 t)
  let v0 ← rv (.value 0 t)
  let vals : Vector E 3 := #v[v0, v1, v2]
  let next := wiringValue circuit t
  let c := (vals.toList.foldl Chain.absorb c).absorb next
  let (ρ, _) ← c.squeezeWith edgePerm
  return (⟨zW, zT, α, β, μ, t, ρ⟩,
    ⟨indexTree, index, ⟨wS, tS, vals, next⟩,
      (claimsAt circuit.logRows stmt α β μ t ρ vals next).map fun cl ↦ ⟨⟨wCom, tCom⟩, cl⟩⟩)

/-- **The openings**: the wiring claim by the real WHIR prover (the public table and the circuit's tree), the two
secret claims by the opening simulator; `none` if the reduction rejected or an opening fails. -/
noncomputable def finishOpenings (sim : PcsSimulator) (circuit : Circuit) (out : PhaseOut) :
    StateT sim.S ProbComp (Option Proof) :=
  match out.reduced with
  | none => return none
  | some r => do
    let some oW ← sim.simOpen r.commitments.witness r.claims.witness | return none
    let some oσ ← proveClaimWith sim.perm nonceFuel out.indexTree circuit.wiringTable out.index r.claims.wiring
      | return none
    let some oT ← sim.simOpen r.commitments.table r.claims.copy | return none
    return some ⟨out.proof, ⟨oW, oσ, oT⟩⟩

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
