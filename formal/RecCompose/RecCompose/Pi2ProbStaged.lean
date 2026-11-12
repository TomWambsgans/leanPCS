-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π2's analogue of `formal/UniComplete/UniComplete/
-- ProbExp.lean` (`stagedU`, its stages) and `ProbGrind.lean` (`rejectGood_uni`, the grinding through mumbai's
-- proof-of-work potential), from π2's honest prover (`RecCompose.Pi2Prover`, `crates/leanvm/rec/src/pi2/prover.rs`) and
-- the Statement's contract (`formal/RecStatement`, written with Keccak-256 explicit in `Pi2CompleteH`). Uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls, the
-- logged random oracle and its potential engine, `powPot`, `missProb`, the run at a log's answers.
import RecCompose.Pi2Accepts
import RecCompose.Holds
import RecCompose.Pi2Chain
import UniKeccakComplete.K.ProbGrind

/-!
# π2's completeness experiment, staged (π2v4)

**The P1 class**: π1-rec4's prover is a two-call program `P1k` (Keccak-256 and Keccak-f[1600] its calls) whose run over
the random permutation is `P1` (`Pi2ExperimentLe`).

**`pi2Staged D C Fa P1k input : Pi2Staged`**, π2's experiment's stages over the two calls:

* `A` (`stageA`): the setup, `P1k`, π1-rec4's graph on its proof (`a1`), then π2's prover up to `α`: its setup, IV, π1's
  claims, the witness it takes, the seed (the frame words last), the public values, `W`'s commitment, out-of-domain
  point (`oodPointM`), root and answer (`pre2`); `inp` `α`'s input (`fixLen 88` of the writer's: `88` bytes when the
  values match the real circuit's reads);
* the three chained answers `α, β, γ`; `B` (`stageB`) `Q`'s stack, commitment, out-of-domain point, root and answer
  (`mid2`); `t`'s query on the writer's input; `C` (`stageC`) the values at `t` and `ρ` (`post2`), then `restC`: the
  four openings and the contract (`Pi2H.verifierWithH`); a proof of `P1k`'s none is the pair `(false, false)`;
* the priors: `(roots, w, pub)` for the triple (`badSet2`: the copy argument's `BadCopy`), with the triple for `t`
  (`badT2`: `¬ BadCopy ∧ BadT`), `(roots, t)` for `ρ` (`badR2`: `BadRho`).

**The named inputs** (statements about the explicit `pi2Staged`): `Pi2ExperimentLe`, `Pi2RunDuplex`, `Pi2RunCost N`;
the other helpers' `Pi2Pi1Openings` (π1's three claims in the contract open) and `Pi2WitnessExists` (the circuit
compiler's completeness).

**The grinding**: `rejectGood_of_pot` (mumbai's potential, as `ProbGrind`), `pot_of_rejects` (from the core at every
pure `(H, F)`: `Pi2SimCore.rejects_at_good`), `grind_le`. **Postconditions** of the stages (`holds_restC`,
`holds_stageC`, `holds_stageB`): off `GAccA` (π1's prover returned a proof the graph accepted) the verdict rejects.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2G

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM LeanVM.Rpm
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom
open E2ECompleteness (ro runAt HashOK Cache)
open UniKeccakComplete.Prob (GoodL winState one_le_powPot_of_pcs_none)
open Pi2S Pi2K Pi2P Pi2E
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## π2's prover, cut at `α` and at `t` -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- **Before `α`**: the public values, `W`'s stack, commitment, out-of-domain point, root and answer
(`pi2ProveStreamWith`'s first lines). -/
def pre2 (G : RecPiop.Circuit E) (oodPt : ℕ → Digest → m (List E)) (reads : List Read) (values : List PublicValue)
    (w : ℕ → K) : UniComplete.WrM m (Array K × LeanVM.Prover.Tree × List E) := do
  sendPublic (reads.zip values)
  let wStack := padStack (stackVars G.logN).1 fun i ↦ (wTableB G w).getD i 0
  let wTree ← (StateT.lift (E2ECompleteness.commitWithH H (stackVars G.logN).1 wStack) :
    UniComplete.WrM m LeanVM.Prover.Tree)
  let wz ← (StateT.lift (oodPt (stackVars G.logN).1 wTree.root) : UniComplete.WrM m (List E))
  UniComplete.sendRoot (UniStatement.rootHalves wTree.root)
  UniComplete.sendScalar (pi2OodAt wStack wz)
  return (wStack, wTree, wz)

/-- **From `γ` to `t`**: `Q`'s stack, commitment, out-of-domain point, root and answer. -/
def mid2 (G : RecPiop.Circuit E) (S : CoreSpec E) (oodPt : ℕ → Digest → m (List E)) (pubs : List E) (w : ℕ → K)
    (α β γ : E) : UniComplete.WrM m (Array K × LeanVM.Prover.Tree × List E) := do
  let qStack := padStack (stackVars G.logN).2.1 (qEntry G.logN (mulX (hNovel G w α β))
    (qNovel G w α β γ (phiOn S pubs γ)) (pNovel G w) (qpNovel G w γ))
  let qTree ← (StateT.lift (E2ECompleteness.commitWithH H (stackVars G.logN).2.1 qStack) :
    UniComplete.WrM m LeanVM.Prover.Tree)
  let qz ← (StateT.lift (oodPt (stackVars G.logN).2.1 qTree.root) : UniComplete.WrM m (List E))
  UniComplete.sendRoot (UniStatement.rootHalves qTree.root)
  UniComplete.sendScalar (pi2OodAt qStack qz)
  return (qStack, qTree, qz)

/-- **After `t`**: the values at `t`, `ρ`, the output. -/
def post2 (G : RecPiop.Circuit E) (setupStack : Array K) (input : List UInt8) (values : List PublicValue) (w : ℕ → K)
    (wS : Array K) (wT : LeanVM.Prover.Tree) (qS : Array K) (qT : LeanVM.Prover.Tree) (α β γ t : E)
    (wP qP : List E) : UniComplete.WrM m Pi2Out := do
  let a := foldValues G.logN G.logW (wTableB G w) t
  let ξ := xiOf G.logN setupStack β t
  let sv := sOf G.logN (pNovel G w) t
  UniComplete.sendScalars (a ++ [ξ, sv])
  let ρ ← UniComplete.sampleW H
  let c ← get
  return ⟨c.stream, wS, wT, qS, qT, ⟨publicScalarsOf input values, α, β, γ, t, a, ξ, sv, ρ⟩, wP, qP⟩

end With

/-- The writer after a challenge whose hash is `s` (`sampleW`'s update). -/
def absorbW (w : UniComplete.Wr) (s : Digest) : UniComplete.Wr :=
  { w with absorbed := w.stream.size, state := s, challenges := w.challenges.push (chalP s) }

/-- `x` if it has `L` bytes, else `L` zeros. -/
def fixLen (L : ℕ) (x : List UInt8) : List UInt8 := if x.length = L then x else List.replicate L 0

theorem fixLen_length (L : ℕ) (x : List UInt8) : (fixLen L x).length = L := by
  unfold fixLen
  split_ifs with h
  · exact h
  · exact List.length_replicate

/-! ## The experiment with Keccak-256 explicit -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- **π2's completeness experiment with Keccak-256 explicit**: the setup, π1's proof `p1o`, π1-rec3's graph on it, π2's
honest prover (`nonceFuel` its search), the contract. -/
noncomputable def expW2 (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (p1o : m (Option UniKeccak.KeccakProof)) (input : Vector UInt8 32) : m (Bool × Bool) := do
  let trees ← Pi2H.setupTreesWithH H F D
  match ← p1o with
  | none => return (false, false)
  | some p1 =>
    let a1 ← Pi2H.pi1GraphVerifierWithH H F D trees.roots.pi1 input p1
    match ← pi2ProverWith H F D C.G Fa.pubOf PcsQuotient.nonceFuel input p1 with
    | none => return (a1, false)
    | some p2 => return (a1, ← Pi2H.verifierWithH H F D trees.roots input p2)

/-- What stage `A` carries: the setup, π1's proof and the graph's verdict, π2's prover's roots, setup tree, witness,
`W`'s stack and tree, the writer before `α`, `W`'s out-of-domain point. -/
structure StA where
  trees : RecSetupTrees
  p1 : Option UniKeccak.KeccakProof
  a1 : Bool
  roots : RecSetupRoots
  setupTree : LeanVM.Prover.Tree
  claims : List (List (List UInt8))
  vw : List PublicValue × (ℕ → K)
  wS : Array K
  wT : LeanVM.Prover.Tree
  wr : UniComplete.Wr
  wP : List E

/-- What stage `B` carries: `A`'s, the triple, `Q`'s stack and tree, the writer before `t`, `Q`'s out-of-domain
point. -/
structure StB where
  a : StA
  α : E
  β : E
  γ : E
  qS : Array K
  qT : LeanVM.Prover.Tree
  wr : UniComplete.Wr
  qP : List E

/-- **Stage A**: the setup, π1's proof, the graph, π2's prover up to `α`. -/
noncomputable def stageA (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (p1o : m (Option UniKeccak.KeccakProof)) (input : Vector UInt8 32) : m StA := do
  let trees ← Pi2H.setupTreesWithH H F D
  match ← p1o with
  | none => return ⟨trees, none, false, trees.roots, trees.pi2, [], ([], fun _ ↦ 0), #[], trees.pi2,
      UniComplete.Wr.start default, []⟩
  | some p1 =>
    let a1 ← Pi2H.pi1GraphVerifierWithH H F D trees.roots.pi1 input p1
    let tr ← Pi2H.setupTreesWithH H F D
    let iv ← Pi2H.ivOfH H D tr.roots
    let claims := pi1ClaimsOf D tr.roots.pi1 input p1.stream
    let vw := pi2Choice D C.G Fa.pubOf tr.roots input p1.stream claims
    let seed ← H (RecStatement.name ++ iv ++ input.toList ++ frameWordsOf vw.1)
    let (ws, wr) ← (pre2 H (C.G tr.roots) (WhirBridge.Pcs.oodPointM H) (D.circuitAt tr.roots.pi1).circuit.reads vw.1
      vw.2).run (UniComplete.Wr.start seed)
    return ⟨trees, some p1, a1, tr.roots, tr.pi2, claims, vw, ws.1, ws.2.1, wr, ws.2.2⟩

/-- **Stage B**: after `α, β, γ` (their hashes `s₁, s₂, s₃`), `Q`. -/
def stageB (D : RecDeployment) (C : Pi2Circuits D) (input : Vector UInt8 32) (a : StA) (s₁ s₂ s₃ : Digest) :
    m StB := do
  let w3 := absorbW (absorbW (absorbW a.wr s₁) s₂) s₃
  let (qs, wr) ← (mid2 H (C.G a.roots) (Spec.of (D.circuitAt a.roots.pi1).circuit).core (WhirBridge.Pcs.oodPointM H)
    (publicScalarsOf input.toList a.vw.1) a.vw.2 (chalP s₁) (chalP s₂) (chalP s₃)).run w3
  return ⟨a, chalP s₁, chalP s₂, chalP s₃, qs.1, qs.2.1, wr, qs.2.2⟩

/-- **After `ρ`**: π2's four openings on the prover's output, the contract on the proof (π1's claims and openings
first); the verdicts. -/
noncomputable def restC (D : RecDeployment) (C : Pi2Circuits D) (input : Vector UInt8 32) (b : StB)
    (p1 : UniKeccak.KeccakProof) (out : Pi2Out) : m (Bool × Bool) := do
  let G := C.G b.a.roots
  let c := D.circuitAt b.a.roots.pi1
  let o := (Spec.of c.circuit).core.run out.inputs
  let pW ← PcsZ.pcsProveZH H F PcsQuotient.nonceFuel (stackVars G.logN).1 out.wPoint out.wTree out.wStack
    o.witnessPoint o.fold
  let pS ← PcsZ.pcsProveZH H F PcsQuotient.nonceFuel (stackVars G.logN).2.2
    (UniKeccakComplete.pcsZ (stackVars G.logN).2.2 b.a.setupTree.root) b.a.setupTree
    (padStack (stackVars G.logN).2.2 fun i ↦ c.setupStack.getD i 0) o.setupPoint out.inputs.ξ
  let pQ1 ← PcsZ.pcsProveZH H F PcsQuotient.nonceFuel (stackVars G.logN).2.1 out.qPoint out.qTree out.qStack
    o.quotientPoint o.quotientValue
  let pQ2 ← PcsZ.pcsProveZH H F PcsQuotient.nonceFuel (stackVars G.logN).2.1 out.qPoint out.qTree out.qStack
    o.pushesPoint o.pushesValue
  match pW, pS, pQ1, pQ2 with
  | some x, some y, some z1, some z2 =>
    let v ← Pi2H.verifierWithH H F D b.a.trees.roots input
      ⟨out.stream, b.a.claims, p1.c1, p1.c2, p1.setup, x, y, z1, z2⟩
    return (b.a.a1, v)
  | _, _, _, _ => return (b.a.a1, false)

/-- **Stage C**: after `t` (its hash `st`), the rest of the prover (the values at `t`, `ρ` drawn in `post2`), its
openings and the contract (`restC`); the verdicts and `ρ` with its prior `(roots, t)`. -/
noncomputable def stageC (D : RecDeployment) (C : Pi2Circuits D) (input : Vector UInt8 32) (b : StB) (st : Digest) :
    m ((Bool × Bool) × ((RecSetupRoots × E) × E)) := do
  match b.a.p1 with
  | none => return ((false, false), ((b.a.roots, chalP st), 0))
  | some p1 =>
    let (out, _) ← (post2 H (C.G b.a.roots) (D.circuitAt b.a.roots.pi1).setupStack input.toList b.a.vw.1 b.a.vw.2
      b.a.wS b.a.wT b.qS b.qT b.α b.β b.γ (chalP st) b.a.wP b.qP).run (absorbW b.wr st)
    let v ← restC H F D C input b p1 out
    return (v, ((b.a.roots, chalP st), out.inputs.ρ))

end With

/-- The prior of the triple: the prover's roots, its witness, the public limbs. -/
abbrev Pr2 : Type := RecSetupRoots × (ℕ → K) × (ℕ → List E)

/-- **π2's experiment's stages over the two calls.** -/
noncomputable def pi2Staged (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : OracleComp KeccakCalls (Option UniKeccak.KeccakProof)) (input : Vector UInt8 32) : Pi2Staged where
  α := StA
  β := StB
  ρ := Pr2
  τ := Pr2 × E × E × E
  υ := RecSetupRoots × E
  inp a := fixLen 88 (UniKeccakComplete.Prob.tInput a.wr)
  pr a := (a.roots, a.vw.2, Fa.pubOf a.roots (publicScalarsOf input.toList a.vw.1))
  A := stageA callKeccak256 callKeccakF1600 D C Fa P1k input
  B := stageB callKeccak256 D C input
  tin b := UniKeccakComplete.Prob.tInput b.wr
  prT b := ((b.a.roots, b.a.vw.2, Fa.pubOf b.a.roots (publicScalarsOf input.toList b.a.vw.1)), b.α, b.β, b.γ)
  C := stageC callKeccak256 callKeccakF1600 D C input

open Classical in
/-- **The bad triples**: the copy argument's at the prior's circuit, witness and public limbs. -/
noncomputable def badSet2 (C' : RecSetupRoots → RecPiop.Circuit E) (p : Pr2) : Finset (E × E × E) :=
  Finset.univ.filter fun v ↦ BadCopy (C' p.1) p.2.1 p.2.2 v.1 v.2.1 v.2.2

/-- **The bad `t`**: for a witness, off the bad triples, `BadT`. -/
def badT2 (C' : RecSetupRoots → RecPiop.Circuit E) (fp : Pr2 × E × E × E) (t : E) : Prop :=
  (C' fp.1.1).Satisfies fp.1.2.2 (RecCircuit.emb fp.1.2.1) ∧ ¬ BadCopy (C' fp.1.1) fp.1.2.1 fp.1.2.2 fp.2.1 fp.2.2.1 fp.2.2.2 ∧ BadT (C' fp.1.1) fp.1.2.1 fp.2.1 fp.2.2.1 fp.2.2.2 t

/-- **The bad `ρ`** (π2v4): `Y_3 = 1 + ρ (1 + Z_V(t))` zero, at the prior's circuit and `t`. -/
def badR2 (C' : RecSetupRoots → RecPiop.Circuit E) (fr : RecSetupRoots × E) (ρ : E) : Prop :=
  BadRho (C' fr.1) fr.2 ρ

/-! ## The named inputs -/

/-- The roots of the setup at a pure `(H, F)`. -/
abbrev rootsH (D : RecDeployment) (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState) : RecSetupRoots :=
  (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Ht) Ft D)).roots

/-- π1's claims as the prover takes them, at a pure `(H, F)`. -/
abbrev claimsH (D : RecDeployment) (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState)
    (input : Vector UInt8 32) (p1 : UniKeccak.KeccakProof) : List (List (List UInt8)) :=
  pi1ClaimsOf D (rootsH D Ht Ft).pi1 input p1.stream

/-- The witness and public values π2's prover takes, at a pure `(H, F)`. -/
noncomputable abbrev vwH (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) (Ht : List UInt8 → Digest)
    (Ft : KeccakState → KeccakState) (input : Vector UInt8 32) (p1 : UniKeccak.KeccakProof) :
    List PublicValue × (ℕ → K) :=
  pi2Choice D C.G Fa.pubOf (rootsH D Ht Ft) input p1.stream (claimsH D Ht Ft input p1)

/-- The honest prover's transcript inputs, at a pure `(H, F)`. -/
noncomputable abbrev inpH (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) (Ht : List UInt8 → Digest)
    (Ft : KeccakState → KeccakState) (input : Vector UInt8 32) (p1 : UniKeccak.KeccakProof) : Inputs E :=
  (outOf D Ht (rootsH D Ht Ft) (C.G (rootsH D Ht Ft)) (pi2Z Ht) input (vwH D C Fa Ht Ft input p1).1
    (vwH D C Fa Ht Ft input p1).2).inputs

/-- **Named: the experiment, staged.** π2's completeness experiment's event (the graph accepting, the contract
rejecting) is at most the staged run's against the random permutation. -/
def Pi2ExperimentLe (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) (P1 : Pi1Prover D)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniKeccak.KeccakProof)) :
    Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q →
    Pr{let v ← recCompletenessExperiment2 D P1 (pi2Prover D C.G Fa.pubOf PcsQuotient.nonceFuel) input rows q}[
      v.1 = true ∧ v.2 = false] ≤
    Pr{let z ← (simulateQ keccakCallsOverRandomPermutation (pi2Staged D C Fa (P1k input rows q) input).run).run' []}[
      z.1.1.1 = true ∧ z.1.1.2 = false]

/-- **Named: the staged run follows the duplex discipline.** -/
def Pi2RunDuplex (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniKeccak.KeccakProof)) :
    Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q → DuplexVm (pi2Staged D C Fa (P1k input rows q) input).run []

/-- **Named: the staged run's block count** is at most `N`. -/
def Pi2RunCost (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniKeccak.KeccakProof))
    (N : ℕ) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q →
    Common.QueryCostAtMost (pi2Staged D C Fa (P1k input rows q) input).run hashBlocks N

/-- **Named: π1's claims in the contract** (deterministic; `pi2_accepts`' `hp3` and `hpi1`): at pure `(H, F)`, on a
π1 proof π1-rec4's graph accepts (its openings over `(H, F)`), the graph makes three claims and the contract's openings
of them, with π1's three opening proofs, accept. -/
def Pi2Pi1Openings (D : RecDeployment) : Prop :=
  ∀ (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState) (input : Vector UInt8 32)
    (p1 : UniKeccak.KeccakProof),
    Id.run (Pi2H.pi1GraphVerifierWithH (m := Id) (Pure.pure ∘ Ht) Ft D (rootsH D Ht Ft).pi1 input p1) = true →
      (claimsH D Ht Ft input p1).length = 3 ∧
      Id.run (Pi2H.pcsOpenWordsH (m := Id) (Pure.pure ∘ Ht) Ft ((claimsH D Ht Ft input p1).getD 0 []) p1.c1) = true ∧
      Id.run (Pi2H.pcsOpenWordsH (m := Id) (Pure.pure ∘ Ht) Ft ((claimsH D Ht Ft input p1).getD 1 []) p1.c2) = true ∧
      Id.run (Pi2H.pcsOpenWordsH (m := Id) (Pure.pure ∘ Ht) Ft ((claimsH D Ht Ft input p1).getD 2 []) p1.setup) = true

/-- **Named: the circuit compiler's completeness** (`pi2_accepts`' `hgood`; `Pi2Witness`'s `Pi2WitnessComplete`): on a
stream whose π1-rec4 graph checks hold, an honest witness exists for the claims the graph makes. -/
def Pi2WitnessExists (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) : Prop :=
  ∀ (roots : RecSetupRoots) (input : Vector UInt8 32) (s : Array UInt8),
    pi1GraphChecks (pi1GraphAt roots.pi1) (D.pi1IvAt roots.pi1) input s = true →
      ∃ vw, Pi2Good D C.G Fa.pubOf roots input s (pi1ClaimsOf D roots.pi1 input s) vw

/-! ## The core at pure functions -/

/-- **The graph's verdict includes its checks.** -/
theorem graphChecks_of_verifierH {H : List UInt8 → Id Digest} {F : KeccakState → Id KeccakState} {D : RecDeployment}
    {roots : UniKeccak.SetupRootsK} {input : Vector UInt8 32} {p1 : UniKeccak.KeccakProof}
    (h : Id.run (Pi2H.pi1GraphVerifierWithH (m := Id) H F D roots input p1) = true) :
    pi1GraphChecks (pi1GraphAt roots) (D.pi1IvAt roots) input p1.stream = true := by
  unfold Pi2H.pi1GraphVerifierWithH at h
  unfold pi1GraphChecks
  split at h
  · exact absurd h (by simp)
  · rename_i out hout
    rw [hout]
    dsimp only
    by_contra hc
    rw [Bool.not_eq_true] at hc
    rw [hc] at h
    exact absurd h (by simp)

/-- **A failed PCS opening** at pure `(H, F)`: the honest PCS prover (at some out-of-domain point `z`) returns none on
a point of its variables. -/
def PcsFails (Hk : List UInt8 → Digest) (F : KeccakState → Id KeccakState) (fuel : ℕ) : Prop :=
  ∃ (n : ℕ) (z : List E) (tree : LeanVM.Prover.Tree) (stack : Array K) (pt : List E) (v : E), pt.length = n ∧
    PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel n z tree stack pt v = none

/-- **π2's honest prover returns none only at a failed opening.** -/
theorem pi2Prover_none {D : RecDeployment} {C : Pi2Circuits D} (Fa : Pi2Facts D C) (Hk : List UInt8 → Digest)
    (F : KeccakState → Id KeccakState) (fuel : ℕ) (input : Vector UInt8 32) (p1 : UniKeccak.KeccakProof)
    (hp : Id.run (pi2ProverWith (m := Id) (Pure.pure ∘ Hk) F D C.G Fa.pubOf fuel input p1) = none) :
    PcsFails Hk F fuel := by
  rw [pi2ProverWith_run] at hp
  simp only at hp
  rw [pi2ProveWith_run] at hp
  simp only at hp
  set roots := (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots
  have hview := view_logN24 Fa roots
  obtain ⟨lW, lS, lQ, lP⟩ := Pi2K.run_points_length (Spec.of (D.circuitAt roots.pi1).circuit).core
    (by rw [spec_core_logN, hview]) (by rw [spec_core_logRow, view_logRow4 Fa roots]) _
  rw [logN_G Fa roots, Pi2W.stackVars_24] at hp
  simp only at hp
  revert hp
  generalize hW : PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel 24 _ _ _ _ _ = rW
  generalize hS : PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel 25 _ _ _ _ _ = rS
  generalize hQ1 : PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel 28 _ _ _ _
    ((Spec.of _).core.run _).quotientValue = rQ1
  generalize hQ2 : PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel 28 _ _ _ _
    ((Spec.of _).core.run _).pushesValue = rQ2
  intro hp
  rcases rW with _ | a
  · exact ⟨_, _, _, _, _, _, lW, hW⟩
  rcases rS with _ | b
  · exact ⟨_, _, _, _, _, _, lS, hS⟩
  rcases rQ1 with _ | c
  · exact ⟨_, _, _, _, _, _, lQ, hQ1⟩
  rcases rQ2 with _ | d
  · exact ⟨_, _, _, _, _, _, lP, hQ2⟩
  simp at hp

/-- **The experiment at `Id`, π1's prover giving none.** -/
theorem expW2_none (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState) (D : RecDeployment)
    (C : Pi2Circuits D) (Fa : Pi2Facts D C) (input : Vector UInt8 32) :
    Id.run (expW2 (m := Id) (Pure.pure ∘ Ht) Ft D C Fa (pure none) input) = (false, false) := rfl

/-- **The experiment at `Id`, π1's prover giving `p1`**: the graph's verdict, and the contract's on π2's proof. -/
theorem expW2_some (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState) (D : RecDeployment)
    (C : Pi2Circuits D) (Fa : Pi2Facts D C) (input : Vector UInt8 32) (p1 : UniKeccak.KeccakProof) :
    Id.run (expW2 (m := Id) (Pure.pure ∘ Ht) Ft D C Fa (pure (some p1)) input) =
      match Id.run (pi2ProverWith (m := Id) (Pure.pure ∘ Ht) Ft D C.G Fa.pubOf PcsQuotient.nonceFuel input p1) with
      | none => (Id.run (Pi2H.pi1GraphVerifierWithH (m := Id) (Pure.pure ∘ Ht) Ft D
          (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Ht) Ft D)).roots.pi1 input p1), false)
      | some p2 => (Id.run (Pi2H.pi1GraphVerifierWithH (m := Id) (Pure.pure ∘ Ht) Ft D
          (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Ht) Ft D)).roots.pi1 input p1),
        (Id.run (Pi2H.contractWithH (m := Id) (Pure.pure ∘ Ht) Ft D
          (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Ht) Ft D)).roots input p2)).1) := by
  unfold expW2
  simp only [pure_bind]
  generalize pi2ProverWith (m := Id) (Pure.pure ∘ Ht) Ft D C.G Fa.pubOf PcsQuotient.nonceFuel input p1 = x
  cases x with
  | none => rfl
  | some p2 => rfl

/-- The run's outcome type of `pi2Staged`. -/
abbrev Z2 : Type := ((Bool × Bool) × ((Pr2 × E × E × E) × E) × ((RecSetupRoots × E) × E)) × (Pr2 × E × E × E)

/-- **The good event**: the graph accepting, the contract rejecting at good challenges (the triple, `t`, `ρ`). -/
def GoodRej (C' : RecSetupRoots → RecPiop.Circuit E) (z : Z2) : Prop :=
  z.1.1.1 = true ∧ z.1.1.2 = false ∧ z.2.2 ∉ badSet2 C' z.2.1 ∧ ¬ badT2 C' z.1.2.1.1 z.1.2.1.2 ∧
    ¬ badR2 C' z.1.2.2.1 z.1.2.2.2

/-! ## The grinding -/

/-- **The grinding, from the core at the log's extension** (`ProbGrind.rejectGood_uni`'s proof): a two-call run of at
most `Q` block calls whose event puts mumbai's proof-of-work potential at one has the event with probability at most
`Q · (1 − 2^-17)^nonceFuel`. -/
theorem rejectGood_of_pot {β : Type} (X : OracleComp KeccakCalls β) (Ev : β → Prop) {Q : ℕ}
    (hQ : Common.QueryCostAtMost X hashBlocks Q)
    (hpot : ∀ (ℓ : Log) (z : β), simulateQ (lookImpl ℓ) X = some z → Ev z →
      1 ≤ powPot Whir.queryGrindingBits PcsQuotient.nonceFuel ℓ) :
    Pr{let z ← (simulateQ ro X).run' ∅}[Ev z] ≤
      (Q : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel := by
  have hfuel : PcsQuotient.nonceFuel ≤ 2 ^ 64 := by norm_num [PcsQuotient.nonceFuel]
  have hstep : LogFreshStepBound (powPot Whir.queryGrindingBits PcsQuotient.nonceFuel)
      (missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) := by
    rw [logFreshStepBound_iff]
    refine ⟨fun ℓ x _ ↦ ?_, fun ℓ s hs' ↦ ?_⟩
    · simp only [powPot_append_inl]
      exact (avg_le_of_le fun _ ↦ le_rfl).trans le_self_add
    · exact powPot_stepF (by decide) (by decide) hfuel ((lookR_eq_none_iff ℓ s).mpr hs')
  have e : Pr{let z ← (simulateQ ro X).run' ∅}[Ev z] = Pr{let z ← (simulateQ loggedRO X).run []}[Ev z.1] := by
    rw [StateT.run'_eq, prEvent_map]
    exact prEvent_run_randomOracle_eq_loggedRO _ (fun (z : β) _ ↦ Ev z)
  rw [e]
  refine (prEvent_run_loggedRO_le_of_freshStepBound hstep _ Q
    (E2ECompleteness.isTotalQueryBound_of_queryCostAtMost hQ) [] (fun (z : β) _ ↦ Ev z) fun z hz hev ↦ ?_).trans ?_
  · have hlook := (simulateQ_look_of_mem_support _ [] z hz).2 z.2 (List.prefix_refl _)
    exact hpot z.2 z.1 hlook hev
  · rw [powPot_nil, zero_add]

/-- **A PCS opening at `z` that fails at a pure `(H, F)` fails at `Option`.** -/
theorem pcsProveZH_some_none {H : Bytes → Digest} {F : KeccakState → KeccakState} {fuel n : ℕ} {z : List E}
    {tree : LeanVM.Prover.Tree} {stack : Array K} {pt : List E} {v : E}
    (h : PcsZ.pcsProveZH (m := Id) H F fuel n z tree stack pt v = none) :
    PcsZ.pcsProveZH (m := Option) (fun x ↦ some (H x)) (fun s ↦ some (F s)) fuel n z tree stack pt v = some none := by
  have e1 := PcsZ.simulateQ_pcsProveZH (UniKeccakComplete.Prob.someImpl H F) fuel n z tree stack pt v
  have e2 := PcsZ.simulateQ_pcsProveZH (totalImpl H F) fuel n z tree stack pt v
  rw [UniKeccakComplete.Prob.simulateQ_someImpl, e2] at e1
  rw [← h]
  exact e1.symm

/-- **A failed opening at `z` puts the potential at one** (`one_le_powPot_of_pcs_none` at any point). -/
theorem one_le_powPot_of_pcsZ_none (ℓ : Log) (Ht : Bytes → Digest) {n : ℕ} {z : List E} {tree : LeanVM.Prover.Tree}
    {stack : Array K} {pt : List E} {v : E} (hpt : pt.length = n)
    (h : PcsZ.pcsProveZH (m := Id) Ht (fun s ↦ (lookF ℓ s).getD winState) PcsQuotient.nonceFuel n z tree stack pt v =
      none) :
    1 ≤ powPot Whir.queryGrindingBits PcsQuotient.nonceFuel ℓ := by
  obtain ⟨sp, hsp, hf⟩ := PcsZ.pcsProveZH_eq_some_none (pcsProveZH_some_none h) hpt
  exact UniKeccakComplete.Prob.one_le_powPot_of_findNonce_ext (by decide) (by norm_num [PcsQuotient.nonceFuel])
    (by norm_num [PcsQuotient.nonceFuel]) hsp hf

/-- **The potential at a log**, from the core at every pure `(H, F)`: the log's extension (unseen permutation inputs
answered by the zero state, which passes every proof of work) fails one opening, so its search's inputs are in the
log, failing. -/
theorem pot_of_rejects {β : Type} (X : OracleComp KeccakCalls β) (Ev : β → Prop)
    (hcore : ∀ (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState), Ev (runAt Ht Ft X) →
      PcsFails Ht Ft PcsQuotient.nonceFuel)
    (ℓ : Log) (z : β) (hz : simulateQ (lookImpl ℓ) X = some z) (hev : Ev z) :
    1 ≤ powPot Whir.queryGrindingBits PcsQuotient.nonceFuel ℓ := by
  let Ht : List UInt8 → Digest := fun x ↦ (lookH ℓ x).getD default
  let Ft : KeccakState → KeccakState := fun s ↦ (lookF ℓ s).getD winState
  have hH : ∀ x u, lookH ℓ x = some u → Ht x = u := fun x u hx ↦ by simp [Ht, hx]
  have hF : ∀ s u, lookF ℓ s = some u → Ft s = u := fun s u hs ↦ by simp [Ft, hs]
  have hrun : runAt Ht Ft X = z := simulateQ_id_of_look ℓ Ht Ft hH hF _ z hz
  obtain ⟨n, zp, tree, stack, pt, v, hpt, hfail⟩ := hcore Ht Ft (by rw [hrun]; exact hev)
  exact one_le_powPot_of_pcsZ_none ℓ Ht hpt hfail

/-- **The numbers**: at most `2^50` block calls, each completing a `17`-bit proof of work whose `2^25` nonces all
failed: below `2^-300` (`E2ECompleteness.grinding_le`'s `2^-304` at `2^48`). -/
theorem grind_le {N : ℕ} (hN : N ≤ 2 ^ 50) :
    (N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel ≤ (2 : ℝ≥0∞)⁻¹ ^ 300 := by
  calc (N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel
      ≤ ((2 ^ 50 : ℕ) : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel := by
        gcongr
    _ = 2 ^ 2 * (((2 ^ 48 : ℕ) : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) := by
        push_cast
        ring
    _ ≤ 2 ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ (302 + 2) := by
        gcongr
        exact E2ECompleteness.grinding_le
    _ = (2 : ℝ≥0∞)⁻¹ ^ 302 := E2ECompleteness.two_pow_mul_inv_pow 2 302
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 300 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)

/-! ## Off the graph's acceptance the verdict rejects -/

/-- **The graph accepted**: π1's prover returned a proof and π1-rec4's graph accepted it. -/
def GAccA (a : StA) : Prop := a.p1.isSome = true ∧ a.a1 = true

section Holds

variable {m : Type → Type} [Monad m] [LawfulMonad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

theorem holds_restC (D : RecDeployment) (C : Pi2Circuits D) (input : Vector UInt8 32) (b : StB)
    (p1 : UniKeccak.KeccakProof) (out : Pi2Out) :
    Holds (restC H F D C input b p1 out) fun v ↦ v.1 = b.a.a1 := by
  unfold restC
  refine holds_bind (holds_true _) fun pW _ ↦ holds_bind (holds_true _) fun pS _ ↦
    holds_bind (holds_true _) fun pQ1 _ ↦ holds_bind (holds_true _) fun pQ2 _ ↦ ?_
  split
  · exact holds_bind (holds_true _) fun _ _ ↦ holds_pure rfl
  · exact holds_pure rfl

theorem holds_stageC (D : RecDeployment) (C : Pi2Circuits D) (input : Vector UInt8 32) (b : StB) (st : Digest)
    (hb : ¬ GAccA b.a) : Holds (stageC H F D C input b st) fun z ↦ z.1.1 = false := by
  unfold stageC
  rcases hp : b.a.p1 with _ | p1
  · exact holds_pure rfl
  · have ha1 : b.a.a1 = false := by
      unfold GAccA at hb
      rw [hp] at hb
      simpa using hb
    refine holds_bind (holds_true _) fun x _ ↦ ?_
    rcases x with ⟨out, w⟩
    exact holds_bind (holds_restC H F D C input b p1 out) fun v hv ↦ holds_pure (hv.trans ha1)

theorem holds_stageB (D : RecDeployment) (C : Pi2Circuits D) (input : Vector UInt8 32) (a : StA)
    (s₁ s₂ s₃ : Digest) : Holds (stageB H D C input a s₁ s₂ s₃) fun b ↦ b.a = a := by
  unfold stageB
  refine holds_bind (holds_true _) fun x _ ↦ ?_
  rcases x with ⟨qs, wr⟩
  exact holds_pure rfl

end Holds

/-- A postcondition of a two-call computation holds on its random-oracle run's support. -/
theorem holds_ro_support {α : Type} {X : OracleComp KeccakCalls α} {P : α → Prop} (h : Holds X P) (c : Cache)
    (z : α × Cache) (hz : z ∈ support ((simulateQ ro X).run c)) : P z.1 := by
  have h2 := holds_run' (holds_simulateQ ro h) c
  refine holds_support h2 z.1 ?_
  rw [StateT.run'_eq, support_map]
  exact ⟨z, hz, rfl⟩

/-- **A postcondition at `Id`** holds of the value. -/
theorem holds_id {α : Type} {X : Id α} {P : α → Prop} (h : Holds X P) : P (Id.run X) :=
  of_eq_true (congrArg Prod.snd h)

end RecCompose.Pi2G

/-- info: 'RecCompose.Pi2G.rejectGood_of_pot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.rejectGood_of_pot
