-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: `PcsQuotient.challengePhase` with the permutation calls of its challenges as tracked queries. Keccak-256
-- over a permutation is leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/Keccak.lean`).
import ZK.PcsFresh

/-!
# The challenge phase with tracked queries

`phaseF circuit stmt`: the Statement's `challengePhase` (with the simulator's uniform scalars), each permutation
call of the out-of-domain points and of the chain's challenges `α, β, γ, t, ρ` a tracked query (`FProg.q`),
every other step (the circuit's commitment, the chain's seed, the coins) a black box. **`interpR_phaseF`**: run
for real, it is `challengePhase circuit stmt uniformReveal`.
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open PcsQuotient.Transcript PcsQuotient.Domain
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open FProg

variable {A : Type}

/-- The permutation's input when the block `block` is absorbed into `st`. -/
def blockIn (st : KeccakState) (block : List UInt8) : KeccakState :=
  Vector.ofFn fun i ↦ if i.val < 17 then Keccak.lane st i ^^^ leLane block i else Keccak.lane st i

/-- The digest of a state: its first four lanes. -/
def digestOf (st : KeccakState) : Digest :=
  #v[Keccak.lane st 0, Keccak.lane st 1, Keccak.lane st 2, Keccak.lane st 3]

/-- `absorbWith`, each permutation call tracked. -/
def absorbF : ℕ → KeccakState → List UInt8 → FProg A KeccakState
  | 0, st, d => .q (blockIn st (padBlock d)) .ret
  | b + 1, st, d => .q (blockIn st (d.take rate)) fun st' ↦ absorbF b st' (d.drop rate)

/-- Keccak-256, each permutation call tracked. -/
def keccakF (data : List UInt8) : FProg A Digest :=
  (absorbF (data.length / rate) (Vector.replicate 25 0) data).bind fun st ↦ .ret (digestOf st)

/-- `List.mapM` of programs. -/
def listF {β γ : Type} : List β → (β → FProg A γ) → FProg A (List γ)
  | [], _ => .ret []
  | b :: l, f => (f b).bind fun c ↦ (listF l f).bind fun cs ↦ .ret (c :: cs)

/-- The out-of-domain point, its calls tracked. -/
def oodF (n : ℕ) (root : Digest) : FProg A (List E) :=
  listF (List.range n) fun j ↦ (keccakF (oodInput n root j)).bind fun d ↦ .ret (elementOf ((digestBytes d).drop 8))

/-- A challenge of the chain, its calls tracked. -/
def squeezeF (c : Chain) : FProg A (E × Chain) :=
  (keccakF (digestBytes c.state ++ c.pending.flatMap scalarBytes)).bind fun st ↦ .ret (challengeOf st, ⟨st, []⟩)

theorem interpR_absorbF : ∀ (b : ℕ) (st : KeccakState) (d : List UInt8),
    interpR (absorbF (A := A) b st d) = absorbWith edgePerm b st d
  | 0, st, d => by simp [absorbF, interpWith, absorbWith, absorbBlockWith, blockIn]
  | b + 1, st, d => by
    simp only [absorbF, interpWith, absorbWith, absorbBlockWith, blockIn]
    exact congrArg _ (funext fun st' ↦ interpR_absorbF b st' _)

theorem interpR_keccakF (data : List UInt8) : interpR (keccakF (A := A) data) = keccak256With edgePerm data := by
  simp only [keccakF, interpWith_bind, interpR_absorbF, interpWith, keccak256With, digestOf]

theorem interpR_listF {β γ : Type} (f : β → FProg A γ) :
    ∀ l : List β, interpR (listF l f) = l.mapM fun b ↦ interpR (f b)
  | [] => by simp [listF, interpWith]
  | b :: l => by
    simp only [listF, interpWith_bind, interpWith, List.mapM_cons, interpR_listF f l]

theorem interpR_oodF (n : ℕ) (root : Digest) : interpR (oodF (A := A) n root) = oodPointWith edgePerm n root := by
  simp only [oodF, oodPointWith, interpR_listF, interpWith_bind, interpR_keccakF, interpWith]

theorem interpR_squeezeF (c : Chain) : interpR (squeezeF (A := A) c) = c.squeezeWith edgePerm := by
  simp only [squeezeF, Chain.squeezeWith, interpWith_bind, interpR_keccakF, interpWith]

/-- **The challenge phase with tracked queries.** -/
noncomputable def phaseF (circuit : Circuit) (stmt : Statement) : FProg A (Challenges × PhaseOut) :=
  let mv := cellVars circuit.logRows
  .step (commitmentWith edgePerm mv circuit.wiringTable) fun (indexTree, index) ↦
  .step (simulateQ edgeOracle sampleDigest) fun rW ↦
  (oodF (mv + 1) rW).bind fun zW ↦
  .step (keccak256With edgePerm (label index stmt)) fun d ↦
  let c : Chain := ⟨d, []⟩
  .step (uniformReveal (.oodW zW)) fun oW ↦
  let wCom : Commitment := ⟨rW, oW⟩
  let wS := CommitmentScalars.of wCom
  let c := c.absorbCommitment wS
  (squeezeF c).bind fun pα ↦
  let α := pα.1
  let c : Chain := ⟨pα.2.state, []⟩
  (squeezeF c).bind fun pβ ↦
  let β := pβ.1
  let c : Chain := ⟨pβ.2.state, []⟩
  (squeezeF c).bind fun pγ ↦
  let γ := pγ.1
  let c : Chain := ⟨pγ.2.state, []⟩
  .step (simulateQ edgeOracle sampleDigest) fun rH ↦
  (oodF (mv + 3) rH).bind fun zH ↦
  .step (simulateQ edgeOracle sampleDigest) fun rQ ↦
  (oodF (mv + 4) rQ).bind fun zQ ↦
  .step (simulateQ edgeOracle sampleDigest) fun rG ↦
  (oodF (mv + 1) rG).bind fun zG ↦
  .step (uniformReveal (.oodQ α β γ zQ)) fun oQ ↦
  .step (uniformReveal (.oodG α β γ zG)) fun oG ↦
  .step (uniformReveal (.oodH α β γ zH)) fun oH ↦
  let hCom : Commitment := ⟨rH, oH⟩
  let qCom : Commitment := ⟨rQ, oQ⟩
  let gCom : Commitment := ⟨rG, oG⟩
  let hS := CommitmentScalars.of hCom
  let qS := CommitmentScalars.of qCom
  let gS := CommitmentScalars.of gCom
  let c := ((c.absorbCommitment hS).absorbCommitment qS).absorbCommitment gS
  (squeezeF c).bind fun pt ↦
  let t := pt.1
  let c : Chain := ⟨pt.2.state, []⟩
  .step (uniformReveal (.value 1 t)) fun a1 ↦
  .step (uniformReveal (.value 2 t)) fun a2 ↦
  .step (uniformReveal (.value 3 t)) fun a3 ↦
  .step (uniformReveal (.value 0 t)) fun a0 ↦
  let a : Vector E 4 := #v[a0, a1, a2, a3]
  let next := wiringValue circuit t
  let c := (a.toList.foldl Chain.absorb c).absorb next
  (squeezeF c).bind fun pρ ↦
  let ρ := pρ.1
  .step (uniformReveal (.qValue α β γ t ρ)) fun vq ↦
  .step (uniformReveal (.gValue α β γ t ρ)) fun vg ↦
  .ret (⟨zW, zH, zQ, zG, α, β, γ, t, ρ⟩,
    ⟨indexTree, index, ⟨wS, hS, qS, gS, a, next, vq, vg⟩,
      (claimsAt circuit.logRows stmt α β γ t ρ a next vq vg).map fun cl ↦ ⟨⟨wCom, hCom, qCom, gCom⟩, cl⟩⟩)

/-- **The program run for real is the challenge phase.** -/
theorem interpR_phaseF (circuit : Circuit) (stmt : Statement) :
    interpR (phaseF (A := A) circuit stmt) = challengePhase circuit stmt uniformReveal := by
  simp only [phaseF, interpWith, interpWith_bind, interpR_oodF, interpR_squeezeF, challengePhase,
    Chain.startWith, Chain.squeezeWith, bind_assoc, pure_bind]

end PcsQuotient.EndToEnd
