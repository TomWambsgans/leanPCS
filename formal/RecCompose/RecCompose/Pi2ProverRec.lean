-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π2's honest prover is `crates/leanvm/rec/src/pi2/prover.rs`'s
-- (`RecCompose.Pi2Prover`), its witness the circuit compiler's (`crates/leanvm/rec/src/circuit/compile.rs`, not
-- transcribed: chosen here); the statements are `formal/RecStatement`'s (`Pi2Prover`, `RecProof`).
import RecCompose.Pi2Complete

/-!
# π2's honest prover as the recursion runs it (π2v4)

**`pi2ProverWith D G pubOf fuel`** over a Keccak-256 `H` and a permutation `F`, from the public input and π1's proof:

1. the setup's trees and π2's IV, recomputed (`Pi2H.setupTreesWithH`, `Pi2H.ivOfH`);
2. **π1's claims** as π1-rec4's graph at π1's setup commitment makes them on π1's stream (`pi1ClaimsOf`: each call's
   32-byte words; off the merge hazard, `UniKeccak.pcsClaimWordsK`'s): the claims the proof declares
   (`RecProof.pi1Claims`), the frame's payloads `0, 1, 2` their Keccak-256s (`frameOf`);
3. the circuit's witness and public values (`pi2Choice`: a choice of one satisfying π2's circuit `G roots` at the
   values' public limbs `pubOf`, holding π1's stream, the values matching the reads, the frame words the declared
   claims' Keccak-256s: `Pi2Good`);
4. `pi2ProveWith` (`prover.rs`'s `prove_with` and `open`), its stream and four PCS openings after π1's three.

`G` and `pubOf` are parameters (at the deployment, the compiled circuit's `toPiop` and its public limbs). The deployed
Rust prover is trusted for completeness; this Lean prover is a transcription, compared with the Rust on the circuit
compiler's example only (`RecComposeTest/Pi2Prover.lean`), and its witness is `Classical.choose` among the `Pi2Good`
ones, not the Rust's witness generation.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2E

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open Pi2S Pi2K

/-! ## π1's claims -/

/-- **π1's claims as π1-rec4's graph makes them** at π1's setup commitment on π1's stream: each call's 32-byte words
(none if the graph does not run). -/
def pi1ClaimsOf (D : RecDeployment) (roots : UniKeccak.SetupRootsK) (input : Vector UInt8 32) (s : Array UInt8) :
    List (List (List UInt8)) :=
  match RecGraph.evalGraphDeployed (pi1GraphAt roots) (D.pi1IvAt roots) input.toList s with
  | some out => out.calls.map words32
  | none => []

/-! ## The witness -/

/-- **An honest witness and public values** for π1's stream `s` and the declared claims `claims` at a setup: the values
match the reads (the frame words the claims' Keccak-256s), the witness satisfies π2's circuit at the public limbs of
the values' scalars, and it holds `s`. -/
def Pi2Good (D : RecDeployment) (G : RecSetupRoots → RecPiop.Circuit E)
    (pubOf : RecSetupRoots → List E → ℕ → List E) (roots : RecSetupRoots) (input : Vector UInt8 32) (s : Array UInt8)
    (claims : List (List (List UInt8))) (vw : List PublicValue × (ℕ → K)) : Prop :=
  List.Forall₂ (ReadMatch (frameOf claims)) (D.circuitAt roots.pi1).circuit.reads vw.1 ∧
    (G roots).Satisfies (pubOf roots (publicScalarsOf input.toList vw.1)) (RecCircuit.emb vw.2) ∧
    D.pi1Stream vw.2 = s

open Classical in
/-- **The witness π2's prover takes**: an honest one if there is one. -/
noncomputable def pi2Choice (D : RecDeployment) (G : RecSetupRoots → RecPiop.Circuit E)
    (pubOf : RecSetupRoots → List E → ℕ → List E) (roots : RecSetupRoots) (input : Vector UInt8 32) (s : Array UInt8)
    (claims : List (List (List UInt8))) : List PublicValue × (ℕ → K) :=
  if h : ∃ vw, Pi2Good D G pubOf roots input s claims vw then h.choose else ([], fun _ ↦ 0)

theorem pi2Choice_good {D : RecDeployment} {G : RecSetupRoots → RecPiop.Circuit E}
    {pubOf : RecSetupRoots → List E → ℕ → List E} {roots : RecSetupRoots} {input : Vector UInt8 32} {s : Array UInt8}
    {claims : List (List (List UInt8))} (h : ∃ vw, Pi2Good D G pubOf roots input s claims vw) :
    Pi2Good D G pubOf roots input s claims (pi2Choice D G pubOf roots input s claims) := by
  unfold pi2Choice
  split
  next h' => exact h'.choose_spec
  next h' => exact absurd h h'

/-! ## The prover -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- **π2's honest prover** over `H`, `F`: the setup's trees, the IV, π1's claims, the witness, `pi2ProveWith` (`W`'s
and `Q`'s out-of-domain points read off `H`, `WhirBridge.Pcs.oodPointM H`), π1's claims and openings first. -/
noncomputable def pi2ProverWith (D : RecDeployment) (G : RecSetupRoots → RecPiop.Circuit E)
    (pubOf : RecSetupRoots → List E → ℕ → List E) (fuel : ℕ) (input : Vector UInt8 32) (p1 : UniKeccak.KeccakProof) :
    m (Option RecProof) := do
  let trees ← Pi2H.setupTreesWithH H F D
  let iv ← Pi2H.ivOfH H D trees.roots
  let claims := pi1ClaimsOf D trees.roots.pi1 input p1.stream
  let vw := pi2Choice D G pubOf trees.roots input p1.stream claims
  let c := D.circuitAt trees.roots.pi1
  let res ← pi2ProveWith H F fuel (G trees.roots) (WhirBridge.Pcs.oodPointM H) c.circuit c.setupStack trees.pi2 iv
    input.toList vw.1 vw.2
  return res.map fun x ↦ ⟨x.1, claims, p1.c1, p1.c2, p1.setup, x.2.w, x.2.setup, x.2.qId, x.2.qPush⟩

end With

/-- **π2's honest prover in the random-permutation model**: Keccak-256 the sponge over `π`, `π` itself for WHIR's
proofs of work. -/
noncomputable def pi2Prover (D : RecDeployment) (G : RecSetupRoots → RecPiop.Circuit E)
    (pubOf : RecSetupRoots → List E → ℕ → List E) (fuel : ℕ) : Pi2Prover :=
  pi2ProverWith (keccak256With queryPermutation) queryPermutation D G pubOf fuel

/-! ## At a pure permutation -/

/-- **The prover's run at a pure permutation**: the stream, then the four openings at the arithmetic's claims. -/
theorem pi2ProveWith_run (Hk : List UInt8 → Digest) (F : KeccakState → Id KeccakState) (fuel : ℕ)
    (G : RecPiop.Circuit E) (zf : ℕ → Digest → List E) (view : Circuit) (setupStack : Array K)
    (setupTree : LeanVM.Prover.Tree) (iv input : List UInt8) (values : List PublicValue) (w : ℕ → K) :
    Id.run (pi2ProveWith (m := Id) (Pure.pure ∘ Hk) F fuel G (pureZ zf) view setupStack setupTree iv input values w) =
      let out := proverOut Hk G zf view setupStack iv input values w
      let o := (Spec.of view).core.run out.inputs
      (PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel (stackVars G.logN).1 out.wPoint out.wTree out.wStack
        o.witnessPoint o.fold).bind fun a ↦
      (PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel (stackVars G.logN).2.2
        (UniKeccakComplete.pcsZ (stackVars G.logN).2.2 setupTree.root) setupTree
        (padStack (stackVars G.logN).2.2 fun i ↦ setupStack.getD i 0) o.setupPoint out.inputs.ξ).bind fun b ↦
      (PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel (stackVars G.logN).2.1 out.qPoint out.qTree out.qStack
        o.quotientPoint o.quotientValue).bind fun c ↦
      (PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel (stackVars G.logN).2.1 out.qPoint out.qTree out.qStack
        o.pushesPoint o.pushesValue).bind fun d ↦
      some (out.stream, ⟨a, b, c, d⟩) := rfl

/-- **π2's honest prover at a pure permutation**: `pi2ProveWith` at the setup's trees, the contract's IV, π1's claims
and the witness it takes, π1's claims and openings first. -/
theorem pi2ProverWith_run (Hk : List UInt8 → Digest) (F : KeccakState → Id KeccakState) (D : RecDeployment)
    (G : RecSetupRoots → RecPiop.Circuit E) (pubOf : RecSetupRoots → List E → ℕ → List E) (fuel : ℕ)
    (input : Vector UInt8 32) (p1 : UniKeccak.KeccakProof) :
    Id.run (pi2ProverWith (m := Id) (Pure.pure ∘ Hk) F D G pubOf fuel input p1) =
      let trees := Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)
      let claims := pi1ClaimsOf D trees.roots.pi1 input p1.stream
      let vw := pi2Choice D G pubOf trees.roots input p1.stream claims
      (Id.run (pi2ProveWith (m := Id) (Pure.pure ∘ Hk) F fuel (G trees.roots) (pureZ (pi2Z Hk))
        (D.circuitAt trees.roots.pi1).circuit (D.circuitAt trees.roots.pi1).setupStack trees.pi2
        (ivOf D Hk trees.roots) input.toList vw.1 vw.2)).map
        fun x ↦ ⟨x.1, claims, p1.c1, p1.c2, p1.setup, x.2.w, x.2.setup, x.2.qId, x.2.qPush⟩ := by
  unfold pi2ProverWith
  rw [oodPointM_id_eq]
  rfl

end RecCompose.Pi2E
