-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecGraphKeccak.Main
import RecGraphKeccak.Pi1.Verifier4
import RecGraphKeccak.Emitted

/-!
# Graph = verifier for the Keccak VM's π1-rec4: the statement, and its reduction

As `Main.lean` (π1-rec3), at π1-rec4's Fiat–Shamir shape:

* `verifierOutputsWithK4`: the outputs of `UniKeccak.runWithK4` at `keccakRec4` and the point-claim ABI (the three
  PCS claims' words `pcsClaimWordsK`, the values collected as zeros, nothing nonzero), at `keccak128` and the
  reference setup commitment `referenceRootsK`;
* `MergeHazardK4`: the merge hazard (`HazardK`, `Z_bad(t) = 0`, the same polynomial as π1-rec3's) at π1-rec4's
  challenges: `p_0` is challenge 45 (the bus's wide draw gives 4, Flock 42, its 42nd the lincheck's last round) and `t`
  challenge 46 (the first of the wide draw after `C2`'s commitment). `hazard_probK` bounds it (`t` uniform, `p_0`
  fixed before it): `2^16 / |E| = 2^-176`;
* **`Pi1GraphIsVerifierK4`**: off the hazard, the Keccak π1-rec4 graph recorded in Lean (`Pi1.pi1GraphK4`) evaluates to
  `verifierOutputsWithK4`;
* **`GraphsAgreeK4`**: `Pi1.pi1GraphK4 = Emitted.graph` (the Rust's recording), evaluated by
  `RecGraphKeccakTest/Pi1Check.lean`, not proved: with it, `Pi1GraphIsVerifierK4` is about `Emitted.graph`
  (`emitted_isVerifierK4`).
-/

namespace RecGraphKeccak

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement RecGraph RecGraphKeccak.Pi1

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The Keccak verifier's outputs** at π1-rec4's Fiat–Shamir shape (`keccakRec4`) and the point-claim ABI. -/
def verifierOutputsWithK4 (shape : UniStatement.Shape) (roots : UniKeccak.SetupRootsK) (iv publicInput : List UInt8)
    (stream : Array UInt8) : m (Option Outputs) := do
  let o ← UniKeccak.runWithK4 F shape iv publicInput stream UniKeccak.keccakRec4 .point
  return match o.result with
    | .ok r => some ⟨UniKeccak.pcsClaimWordsK roots r, o.chan.zeros.toList, []⟩
    | .error _ => none

end With

/-- **The hazard at a run of the Keccak π1-rec4 verifier** over `π`: the run draws `t` (challenge 46: at least 47
challenges), and `t` is hazardous for Flock's point's first coordinate (challenge 45). -/
def MergeHazardK4 (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) : Prop :=
  let ch := (Id.run (UniKeccak.runWithK4 (m := Id) (fun s ↦ pure (π s)) keccak128 iv publicInput stream
    UniKeccak.keccakRec4 .point)).chan.challenges
  47 ≤ ch.size ∧ HazardK (ch.getD 45 0) (ch.getD 46 0)

/-- **Graph = verifier for the Keccak VM's π1-rec4, off the merge hazard.** -/
def Pi1GraphIsVerifierK4 : Prop :=
  ∀ (π : KeccakState → KeccakState) (iv : List UInt8) (publicInput : Vector UInt8 32) (stream : Array UInt8),
    ¬ MergeHazardK4 π iv publicInput.toList stream →
      evalGraph (m := Id) (fun s ↦ pure (π s)) pi1GraphK4 iv publicInput.toList stream =
        verifierOutputsWithK4 (m := Id) (fun s ↦ pure (π s)) keccak128 referenceRootsK iv publicInput.toList stream

/-- **What is left**: the program's run on `E` computes the Keccak π1-rec4 verifier's outputs, off the hazard. -/
def Pi1SimK4 : Prop :=
  ∀ (π : KeccakState → KeccakState) (iv : List UInt8) (publicInput : Vector UInt8 32) (stream : Array UInt8),
    ¬ MergeHazardK4 π iv publicInput.toList stream →
      (if stream.size = (recordedGraphK pi1Rec4K).streamLen then
          some (outputsOf (recordedGraphK pi1Rec4K) stream
            (pi1Rec4K.run π iv publicInput.toList stream
              (RecState.start, evalAll π iv publicInput.toList stream RecState.start)).2.2)
        else none) =
        verifierOutputsWithK4 (m := Id) (fun s ↦ pure (π s)) keccak128 referenceRootsK iv publicInput.toList stream

/-- **The simulation gives graph = verifier.** -/
theorem pi1GraphIsVerifierK4_of_sim (h : Pi1SimK4) : Pi1GraphIsVerifierK4 := by
  intro π iv publicInput stream hz
  rw [evalGraph_recordedGraphK]
  exact h π iv publicInput stream hz

/-- **The Lean recording of π1-rec4's verifier is the Rust's graph** (`Emitted.lean`): evaluated by
`RecGraphKeccakTest/Pi1Check.lean` (`lake env lean`), node for node. -/
def GraphsAgreeK4 : Prop := pi1GraphK4 = Emitted.graph

/-- **Graph = verifier for the emitted π1-rec4 graph**, given that it is the Lean recording. -/
theorem emitted_isVerifierK4 (hg : GraphsAgreeK4) (h : Pi1GraphIsVerifierK4) :
    ∀ (π : KeccakState → KeccakState) (iv : List UInt8) (publicInput : Vector UInt8 32) (stream : Array UInt8),
      ¬ MergeHazardK4 π iv publicInput.toList stream →
        evalGraph (m := Id) (fun s ↦ pure (π s)) Emitted.graph iv publicInput.toList stream =
          verifierOutputsWithK4 (m := Id) (fun s ↦ pure (π s)) keccak128 referenceRootsK iv publicInput.toList
            stream := by
  rw [← hg]
  exact h

end RecGraphKeccak
