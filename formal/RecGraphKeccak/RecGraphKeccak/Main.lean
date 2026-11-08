-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `Z_bad` is `formal/UniSound`'s (`UniSound.Ids.zBad`,
-- on the shape's hash table's height).
import RecGraph.Pi1.Main
import RecGraphKeccak.Pi1.Verifier
import UniSound.Ids.Model

/-!
# Graph = verifier for the Keccak VM's π1-rec3: the statement, and its reduction

* `verifierOutputsWithK`: the outputs of `UniKeccak`'s verifier at `keccakRec3` and the point-claim ABI (`runWithK`, its
  three `PCS_OPEN` calls `pcsCallsK`, the values it collected as zeros, nothing nonzero), on the shape and setup
  roots the graph was recorded with (`keccak128`, `referenceRootsK`).
* `MergeHazardK`: the merge hazard of the Keccak verifier. `combine` merges points by value in `UniKeccak`,
  by symbol in the graph; the merge that changes a weight is of `y(t)` (the `SHA3` table's `q_flock` slot point, its
  `h_SHA3 = 15` coordinates) into a `C1` point starting with `t` or into Flock's point: `Z_bad(t) = 0`,
  `Z_bad = (y_0 + X)(y_0 + p_0)` (`UniSound.Ids.zBad` at `keccak128`), `t` the run's challenge 52 and `p_0` its
  challenge 45 (the lincheck's last round). A run that does not draw `t` is off it.
* **`Pi1GraphIsVerifierK`**, the target: off the hazard, the Keccak graph recorded in Lean (`Pi1.pi1GraphK`, equal node
  for node to the Rust's `Emitted.graph`: `RecGraphKeccakTest/Pi1Check.lean`) evaluates to `verifierOutputsWithK`.
* `pi1GraphIsVerifierK_of_sim : Pi1SimK → Pi1GraphIsVerifierK` (`RecGraph.Pi1.evalGraph_recorded`).
-/

namespace RecGraphKeccak

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement RecGraph RecGraphKeccak.Pi1

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The Keccak verifier's outputs** at π1-rec3's Fiat–Shamir shape (`keccakRec3`) and the point-claim ABI: the run
on the stream (`runWithK`), and on success its `PCS_OPEN` inputs (`pcsCallsK`) and the values it collected as zeros;
nothing is required nonzero. A run that ends in an error has none. -/
def verifierOutputsWithK (shape : UniStatement.Shape) (roots : SetupRoots) (iv publicInput : List UInt8) (stream : Array UInt8) :
    m (Option Outputs) := do
  let o ← UniKeccak.runWithK F shape iv publicInput stream UniKeccak.keccakRec3 .point
  return match o.result with
    | .ok r => some ⟨UniKeccak.pcsCallsK shape roots r, o.chan.zeros.toList, []⟩
    | .error _ => none

end With

/-- **The hazard polynomial at the Keccak shape**: `Z_bad = (y_0 + X)(y_0 + p_0)` (`UniSound.Ids.zBad keccak128`). -/
noncomputable def hazardPolyK (p0 : E) : Polynomial E := UniSound.Ids.zBad keccak128 p0

/-- `t` is hazardous for `p_0`. -/
def HazardK (p0 t : E) : Prop := (hazardPolyK p0).eval t = 0

/-- **The hazard at a run of the Keccak π1-rec3 verifier** over `π`: the run draws `t` (challenge 52: at least 53
challenges), and `t` is hazardous for Flock's point's first coordinate (challenge 45). -/
def MergeHazardK (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) : Prop :=
  let ch := (Id.run (UniKeccak.runWithK (m := Id) (fun s ↦ pure (π s)) keccak128 iv publicInput stream
    UniKeccak.keccakRec3 .point)).chan.challenges
  53 ≤ ch.size ∧ HazardK (ch.getD 45 0) (ch.getD 52 0)

/-- **Graph = verifier for the Keccak VM's π1-rec3, off the merge hazard.** -/
def Pi1GraphIsVerifierK : Prop :=
  ∀ (π : KeccakState → KeccakState) (iv : List UInt8) (publicInput : Vector UInt8 32) (stream : Array UInt8),
    ¬ MergeHazardK π iv publicInput.toList stream →
      evalGraph (m := Id) (fun s ↦ pure (π s)) pi1GraphK iv publicInput.toList stream =
        verifierOutputsWithK (m := Id) (fun s ↦ pure (π s)) keccak128 referenceRootsK iv publicInput.toList stream

/-- **What is left**: the program's run on `E` computes the Keccak verifier's outputs, off the merge hazard. -/
def Pi1SimK : Prop :=
  ∀ (π : KeccakState → KeccakState) (iv : List UInt8) (publicInput : Vector UInt8 32) (stream : Array UInt8),
    ¬ MergeHazardK π iv publicInput.toList stream →
      (if stream.size = (recordedGraphK pi1Rec3K).streamLen then
          some (outputsOf (recordedGraphK pi1Rec3K) stream
            (pi1Rec3K.run π iv publicInput.toList stream
              (RecState.start, evalAll π iv publicInput.toList stream RecState.start)).2.2)
        else none) =
        verifierOutputsWithK (m := Id) (fun s ↦ pure (π s)) keccak128 referenceRootsK iv publicInput.toList stream

/-- `evalGraph_recorded` for `recordedGraphK`. -/
theorem evalGraph_recordedGraphK (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)
    (p : Prog RecGraph.Pi1.ReducedS) :
    evalGraph (m := Id) (fun s ↦ pure (π s)) (recordedGraphK p) iv publicInput stream =
      if stream.size = (recordedGraphK p).streamLen then
        some (outputsOf (recordedGraphK p) stream
          (p.run π iv publicInput stream (RecState.start, evalAll π iv publicInput stream RecState.start)).2.2)
      else none :=
  RecGraph.Pi1.evalGraph_recorded π iv publicInput stream p (recordedGraphK p) rfl rfl

/-- **The simulation gives graph = verifier.** -/
theorem pi1GraphIsVerifierK_of_sim (h : Pi1SimK) : Pi1GraphIsVerifierK := by
  intro π iv publicInput stream hz
  rw [evalGraph_recordedGraphK]
  exact h π iv publicInput stream hz

end RecGraphKeccak
