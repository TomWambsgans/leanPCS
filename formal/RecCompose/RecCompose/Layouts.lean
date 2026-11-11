-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecStatement

/-!
# π1's claims at the real deployment: none encoded

On the EIP draft's PCS claims there are no layout words, and at π2v4 over π1-rec4 the contract encodes no π1 claim:
π1's three claims are declared in the transaction's frame of PCS claims and hashed in π2's circuit (`Data.hashed =
[0, 1, 2]`, `Data.pi1Calls = []`). What this file held at π2v3 (the shape of the claims the contract encoded,
`Pi1CallsShape`) has no object; **`pi1Calls_real`**: the real deployment encodes none, and reads the three frame
payloads (`frameReads_real`).
-/

namespace RecCompose

open RecStatement

/-- **The real deployment encodes no π1 claim.** -/
theorem pi1Calls_real {D : RecDeployment} (hD : D.Real) : D.pi1Calls = [] := hD.2.1

/-- **The real circuit reads the frame's payloads `0, 1, 2`** (π1's three claims' Keccak-256s). -/
theorem frameReads_real {D : RecDeployment} (hD : D.Real) (roots : UniKeccak.SetupRootsK) :
    frameReads (D.circuitAt roots).circuit.reads = [0, 1, 2] := by
  rw [RecDeployment.circuitAt, hD.1]
  rfl

end RecCompose

/-- info: 'RecCompose.pi1Calls_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi1Calls_real
