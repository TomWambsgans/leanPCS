-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecCircuit.End
import RecGraphKeccak.Emitted

/-!
# π2's circuit for the Keccak VM's π1-rec4

`RecCircuit.Compiled.compile_sound_end` at the Keccak π1-rec4 recorded graph (`RecGraphKeccak.Emitted.graph`, its roots
at `RecGraphKeccak.Emitted.rootsAt`), π1's three claims hashed in the circuit (`compile::hashed_claims` of π1-rec4,
`[0, 1, 2]`: `RecStatement.Data.hashed`), and any π1 contract IV: if the compiler accepts it, every witness satisfying
π2's PIOP has ports and rebuilt claims equal to the Keccak graph's outputs over Keccak-f[1600] (`EndStatement`), and
(`pi1rec4K_claimHashes`) its three `claimHash` ports carry the Keccak-256s of the EIP draft's encodings of the graph's
three claims, given its zero ports zero. That the compiler accepts it is a run, not a proof: `rec-circuit-keccak`
(`RecGraphKeccakTest/Circuit.lean`) reads the graph the Rust emits (`crates/leanvm/rec/tests/lean_circuit_keccak.rs`),
checks it is `RecGraphKeccak.Emitted.graph`, compiles it in Lean and prints a circuit to `diff` against the Rust's.
-/

namespace RecGraphKeccak

open RecCircuit Primitives LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement

/-- π1-rec4's claims hashed in π2's circuit (`compile::hashed_claims(FsShape::Rec4)`). -/
def hashedK4 : List ℕ := [0, 1, 2]

theorem emitted_calls_length : Emitted.graph.calls.length = 3 := rfl

/-- **π2's circuit for the Keccak π1-rec4 carries the Keccak graph's outputs.** -/
theorem pi1rec4K_end {iv : List UInt8} {c : Compiled}
    (hc : compile (ofRG Emitted.graph Emitted.rootsAt iv hashedK4) = .ok c) {pub : ℕ → List F192}
    {w : ℕ → K} (hw : c.circuit.toPiop.Satisfies pub (emb w)) :
    Compiled.EndStatement Emitted.graph Emitted.rootsAt iv hashedK4 c w :=
  Compiled.compile_sound_end hc hw

/-- **A satisfied π2 circuit carries the Keccak-256s of the graph's three claims**: its `claimHash j` ports
(`j < 3`, claim `j`) carry the statement-order words of the Keccak-256 of the EIP draft's encoding of the Keccak
π1-rec4 graph's claim `j`, in `RecGraph`'s semantics over Keccak-f[1600] on the witness's stream and public input,
given every zero port zero (as π2's verifier reads them). No claim is encoded by the contract. -/
theorem pi1rec4K_claimHashes {iv : List UInt8} {c : Compiled}
    (hc : compile (ofRG Emitted.graph Emitted.rootsAt iv hashedK4) = .ok c) {pub : ℕ → List F192}
    {w : ℕ → K} (hw : c.circuit.toPiop.Satisfies pub (emb w))
    (hz : ∀ J < c.circuit.ports.size, (c.circuit.ports.getD J default).source = .zero →
      c.circuit.portLimbs w J = [0, 0, 0]) :
    c.circuit.hashed = [0, 1, 2] ∧ encodedCalls Emitted.graph hashedK4 = [] ∧
    ∀ J < c.circuit.ports.size, ∀ j, (c.circuit.ports.getD J default).source = .claimHash j →
      j < 3 ∧ c.circuit.portLimbs w J = (List.range 4).map fun l => LeanVM.Parameters.K.ofLane (beWordAt (digestBytes (keccak256
        (claimEncoding (c.streamW (ofRG Emitted.graph Emitted.rootsAt iv hashedK4) w).toArray
          (rgVals Emitted.graph iv (c.pubW w) (c.streamW (ofRG Emitted.graph Emitted.rootsAt iv hashedK4) w))
          (Emitted.graph.calls.getD j [])))).toArray (8 * l)) := by
  have hh : c.circuit.hashed = [0, 1, 2] := by
    rw [Compiled.compile_hashed hc, emitted_calls_length]; rfl
  refine ⟨hh, by simp [encodedCalls, emitted_calls_length, hashedK4]; omega, fun J hJ j hs => ?_⟩
  obtain ⟨hj, -, hp⟩ := Compiled.claimHash_port hc hw hz hJ hs
  rw [hh] at hj hp
  simp only [List.length_cons, List.length_nil] at hj
  refine ⟨hj, ?_⟩
  rw [hp]
  interval_cases j <;> rfl

end RecGraphKeccak
