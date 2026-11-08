-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.End
import RecGraphKeccak.Emitted

/-!
# π2's circuit for the Keccak VM's π1-rec3

`RecCircuit.Compiled.compile_sound_end` at the Keccak π1-rec3 recorded graph (`RecGraphKeccak.Emitted.graph`, its
roots at `RecGraphKeccak.Emitted.rootsAt`) and any π1 contract IV: if the compiler accepts it, every witness satisfying
π2's PIOP has ports and rebuilt `PCS_OPEN` inputs equal to the Keccak graph's outputs over Keccak-f[1600]
(`EndStatement`). That the compiler accepts it is a run, not a proof: `rec-circuit-keccak` (`RecGraphKeccakTest/
Circuit.lean`) reads the graph the Rust emits (`crates/leanvm_rec/tests/lean_circuit_keccak128.rs`), checks it is
`RecGraphKeccak.Emitted.graph`, compiles it in Lean and prints a circuit to `diff` against the Rust's.
-/

namespace RecGraphKeccak

open RecCircuit Primitives

/-- **π2's circuit for the Keccak π1-rec3 carries the Keccak graph's outputs.** -/
theorem pi1rec3K_end {iv : List UInt8} {c : Compiled}
    (hc : compile (ofRG Emitted.graph Emitted.rootsAt iv) = .ok c) {pub : ℕ → List F192}
    {w : ℕ → K} (hw : c.circuit.toPiop.Satisfies pub (emb w)) :
    Compiled.EndStatement Emitted.graph Emitted.rootsAt iv c w :=
  Compiled.compile_sound_end hc hw

end RecGraphKeccak
