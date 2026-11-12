-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecCircuitTest.Parse

/-!
# The differential runner: the Lean compiler against the Rust's

`rec-circuit-diff GRAPH [--raw]`: reads a recorded graph written by `crates/leanvm/rec/tests/lean_circuit_keccak.rs`,
compiles it with `RecCircuit.compile` (compiled code, not the kernel; the checker included; with `--raw`, the
transcription `compileRaw` alone), and prints the circuit's summary in
the Rust test's format (the shape, the regions and their formula tables, the blocks, the ports, the calls, `κ`, `σ`'s
FNV-1a hash); `diff` it against the Rust's `.circuit` file.
-/

open RecCircuit Primitives

open RecCircuitTest in
def main (args : List String) : IO UInt32 := do
  let (path, raw) ← match args with
    | [path] => pure (path, false)
    | [path, "--raw"] => pure (path, true)
    | _ => IO.eprintln "usage: rec-circuit-diff GRAPH [--raw]"; return 2
  do
    let text ← IO.FS.readFile path
    match parseGraph text with
    | .error e => IO.eprintln s!"parse: {e}"; return 2
    | .ok r =>
      let t0 ← IO.monoMsNow
      match (if raw then compileRaw r else compile r) with
      | .error e => IO.eprintln s!"the compiler rejects the graph: {e}"; return 1
      | .ok c =>
        let t1 ← IO.monoMsNow
        IO.eprintln s!"compiled in {t1 - t0} ms: {c.nodes.size} expanded nodes, {c.view.producerF.size} values, \
          {c.st.permutations} permutations ({c.st.planesUnmade} planes unmade), {c.circuit.blocks.size} blocks, \
          {c.circuit.ports.size} ports, hashed claims {c.circuit.hashed}, roots ported at {c.rootsAt}"
        IO.print (circuitText c.circuit)
        return 0
