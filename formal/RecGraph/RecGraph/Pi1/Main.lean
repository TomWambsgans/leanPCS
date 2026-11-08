-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecGraph.Pi1.Verifier
import RecGraph.Commute

/-!
# A recorded graph's evaluation is its program's run

`evalGraph_recorded`: for any program `p` and graph with `p`'s recorded nodes and kernels, the graph's evaluation over
any permutation is `p`'s run on `E` (`record_eval`). `RecGraphKeccak.Main` instantiates it at the Keccak VM's π1-rec3
program, reducing graph = verifier to a statement about the program alone.
-/

namespace RecGraph.Pi1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement

/-- **A recorded graph's evaluation is its program's run on `E`** (`record_eval`), for any program: on a stream of
the graph's length, the outputs read off the run's values; on another, none. -/
theorem evalGraph_recorded {α : Type} (π : KeccakState → KeccakState) (iv publicInput : List UInt8)
    (stream : Array UInt8) (p : Prog α) (g : Graph) (hn : g.nodes = (p.record RecState.start).2.nodes)
    (hk : g.kernels = (p.record RecState.start).2.kernels) :
    evalGraph (m := Id) (fun s ↦ pure (π s)) g iv publicInput stream =
      if stream.size = g.streamLen then
        some (outputsOf g stream
          (p.run π iv publicInput stream (RecState.start, evalAll π iv publicInput stream RecState.start)).2.2)
      else none := by
  have h : Id.run (evalNodes (m := Id) (fun s ↦ pure (π s)) g iv publicInput stream) =
      (p.run π iv publicInput stream (RecState.start, evalAll π iv publicInput stream RecState.start)).2.2 := by
    have he := record_eval π iv publicInput stream p g.calls g.streamLen
    rw [← he]
    unfold evalNodes RecState.graph
    rw [hn, hk]
  unfold evalGraph
  split
  · rw [← h]
    rfl
  · rfl

end RecGraph.Pi1
