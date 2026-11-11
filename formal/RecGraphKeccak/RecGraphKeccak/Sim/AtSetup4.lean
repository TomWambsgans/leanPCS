-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `Sim/Top.lean`'s `calls_eqK` and `Sim/Final4.lean`'s
-- `pi1SimK4_of_reduce` at any setup commitment.
import RecGraphKeccak.Sim.Final4

/-!
# Graph = verifier for the Keccak VM's π1-rec4, at every setup commitment

`Emitted.lean` is recorded at the reference setup commitment (`SetupRoots::REFERENCE`, `Pi1.referenceRootsK`): the
setup claim's first two words are its root and answer, constants (`callsOfK`). π2's circuit is compiled from the graph
at the deployment's setup commitment instead (`graphAtSetup`: those two constants replaced). Here:

* `Pi1.callsOfKAt roots`, `Pi1.recordedGraphKAt roots` (`callsOfK`, `recordedGraphK` at `roots`; at
  `referenceRootsK` they are those: `callsOfKAt_reference`, `recordedGraphKAt_reference`);
* **`graphAtSetup g roots`**: the graph `g` with each call that starts with two constant words given `roots`' root
  and answer there (`atSetupCall`: `RecGraph.Pi1.beNat` of their bytes, as `callsOfK` writes them); `graphAtSetup_recorded`:
  `graphAtSetup (recordedGraphK p) roots = recordedGraphKAt roots p`;
* **`pi1GraphIsVerifierK4At`**: for every setup commitment `roots`, permutation, IV, public input and stream off
  `MergeHazardK4`, `evalGraph (graphAtSetup pi1GraphK4 roots) = verifierOutputsWithK4 … keccak128 roots …`.
-/

set_option linter.dupNamespace false

namespace RecGraphKeccak

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph RecGraph.Pi1
  RecGraphKeccak.Pi1

namespace Pi1

/-- **`contract::claims` at the setup commitment `roots`**: `callsOfK` with `roots`' root and answer in the setup
claim. -/
def callsOfKAt (roots : UniKeccak.SetupRootsK) (st : RecState) (red : ReducedSK) : List (List Word) :=
  let streamAt (half : Sym) : Word :=
    match st.nodes[half]? with
    | some (.input off _) => .stream off
    | _ => .stream 0
  red.openings.map fun (c, point, value) ↦
    let (root, ood) : Word × Word := match c with
      | .c1 => (streamAt red.root1.1, .node red.ood1)
      | .c2 => (streamAt red.root2.1, .node red.ood2)
      | .setup => (.const (beNat (LeanVM.Protocol.KeccakHash.digestBytes roots.f)),
          .const (beNat (elementWord roots.fOod)))
    [root, ood] ++ point.map Word.node ++ [.node value]

theorem callsOfKAt_reference : callsOfKAt referenceRootsK = callsOfK := rfl

/-- A program's recorded graph at the setup commitment `roots`. -/
def recordedGraphKAt (roots : UniKeccak.SetupRootsK) (p : Prog ReducedSK) : Graph :=
  { (p.record RecState.start).2.graph
      (callsOfKAt roots (p.record RecState.start).2 (p.record RecState.start).1)
      (p.record RecState.start).2.cursor with nonzero := [] }

theorem recordedGraphKAt_reference : recordedGraphKAt referenceRootsK = recordedGraphK := rfl

end Pi1

/-- **A call at the setup commitment `roots`**: a call starting with two constant words (the setup claim's root and
out-of-domain answer, as `callsOfK` writes them) gets `roots`' root and answer there; another is kept. -/
def atSetupCall (roots : UniKeccak.SetupRootsK) : List Word → List Word
  | .const _ :: .const _ :: rest =>
    .const (beNat (LeanVM.Protocol.KeccakHash.digestBytes roots.f)) :: .const (beNat (elementWord roots.fOod)) :: rest
  | other => other

/-- **The graph `g` at the setup commitment `roots`**: `atSetupCall roots` on each call. -/
def graphAtSetup (g : Graph) (roots : UniKeccak.SetupRootsK) : Graph :=
  { g with calls := g.calls.map (atSetupCall roots) }

theorem atSetupCall_of_ne (roots : UniKeccak.SetupRootsK) (w x : Word) (rest : List Word)
    (hw : ∀ a, w ≠ .const a) : atSetupCall roots (w :: x :: rest) = w :: x :: rest := by
  cases w with
  | const a => exact absurd rfl (hw a)
  | node _ => rfl
  | stream _ => rfl

/-- **The recorded graph at the reference, moved to `roots`, is the graph recorded at `roots`.** -/
theorem graphAtSetup_recorded (p : Prog ReducedSK) (roots : UniKeccak.SetupRootsK) :
    graphAtSetup (recordedGraphK p) roots = recordedGraphKAt roots p := by
  unfold graphAtSetup recordedGraphK recordedGraphKAt RecState.graph callsOfK callsOfKAt
  simp only [List.map_map]
  congr 1
  refine List.map_congr_left fun x _ ↦ ?_
  obtain ⟨c, point, value⟩ := x
  cases c <;> simp only [Function.comp_apply, List.cons_append, List.nil_append]
  · exact atSetupCall_of_ne roots _ _ _ fun a h ↦ by split at h <;> cases h
  · exact atSetupCall_of_ne roots _ _ _ fun a h ↦ by split at h <;> cases h
  · rfl

namespace Sim

open RecGraph.Sim

section Calls

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- **The calls' bytes at `roots` are `pcsClaimWordsK roots`'s**, for a run related by `RedRK`. -/
theorem calls_eqKAt (roots : UniKeccak.SetupRootsK) {st : RecState} {red : ReducedSK} {r : Reduced} (hg : Good st)
    (hR : RedRK π iv publicInput stream st red r) (hb : InputsBelow st) (hs : stream.size = st.cursor) :
    (Pi1.callsOfKAt roots st red).map (·.flatMap (RecGraph.wordBytes stream (evalAll π iv publicInput stream st))) =
      UniKeccak.pcsClaimWordsK roots r := by
  obtain ⟨hr1, hr2, hop, hm, ho1, ho2⟩ := hR
  have hw1 := rootWord_of π iv publicInput stream hg hr1 hb hs
  have hw2 := rootWord_of π iv publicInput stream hg hr2 hb hs
  have h1na := hr1.2.2.1
  have h2na := hr2.2.2.1
  have hel : (elementWord roots.fOod).length = 32 := by simp [elementWord, be64]
  unfold UniKeccak.pcsClaimWordsK Pi1.callsOfKAt
  simp only [List.map_map]
  refine map_eq_of_forall₂ hop ?_
  rintro ⟨c, point, value⟩ y ⟨ptE, vE, rfl, hpt, hv⟩
  simp only at hpt hv
  cases c <;>
  simp only [Function.comp_apply, h1na, h2na, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, RecGraph.wordBytes, UniKeccak.rootBytesK, UniKeccak.commitOfK,
    flatMap_nodes π iv publicInput stream hpt, valE_evalAll, hv.2, hw1, hw2, ho1.2, ho2.2,
    beBytes32_beNat _ hel, beBytes32_beNat _ (digestBytes_len _), List.append_assoc]

end Calls

theorem streamLen_recordedGraphKAt (roots : UniKeccak.SetupRootsK) (p : Prog ReducedSK) :
    (Pi1.recordedGraphKAt roots p).streamLen = (p.record RecState.start).2.cursor := rfl

theorem outputsOf_recordedGraphKAt (roots : UniKeccak.SetupRootsK) (p : Prog ReducedSK) (stream : Array UInt8)
    (vals : Array Value) :
    outputsOf (Pi1.recordedGraphKAt roots p) stream vals =
      ⟨(Pi1.callsOfKAt roots (p.record RecState.start).2 (p.record RecState.start).1).map
          (·.flatMap (RecGraph.wordBytes stream vals)),
        (p.record RecState.start).2.zero.toList.map (valE vals), []⟩ := rfl

/-- The outputs of a walk's outcome at `roots`. -/
def outcomeOutputsKAt (roots : UniKeccak.SetupRootsK) (x : Except UniError Reduced × Chan) : Option Outputs :=
  match x.1 with
  | .ok r => some ⟨UniKeccak.pcsClaimWordsK roots r, x.2.zeros.toList, []⟩
  | .error _ => none

theorem verifierOutputs_eqK4At (roots : UniKeccak.SetupRootsK) (π : KeccakState → KeccakState)
    (iv publicInput : List UInt8) (stream : Array UInt8) :
    verifierOutputsWithK4 (m := Id) (fun s ↦ pure (π s)) keccak128 roots iv publicInput stream =
      outcomeOutputsKAt roots (((walkUK4 π publicInput).run).run
        (Chan.start (Id.run (seedWith (Fp π) iv publicInput)) stream)) :=
  rfl

/-- **Graph = verifier for the Keccak VM's π1-rec4 at every setup commitment**, off the merge hazard: the graph
recorded at `roots` evaluates to the verifier's outputs with `roots`' claim words. -/
theorem pi1GraphIsVerifierK4_recordedAt (roots : UniKeccak.SetupRootsK) (π : KeccakState → KeccakState)
    (iv : List UInt8) (publicInput : Vector UInt8 32) (stream : Array UInt8)
    (hz : ¬ MergeHazardK4 π iv publicInput.toList stream) :
    evalGraph (m := Id) (fun s ↦ pure (π s)) (Pi1.recordedGraphKAt roots pi1Rec4K) iv publicInput.toList stream =
      verifierOutputsWithK4 (m := Id) (fun s ↦ pure (π s)) keccak128 roots iv publicInput.toList stream := by
  rw [RecGraph.Pi1.evalGraph_recorded π iv publicInput.toList stream pi1Rec4K _ rfl rfl]
  rw [mergeHazard_iffK4, not_not] at hz
  rw [verifierOutputs_eqK4At, pi1Rec4K_eq]
  generalize publicInput.toList = pub at hz ⊢
  obtain ⟨hp0, hw0⟩ := statementWords_psim π iv pub stream RecState.start start_good
  have hc0 := (start_couple π iv pub stream).pstep π iv pub stream hp0
  have hseed : (statementWords.record RecState.start).2.nodes[0]? = some Node.seed :=
    nodes_grow hp0.grows (by rw [start_nodes]; rfl)
  have hS := reduce_simQK4 partRK partRK_grows tableSpecK constraintSpecK degreeSpecK heapSpecK tailSpecK4
    shapeSpecK (π := π) (iv := iv) (publicInput := pub) (stream := stream) _ _ _ hp0.good hseed
    (hp0.cursor.trans start_cursor) (hp0.chal.trans start_chIdsK) hw0 (by simp [publicWordsOf])
  have hb : InputsBelow ((Pi1.reduceK4 keccak128 (statementWords.record RecState.start).1).record
      (statementWords.record RecState.start).2).2 :=
    inputsBelow_record _ _ (inputsBelow_record _ _ inputsBelow_start)
  rw [run_vals_recordK, streamLen_recordedGraphKAt, outputsOf_recordedGraphKAt, record_bind]
  have hQ : NoHazardAtK4 (((UniKeccak.reduceWithK4 (Fp π) keccak128 (publicWordsOf pub) UniKeccak.keccakRec4
      .point).run).run (Chan.start (Id.run (seedWith (Fp π) iv pub)) stream)).2 := by
    rw [← walk_chanK]; exact hz
  rcases hS _ hc0 (Nat.zero_le _) hQ with ⟨b, c', hrun, hc', -, -, hR⟩ | ⟨⟨e, c', hrun⟩, hlt⟩
  · rw [walk_okK4 hrun]
    have hcd : c'.data.size = stream.size := by rw [hc'.data]
    by_cases hs : stream.size = ((Pi1.reduceK4 keccak128 (statementWords.record RecState.start).1).record
        (statementWords.record RecState.start).2).2.cursor
    · have hcc : c'.cursor = c'.data.size := by rw [hc'.cursor, hcd, hs]
      rw [ite_eq_left hcc, ite_eq_left hs]
      show some _ = some _
      rw [calls_eqKAt π iv pub stream roots hc'.good hR hb hs, hc'.zeros, valE_evalAll_funK]
    · have hcc : ¬ c'.cursor = c'.data.size := by rw [hc'.cursor, hcd]; exact fun h ↦ hs h.symm
      rw [ite_eq_right hcc, ite_eq_right hs]
      rfl
  · unfold walkUK4
    rw [run_bind_error _ hrun]
    have hlt' : stream.size < ((Pi1.reduceK4 keccak128 (statementWords.record RecState.start).1).record
        (statementWords.record RecState.start).2).2.cursor := hlt
    have hs : ¬ stream.size = ((Pi1.reduceK4 keccak128 (statementWords.record RecState.start).1).record
        (statementWords.record RecState.start).2).2.cursor := by omega
    rw [ite_eq_right hs]
    rfl

/-- **Graph = verifier for the Keccak VM's π1-rec4 at every setup commitment**, in π2's form: the Lean recording
`pi1GraphK4` moved to `roots` (`graphAtSetup`) evaluates, off the merge hazard, to the outputs of
`UniKeccak.runWithK4 … keccakRec4 .point` with `roots`' claim words. -/
theorem pi1GraphIsVerifierK4At (roots : UniKeccak.SetupRootsK) (π : KeccakState → KeccakState) (iv : List UInt8)
    (publicInput : Vector UInt8 32) (stream : Array UInt8) (hz : ¬ MergeHazardK4 π iv publicInput.toList stream) :
    evalGraph (m := Id) (fun s ↦ pure (π s)) (graphAtSetup pi1GraphK4 roots) iv publicInput.toList stream =
      verifierOutputsWithK4 (m := Id) (fun s ↦ pure (π s)) keccak128 roots iv publicInput.toList stream := by
  rw [graphAtSetup_recorded]
  exact pi1GraphIsVerifierK4_recordedAt roots π iv publicInput stream hz

/-- **For the Rust's graph**, given `GraphsAgreeK4` (evaluated): `graphAtSetup Emitted.graph roots` is the verifier at
`roots`. -/
theorem emitted_isVerifierK4At (hg : GraphsAgreeK4) (roots : UniKeccak.SetupRootsK) (π : KeccakState → KeccakState)
    (iv : List UInt8) (publicInput : Vector UInt8 32) (stream : Array UInt8)
    (hz : ¬ MergeHazardK4 π iv publicInput.toList stream) :
    evalGraph (m := Id) (fun s ↦ pure (π s)) (graphAtSetup Emitted.graph roots) iv publicInput.toList stream =
      verifierOutputsWithK4 (m := Id) (fun s ↦ pure (π s)) keccak128 roots iv publicInput.toList stream := by
  rw [← hg]
  exact pi1GraphIsVerifierK4At roots π iv publicInput stream hz

end Sim

end RecGraphKeccak
