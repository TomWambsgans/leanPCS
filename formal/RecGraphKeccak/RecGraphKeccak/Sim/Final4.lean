-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `Sim/Top.lean`'s `pi1SimK_of_reduce` and `Sim/Final.lean`'s
-- `pi1GraphIsVerifierK` at π1-rec4.
import RecGraphKeccak.Sim.Compose4
import RecGraphKeccak.Sim.Top
import RecGraphKeccak.Sim.Final

/-!
# Graph = verifier for the Keccak VM's π1-rec4

* `pi1SimK4_of_reduce`: if `Pi1.reduceK4 keccak128` simulates `UniKeccak.reduceWithK4 … keccakRec4 .point` (`SimE`, off
  the hazard at challenges `45` and `46`, the outputs related by `RedRK`), then `Pi1SimK4` (`Top.lean`'s argument);
* `pi1GraphIsVerifierK4_of_parts`, from the parts (`reduce_simQK4`);
* **`pi1GraphIsVerifierK4 : Pi1GraphIsVerifierK4`**, with no hypothesis: the parts are π1-rec3's (`tableSpecK`,
  `constraintSpecK`, `degreeSpecK`, `heapSpecK`, `shapeSpecK`: π1-rec4 states the same relations), the tail
  `tailSpecK4`, Flock `verifyWalkedK4_sim`, the wide draws `sim_sampleWide`.
-/

set_option linter.dupNamespace false

namespace RecGraphKeccak.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph RecGraph.Pi1
  RecGraph.Sim RecGraphKeccak RecGraphKeccak.Pi1

/-- `pi1Rec4K`: the statement words, then `reduceK4`. -/
theorem pi1Rec4K_eq : pi1Rec4K = statementWords >>= Pi1.reduceK4 keccak128 := by
  unfold pi1Rec4K
  exact statementWords_bind _

/-- The verifier's walk at π1-rec4: reduce, then `finish`. -/
abbrev walkUK4 (π : KeccakState → KeccakState) (publicInput : List UInt8) : ChanM Id Reduced :=
  UniKeccak.reduceWithK4 (Fp π) keccak128 (publicWordsOf publicInput) UniKeccak.keccakRec4 .point >>= fun r ↦
    UniStatement.finish (m := Id) >>= fun _ ↦ pure r

theorem verifierOutputs_eqK4 (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) :
    verifierOutputsWithK4 (m := Id) (fun s ↦ pure (π s)) keccak128 referenceRootsK iv publicInput stream =
      outcomeOutputsK (((walkUK4 π publicInput).run).run
        (Chan.start (Id.run (seedWith (Fp π) iv publicInput)) stream)) :=
  rfl

theorem mergeHazard_iffK4 (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) :
    MergeHazardK4 π iv publicInput stream ↔
      ¬ NoHazardAtK4 (((walkUK4 π publicInput).run).run
        (Chan.start (Id.run (seedWith (Fp π) iv publicInput)) stream)).2 := by
  unfold NoHazardAtK4
  rw [not_not]
  exact Iff.rfl

/-- The walk on a run of reduce that succeeds: `finish` accepts iff the cursor is at the stream's end. -/
theorem walk_okK4 {π : KeccakState → KeccakState} {publicInput : List UInt8} {c c' : Chan} {b : Reduced}
    (h : ((UniKeccak.reduceWithK4 (Fp π) keccak128 (publicWordsOf publicInput) UniKeccak.keccakRec4
      .point).run).run c = (.ok b, c')) :
    ((walkUK4 π publicInput).run).run c =
      if c'.cursor = c'.data.size then (.ok b, c') else (.error .streamNotConsumed, c') := by
  unfold walkUK4
  rw [run_bind_ok _ h, run_bind, finish_run]
  by_cases hc : c'.cursor = c'.data.size
  · simp only [hc, ↓reduceIte]; rfl
  · simp only [hc, ↓reduceIte]

/-- **`Pi1SimK4` from reduce's lockstep.** -/
theorem pi1SimK4_of_reduce
    (hred : ∀ (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) (st : RecState)
      (words : List Nat) (wordsE : List E), Good st → st.nodes[0]? = some Node.seed → st.cursor = 0 →
      chIds st = [] → RpL π iv publicInput stream st words wordsE → wordsE.length = 4 →
      SimE π iv publicInput stream NoHazardAtK4 st (Pi1.reduceK4 keccak128 words)
        (UniKeccak.reduceWithK4 (Fp π) keccak128 wordsE UniKeccak.keccakRec4 .point)
        (RedRK π iv publicInput stream)) :
    Pi1SimK4 := by
  intro π iv publicInput stream hz
  rw [mergeHazard_iffK4, not_not] at hz
  rw [verifierOutputs_eqK4, pi1Rec4K_eq]
  generalize publicInput.toList = pub at hz ⊢
  obtain ⟨hp0, hw0⟩ := statementWords_psim π iv pub stream RecState.start start_good
  have hc0 := (start_couple π iv pub stream).pstep π iv pub stream hp0
  have hseed : (statementWords.record RecState.start).2.nodes[0]? = some Node.seed :=
    nodes_grow hp0.grows (by rw [start_nodes]; rfl)
  have hS := hred π iv pub stream _ _ _ hp0.good hseed (hp0.cursor.trans start_cursor)
    (hp0.chal.trans start_chIdsK) hw0 (by simp [publicWordsOf])
  have hb : InputsBelow ((Pi1.reduceK4 keccak128 (statementWords.record RecState.start).1).record
      (statementWords.record RecState.start).2).2 :=
    inputsBelow_record _ _ (inputsBelow_record _ _ inputsBelow_start)
  rw [run_vals_recordK, streamLen_recordedGraphK, outputsOf_recordedGraphK, record_bind]
  have hQ : NoHazardAtK4 (((UniKeccak.reduceWithK4 (Fp π) keccak128 (publicWordsOf pub) UniKeccak.keccakRec4
      .point).run).run (Chan.start (Id.run (seedWith (Fp π) iv pub)) stream)).2 := by
    rw [← walk_chanK]; exact hz
  rcases hS _ hc0 (Nat.zero_le _) hQ with ⟨b, c', hrun, hc', -, -, hR⟩ | ⟨⟨e, c', hrun⟩, hlt⟩
  · rw [walk_okK4 hrun]
    have hcd : c'.data.size = stream.size := by rw [hc'.data]
    by_cases hs : stream.size = ((Pi1.reduceK4 keccak128 (statementWords.record RecState.start).1).record
        (statementWords.record RecState.start).2).2.cursor
    · have hcc : c'.cursor = c'.data.size := by rw [hc'.cursor, hcd, hs]
      rw [ite_eq_left hcc, ite_eq_left hs, outcomeOutputs_okK, calls_eqK π iv pub stream hc'.good hR hb hs,
        hc'.zeros, valE_evalAll_funK]
    · have hcc : ¬ c'.cursor = c'.data.size := by rw [hc'.cursor, hcd]; exact fun h ↦ hs h.symm
      rw [ite_eq_right hcc, ite_eq_right hs, outcomeOutputs_errorK]
  · unfold walkUK4
    rw [run_bind_error _ hrun]
    have hlt' : stream.size < ((Pi1.reduceK4 keccak128 (statementWords.record RecState.start).1).record
        (statementWords.record RecState.start).2).2.cursor := hlt
    have hs : ¬ stream.size = ((Pi1.reduceK4 keccak128 (statementWords.record RecState.start).1).record
        (statementWords.record RecState.start).2).2.cursor := by omega
    rw [ite_eq_right hs, outcomeOutputs_errorK]

/-- **Graph = verifier for the Keccak VM's π1-rec4, from the parts.** -/
theorem pi1GraphIsVerifierK4_of_parts (PR : PartRep) (hPR : PartRepGrows PR)
    {TS : Table → List E → TablePart × List Relation → Prop} {CS : List E → E → Relation → Prop}
    {HS : List E → List Relation × List (Column × Nat × Bool) → Prop}
    {OK : List Relation → List (Column × Nat × Bool) → Prop} {nT : Table → Nat}
    {nB chB : List Relation → List (Column × Nat × Bool) → Nat}
    (hT : TableSpecK PR TS nT) (hC : ConstraintSpecK PR CS) (hD : DegreeSpecK) (hH : HeapSpecK PR HS)
    (hTail : TailSpecK4 OK nB chB) (hS : ShapeSpecK TS CS HS OK) : Pi1GraphIsVerifierK4 :=
  pi1GraphIsVerifierK4_of_sim (pi1SimK4_of_reduce fun _ _ _ _ st words wordsE hg hseed hcur hch hw hwl ↦
    reduce_simQK4 PR hPR hT hC hD hH hTail hS st words wordsE hg hseed hcur hch hw hwl)

/-- **Graph = verifier for the Keccak VM's π1-rec4, off the merge hazard**: no hypothesis. For every permutation,
IV, public input and stream off `MergeHazardK4`, the recorded graph `Pi1.pi1GraphK4` evaluates to the outputs of
`UniKeccak.runWithK4` at `keccakRec4` (its three PCS claims' words and its zeros). -/
theorem pi1GraphIsVerifierK4 : Pi1GraphIsVerifierK4 :=
  pi1GraphIsVerifierK4_of_parts partRK partRK_grows tableSpecK constraintSpecK degreeSpecK heapSpecK tailSpecK4
    shapeSpecK

end RecGraphKeccak.Sim
