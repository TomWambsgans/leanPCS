-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecGraphKeccak.Sim.Compose
import RecGraph.Sim.Calls

/-!
# `Pi1SimK` from `reduceK`'s lockstep

On `RecGraph.Sim.Calls`'s lemmas:

* `calls_eqK`: the recorded calls' bytes (`callsOfK`) are `UniKeccak.pcsClaimWordsK`'s, for a run related by `RedRK`;
* `pi1SimK_of_reduce`: if `Pi1.reduceK keccak128` simulates `UniKeccak.reduceWithK … keccakRec3 .point` (`SimE`, off
  the hazard at challenges `45` and `52`, the outputs related by `RedRK`) from any state like the one the statement
  words leave, then `Pi1SimK`: the seed and the statement words couple the recorder with `Chan.start`; a run that
  succeeds is accepted by `finish` exactly on a stream of the record's length; a run that fails is on a shorter stream.
-/

set_option linter.dupNamespace false

namespace RecGraphKeccak.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph RecGraph.Pi1
  RecGraph.Sim RecGraphKeccak RecGraphKeccak.Pi1

section Calls

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- **The calls' bytes are `pcsClaimWordsK`'s**, for a run related by `RedRK`, on a stream of the record's
length. -/
theorem calls_eqK {st : RecState} {red : ReducedSK} {r : Reduced} (hg : Good st)
    (hR : RedRK π iv publicInput stream st red r) (hb : InputsBelow st) (hs : stream.size = st.cursor) :
    (callsOfK st red).map (·.flatMap (RecGraph.wordBytes stream (evalAll π iv publicInput stream st))) =
      UniKeccak.pcsClaimWordsK referenceRootsK r := by
  obtain ⟨hr1, hr2, hop, hm, ho1, ho2⟩ := hR
  have hw1 := rootWord_of π iv publicInput stream hg hr1 hb hs
  have hw2 := rootWord_of π iv publicInput stream hg hr2 hb hs
  have h1na := hr1.2.2.1
  have h2na := hr2.2.2.1
  have hel : (elementWord referenceRootsK.fOod).length = 32 := by simp [elementWord, be64]
  unfold UniKeccak.pcsClaimWordsK callsOfK
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

/-- `pi1Rec3`: the statement words, then `reduce`. -/
theorem pi1Rec3K_eq : pi1Rec3K = statementWords >>= Pi1.reduceK keccak128 := by
  unfold pi1Rec3K
  exact statementWords_bind _

theorem start_chIdsK : chIds RecState.start = [] := by
  unfold chIds
  rw [start_nodes]
  rfl

/-- The verifier's walk: reduce, then `finish`. -/
abbrev walkUK (π : KeccakState → KeccakState) (publicInput : List UInt8) : ChanM Id Reduced :=
  UniKeccak.reduceWithK (Fp π) keccak128 (publicWordsOf publicInput) UniKeccak.keccakRec3 .point >>= fun r ↦
    UniStatement.finish (m := Id) >>= fun _ ↦ pure r

/-- The outputs of a walk's outcome. -/
def outcomeOutputsK (x : Except UniError Reduced × Chan) : Option Outputs :=
  match x.1 with
  | .ok r => some ⟨UniKeccak.pcsClaimWordsK referenceRootsK r, x.2.zeros.toList, []⟩
  | .error _ => none

theorem verifierOutputs_eqK (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) :
    verifierOutputsWithK (m := Id) (fun s ↦ pure (π s)) keccak128 referenceRootsK iv publicInput stream =
      outcomeOutputsK (((walkUK π publicInput).run).run (Chan.start (Id.run (seedWith (Fp π) iv publicInput)) stream)) :=
  rfl

theorem mergeHazard_iffK (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) :
    MergeHazardK π iv publicInput stream ↔
      ¬ NoHazardAtK (((walkUK π publicInput).run).run (Chan.start (Id.run (seedWith (Fp π) iv publicInput)) stream)).2 := by
  unfold NoHazardAtK
  rw [not_not]
  exact Iff.rfl

/-- `finish` keeps the channel. -/
theorem walk_chanK (u : ChanM Id Reduced) (c : Chan) :
    (((u >>= fun r ↦ UniStatement.finish (m := Id) >>= fun _ ↦ pure r).run).run c).2 = ((u.run).run c).2 := by
  rw [run_bind]
  cases h : (u.run).run c with
  | mk r c' =>
    cases r with
    | error e => rfl
    | ok b =>
      show (((UniStatement.finish (m := Id) >>= fun _ ↦ pure b).run).run c').2 = c'
      rw [run_bind, finish_run]
      by_cases hc : c'.cursor = c'.data.size
      · simp only [hc, ↓reduceIte]; rfl
      · simp only [hc, ↓reduceIte]

/-- The run's values are the record's evaluation (`run_vals`). -/
theorem run_vals_recordK {α : Type} (π : KeccakState → KeccakState) (iv publicInput : List UInt8)
    (stream : Array UInt8) (p : Prog α) :
    (p.run π iv publicInput stream (RecState.start, evalAll π iv publicInput stream RecState.start)).2.2 =
      evalAll π iv publicInput stream (p.record RecState.start).2 := by
  obtain ⟨h1, h2, -⟩ := run_vals π iv publicInput stream p RecState.start start_kinv
  rw [h1, ← h2]

theorem streamLen_recordedGraphK (p : Prog ReducedSK) :
    (recordedGraphK p).streamLen = (p.record RecState.start).2.cursor := by
  unfold recordedGraphK RecState.graph
  rfl

theorem outputsOf_recordedGraphK (p : Prog ReducedSK) (stream : Array UInt8) (vals : Array Value) :
    outputsOf (recordedGraphK p) stream vals =
      ⟨(callsOfK (p.record RecState.start).2 (p.record RecState.start).1).map
          (·.flatMap (RecGraph.wordBytes stream vals)),
        (p.record RecState.start).2.zero.toList.map (valE vals), []⟩ := by
  unfold outputsOf recordedGraphK RecState.graph
  rfl

theorem outcomeOutputs_okK (b : Reduced) (c : Chan) :
    outcomeOutputsK (.ok b, c) = some ⟨UniKeccak.pcsClaimWordsK referenceRootsK b, c.zeros.toList, []⟩ := rfl

theorem outcomeOutputs_errorK (e : UniError) (c : Chan) : outcomeOutputsK (.error e, c) = none := rfl

/-- The walk on a run of reduce that succeeds: `finish` accepts iff the cursor is at the stream's end. -/
theorem walk_okK {π : KeccakState → KeccakState} {publicInput : List UInt8} {c c' : Chan} {b : Reduced}
    (h : ((UniKeccak.reduceWithK (Fp π) keccak128 (publicWordsOf publicInput) UniKeccak.keccakRec3
      .point).run).run c = (.ok b, c')) :
    ((walkUK π publicInput).run).run c =
      if c'.cursor = c'.data.size then (.ok b, c') else (.error .streamNotConsumed, c') := by
  unfold walkUK
  rw [run_bind_ok _ h, run_bind, finish_run]
  by_cases hc : c'.cursor = c'.data.size
  · simp only [hc, ↓reduceIte]; rfl
  · simp only [hc, ↓reduceIte]

/-- `valE` of the evaluation, as a function, is `val` (rewritten so as not to unfold a record's zeros). -/
theorem valE_evalAll_funK (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)
    (st : RecState) : valE (evalAll π iv publicInput stream st) = val π iv publicInput stream st := rfl

/-- **`Pi1Sim` from reduce's lockstep.** -/
theorem pi1SimK_of_reduce
    (hred : ∀ (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) (st : RecState)
      (words : List Nat) (wordsE : List E), Good st → st.nodes[0]? = some Node.seed → st.cursor = 0 →
      chIds st = [] → RpL π iv publicInput stream st words wordsE → wordsE.length = 4 →
      SimE π iv publicInput stream NoHazardAtK st (Pi1.reduceK keccak128 words)
        (UniKeccak.reduceWithK (Fp π) keccak128 wordsE UniKeccak.keccakRec3 .point) (RedRK π iv publicInput stream)) :
    Pi1SimK := by
  intro π iv publicInput stream hz
  rw [mergeHazard_iffK, not_not] at hz
  rw [verifierOutputs_eqK, pi1Rec3K_eq]
  generalize publicInput.toList = pub at hz ⊢
  obtain ⟨hp0, hw0⟩ := statementWords_psim π iv pub stream RecState.start start_good
  have hc0 := (start_couple π iv pub stream).pstep π iv pub stream hp0
  have hseed : (statementWords.record RecState.start).2.nodes[0]? = some Node.seed :=
    nodes_grow hp0.grows (by rw [start_nodes]; rfl)
  have hS := hred π iv pub stream _ _ _ hp0.good hseed (hp0.cursor.trans start_cursor)
    (hp0.chal.trans start_chIdsK) hw0 (by simp [publicWordsOf])
  have hb : InputsBelow ((Pi1.reduceK keccak128 (statementWords.record RecState.start).1).record
      (statementWords.record RecState.start).2).2 :=
    inputsBelow_record _ _ (inputsBelow_record _ _ inputsBelow_start)
  rw [run_vals_recordK, streamLen_recordedGraphK, outputsOf_recordedGraphK, record_bind]
  have hQ : NoHazardAtK (((UniKeccak.reduceWithK (Fp π) keccak128 (publicWordsOf pub) UniKeccak.keccakRec3
      .point).run).run (Chan.start (Id.run (seedWith (Fp π) iv pub)) stream)).2 := by
    rw [← walk_chanK]; exact hz
  rcases hS _ hc0 (Nat.zero_le _) hQ with ⟨b, c', hrun, hc', -, -, hR⟩ | ⟨⟨e, c', hrun⟩, hlt⟩
  · rw [walk_okK hrun]
    have hcd : c'.data.size = stream.size := by rw [hc'.data]
    by_cases hs : stream.size = ((Pi1.reduceK keccak128 (statementWords.record RecState.start).1).record
        (statementWords.record RecState.start).2).2.cursor
    · have hcc : c'.cursor = c'.data.size := by rw [hc'.cursor, hcd, hs]
      rw [ite_eq_left hcc, ite_eq_left hs, outcomeOutputs_okK, calls_eqK π iv pub stream hc'.good hR hb hs,
        hc'.zeros, valE_evalAll_funK]
    · have hcc : ¬ c'.cursor = c'.data.size := by rw [hc'.cursor, hcd]; exact fun h ↦ hs h.symm
      rw [ite_eq_right hcc, ite_eq_right hs, outcomeOutputs_errorK]
  · unfold walkUK
    rw [run_bind_error _ hrun]
    have hlt' : stream.size < ((Pi1.reduceK keccak128 (statementWords.record RecState.start).1).record
        (statementWords.record RecState.start).2).2.cursor := hlt
    have hs : ¬ stream.size = ((Pi1.reduceK keccak128 (statementWords.record RecState.start).1).record
        (statementWords.record RecState.start).2).2.cursor := by omega
    rw [ite_eq_right hs, outcomeOutputs_errorK]

end RecGraphKeccak.Sim
