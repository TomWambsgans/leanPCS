-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecCompose.RealDeployment
import RecCompose.FsWalk

/-!
# The real deployment's circuit facts and the circuit's corollary (`pi2Facts_real`, `pi2CircuitAccepts_real`)

* **`pi2Facts_real hg hd hs hiv`**: `Facts.lean`'s `pi2Facts` at the real deployment (`realDeployment_real`),
  its compiled circuits (`pi2Circuits_real`) and their view check (`pi2ViewChecked_real`, from `IvChecked`).
* **`pi2CircuitAccepts_real`**: RecCircuit's corollary for π1-rec4 (`pi1GraphAccepts_of_ports`, `Circuit.lean`) at the
  real deployment's public limbs. On a stream of `pi2Bytes` bytes π2's public scalars are the statement's four words and
  the three frame words' (`pi2Scalars_real`, `pi2Pubs_cc`); `pubOfC` of them gives the statement port (port `95`) the
  input's words, the `claimHash j` port (port `92 + j`) the words of `claimHash (declared[j])`, a zero port zeros (the
  ports' sources read off the view check: `Data.publicTerms`). The graph's facts: `pi1GraphAt = emittedAt`
  (`GraphsAgreeK4`), no nonzero check, three calls, their stream words inside the stream.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters Primitives

/-! ## Limbs -/

theorem limbVals_toPiop' {r : RecCircuit.Recorded} {c : RecCircuit.Compiled} (hc : RecCircuit.compile r = .ok c)
    {J : ℕ} (hJ : J < c.circuit.ports.size) (w : ℕ → K) :
    c.circuit.toPiop.limbVals (RecCircuit.emb w) J = (c.circuit.portLimbs w J).map F192.ofF64 := by
  have hck := RecCircuit.Compiled.checked_of_compile hc
  have hparts := RecCircuit.Compiled.portsOk_parts hck.ports J hJ
  dsimp only at hparts
  have hnP : J < c.circuit.toPiop.nP := by simpa [RecPiop.Circuit.nP, RecCircuit.Circuit.toPiop] using hJ
  have hport : c.circuit.toPiop.port J = (c.circuit.ports.getD J default).position := by
    simp only [RecPiop.Circuit.port, RecCircuit.Circuit.toPiop, List.getD_eq_getElem?_getD,
      Array.getD_eq_getD_getElem?, List.getElem?_map, Array.getElem?_toList]
    rw [Array.getElem?_eq_getElem hJ]
    rfl
  have hW : c.circuit.toPiop.W = c.circuit.width := rfl
  unfold RecPiop.Circuit.limbVals RecCircuit.Circuit.portLimbs
  dsimp only
  rw [limbs_toPiop hc hnP, hport, hparts.2.1]
  rcases source_limbs (c.circuit.ports.getD J default).source with h | h <;> rw [h] <;>
    simp [RecCircuit.portWeights, RecPiop.Circuit.base, hW, RecCircuit.Circuit.cells, RecCircuit.emb,
      List.range_succ, mul_comm]

theorem map_ofF64_inj' {a b : List K} (h : a.map F192.ofF64 = b.map F192.ofF64) : a = b :=
  List.map_injective_iff.mpr F192.ofF64_injective h

theorem eK_ofF64 (w : UInt64) : UniStatement.eK w = F192.ofF64 (K.ofLane w) := by
  show F192.ofLimbs (K.ofLane w) (K.ofLane 0) (K.ofLane 0) = _
  rw [F192.ofLimbs_eq, show K.ofLane 0 = 0 from rfl, F192.ofF64_zero]
  ring

theorem canon2_eK (a b : UInt64) :
    canon2 (UniStatement.eK a + F192.Y * UniStatement.eK b) = [F192.ofF64 (K.ofLane a), F192.ofF64 (K.ofLane b)] := by
  rw [eK_ofF64, eK_ofF64, canon2_ofF64]

/-! ## The scalars -/

/-- The real circuit's public scalars: the statement's words at `0 .. 4`, frame word `j`'s at `4 + 4 j ..`. -/
theorem pubs_words {L : List E} {input f0 f1 f2 : List UInt8}
    (hL : L = UniStatement.publicWordsOf input ++ UniStatement.publicWordsOf f0 ++ UniStatement.publicWordsOf f1 ++
      UniStatement.publicWordsOf f2) :
    (∀ k < 4, L.getD (0 + k) 0 = UniStatement.eK (UniStatement.beWordAt input.toArray (8 * k))) ∧
    ∀ j < 3, ∀ k < 4, L.getD (4 + 4 * j + k) 0 =
      UniStatement.eK (UniStatement.beWordAt ([f0, f1, f2].getD j []).toArray (8 * k)) := by
  subst hL
  refine ⟨fun k hk ↦ ?_, fun j hj k hk ↦ ?_⟩
  · interval_cases k <;> rfl
  · interval_cases j <;> interval_cases k <;> rfl

/-- The four-word port's public limbs of four scalars' words. -/
theorem canon2_four (pubs : List E) (b : Array UInt8) (n : ℕ)
    (h : ∀ k < 4, pubs.getD (n + k) 0 = UniStatement.eK (UniStatement.beWordAt b (8 * k))) :
    canon2 (pubs.getD n 0 + F192.Y * pubs.getD (n + 1) 0) ++ canon2 (pubs.getD (n + 2) 0 + F192.Y * pubs.getD (n + 3) 0) =
      ((List.range 4).map fun k ↦ K.ofLane (UniStatement.beWordAt b (8 * k))).map F192.ofF64 := by
  have h0 := h 0 (by norm_num)
  rw [Nat.add_zero] at h0
  rw [h0, h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), canon2_eK, canon2_eK]
  rfl

/-! ## The ports' sources -/

theorem data_term_statement : ((Data.publicTerms.getD 95 default).value.terms.map Prod.snd) = [0, 1, 2, 3] := by
  decide +kernel

theorem data_term_claimHash : ∀ j < 3, ((Data.publicTerms.getD (92 + j) default).value.terms.map Prod.snd) =
    [4 + 4 * j, 4 + 4 * j + 1, 4 + 4 * j + 2, 4 + 4 * j + 3] := by
  decide +kernel

theorem source_terms {c : RecCircuit.Compiled} (hview : viewOf c.circuit = Data.circuit)
    (hhash : c.circuit.hashed = Data.hashed) {J : ℕ} (hJ : J < 99) :
    (termOf 3 0 (c.circuit.ports.getD J default).source).map Prod.snd =
      (Data.publicTerms.getD J default).value.terms.map Prod.snd := by
  rw [← viewOf_terms hview, publicTermsOf_getD _ (by rw [viewOf_ports hview]; exact hJ), viewOf_roots hview, hhash]
  rfl

theorem source_statement {c : RecCircuit.Compiled} (hview : viewOf c.circuit = Data.circuit)
    (hhash : c.circuit.hashed = Data.hashed) : (c.circuit.ports.getD 95 default).source = .statement := by
  have h := (source_terms hview hhash (J := 95) (by norm_num)).trans data_term_statement
  cases hs : (c.circuit.ports.getD 95 default).source <;> rw [hs] at h <;> simp [termOf] at h ⊢

theorem source_claimHash {c : RecCircuit.Compiled} (hview : viewOf c.circuit = Data.circuit)
    (hhash : c.circuit.hashed = Data.hashed) {j : ℕ} (hj : j < 3) :
    (c.circuit.ports.getD (92 + j) default).source = .claimHash j := by
  have h := (source_terms hview hhash (J := 92 + j) (by omega)).trans (data_term_claimHash j hj)
  cases hs : (c.circuit.ports.getD (92 + j) default).source <;> rw [hs] at h <;> simp [termOf] at h ⊢
  omega

/-! ## The graph -/

theorem mem_atSetupCall {roots : UniKeccak.SetupRootsK} {l : List RecGraph.Word} {a : ℕ}
    (h : RecGraph.Word.stream a ∈ RecGraphKeccak.atSetupCall roots l) : RecGraph.Word.stream a ∈ l := by
  unfold RecGraphKeccak.atSetupCall at h
  split at h
  · simp only [List.mem_cons, reduceCtorEq, false_or] at h ⊢
    exact h
  · exact h

theorem emitted_streams_b : (RecGraphKeccak.Emitted.graph.calls.all fun c ↦ c.all fun w ↦
    match w with
    | .stream a => decide (a + 32 ≤ 9280)
    | _ => true) = true := by
  decide +kernel

theorem emittedAt_calls_length (roots : UniKeccak.SetupRootsK) : (emittedAt roots).calls.length = 3 := by
  show (RecGraphKeccak.Emitted.graph.calls.map (RecGraphKeccak.atSetupCall roots)).length = 3
  rw [List.length_map]
  rfl

theorem emittedAt_streams (roots : UniKeccak.SetupRootsK) :
    ∀ j < (emittedAt roots).calls.length, ∀ a, RecGraph.Word.stream a ∈ (emittedAt roots).calls.getD j [] →
      a + 32 ≤ (emittedAt roots).streamLen := by
  intro j hj a ha
  have hj' : j < RecGraphKeccak.Emitted.graph.calls.length := by
    rw [emittedAt_calls_length] at hj
    exact hj
  have hget : (emittedAt roots).calls.getD j [] =
      RecGraphKeccak.atSetupCall roots (RecGraphKeccak.Emitted.graph.calls.getD j []) := by
    show (RecGraphKeccak.Emitted.graph.calls.map (RecGraphKeccak.atSetupCall roots)).getD j
      (RecGraphKeccak.atSetupCall roots []) = _
    rw [List.getD_map]
  rw [hget] at ha
  have hm := mem_atSetupCall ha
  have hc : RecGraphKeccak.Emitted.graph.calls.getD j [] ∈ RecGraphKeccak.Emitted.graph.calls := by
    rw [List.getD_eq_getElem _ _ hj']
    exact List.getElem_mem hj'
  have hb := List.all_eq_true.mp (List.all_eq_true.mp emitted_streams_b _ hc) _ hm
  show a + 32 ≤ 9280
  simpa using hb

/-! ## The circuit's corollary -/

section Accepts

variable {D : RecDeployment} (hD1 : ∀ roots, (D.pi2 roots).circuit = Data.circuit) (C : Pi2Circuits D)
  (hchk : Pi2ViewChecked C) (Fa : Pi2Facts D C)
  (hpub : ∀ roots, Fa.pubOf roots = pubOfC (C.compiled roots.pi1).circuit)
  (hgr : ∀ roots, pi1GraphAt roots = emittedAt roots)

include hD1 hchk hpub hgr in
/-- **The circuit's corollary from the view check**: for a deployment whose π2 circuit is `Data.circuit`, whose
compiled circuits pass the view check and whose public limbs are `pubOfC`, at π1-rec4's emitted graph. -/
theorem pi2CircuitAccepts_of : Pi2CircuitAccepts C Fa := by
  intro roots input proof w hlen hsz hw
  obtain ⟨hview, -, -, hhash⟩ := viewChecked_at C hchk roots
  have hc := C.compile_okAt roots.pi1
  rw [C.stream_eqAt roots.pi1 w]
  rw [hpub roots] at hw
  change (C.compiled roots.pi1).circuit.toPiop.Satisfies _ _ at hw
  generalize hcd : C.compiled roots.pi1 = c at hc hview hhash hw
  have hports : c.circuit.ports.size = 99 := viewOf_ports hview
  -- π2's public scalars
  have hsz' : proof.stream.size = sLen := by
    rw [hsz]
    show pi2Bytes (Spec.of (D.pi2 roots.pi1).circuit) = sLen
    rw [hD1]
    exact pi2Bytes_cc
  have hsc : pi2Scalars D roots input proof = UniStatement.publicWordsOf input.toList ++
      UniStatement.publicWordsOf (frameOf proof.pi1Claims 0) ++ UniStatement.publicWordsOf (frameOf proof.pi1Claims 1) ++
      UniStatement.publicWordsOf (frameOf proof.pi1Claims 2) := by
    rw [pi2Scalars_real D hD1 roots input proof hsz', pi2Pubs_cc]
  obtain ⟨hwS, hwH⟩ := pubs_words hsc
  -- a port's limbs are its public limbs
  have hP : ∀ J < c.circuit.ports.size, (c.circuit.portLimbs w J).map F192.ofF64 =
      pubOfC c.circuit (pi2Scalars D roots input proof) J := by
    intro J hJ
    rw [← limbVals_toPiop' hc hJ w]
    exact hw.ports J (by simpa [RecPiop.Circuit.nP, RecCircuit.Circuit.toPiop] using hJ)
  have hhl : c.circuit.hashed.length = 3 := by rw [hhash]; rfl
  have hroots0 : (publicCounts c.circuit).1 = 0 := viewOf_roots hview
  have hg := hgr roots.pi1
  refine pi1GraphAccepts_of_ports hc hw ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the statement port
    have h95 : 95 < c.circuit.ports.size := by rw [hports]; norm_num
    refine ⟨95, h95, source_statement hview hhash, map_ofF64_inj' ((hP 95 h95).trans ?_)⟩
    unfold pubOfC
    rw [source_statement hview hhash, hhl, hroots0]
    have e := canon2_four _ _ 0 hwS
    simp only [Nat.zero_add] at e
    exact e
  · -- the zero ports
    intro J hJ hs
    apply map_ofF64_inj'
    rw [hP J hJ]
    unfold pubOfC
    rw [hs]
    simp [pubOfSource, F192.ofF64_zero]
  · rw [hg]
    rfl
  · rw [hhash, hg, emittedAt_calls_length]
    rfl
  · rw [hg, emittedAt_calls_length]
    exact hlen
  · rw [hg]
    exact emittedAt_streams roots.pi1
  · -- the claims' Keccak-256 ports
    intro j hj
    rw [hg, emittedAt_calls_length] at hj
    refine ⟨92 + j, by rw [hports]; omega, source_claimHash hview hhash hj,
      map_ofF64_inj' ((hP _ (by rw [hports]; omega)).trans ?_)⟩
    unfold pubOfC
    rw [source_claimHash hview hhash hj, hhl, hroots0]
    have hf : [frameOf proof.pi1Claims 0, frameOf proof.pi1Claims 1, frameOf proof.pi1Claims 2].getD j [] =
        claimHash (proof.pi1Claims.getD j []) := by
      interval_cases j <;> rfl
    exact canon2_four _ _ (4 + 4 * j) fun k hk ↦ by rw [hwH j hj k hk, hf]

end Accepts

/-! ## The real deployment -/

variable (prog : KeccakVm.Program) (hprog : RecGraphKeccak.Pi1.keccak128.logBytecode = prog.logSize)

/-- **The real deployment's circuit facts** (`Pi2Facts`), from `GraphsAgreeK4` and the evaluated checks
(`DigestChecked`, `SetupRootChecked`, `IvChecked`). -/
def pi2Facts_real (hg : RecGraphKeccak.GraphsAgreeK4) (hd : DigestChecked) (hs : SetupRootChecked)
    (hiv : IvChecked) : Pi2Facts (realDeployment prog hprog) (pi2Circuits_real prog hprog hg hiv) :=
  pi2Facts (realDeployment_real prog hprog hg hd hs) (pi2Circuits_real prog hprog hg hiv)
    (pi2ViewChecked_real prog hprog hg hiv)

/-- **The circuit's corollary at the real deployment** (`Pi2CircuitAccepts`), from `GraphsAgreeK4` and the evaluated
checks. -/
theorem pi2CircuitAccepts_real (hg : RecGraphKeccak.GraphsAgreeK4) (hd : DigestChecked) (hs : SetupRootChecked)
    (hiv : IvChecked) :
    Pi2CircuitAccepts (pi2Circuits_real prog hprog hg hiv) (pi2Facts_real prog hprog hg hd hs hiv) :=
  pi2CircuitAccepts_of (fun _ ↦ rfl) _ (pi2ViewChecked_real prog hprog hg hiv) _ (fun _ ↦ rfl) (pi1GraphAt_eq hg)

end RecCompose

/-- info: 'RecCompose.pi2CircuitAccepts_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2CircuitAccepts_real

/-- info: 'RecCompose.pi2Facts_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2Facts_real
