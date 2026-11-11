-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The honest witness is the circuit compiler's
-- (`crates/leanvm/rec/src/circuit/layout.rs`'s `finish`, `RecCircuit.Compiled.witness`), the public values π2's prover
-- sends `prover.rs`'s (`public_values`: π2v4's three frame words, the Keccak-256s of π1's declared claims).
import RecCompose.Pi2ProverRec
import RecCompose.RealCircuit
import RecCompose.OpeningsAgree
import RecCircuit.Complete

/-!
# π2's honest witness and π1's openings, from π1's graph accepting (π2v4, π1-rec4)

`Pi2Accepts.pi2_accepts` takes three hypotheses about π1's proof `p1`: an honest witness (`hgood`), π1's claims as the
graph makes them three (`hp3`), and their openings accepting (`hpi1`). Here they are proved from what
`RecCompleteness2`'s event gives: π1-rec4's graph verifier accepting `p1` (`Pi2H.pi1GraphVerifierWithH`, the
experiment's first verdict, at the same pure `(Hk, F)` and setup as the contract).

* **`pi2Good_of_checks`**, **`pi2WitnessExists_real`** (the circuit compiler's completeness): on a stream on which
  π1-rec4's graph checks hold (`pi1GraphChecks`), the compiler's honest witness `RecCircuit.Compiled.witness` with the
  public values `frameValues claims` (the three frame words `frameOf claims p`, `p = 0, 1, 2`, as `Data.reads` reads
  them) is `Pi2Good`: the values match the reads; the witness satisfies the copy constraints (`witness_copy`) and its
  ports carry their public limbs (the statement port the input's words, `pubW_witness`; the `claimHash j` port the
  Keccak-256 of the graph's claim `j`'s encoding, `claimHash_port` via `compile_sound_end`, which is `frameOf claims j`
  by `claimHash_words32`; a zero port zeros: the hashed claims' sums by `claim_zero_port_witness`, π1's zero checks by
  the graph's checks; a padding port zeros; no root or element port, the view reading none); it holds the stream
  (`streamW_witness`).
* **`pi1Openings_of_verifierH`**: π1's graph verifier accepting `p1` gives three claims (its decoded calls are three)
  and, for each, `Pi2H.pcsOpenWordsH` of the claim's words with `p1`'s opening proof: the claim's words decode to the
  verifier's opening (`decodePi1Call`), at `C1`'s, `C2`'s and the setup's sizes (`27`, `26`, `23` variables: not
  `oodRead`), so the contract's check is `pcsOpenKH` at the fixed point, the verifier's own.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2W

open RecStatement LeanVM.Parameters LeanVM.Semantics Primitives LeanVM.Protocol LeanVM.Protocol.KeccakHash
open Pi2E Pi2S

/-! ## `public_counts` bounds the ports' sources -/

theorem sourceCounts_mono (l : List RecCircuit.Port) (acc : ℕ × ℕ) :
    acc.1 ≤ (l.foldl (fun a p ↦ sourceCounts a p.source) acc).1 ∧
      acc.2 ≤ (l.foldl (fun a p ↦ sourceCounts a p.source) acc).2 := by
  induction l generalizing acc with
  | nil => exact ⟨le_rfl, le_rfl⟩
  | cons p l ih =>
    obtain ⟨h1, h2⟩ := ih (sourceCounts acc p.source)
    simp only [List.foldl_cons]
    cases hs : p.source <;> simp only [sourceCounts, hs] at h1 h2 ⊢ <;> omega

theorem wordCounts_mono (l : List RecCircuit.CallWord) (acc : ℕ × ℕ) :
    acc.1 ≤ (l.foldl wordCounts acc).1 ∧ acc.2 ≤ (l.foldl wordCounts acc).2 := by
  induction l generalizing acc with
  | nil => exact ⟨le_rfl, le_rfl⟩
  | cons p l ih =>
    obtain ⟨h1, h2⟩ := ih (wordCounts acc p)
    simp only [List.foldl_cons]
    cases p <;> simp only [wordCounts] at h1 h2 ⊢ <;> omega

theorem sourceCounts_mem (l : List RecCircuit.Port) (acc : ℕ × ℕ) (p : RecCircuit.Port) (hp : p ∈ l) :
    (∀ i, p.source = .root i → i < (l.foldl (fun a p ↦ sourceCounts a p.source) acc).1) ∧
      (∀ e, p.source = .element e → e < (l.foldl (fun a p ↦ sourceCounts a p.source) acc).2) := by
  induction l generalizing acc with
  | nil => cases hp
  | cons q l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · obtain ⟨h1, h2⟩ := sourceCounts_mono l (sourceCounts acc p.source)
      refine ⟨fun i hi ↦ ?_, fun e he ↦ ?_⟩
      · rw [hi] at h1 ⊢; simp only [sourceCounts] at h1 ⊢
        exact lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_right _ _)) h1
      · rw [he] at h2 ⊢; simp only [sourceCounts] at h2 ⊢
        exact lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self e) (le_max_right _ _)) h2
    · exact ih _ hp'

theorem publicCounts_port (c : RecCircuit.Circuit) {J : ℕ} (hJ : J < c.ports.size) :
    (∀ i, (c.ports.getD J default).source = .root i → i < (publicCounts c).1) ∧
      (∀ e, (c.ports.getD J default).source = .element e → e < (publicCounts c).2) := by
  have hmem : c.ports.getD J default ∈ c.ports.toList := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hJ, Option.getD_some]
    exact Array.getElem_mem_toList hJ
  obtain ⟨h1, h2⟩ := sourceCounts_mem c.ports.toList (0, 0) _ hmem
  obtain ⟨m1, m2⟩ := wordCounts_mono c.calls.flatten (c.ports.toList.foldl (fun a p ↦ sourceCounts a p.source) (0, 0))
  exact ⟨fun i hi ↦ lt_of_lt_of_le (h1 i hi) m1, fun e he ↦ lt_of_lt_of_le (h2 e he) m2⟩

/-- **The real view reads no element** (its reads are the three frame words, `Data.reads`). -/
theorem viewOf_elements {C : RecCircuit.Circuit} (hview : viewOf C = Data.circuit) (hhash : C.hashed = Data.hashed) :
    (publicCounts C).2 = 0 := by
  have h := congrArg List.length (viewOf_reads hview)
  rw [readsOf, List.length_append, List.length_append, List.length_map, List.length_replicate, List.length_map,
    List.length_range, hhash] at h
  have h1 : Data.reads.length = 3 := rfl
  have h2 : Data.hashed.length = 3 := rfl
  omega

/-! ## The public values -/

/-- **The public values π2's prover sends** (π2v4): the three frame words, the declared claims' Keccak-256s. -/
def frameValues (claims : List (List (List UInt8))) : List PublicValue :=
  [.word (frameOf claims 0), .word (frameOf claims 1), .word (frameOf claims 2)]

theorem publicScalars_frameValues (input : List UInt8) (claims : List (List (List UInt8))) :
    publicScalarsOf input (frameValues claims) = UniStatement.publicWordsOf input ++
      UniStatement.publicWordsOf (frameOf claims 0) ++ UniStatement.publicWordsOf (frameOf claims 1) ++
      UniStatement.publicWordsOf (frameOf claims 2) := by
  simp [publicScalarsOf, frameValues, PublicValue.scalars, List.append_assoc]

/-! ## The graph's run -/

theorem rgVals_eq (g : RecGraph.Graph) (iv : List UInt8) (input : Vector UInt8 32) (s : Array UInt8) :
    RecCircuit.rgVals g iv input.toList s.toList =
      Id.run (RecGraph.evalNodes (m := Id) (fun x ↦ pure (LeanVM.Semantics.keccakF1600 x)) g iv input.toList s) := by
  unfold RecCircuit.rgVals; rw [Array.toArray_toList]; rfl

/-- **The graph's outputs on a stream it runs on**, at `RecCircuit.rgVals`. -/
theorem eval_some {g : RecGraph.Graph} {iv : List UInt8} {input : Vector UInt8 32} {s : Array UInt8}
    {out : RecGraph.Outputs} (hev : RecGraph.evalGraphDeployed g iv input.toList s = some out) :
    s.size = g.streamLen ∧ out = RecGraph.outputsOf g s (RecCircuit.rgVals g iv input.toList s.toList) := by
  unfold RecGraph.evalGraphDeployed RecGraph.evalGraph at hev
  by_cases hsz : s.size = g.streamLen
  · simp only [hsz, ↓reduceIte] at hev
    refine ⟨hsz, ?_⟩
    rw [rgVals_eq]
    exact (Option.some.inj hev).symm
  · simp only [hsz, ↓reduceIte] at hev
    cases hev

/-- **π1's zero checks are zero on a stream the graph accepts** (in `RecGraph`'s semantics over Keccak-f[1600]). -/
theorem zeros_of_checks {g : RecGraph.Graph} {iv : List UInt8} {input : Vector UInt8 32} {s : Array UInt8}
    {out : RecGraph.Outputs} (hev : RecGraph.evalGraphDeployed g iv input.toList s = some out)
    (h : out.zeros.all (· == 0) = true) :
    ∀ id ∈ g.zero, RecGraph.valE (RecCircuit.rgVals g iv input.toList s.toList) id = 0 := by
  obtain ⟨-, rfl⟩ := eval_some hev
  intro id hid
  unfold RecGraph.outputsOf at h
  simp only [List.all_eq_true, List.mem_map, beq_iff_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at h
  exact h id hid

theorem getD_map_words32 (l : List (List UInt8)) (j : ℕ) : (l.map words32).getD j [] = words32 (l.getD j []) := by
  rw [show ([] : List (List UInt8)) = words32 [] from rfl, List.getD_map]

/-! ## The witness's completeness -/

section Witness

variable {D : RecDeployment} (hD1 : ∀ roots, (D.pi2 roots).circuit = Data.circuit) (C : Pi2Circuits D)
  (hchk : Pi2ViewChecked C) (Fa : Pi2Facts D C)
  (hpub : ∀ roots, Fa.pubOf roots = pubOfC (C.compiled roots.pi1).circuit)
  (hgr : ∀ roots, pi1GraphAt roots = emittedAt roots)

include hD1 hchk hpub hgr in
/-- **The compiled circuit is complete**: on every stream on which π1-rec4's graph checks hold, the compiler's honest
witness with the three frame words as public values is an honest witness (`Pi2Good`). -/
theorem pi2Good_of_checks (roots : RecSetupRoots) (input : Vector UInt8 32) (s : Array UInt8)
    (hgc : pi1GraphChecks (pi1GraphAt roots.pi1) (D.pi1IvAt roots.pi1) input s = true) :
    Pi2Good D C.G Fa.pubOf roots input s (pi1ClaimsOf D roots.pi1 input s)
      (frameValues (pi1ClaimsOf D roots.pi1 input s), (C.compiled roots.pi1).witness input.toList s.toList) := by
  obtain ⟨hview, -, -, hhash⟩ := viewChecked_at C hchk roots
  have hc := C.compile_okAt roots.pi1
  have hck := RecCircuit.Compiled.checked_of_compile hc
  unfold pi1GraphChecks at hgc
  rcases hev : RecGraph.evalGraphDeployed (pi1GraphAt roots.pi1) (D.pi1IvAt roots.pi1) input.toList s with _ | out
  · rw [hev] at hgc; cases hgc
  rw [hev] at hgc
  dsimp only at hgc
  have hzero := zeros_of_checks hev ((Bool.and_eq_true _ _).mp hgc).1
  obtain ⟨hsz, hout⟩ := eval_some hev
  have hclaims : pi1ClaimsOf D roots.pi1 input s = out.calls.map words32 := by
    unfold pi1ClaimsOf; rw [hev]
  unfold Pi2Good Pi2Circuits.G
  generalize hcd : C.compiled roots.pi1 = c at hc hck hview hhash ⊢
  have hports : c.circuit.ports.size = 99 := viewOf_ports hview
  have hhl : c.circuit.hashed.length = 3 := by rw [hhash]; rfl
  have hroots0 : (publicCounts c.circuit).1 = 0 := viewOf_roots hview
  have helts0 : (publicCounts c.circuit).2 = 0 := viewOf_elements hview hhash
  have hsat : c.circuit.Satisfied (c.witness input.toList s.toList) := RecCircuit.Compiled.witness_satisfied hck
  have hpubW : c.pubW (c.witness input.toList s.toList) = input.toList :=
    RecCircuit.Compiled.pubW_witness hck (by simp)
  have hstr : c.streamW (RecCircuit.ofRG (pi1GraphAt roots.pi1) C.rootsAt (D.pi1IvAt roots.pi1) Data.hashed)
      (c.witness input.toList s.toList) = s.toList :=
    RecCircuit.Compiled.streamW_witness hck (by rw [ofRG_streamLen', Array.length_toList]; exact hsz)
  have hcopy := RecCircuit.Compiled.witness_copy (input := input.toList) (s := s.toList) hck
  have hwP : c.circuit.toPiop.Satisfies
      (fun j ↦ c.circuit.toPiop.limbVals (RecCircuit.emb (c.witness input.toList s.toList)) j)
      (RecCircuit.emb (c.witness input.toList s.toList)) := ⟨hcopy, fun _ _ ↦ rfl⟩
  have hE := RecCircuit.Compiled.compile_sound_end hc hwP
  -- the zero ports carry zeros
  have hz : ∀ J < c.circuit.ports.size, (c.circuit.ports.getD J default).source = .zero →
      c.circuit.portLimbs (c.witness input.toList s.toList) J = [0, 0, 0] := by
    intro J hJ hs
    by_cases hcz : c.zeroIndex J < c.claimZeros
    · exact RecCircuit.Compiled.claim_zero_port_witness hck hJ hs hcz
    · obtain ⟨hmem, hl⟩ := RecCircuit.Compiled.zero_port_sat hc hsat hJ hs (by omega)
      rw [hl, hpubW, hstr, hzero _ hmem]
      simp [RecCircuit.Compiled.limbsL]
  -- π2's public scalars
  obtain ⟨hwS, hwH⟩ := pubs_words (publicScalars_frameValues input.toList (pi1ClaimsOf D roots.pi1 input s))
  refine ⟨?_, ⟨hcopy, fun J hJ' ↦ ?_⟩, ?_⟩
  · -- the reads
    show List.Forall₂ (ReadMatch (frameOf _)) (D.pi2 roots.pi1).circuit.reads _
    rw [hD1]
    exact .cons rfl (.cons rfl (.cons rfl .nil))
  · -- the ports
    have hJ : J < c.circuit.ports.size := by simpa [RecPiop.Circuit.nP, RecCircuit.Circuit.toPiop] using hJ'
    show c.circuit.toPiop.limbVals (RecCircuit.emb (c.witness input.toList s.toList)) J = Fa.pubOf roots _ J
    rw [hpub roots, hcd, limbVals_toPiop' hc hJ]
    unfold pubOfC
    obtain ⟨hcR, hcE⟩ := publicCounts_port c.circuit hJ
    cases hs : (c.circuit.ports.getD J default).source with
    | statement =>
      rw [hE.1 J hJ hs, hpubW]
      have e := canon2_four _ _ 0 hwS
      simp only [Nat.zero_add] at e
      exact e.symm
    | claimHash j =>
      obtain ⟨hjl, -, hl⟩ := hE.2.2.2.2.2.2 hz J hJ j hs
      have hj : j < 3 := hhl ▸ hjl
      have hgj : c.circuit.hashed.getD j 0 = j := by rw [hhash]; interval_cases j <;> rfl
      rw [hl, hgj, hpubW, hstr, Array.toArray_toList]
      have hf : [frameOf (pi1ClaimsOf D roots.pi1 input s) 0, frameOf (pi1ClaimsOf D roots.pi1 input s) 1,
          frameOf (pi1ClaimsOf D roots.pi1 input s) 2].getD j [] = frameOf (pi1ClaimsOf D roots.pi1 input s) j := by
        interval_cases j <;> rfl
      have hgl : (pi1GraphAt roots.pi1).calls.length = 3 := by rw [hgr]; exact emittedAt_calls_length _
      have hjg : j < (pi1GraphAt roots.pi1).calls.length := by omega
      have hcall : out.calls.getD j [] = ((pi1GraphAt roots.pi1).calls.getD j []).flatMap
          (RecGraph.wordBytes s (RecCircuit.rgVals (pi1GraphAt roots.pi1) (D.pi1IvAt roots.pi1) input.toList
            s.toList)) := by
        rw [hout]
        simp [RecGraph.outputsOf, List.getD_eq_getElem?_getD, hjg]
      have hS : ∀ a, RecGraph.Word.stream a ∈ (pi1GraphAt roots.pi1).calls.getD j [] → a + 32 ≤ s.size := by
        intro a ha
        rw [hsz]
        rw [hgr] at ha hjg ⊢
        exact emittedAt_streams roots.pi1 j hjg a ha
      have hword : frameOf (pi1ClaimsOf D roots.pi1 input s) j = digestBytes (keccak256 (RecCircuit.claimEncoding s
          (RecCircuit.rgVals (pi1GraphAt roots.pi1) (D.pi1IvAt roots.pi1) input.toList s.toList)
          ((pi1GraphAt roots.pi1).calls.getD j []))) := by
        unfold frameOf
        rw [hclaims, getD_map_words32, hcall, claimHash_words32 _ _ _ hS]
      exact (canon2_four _ _ (4 + 4 * j) fun k hk ↦ by rw [hwH j hj k hk, hf, hword]).symm
    | zero =>
      rw [hz J hJ hs]
      simp [pubOfSource, F192.ofF64_zero]
    | pad =>
      rw [RecCircuit.Compiled.ports_carry hck hsat J hJ, RecCircuit.Compiled.portMeaning, hs]
      simp [pubOfSource, F192.ofF64_zero]
    | root i => exact absurd (hcR i hs) (by omega)
    | element e => exact absurd (hcE e hs) (by omega)
  · -- the stream
    show D.pi1Stream (c.witness input.toList s.toList) = s
    rw [C.stream_eqAt roots.pi1, hcd, hstr, Array.toArray_toList]

end Witness

variable (prog : KeccakVm.Program) (hprog : RecGraphKeccak.Pi1.keccak128.logBytecode = prog.logSize)

/-- **The circuit compiler's completeness at the real deployment** (`Pi2WitnessExists` of its compiled circuits
`pi2Circuits_real` and facts `pi2Facts_real`), from `GraphsAgreeK4` and the evaluated checks: on a stream on which
π1-rec4's graph checks hold, an honest witness exists. -/
theorem pi2WitnessExists_real (hg : RecGraphKeccak.GraphsAgreeK4) (hd : DigestChecked) (hs : SetupRootChecked)
    (hiv : IvChecked) (roots : RecSetupRoots) (input : Vector UInt8 32) (s : Array UInt8)
    (hgc : pi1GraphChecks (pi1GraphAt roots.pi1) ((realDeployment prog hprog).pi1IvAt roots.pi1) input s = true) :
    ∃ vw, Pi2Good (realDeployment prog hprog) (pi2Circuits_real prog hprog hg hiv).G
      (pi2Facts_real prog hprog hg hd hs hiv).pubOf roots input s
      (pi1ClaimsOf (realDeployment prog hprog) roots.pi1 input s) vw :=
  ⟨_, pi2Good_of_checks (fun _ ↦ rfl) _ (pi2ViewChecked_real prog hprog hg hiv) _ (fun _ ↦ rfl) (pi1GraphAt_eq hg)
    roots input s hgc⟩

/-! ## A non-hole position -/

/-- **A non-hole position** in every valid circuit with fewer ports than positions. -/
theorem exists_nonhole {G : RecPiop.Circuit E} (hV : G.Valid) (h : G.nP < G.N) : ∃ i < G.N, ¬ G.IsHole i := by
  by_contra hc
  have hall : ∀ i ∈ Finset.range G.N, G.IsHole i := fun i hi ↦ by
    by_contra hh
    exact hc ⟨i, Finset.mem_range.mp hi, hh⟩
  have hcard := RecPiop.Circuit.card_holes hV
  rw [Finset.filter_true_of_mem hall, Finset.card_range] at hcard
  omega

/-- **π2's circuit has a non-hole position** (`99` ports among `2^24` positions), from the view check. -/
theorem nonhole_of_view {D : RecDeployment} (C : Pi2Circuits D) (hchk : Pi2ViewChecked C) (Fa : Pi2Facts D C)
    (roots : RecSetupRoots) : ∃ i < (C.G roots).N, ¬ (C.G roots).IsHole i := by
  refine exists_nonhole (Fa.valid roots) ?_
  have hnP : (C.G roots).nP = 99 := by
    show ((C.compiled roots.pi1).circuit.ports.toList.map (·.position)).length = 99
    rw [List.length_map, Array.length_toList, viewOf_ports (viewChecked_at C hchk roots).1]
  rw [hnP, RecPiop.Circuit.N, Fa.logN roots]
  norm_num

/-- **The real circuit has a non-hole position** at every setup. -/
theorem nonhole_real (hg : RecGraphKeccak.GraphsAgreeK4) (hd : DigestChecked) (hs : SetupRootChecked)
    (hiv : IvChecked) (roots : RecSetupRoots) :
    ∃ i < ((pi2Circuits_real prog hprog hg hiv).G roots).N, ¬ ((pi2Circuits_real prog hprog hg hiv).G roots).IsHole i :=
  nonhole_of_view _ (pi2ViewChecked_real prog hprog hg hiv) (pi2Facts_real prog hprog hg hd hs hiv) roots

/-! ## π1's openings, from π1's graph verifier -/

theorem length_of_mapM_some {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys → l.length = ys.length
  | [], ys, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | a :: l, ys, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some x =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some zs =>
        simp only [ha, hl, Option.bind_some, Option.some.injEq] at h
        subst h
        simp [length_of_mapM_some f l zs hl]

theorem list_three' {α : Type} {u : List α} (h : u.length = 3) : ∃ a b c, u = [a, b, c] := by
  match u, h with
  | [a, b, c], _ => exact ⟨a, b, c, rfl⟩

/-- **π1's graph verifier's verdict includes the graph's checks.** -/
theorem graphChecks_of_verifier {H : List UInt8 → Id Digest} {F : KeccakState → Id KeccakState} {D : RecDeployment}
    {roots : UniKeccak.SetupRootsK} {input : Vector UInt8 32} {p1 : UniKeccak.KeccakProof}
    (h : Id.run (Pi2H.pi1GraphVerifierWithH (m := Id) H F D roots input p1) = true) :
    pi1GraphChecks (pi1GraphAt roots) (D.pi1IvAt roots) input p1.stream = true := by
  unfold Pi2H.pi1GraphVerifierWithH at h
  unfold pi1GraphChecks
  rcases hev : RecGraph.evalGraphDeployed (pi1GraphAt roots) (D.pi1IvAt roots) input.toList p1.stream with _ | out
  · rw [hev] at h; exact absurd h (by simp)
  rw [hev] at h
  dsimp only at h ⊢
  by_contra hc
  rw [Bool.not_eq_true] at hc
  rw [hc] at h
  exact absurd h (by simp)

/-- **A π1 opening the verifier accepts, as the contract checks it**: a call decoding to the opening, at a size the
contract does not read the out-of-domain point of (`oodRead`), opened by `pcsOpenWordsH` on its words. -/
theorem pcsOpenWordsH_of_decoded (Hk : List UInt8 → Digest) (F : KeccakState → Id KeccakState) {call : List UInt8}
    {o : Pi1Opening} (hd : decodePi1Call call = some o) {n : ℕ} (hn : oodRead n = false) {p : Compile.Proof}
    (h : Id.run (UniKeccakComplete.pcsOpenKH (m := Id) (Pure.pure ∘ Hk) F n o.1 o.2.1 o.2.2.1 o.2.2.2 p) = true) :
    Id.run (Pi2H.pcsOpenWordsH (m := Id) (Pure.pure ∘ Hk) F (words32 call) p) = true := by
  have hw := claimOfWords_of_decodePi1Call hd
  have hlen : o.2.2.1.length = n := by
    by_contra hne
    unfold UniKeccakComplete.pcsOpenKH at h
    simp [hne] at h
  rw [Pi2H.pcsOpenWordsH_eq _ _ _ _ _ hw, Pi2H.openAtH_of_not _ _ _ _ (by rw [hlen]; exact hn), hlen]
  exact h

theorem oodRead_c1 : oodRead (UniKeccak.stackVarsK RecGraphKeccak.Pi1.keccak128 .c1) = false := by
  rw [show RecGraphKeccak.Pi1.keccak128 = UniKeccakSound.keccakRefShape from rfl,
    UniKeccakComplete.reference_stackVars_c1]; rfl
theorem oodRead_c2 : oodRead (UniKeccak.stackVarsK RecGraphKeccak.Pi1.keccak128 .c2) = false := by
  rw [show RecGraphKeccak.Pi1.keccak128 = UniKeccakSound.keccakRefShape from rfl,
    UniKeccakComplete.reference_stackVars_c2]; rfl
theorem oodRead_setup : oodRead (UniKeccak.stackVarsK RecGraphKeccak.Pi1.keccak128 .setup) = false := by
  rw [show RecGraphKeccak.Pi1.keccak128 = UniKeccakSound.keccakRefShape from rfl,
    UniKeccakComplete.reference_stackVars_setup]; rfl

/-- **π1's openings in the contract, from π1's graph verifier** (`Pi2Pi1Openings`'s content): at pure `(Hk, F)`, if
π1-rec4's graph verifier accepts `p1` at a setup commitment `roots`, π1's claims as the graph makes them there are three
and their openings with `p1`'s `C1`, `C2`, setup proofs accept as the contract checks them (`pcsOpenWordsH`). -/
theorem pi1Openings_of_verifierH {D : RecDeployment} (hshape : D.pi1.shape = RecGraphKeccak.Pi1.keccak128)
    (Hk : List UInt8 → Digest) (F : KeccakState → Id KeccakState) (roots : UniKeccak.SetupRootsK)
    (input : Vector UInt8 32) (p1 : UniKeccak.KeccakProof)
    (h : Id.run (Pi2H.pi1GraphVerifierWithH (m := Id) (Pure.pure ∘ Hk) F D roots input p1) = true) :
    (pi1ClaimsOf D roots input p1.stream).length = 3 ∧
      Id.run (Pi2H.pcsOpenWordsH (m := Id) (Pure.pure ∘ Hk) F ((pi1ClaimsOf D roots input p1.stream).getD 0 [])
        p1.c1) = true ∧
      Id.run (Pi2H.pcsOpenWordsH (m := Id) (Pure.pure ∘ Hk) F ((pi1ClaimsOf D roots input p1.stream).getD 1 [])
        p1.c2) = true ∧
      Id.run (Pi2H.pcsOpenWordsH (m := Id) (Pure.pure ∘ Hk) F ((pi1ClaimsOf D roots input p1.stream).getD 2 [])
        p1.setup) = true := by
  unfold Pi2H.pi1GraphVerifierWithH at h
  unfold pi1ClaimsOf
  rcases hev : RecGraph.evalGraphDeployed (pi1GraphAt roots) (D.pi1IvAt roots) input.toList p1.stream with _ | out
  · rw [hev] at h; exact absurd h (by simp)
  rw [hev] at h
  dsimp only at h ⊢
  rcases hm : out.calls.mapM decodePi1Call with _ | ops
  · rw [hm] at h; simp at h
  rw [hm] at h
  by_cases h3 : ops.length = 3
  · obtain ⟨c1, c2, c3, hcl⟩ := list_three' ((length_of_mapM_some _ _ _ hm).trans h3)
    rw [hcl] at hm
    obtain ⟨o1, o2, o3, rfl, hd1, hd2, hd3⟩ := mapM_three _ _ _ _ _ hm
    rw [hshape] at h
    dsimp only at h
    split_ifs at h with hck hne
    all_goals try (simp at h; done)
    have h' : (((true && Id.run (UniKeccakComplete.pcsOpenKH (m := Id) (Pure.pure ∘ Hk) F
        (UniKeccak.stackVarsK RecGraphKeccak.Pi1.keccak128 .c1) o1.1 o1.2.1 o1.2.2.1 o1.2.2.2 p1.c1)) &&
        Id.run (UniKeccakComplete.pcsOpenKH (m := Id) (Pure.pure ∘ Hk) F
        (UniKeccak.stackVarsK RecGraphKeccak.Pi1.keccak128 .c2) o2.1 o2.2.1 o2.2.2.1 o2.2.2.2 p1.c2)) &&
        Id.run (UniKeccakComplete.pcsOpenKH (m := Id) (Pure.pure ∘ Hk) F
        (UniKeccak.stackVarsK RecGraphKeccak.Pi1.keccak128 .setup) o3.1 o3.2.1 o3.2.2.1 o3.2.2.2 p1.setup)) = true := h
    simp only [Bool.and_eq_true, Bool.true_and] at h'
    obtain ⟨⟨b1, b2⟩, b3⟩ := h'
    rw [hcl]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · exact pcsOpenWordsH_of_decoded Hk F hd1 oodRead_c1 b1
    · exact pcsOpenWordsH_of_decoded Hk F hd2 oodRead_c2 b2
    · exact pcsOpenWordsH_of_decoded Hk F hd3 oodRead_setup b3
  · simp [h3] at h

end RecCompose.Pi2W

/-- info: 'RecCompose.Pi2W.pi2Good_of_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2W.pi2Good_of_checks

/-- info: 'RecCompose.Pi2W.pi2WitnessExists_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2W.pi2WitnessExists_real

/-- info: 'RecCompose.Pi2W.nonhole_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2W.nonhole_real

/-- info: 'RecCompose.Pi2W.pi1Openings_of_verifierH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2W.pi1Openings_of_verifierH
