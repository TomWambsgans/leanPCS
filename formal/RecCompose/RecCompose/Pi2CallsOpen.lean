-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The contract's π1 calls (`formal/RecStatement`:
-- `pi1OpsOf`, `decodeWith`; `Data.pi1Calls`, the Rust's `spec::Circuit::calls`) on π2's honest stream, and π1-rec3's
-- graph's openings (`pi1GraphVerifierWith`, with Keccak-256 explicit in `Pi2CompleteH`).
import RecCompose.Pi2ProbStaged
import RecCompose.Layouts
import RecCompose.FsVerifier
import RecCompose.Meanings
import RecCompose.End

/-!
# π1's openings in the contract, on π2's honest proof

**`pi2Pi1Openings hD C hchk hroots hg : Pi2Pi1Openings D C (pi2Facts hD C hchk)`**: at pure `(H, F)`, on a π1 proof
π1-rec3's graph accepts (its openings over `(H, F)`) with the honest witness π2's prover takes, the contract's three π1
calls on π2's honest proof decode (`pi1OpsOf_some`: each of `Data.pi1Calls` is a root word, a registered layout word, the
count one and one claim's element words, `decode_call`) and their openings accept: the circuit's corollary
(`circuitBridge` with the facts helper's meanings, `Pi2CircuitAccepts`) makes the graph's decoded calls the contract's
(their layouts, claims and `C1`'s, `C2`'s roots; the setup's root the contract's constant), so the graph's three
openings (`graphH_eq`) are the contract's `openSeqH` (`openSeqH_eq`).

**`recCompleteness2_pi2_closed`**, **`recCompleteness_pi2_closed_fs`**: `Pi2ProbStaged`'s, without `Pi2Pi1Openings`
(taking `GraphsAgree`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2O

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM (KeccakCalls)
open LeanVM.Protocol.Compile.Rom (missProb)
open Pi2S Pi2K Pi2E Pi2G
open scoped ENNReal

/-! ## A call's words decode -/

/-- The words that are claims' elements. -/
def isElt : CallWord → Bool
  | .element _ => true
  | .pair _ _ => true
  | _ => false

/-- An element word's element. -/
def cwE (reads : List Read) (r : Reduced) : CallWord → E
  | .element i => r.scalars.getD ((elementIndices reads).getD i 0) 0
  | .pair e c =>
    let pp := r.pairPoints.getD ((elementIndices reads).getD e 0) (0, 0)
    if c = 0 then pp.1 else pp.2
  | _ => 0

theorem callWord_of_isElt (reads : List Read) (stream : Array UInt8) (r : Reduced) (c : CallWord)
    (h : isElt c = true) : callWord reads stream r c = UniStatement.elementWord (cwE reads r c) := by
  cases c with
  | const w => simp [isElt] at h
  | root i => simp [isElt] at h
  | element i => rfl
  | pair e c => rfl

/-- **A PCS claim's words of element words decode**: a root's `32` bytes, then at least two elements (the answer, the
point's coordinates, the value). -/
theorem claimOfWords_elems (r : List UInt8) (hr : r.length = 32) (es : List E) (hes : 2 ≤ es.length) :
    ∃ x, claimOfWords (r :: es.map UniStatement.elementWord) = some x := by
  match es, hes with
  | e0 :: e1 :: rest, _ =>
    have h : r :: (e0 :: e1 :: rest).map UniStatement.elementWord =
        [r, UniStatement.elementWord e0] ++ claimWords ((e1 :: rest).dropLast, (e1 :: rest).getLast (by simp)) := by
      simp only [claimWords, List.dropLast_append_getLast, List.map_cons, List.cons_append, List.nil_append]
    rw [h]
    exact ⟨_, Pi2C.claimOfWords_claim _ hr _ _⟩

/-- A call of a root word and element words decodes. -/
theorem decode_call (reads : List Read) (stream : Array UInt8) (r : Reduced) (c0 : CallWord) (rest : List CallWord)
    (hroot : (callWord reads stream r c0).length = 32) (hall : rest.all isElt = true) (hl : 2 ≤ rest.length) :
    ∃ x, claimOfWords ((c0 :: rest).map (callWord reads stream r)) = some x := by
  have hmap : rest.map (callWord reads stream r) = (rest.map (cwE reads r)).map UniStatement.elementWord := by
    rw [List.map_map]
    exact List.map_congr_left fun c hc ↦ callWord_of_isElt reads stream r c (List.all_eq_true.mp hall c hc)
  rw [List.map_cons, hmap]
  exact claimOfWords_elems _ hroot _ (by simpa using hl)

/-! ## `Data.pi1Calls` -/

/-- **`Data.pi1Calls`' shape** (kernel decisions on the recorded calls): three calls, `C1`'s and `C2`'s a stream root
then element words, the setup's two constants (its root and answer, which the contract replaces) then element words. -/
theorem data_calls :
    Data.pi1Calls.length = 3 ∧
    (Data.pi1Calls.getD 0 []).head? = some (.root 0) ∧ ((Data.pi1Calls.getD 0 []).drop 1).all isElt = true ∧
      2 ≤ ((Data.pi1Calls.getD 0 []).drop 1).length ∧
    (Data.pi1Calls.getD 1 []).head? = some (.root 1) ∧ ((Data.pi1Calls.getD 1 []).drop 1).all isElt = true ∧
      2 ≤ ((Data.pi1Calls.getD 1 []).drop 1).length ∧
    ((Data.pi1Calls.getD 2 []).drop 2).all isElt = true ∧ 1 ≤ ((Data.pi1Calls.getD 2 []).drop 2).length := by
  decide +kernel

/-- **The contract's π1 calls decode on π2's stream**, its run over Keccak-f[1600] succeeding. -/
theorem pi1OpsOf_some (D : RecDeployment) (hD : D.Real) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (stream : Array UInt8) (r : Reduced)
    (hr : (run (Spec.of (D.circuitAt roots.pi1).circuit) [] input.toList stream).result = .ok r)
    (hsz : stream.size = pi2Bytes (Spec.of Data.circuit)) :
    ∃ ops, pi1OpsOf D roots input stream = some ops := by
  have hview : (D.circuitAt roots.pi1).circuit = Data.circuit := hD.1 _
  obtain ⟨hl3, h0, ha0, hn0, h1, ha1, hn1, ha2, hn2⟩ := data_calls
  have hrl : ∀ i < 2, (callWord (D.circuitAt roots.pi1).circuit.reads stream r (.root i)).length = 32 := by
    intro i hi
    show (streamWord stream ((rootsAt (D.circuitAt roots.pi1).circuit.reads).getD i 0)).length = 32
    refine streamWord_length _ _ ?_
    rw [hsz, hview]
    interval_cases i <;> decide +kernel
  obtain ⟨a, b, c, hcl⟩ : ∃ a b c, Data.pi1Calls = [a, b, c] := by
    match Data.pi1Calls, hl3 with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  obtain ⟨-, w1, w2, rest, hw⟩ := pi1CallsShape_data D hD.2.1
  rw [hD.2.1, hcl] at hw
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hw
  subst hw
  rw [hcl] at h0 ha0 hn0 h1 ha1 hn1 ha2 hn2
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h0 ha0 hn0 h1 ha1 hn1 ha2 hn2
  obtain ⟨a0, as', rfl⟩ : ∃ a0 as', a = a0 :: as' := by
    cases a with
    | nil => simp at h0
    | cons x xs => exact ⟨x, xs, rfl⟩
  obtain ⟨b0, bs, rfl⟩ : ∃ b0 bs, b = b0 :: bs := by
    cases b with
    | nil => simp at h1
    | cons x xs => exact ⟨x, xs, rfl⟩
  simp only [List.head?_cons, Option.some.injEq, List.drop_succ_cons, List.drop_zero] at h0 h1 ha0 hn0 ha1 hn1 ha2 hn2
  subst h0 h1
  obtain ⟨x0, hx0⟩ := decode_call (D.circuitAt roots.pi1).circuit.reads stream r (.root 0) as' (hrl 0 (by decide)) ha0 hn0
  obtain ⟨x1, hx1⟩ := decode_call (D.circuitAt roots.pi1).circuit.reads stream r (.root 1) bs (hrl 1 (by decide)) ha1 hn1
  have hmap2 : rest.map (callWord (D.circuitAt roots.pi1).circuit.reads stream r) = (rest.map (cwE (D.circuitAt roots.pi1).circuit.reads r)).map UniStatement.elementWord := by
    rw [List.map_map]
    exact List.map_congr_left fun c hc ↦ callWord_of_isElt (D.circuitAt roots.pi1).circuit.reads stream r c (List.all_eq_true.mp ha2 c hc)
  obtain ⟨x2, hx2⟩ := claimOfWords_elems (digestBytes roots.pi1.f) (Pi1Decode.length_digestBytes _)
    (roots.pi1.fOod :: rest.map (cwE (D.circuitAt roots.pi1).circuit.reads r)) (by simpa using hn2)
  refine ⟨[x0, x1, x2], ?_⟩
  unfold pi1OpsOf
  dsimp only
  rw [hr]
  dsimp only
  unfold contractPi1Openings
  rw [pcsCalls_take _ _ _ _ _ _ (by simp [pi1CallsWith, hD.2.1, hcl]), hD.2.1, hcl]
  simp only [pi1CallsWith, List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil]
  rw [List.map_cons] at hx0 hx1
  rw [hx0, hx1]
  have e2 : callWord (D.circuitAt roots.pi1).circuit.reads stream r (CallWord.const (digestBytes roots.pi1.f)) ::
      callWord (D.circuitAt roots.pi1).circuit.reads stream r
        (CallWord.const (UniStatement.elementWord roots.pi1.fOod)) ::
      rest.map (callWord (D.circuitAt roots.pi1).circuit.reads stream r) =
      digestBytes roots.pi1.f :: (roots.pi1.fOod :: rest.map (cwE (D.circuitAt roots.pi1).circuit.reads r)).map
        UniStatement.elementWord := by
    rw [hmap2]
    rfl
  rw [e2, hx2]
  rfl

/-! ## The graph's openings and the contract's -/

/-- **π1-rec3's graph with its openings over `(H, F)`**, its checks holding and its calls decoding to three openings:
the three PCS checks, the setup's commitment the deployment's. -/
theorem graphH_eq (H : List UInt8 → Id Digest) (F : KeccakState → Id KeccakState) (D : RecDeployment)
    (roots : UniKeccak.SetupRootsK) (input : Vector UInt8 32) (p1 : UniKeccak.KeccakProof)
    (gout : RecGraph.Outputs) (g0 g1 g2 : Pi1Opening)
    (hev : RecGraph.evalGraphDeployed RecGraphKeccak.Pi1.pi1GraphK (D.pi1IvAt roots) input.toList p1.stream = some gout)
    (hchk : (gout.zeros.all (· == 0) && gout.nonzeros.all (· != 0)) = true)
    (hdec : gout.calls.mapM decodePi1Call = some [g0, g1, g2]) :
    Id.run (Pi2H.pi1GraphVerifierWithH (m := Id) H F D roots input p1) =
      (((true && Id.run (UniKeccakComplete.pcsOpenKH H F (UniKeccak.stackVarsK D.pi1.shape .c1) g0.1 g0.2.1 g0.2.2.1
          g0.2.2.2 p1.c1)) &&
        Id.run (UniKeccakComplete.pcsOpenKH H F (UniKeccak.stackVarsK D.pi1.shape .c2) g1.1 g1.2.1 g1.2.2.1 g1.2.2.2
          p1.c2)) &&
        Id.run (UniKeccakComplete.pcsOpenKH H F (UniKeccak.stackVarsK D.pi1.shape .setup) roots.f roots.fOod g2.2.2.1
          g2.2.2.2 p1.setup)) := by
  unfold Pi2H.pi1GraphVerifierWithH
  rw [hev]
  simp only [hchk, hdec, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- **The contract's three π1 openings**: each a PCS check at its point's length. -/
theorem openSeqH_eq (H : List UInt8 → Id Digest) (F : KeccakState → Id KeccakState) (o0 o1 o2 : Pi1Opening)
    (proof : RecProof) :
    Id.run (Pi2H.openSeqH (m := Id) H F [o0, o1, o2] proof) =
      ((Id.run (UniKeccakComplete.pcsOpenKH H F o0.2.2.1.length o0.1 o0.2.1 o0.2.2.1 o0.2.2.2 proof.c1) &&
        Id.run (UniKeccakComplete.pcsOpenKH H F o1.2.2.1.length o1.1 o1.2.1 o1.2.2.1 o1.2.2.2 proof.c2)) &&
        Id.run (UniKeccakComplete.pcsOpenKH H F o2.2.2.1.length o2.1 o2.2.1 o2.2.2.1 o2.2.2.2 proof.f)) := by
  unfold Pi2H.openSeqH Pi2H.openAtH
  rfl

/-- **π2's honest proof**: its stream the honest prover's, π1's opening proofs π1's. -/
theorem pi2Prover_some {D : RecDeployment} {C : Pi2Circuits D} (Fa : Pi2Facts D C) (Hk : List UInt8 → Digest)
    (F : KeccakState → Id KeccakState) (fuel : ℕ) (input : Vector UInt8 32) (p1 : UniKeccak.KeccakProof)
    (proof : RecProof) (hp : Id.run (pi2ProverWith (m := Id) (Pure.pure ∘ Hk) F D C Fa fuel input p1) = some proof) :
    proof.stream = (outOf D Hk (rootsH D Hk F) (C.G (rootsH D Hk F)) pi2Ood input
        (pi2Choice D C Fa (rootsH D Hk F) input p1.stream).1 (pi2Choice D C Fa (rootsH D Hk F) input p1.stream).2).stream ∧
      proof.c1 = p1.c1 ∧ proof.c2 = p1.c2 ∧ proof.f = p1.setup := by
  rw [pi2ProverWith_run] at hp
  simp only at hp
  rw [pi2ProveWith_run] at hp
  simp only at hp
  revert hp
  generalize UniKeccakComplete.pcsProveH (m := Id) (Pure.pure ∘ Hk) F fuel _ _ _ _ ((Spec.of _).core.run _).fold = rW
  generalize UniKeccakComplete.pcsProveH (m := Id) (Pure.pure ∘ Hk) F fuel _ _ _ _ (proverOut _ _ _ _ _ _ _ _ _).inputs.ξ = rS
  generalize UniKeccakComplete.pcsProveH (m := Id) (Pure.pure ∘ Hk) F fuel _ _ _ _
    ((Spec.of _).core.run _).quotientValue = rQ1
  generalize UniKeccakComplete.pcsProveH (m := Id) (Pure.pure ∘ Hk) F fuel _ _ _ _
    ((Spec.of _).core.run _).pushesValue = rQ2
  generalize UniKeccakComplete.pcsProveH (m := Id) (Pure.pure ∘ Hk) F fuel _ _ _ _
    ((Spec.of _).core.run _).sumValue = rQ3
  intro hp
  rcases rW with _ | a
  · simp at hp
  rcases rS with _ | b
  · simp at hp
  rcases rQ1 with _ | c
  · simp at hp
  rcases rQ2 with _ | d
  · simp at hp
  rcases rQ3 with _ | e
  · simp at hp
  simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hp
  subst hp
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## π1's openings in the contract -/

/-- **`Pi2Pi1Openings` at the real deployment's facts**: the circuit's corollary (`circuitBridge` with the facts
helper's meanings) makes the graph's calls the contract's, so the graph's openings are the contract's. -/
theorem pi2Pi1Openings {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hg : GraphsAgree) :
    Pi2Pi1Openings D C (pi2Facts hD C hchk) := by
  intro Ht Ft input p1 proof hgood ha1 hpr
  obtain ⟨hmatch, hsat, hstr⟩ := hgood
  have hview : (D.circuitAt (rootsH D Ht Ft).pi1).circuit = Data.circuit := hD.1 _
  obtain ⟨hps, hc1, hc2, hcf⟩ := pi2Prover_some (pi2Facts hD C hchk) Ht Ft _ input p1 proof hpr
  -- π2's run on the honest stream, over `Ht` and over Keccak-f[1600]
  obtain ⟨r, hr, -, hsc, -, -, -, -, -, hi, -, -⟩ := runWith_honest Ht (C.G (rootsH D Ht Ft)) pi2Ood
    (D.circuitAt (rootsH D Ht Ft).pi1).circuit (D.circuitAt (rootsH D Ht Ft).pi1).setupStack
    (ivOf D Ht (rootsH D Ht Ft)) input.toList (pi2Choice D C (pi2Facts hD C hchk) (rootsH D Ht Ft) input p1.stream).1
    (pi2Choice D C (pi2Facts hD C hchk) (rootsH D Ht Ft) input p1.stream).2 hmatch
    (by rw [hview, (pi2Facts hD C hchk).logW]; rfl)
  obtain ⟨hpost, -⟩ := holds_id (Pi2H.runWithH_post (m := Id) (Pure.pure ∘ Ht)
    (Spec.of (D.circuitAt (rootsH D Ht Ft).pi1).circuit) (ivOf D Ht (rootsH D Ht Ft)) input.toList
    (outOf D Ht (rootsH D Ht Ft) (C.G (rootsH D Ht Ft)) pi2Ood input
      (pi2Choice D C (pi2Facts hD C hchk) (rootsH D Ht Ft) input p1.stream).1
      (pi2Choice D C (pi2Facts hD C hchk) (rootsH D Ht Ft) input p1.stream).2).stream)
  obtain ⟨hsz, hsc', hpp⟩ := hpost r hr
  obtain ⟨r', hr', hsc'', -⟩ := run_ok_of_runWith (m := Id) _ input.toList _ [] r hsz hsc' hpp
  have hscal : pi2Scalars D (rootsH D Ht Ft) input
      (outOf D Ht (rootsH D Ht Ft) (C.G (rootsH D Ht Ft)) pi2Ood input
        (pi2Choice D C (pi2Facts hD C hchk) (rootsH D Ht Ft) input p1.stream).1
        (pi2Choice D C (pi2Facts hD C hchk) (rootsH D Ht Ft) input p1.stream).2).stream =
      publicScalarsOf input.toList (pi2Choice D C (pi2Facts hD C hchk) (rootsH D Ht Ft) input p1.stream).1 := by
    unfold pi2Scalars
    rw [hr']
    dsimp only
    rw [hsc'', hsc, hi]
  -- the contract's π1 calls
  obtain ⟨ops, hops⟩ := pi1OpsOf_some D hD (rootsH D Ht Ft) input _ r' hr' (by rw [hsz, hview])
  obtain ⟨o0, o1, o2, rfl, l0, l1, l2, hf, hfo⟩ :=
    contract_ops D (pi1CallsShape_data D hD.2.1) (rootsH D Ht Ft) input _ _ hops
  -- the circuit's corollary
  have hca := pi2CircuitAccepts_of_bridge C (pi2Facts hD C hchk) hroots hg
    (circuitBridge D hD C (pi2Facts hD C hchk) hroots hg (statementPortMeaning hD C hchk)
      (zeroPortsMeaning hD C hchk) (callWordsAgree hD C hchk))
  have hacc := hca (rootsH D Ht Ft) input _ _ _ (by rw [hscal]; exact hsat) hops
  rw [hstr] at hacc
  obtain ⟨gout, gops, hev, hz, hnz, hdec, hmap, htake⟩ := hacc
  have hl3 : gops.length = 3 := by
    have := congrArg List.length hmap
    simpa using this
  obtain ⟨g0, g1, g2, rfl⟩ : ∃ a b c, gops = [a, b, c] := by
    match gops, hl3 with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  have hchk' : (gout.zeros.all (· == 0) && gout.nonzeros.all (· != 0)) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    exact ⟨hz, hnz⟩
  rw [graphH_eq _ _ D _ input p1 gout g0 g1 g2 hev hchk' hdec] at ha1
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
  obtain ⟨e0, e1, e2⟩ := hmap
  simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.cons.injEq, and_true,
    Prod.mk.injEq] at htake
  obtain ⟨⟨r0, d0⟩, r1, d1⟩ := htake
  refine ⟨[o0, o1, o2], by rw [hps]; exact hops, ?_⟩
  rw [openSeqH_eq, hc1, hc2, hcf]
  have hsh : D.pi1.shape = RecGraphKeccak.Pi1.keccak128 := hD.2.2.1
  rw [hsh] at ha1
  rw [l0, l1, l2, ← r0, ← d0, ← r1, ← d1, hf, hfo, ← e0, ← e1, ← e2]
  simpa using ha1

/-! ## π2's completeness without `Pi2Pi1Openings` -/

/-- **π2's completeness, `Pi2Pi1Openings` proved** (`pi2Pi1Openings`, from `GraphsAgree`): `recCompleteness2_pi2_staged`
from the staged run's named facts and the witness's completeness. -/
theorem recCompleteness2_pi2_closed {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hg : GraphsAgree) (P1 : Pi1Prover D)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniKeccak.KeccakProof))
    {N : ℕ} {εt : ℝ≥0∞}
    (hexp : Pi2ExperimentLe D C (pi2Facts hD C hchk) P1 P1k) (hrun : Pi2RunAt D C (pi2Facts hD C hchk) P1k)
    (hdup : Pi2RunDuplex D C (pi2Facts hD C hchk) P1k) (hcost : Pi2RunCost D C (pi2Facts hD C hchk) P1k N)
    (hhash : Pi2HashBeforeAlpha D C (pi2Facts hD C hchk) P1k) (htf : Pi2TFresh D C (pi2Facts hD C hchk) P1k εt)
    (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk)) :
    RecCompleteness2 D P1 (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel)
      (delta2 N εt ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness2_pi2_staged hD C hchk hroots P1 P1k hexp hrun hdup hcost hhash htf
    (pi2Pi1Openings hD C hchk hroots hg) hwc

/-- **The recursive verifier's completeness end to end, `Pi2Pi1Openings` proved.** -/
theorem recCompleteness_pi2_closed_fs {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hg : GraphsAgree) (P1 : Pi1Prover D)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniKeccak.KeccakProof))
    {N : ℕ} {εt : ℝ≥0∞}
    (hexp : Pi2ExperimentLe D C (pi2Facts hD C hchk) P1 P1k) (hrun : Pi2RunAt D C (pi2Facts hD C hchk) P1k)
    (hdup : Pi2RunDuplex D C (pi2Facts hD C hchk) P1k) (hcost : Pi2RunCost D C (pi2Facts hD C hchk) P1k N)
    (hhash : Pi2HashBeforeAlpha D C (pi2Facts hD C hchk) P1k) (htf : Pi2TFresh D C (pi2Facts hD C hchk) P1k εt)
    (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk))
    (δ1 δh : ℝ≥0∞) (h1 : Pi1CompletenessKeccak D P1 δ1) (hh : Pi1HazardKeccakHonest D P1 δh) :
    RecCompletenessWith D (composeProver D P1 (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel))
      (δ1 + δh + delta2 N εt ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness_pi2_staged_fs hD C hchk hroots P1 P1k hexp hrun hdup hcost hhash htf
    (pi2Pi1Openings hD C hchk hroots hg) hwc δ1 δh h1 hh

end RecCompose.Pi2O

/-- info: 'RecCompose.Pi2O.pi2Pi1Openings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2O.pi2Pi1Openings

/-- info: 'RecCompose.Pi2O.recCompleteness2_pi2_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2O.recCompleteness2_pi2_closed

/-- info: 'RecCompose.Pi2O.recCompleteness_pi2_closed_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2O.recCompleteness_pi2_closed_fs
