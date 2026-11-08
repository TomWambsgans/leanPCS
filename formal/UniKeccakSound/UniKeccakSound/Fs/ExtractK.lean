-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `UniSound/FsExtract.lean` (after
-- `formal/EndToEnd/Soundness/Extract.lean`) for the Keccak extractor (`formal/UniKeccak`'s `uniExtractorK`:
-- `c1LayoutK`, `kvStack`).
import UniKeccakSound.Fs.SetupK
import UniSound.FsExtract

/-!
# The Keccak extractor's reading: `uniExtractorK` finds what the composed extractor lists

**`uniExtractBridgeK`**: `UniExtractBridgeK` (`CoupleK.lean`), with `C1`'s variables below `256`
(`LayoutVarsSmallK`). As `UniSound.uniExtractBridge_of_c1`: round `0`'s message is `C1`'s root the stream names
(`c1RootOfK`); the composed candidate is a stack of mumbai's `decodeStacks` for the Merkle word under it
(`UniSound.mem_tableCode_cands`, the plain layout's table read back as the stack, `rdTab_tabOf_plain`); the Keccak
extractor's word is mumbai's `committedLeaves` (`c1WordK_eq_committed`) and agrees with the composed one on every
column, so its list decoder lists the same stack; `C1`'s variables are its layout word's (`wvK_zero`); the row counts
are the stream's (`rowsOfBytes_rowBytes`); and `extractFromK` returns the first candidate whose Keccak VM stack
(`kvStack`) satisfies `KvHolds` (`extractFromK_spec`).
-/

-- The relation is `KvHolds` of a symbolic instance: no simprocs here, which would try to decide it.
set_option simprocs false

namespace UniKeccakSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement UniSound UniKeccak

/-- **Round `0`'s message is `C1`'s root** the stream names, without scalars. -/
theorem msgK_uView_c1K {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain) (nV V : ℕ)
    (π : UPf) : msgK (uView (uRoundsK Fl nV V)) π 0 = (some (toB (c1RootOfK (kpOf π))), []) :=
  rfl

/-- **What `C1`'s decoder lists**: under a root, the stacks mumbai's `decodeStacks` lists for the Merkle word, each
read back (through the plain layout's table) as the stack itself. -/
theorem mem_uniTcK_zero {D : KDeployment} (hs : UniShapesK D) (H : Hist) (T : QuotientRpm.Table)
    (r : Bytes32) (q : Stk) (hq : q ∈ (uniTcK hs 0).commit.cands H T r) :
    ∃ st ∈ LeanVM.Extraction.decodeStacks (wvK D 0) logInvRate
        (wordOfMerkle (rootHeight (wvK D 0) logInvRate) (2 ^ WhirBridge.laneFold)
          (merkleWord H T (rootHeight (wvK D 0) logInvRate) leafBytes r)),
      q = fun i => st.toArray.getD i 0 := by
  have e : uniTcK hs 0 = tableCode (shapeKK hs 0 (by decide)).L (shapeKK hs 0 (by decide)).R
      (shapeKK hs 0 (by decide)).adm rdTab := by
    unfold uniTcK
    rw [ite_eq_left rfl]
  rw [e] at hq
  obtain ⟨st, hst, rfl⟩ := mem_tableCode_cands _ _ _ _ _ hq
  exact ⟨st, hst, rdTab_tabOf_plain (wvK D 0) hs.c1 (hs.hi 0 (by decide)) st⟩

/-- **The Keccak extractor's `C1` word is mumbai's `committedLeaves`** on the setup's evaluations and the
transcript's, under the root the stream names. -/
theorem c1WordK_eq_committed (D : KDeployment) (setupEvals : List (List UInt8 × Digest))
    (T : Common.OracleQueryLog) (proof : KeccakProof) :
    c1WordK D (PcsQuotient.Replay.preimageIn (PcsQuotient.Replay.preimageIndex
        (setupEvals ++ PcsQuotient.Replay.transcriptEvaluations PcsQuotient.merkleLengths
          (permutationQueries T)))) proof =
      LeanVM.Extraction.leafAt (LeanVM.Extraction.committedLeaves
        (lookupEvaluation (setupEvals ++ keccakEvaluationsOfTranscript (permutationQueries T)))
        ((setupEvals ++ keccakEvaluationsOfTranscript (permutationQueries T)).map (·.1))
        (c1RootOfK proof) ((c1LayoutK D.shape).vars - 6 + 1) 64)
        ((c1LayoutK D.shape).vars - 6 + 1) 64 := by
  unfold c1WordK
  show LeanVM.Extraction.leafAt (PcsQuotient.Replay.leavesUnder _ 64 _ _) _ 64 =
    LeanVM.Extraction.leafAt (LeanVM.Extraction.subtreeLeaves _ 64 _ _) _ 64
  rw [← Soundness.Replay.leavesUnder_preimage]
  congr 1
  refine Soundness.Replay.leavesUnder_congr _ _ 64 (fun d' => ?_) (fun d' => ?_) _ _
  · exact Soundness.Replay.preimage_merkle setupEvals _ d' 64 (by decide)
  · exact Soundness.Replay.preimage_merkle setupEvals _ d' (8 * 64) (by decide)

/-- **The Keccak extractor returns a stack satisfying the relation** when its list decoder lists a stack whose
Keccak VM stack satisfies it. -/
theorem extractFromK_spec (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (input : Vector UInt8 32)
    (pre : Digest → ℕ → Option (List UInt8)) (proof : KeccakProof)
    (st : Vector K (2 ^ (c1LayoutK D.shape).vars))
    (hst : st ∈ LeanVM.Extraction.decodeStacks (c1LayoutK D.shape).vars 1 (c1WordK D pre proof))
    (hrel : D.Relation F proof.rows input
      (kvStack D.prog (D.sizes proof.rows) D.shape fun i ↦ st.toArray.getD i 0)) :
    ∃ q, extractFromK F D input pre proof = some q ∧ D.Relation F proof.rows input q := by
  have hf : ∀ (a : Vector K (2 ^ (c1LayoutK D.shape).vars)) (b : D.Stack proof.rows),
      (if D.Relation F proof.rows input
          (kvStack D.prog (D.sizes proof.rows) D.shape fun i ↦ a.toArray.getD i 0) then
        some (kvStack D.prog (D.sizes proof.rows) D.shape fun i ↦ a.toArray.getD i 0)
      else none) = some b → D.Relation F proof.rows input b := fun a b hab => by
    by_cases hr : D.Relation F proof.rows input
        (kvStack D.prog (D.sizes proof.rows) D.shape fun i ↦ a.toArray.getD i 0)
    · rw [ite_eq_left hr] at hab
      cases hab
      exact hr
    · rw [ite_eq_right hr] at hab
      cases hab
  unfold extractFromK
  exact Soundness.orElse_spec _ _ _ (Soundness.findSome_sat _ _ _ hf)
    (Soundness.orElse_spec _ _ _ (Soundness.findSome_sat _ _ _ hf)
      (Soundness.findSome_spec _ _ _ hf ⟨st, hst, by rw [ite_eq_left hrel]; rfl⟩))

/-- **The extractor's reading, with `C1`'s variables below `256`**: a candidate of `C1`'s root that the composed
extractor lists, satisfying the Keccak VM's relation, makes `uniExtractorK` find a stack satisfying it. -/
theorem uniExtractBridgeK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (Fl : KFlockSound F κ keccakMain) (nV V : ℕ) (hs : UniShapesK D) (hc1 : (c1LayoutK D.shape).vars < 256) :
    UniExtractBridgeK D Fl nV V hs := by
  intro t T z q hq hrel
  -- the evaluations both extractors read
  have htr : Soundness.treeTr t ++ evalTr (permutationQueries T) = Soundness.trOf
      (PcsQuotient.Tree.evaluations t ++ keccakEvaluationsOfTranscript (permutationQueries T)) := by
    simp only [Soundness.trOf, Soundness.treeTr, evalTr, List.map_append]
  -- the composed candidate: a stack of `C1`'s decoder under the stream's root
  have h0 : extractorK (fun i => (uniTcK hs i).commit) (uView (uRoundsK Fl nV V))
      (z, Soundness.treeTr t ++ evalTr (permutationQueries T)) =
      ((uniTcK hs 0).commit.cands
        (histOfTr (Soundness.trOf
          (PcsQuotient.Tree.evaluations t ++ keccakEvaluationsOfTranscript (permutationQueries T))))
        (tableOfTr (Soundness.trOf
          (PcsQuotient.Tree.evaluations t ++ keccakEvaluationsOfTranscript (permutationQueries T))))
        (toB (c1RootOfK (kpOf z.1)))).map some := by
    rw [htr]
    show optC _ _ _ (msgK (uView (uRoundsK Fl nV V)) z.1 0) = _
    rw [msgK_uView_c1K]
    rfl
  rw [h0] at hq
  have hq' : q ∈ (uniTcK hs 0).commit.cands
      (histOfTr (Soundness.trOf
        (PcsQuotient.Tree.evaluations t ++ keccakEvaluationsOfTranscript (permutationQueries T))))
      (tableOfTr (Soundness.trOf
        (PcsQuotient.Tree.evaluations t ++ keccakEvaluationsOfTranscript (permutationQueries T))))
      (toB (c1RootOfK (kpOf z.1))) := by
    obtain ⟨q', hq', he⟩ := List.mem_map.mp hq
    rw [← Option.some.inj he]
    exact hq'
  obtain ⟨st, hst, rfl⟩ := mem_uniTcK_zero hs _ _ _ q hq'
  -- the Keccak extractor's word agrees with the composed one on every column
  have hμ : (c1LayoutK D.shape).vars = wvK D 0 := (wvK_zero D hc1).symm
  have hadm : Whir.Admissible (wvK D 0) logInvRate := (shapeKK hs 0 (by decide)).adm
  have hst2 : st ∈ LeanVM.Extraction.decodeStacks (wvK D 0) 1
      (c1WordK D (PcsQuotient.Replay.preimageIn (PcsQuotient.Replay.preimageIndex
        (PcsQuotient.Tree.evaluations t ++ PcsQuotient.Replay.transcriptEvaluations PcsQuotient.merkleLengths
          (permutationQueries T)))) (kpOf z.1)) := by
    refine Soundness.mem_decodeStacks_congr hadm (fun p hp => ?_) st hst
    rw [c1WordK_eq_committed, hμ]
    exact Soundness.wordOfMerkle_merkleWord_eq _ _ _ _ hp
  -- the relation, at the proof's row counts
  have hrel' : D.Relation F (rowsOfBytes (rowBytes z.1.proof.stream)) z.1.input
      (kvStack D.prog (D.sizes (rowsOfBytes (rowBytes z.1.proof.stream))) D.shape
        fun i => st.toArray.getD i 0) := hrel
  rw [rowsOfBytes_rowBytes] at hrel'
  obtain ⟨st', hst', hP⟩ := exists_stack_cast hμ
    (fun f => D.Relation F (rowsOf z.1.proof.stream) z.1.input
      (kvStack D.prog (D.sizes (rowsOf z.1.proof.stream)) D.shape f)) _ st hst2 hrel'
  exact extractFromK_spec F D z.1.input _ (kpOf z.1) st' hst' hP

end UniKeccakSound

/-- info: 'UniKeccakSound.uniExtractBridgeK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniExtractBridgeK
