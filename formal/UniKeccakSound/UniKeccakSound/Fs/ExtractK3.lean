-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The Keccak main line's `Fs/ExtractK.lean` at π1-rec3's
-- rounds, as `UniSound/Rec3/FsExtract3.lean`.
import UniKeccakSound.Fs.CoupleK3
import UniKeccakSound.Fs.ExtractK

/-!
# The Keccak extractor's reading at π1-rec3's shape

**`uniExtractBridgeK3`**: `UniExtractBridgeK3`, as `ExtractK.lean`'s `uniExtractBridgeK`: round `0` of `rec3Rounds`
is `C1`'s root without scalars (`msgK_uView_c1K3`), and the rest is the main line's (`mem_uniTcK_zero`,
`c1WordK_eq_committed`, `extractFromK_spec`).
-/

-- The relation is `KvHolds` of a symbolic instance: no simprocs here, which would try to decide it.
set_option simprocs false

namespace UniKeccakSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement UniSound UniKeccak

/-- **Round `0`'s message is `C1`'s root** the stream names, without scalars. -/
theorem msgK_uView_c1K3 {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3) (nV np : ℕ)
    (π : UPf) : msgK (uView (uRoundsK3 F3 nV np)) π 0 = (some (toB (c1RootOfK (kpOf π))), []) :=
  rfl

/-- **The extractor's reading, with `C1`'s variables below `256`**: a candidate of `C1`'s root that the composed
extractor lists, satisfying the Keccak VM's relation, makes `uniExtractorK` find a stack satisfying it. -/
theorem uniExtractBridgeK3 (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (nV np : ℕ) (hs : UniShapesK D) (hc1 : (c1LayoutK D.shape).vars < 256) :
    UniExtractBridgeK3 D F3 nV np hs := by
  intro t T z q hq hrel
  -- the evaluations both extractors read
  have htr : Soundness.treeTr t ++ evalTr (permutationQueries T) = Soundness.trOf
      (PcsQuotient.Tree.evaluations t ++ keccakEvaluationsOfTranscript (permutationQueries T)) := by
    simp only [Soundness.trOf, Soundness.treeTr, evalTr, List.map_append]
  -- the composed candidate: a stack of `C1`'s decoder under the stream's root
  have h0 : extractorK (fun i => (uniTcK hs i).commit) (uView (uRoundsK3 F3 nV np))
      (z, Soundness.treeTr t ++ evalTr (permutationQueries T)) =
      ((uniTcK hs 0).commit.cands
        (histOfTr (Soundness.trOf
          (PcsQuotient.Tree.evaluations t ++ keccakEvaluationsOfTranscript (permutationQueries T))))
        (tableOfTr (Soundness.trOf
          (PcsQuotient.Tree.evaluations t ++ keccakEvaluationsOfTranscript (permutationQueries T))))
        (toB (c1RootOfK (kpOf z.1)))).map some := by
    rw [htr]
    show optC _ _ _ (msgK (uView (uRoundsK3 F3 nV np)) z.1 0) = _
    rw [msgK_uView_c1K3]
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

/-- info: 'UniKeccakSound.uniExtractBridgeK3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniExtractBridgeK3
