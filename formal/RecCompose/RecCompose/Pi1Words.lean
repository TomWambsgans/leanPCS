-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecCompose.Pi1Decode
import RecStatement.Security

/-!
# π1-rec4's run's shape and its claims' words, decoded

`Pi1RunShape` (proved in `RunShape.lean`) and `decode_pcsClaimWordsK`: what the soundness couplings
(`OpeningsAgree.lean`) and the completeness couplings (`CompleteCouplings.lean`) read of π1-rec4's verifier's run.
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- **π1-rec4's run's shape** (a fact of `UniKeccak.reduceWithK4`'s code, named here, proved in
`RunShape.lean`: `pi1RunShape`): on every stream, a run of π1-rec4's verifier (the reference shape
`keccak128`, its Fiat–Shamir over Keccak-f[1600], `UniKeccak.runK4 … keccakRec4 .point`) that returns a result has no
matrices' claim (`reduceWithK4` makes none: the Keccak-f block's Flock has no matrices) and roots whose halves have zero
top limbs (`nextRoot` reads each half as two limbs, `eNew _ _ 0`). The verifier's matrices' check then never fires
(the roots' limbs are no longer needed since roots are read as their bytes, `UniStatement.rootOf`). -/
def Pi1RunShape : Prop :=
  ∀ (iv publicInput : List UInt8) (stream : Array UInt8) (r : UniStatement.Reduced),
    (UniKeccak.runK4 RecGraphKeccak.Pi1.keccak128 iv publicInput stream UniKeccak.keccakRec4 .point).result = .ok r →
      r.matrices = none ∧ r.roots.1.1.limb 2 = 0 ∧ r.roots.1.2.limb 2 = 0 ∧ r.roots.2.1.limb 2 = 0 ∧
        r.roots.2.2.limb 2 = 0

/-- **The graph's claims at a run of three point claims, decoded**: the verifier's commitments (`C1`'s and `C2`'s
roots `rootOf` of the stream's bytes and their answers; the setup's the reference's) with its points and values. -/
theorem decode_pcsClaimWordsK (roots : UniKeccak.SetupRootsK) (r : UniStatement.Reduced) (pt1 pt2 pt3 : List E)
    (v1 v2 v3 : E) (hro : r.openings = [(.c1, .point pt1 v1 none), (.c2, .point pt2 v2 none),
      (.setup, .point pt3 v3 none)]) :
    (UniKeccak.pcsClaimWordsK roots r).mapM decodePi1Call =
      some [(UniStatement.rootOf r.roots.1, r.oods.1, pt1, v1), (UniStatement.rootOf r.roots.2, r.oods.2, pt2, v2),
        (roots.f, roots.fOod, pt3, v3)] := by
  unfold UniKeccak.pcsClaimWordsK
  rw [hro]
  simp only [List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil, UniKeccak.rootBytesK, UniKeccak.commitOfK,
    Pi1Decode.decodePi1Call_claim _ _ _ _ (UniKeccakComplete.length_rootWord _),
    Pi1Decode.decodePi1Call_claim _ _ _ _ (Pi1Decode.length_digestBytes _), digestOfBytes32_rootWord,
    digestOfBytes32_digestBytes]
  rfl

end RecCompose
