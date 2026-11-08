-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/VerifierAccept.lean`.
import UniKeccakComplete.K.VerifierH

/-!
# When the whole Keccak verifier accepts

`verifyWithKH` (the run, then three `PCS_OPEN` calls) accepts at pure `H`, `F` when the run accepts with the three
point claims on `C1`, `C2` and the setup in order (no matrices' claim), and each of the three openings accepts
(`verifyWithKH_of_calls`).
-/

namespace UniKeccakComplete

open UniStatement UniKeccak LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- **The Keccak verifier accepts** when its run does, with the three point claims and no matrices' claim, and the
three openings accept. -/
theorem verifyWithKH_of_calls (H : List UInt8 → Digest) (F : KeccakState → KeccakState) (shape : Shape)
    (v : KeccakVariant) (iv : List UInt8) (roots : SetupRoots) (input : Vector UInt8 32) (π : KeccakProof)
    (o : Outcome) (r : Reduced) (p1 p2 p3 : List E) (v1 v2 v3 : E)
    (hrun : runWithKH (m := Id) (fun b ↦ pure (H b)) shape iv input.toList π.stream v .point = o)
    (hacc : o.accepts = true) (hres : o.result = .ok r)
    (hop : r.openings = [(.c1, .point p1 v1 none), (.c2, .point p2 v2 none), (.setup, .point p3 v3 none)])
    (hmat : r.matrices = none)
    (h1 : pcsOpenWithH (m := Id) (fun b ↦ pure (H b)) (fun s ↦ pure (F s))
      (layoutWordVars ((layoutWordsK shape).getD 0 [])) (rootOf r.roots.1) [⟨p1, v1⟩] π.c1 = true)
    (h2 : pcsOpenWithH (m := Id) (fun b ↦ pure (H b)) (fun s ↦ pure (F s))
      (layoutWordVars ((layoutWordsK shape).getD 1 [])) (rootOf r.roots.2) [⟨p2, v2⟩] π.c2 = true)
    (h3 : pcsOpenWithH (m := Id) (fun b ↦ pure (H b)) (fun s ↦ pure (F s))
      (layoutWordVars ((layoutWordsK shape).getD 2 [])) roots.bytecode [⟨p3, v3⟩] π.setup = true) :
    verifyWithKH (m := Id) (fun b ↦ pure (H b)) (fun s ↦ pure (F s)) shape v iv roots input π = true := by
  unfold verifyWithKH
  simp only [hrun]
  simp only [bind, pure, List.getD_eq_getElem?_getD] at h1 h2 h3 ⊢
  simp only [hacc, hres, hop, hmat, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp [commitments, h1, h2, h3]
  rfl

end UniKeccakComplete

/-- info: 'UniKeccakComplete.verifyWithKH_of_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.verifyWithKH_of_calls
