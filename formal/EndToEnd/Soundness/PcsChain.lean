-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from this repository's `formal/EndToEnd/Bridge/Chain.lean` (`label_eq`, `scalarBytes_eq`,
-- `rootScalars_eq`, `reduceWith_eq`: the old reduction's chain is F4's) at commit abe22812, and from its own version
-- at `f96a7938` (four commitments), to the two commitments of the deployed protocol (`formal/ComposePcs`,
-- `chainWith2`).
import Soundness.PcsOpenBridge

/-!
# The Statement's reduction is the two-root chain

* **the wire** (`pcsWire2`): the statement's 64 bytes read as the eleven pinned values (`stmtVals`: `y`'s and
  `root`'s eight `K`-words, then `0`, `1`, `3`, as the Statement's `anchorValues`), a field element held as its
  three limbs, low first (`eLimbs`: the Statement's `scalarBytes` and `challengeOf`);
* **the bytes**: the label (`label_eq2`: the tag, the circuit's root, its out-of-domain answer as 24 bytes, the
  statement), a root's two scalars (`halfWords_eq_scalars`: the half-words of the root two scalars name are their
  words), a scalar's word (`word_eq`), a state's challenge (`chal_eq`);
* **`reduceWithH_eq_chain2`**: on a proof whose two roots' scalars name digests, the Statement's reduction with
  Keccak-256 `H` (in any lawful monad) hashes exactly what `ComposePcs.chainWith2` hashes, in the same order, and
  returns the commitments and `claimsAt` at its challenges.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp

namespace PcsKS

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open QuotientRpm QuotientSecurity Compose ComposePcs PcsQuotient PcsQuotient.Transcript

/-! ## The wire -/

/-- **The statement's eleven pinned values** (`anchor_values` of `Statement::words`): the statement's 64 bytes as
`y ‖ root`, their eight big-endian `K`-words, then `0`, `1`, `3`. -/
def stmtVals (sb : Vector UInt8 64) : Kc3.Params.Stmt E :=
  fun k => ofK (anchorValues (SoundPcs.stmtOf sb).words k.val)

/-- **The deployed wire** for any parameters `P`: the statement's bytes read as their pinned values (`stmtVals`), the
limbs `eLimbs`. -/
def pcsWire2 (P : Kc3.Params E) : Wire2 P := ⟨stmtVals, Soundness.eLimbs⟩

/-! ## Bytes -/

theorem tag3_eq : protocolName = ComposePcs.tag3 := by decide +kernel

variable (P : Kc3.Params E)

/-- A scalar's word (`Chain::sample`): the Statement's `scalarBytes`. -/
theorem word_eq (x : E) : (pcsWire2 P).word x = scalarBytes x := rfl

/-- A state's challenge: the Statement's `challengeOf`. -/
theorem chal_eq (st : Digest) : (pcsWire2 P).chal (toB st) = challengeOf st :=
  (Bridge.challengeOf_eq st).symm

theorem drop8_word (x : E) : ((pcsWire2 P).word x).drop 8 = elementBytes x := rfl

/-- **The label** (`protocol::label`), transcribed twice. -/
theorem label_eq2 (index : Commitment) (stmt : Statement) :
    label index stmt = labelOf2 (pcsWire2 P) (toB index.root, index.ood, stmt.y ++ stmt.root) := by
  simp only [label, labelOf2, tag3_eq, Bridge.toB_toList, drop8_word, Vector.toList_append,
    List.append_assoc]

/-! ## A root's two scalars -/

theorem chunk8 (b : List UInt8) (i : ℕ) (h : 8 * i + 8 ≤ b.length) :
    (List.range 8).map (fun k => b.getD (8 * i + k) 0) = (b.drop (8 * i)).take 8 := by
  refine List.ext_getElem (by simp; omega) fun k h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
  rw [List.getD_eq_getElem _ _ (by simp at h1; omega)]

theorem digestBytes_lanes (b : List UInt8) (hb : b.length = 32) :
    digestBytes #v[leLane b 0, leLane b 1, leLane b 2, leLane b 3] = b := by
  simp only [digestBytes, Vector.toList_mk, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    LeanVM.Rpm.wordBytes_leLane]
  rw [chunk8 b 0 (by omega), chunk8 b 1 (by omega), chunk8 b 2 (by omega), chunk8 b 3 (by omega)]
  have h32 : (b.drop (8 * 3)).take 8 = b.drop 24 := List.take_of_length_le (by simp; omega)
  rw [h32]
  conv_rhs => rw [← List.take_append_drop 8 b, ← List.take_append_drop 8 (b.drop 8),
    ← List.take_append_drop 8 ((b.drop 8).drop 8)]
  simp only [List.drop_drop]
  rfl

theorem beBytes_zero : beBytes (0 : K).lane = List.replicate 8 0 := rfl

theorem length_beBytes (w : UInt64) : (beBytes w).length = 8 := by
  simp [beBytes, LeanVM.Rpm.wordBytes_len]

theorem halfWords_of_bytes (b : List UInt8) (hb : b.length = 32) :
    halfWords (toB #v[leLane b 0, leLane b 1, leLane b 2, leLane b 3]) =
      List.replicate 16 0 ++ b.take 16 ++ List.replicate 16 0 ++ b.drop 16 := by
  rw [halfWords, Bridge.toB_toList, digestBytes_lanes b hb]

theorem take16 (a b c d : UInt64) : (beBytes a ++ beBytes b ++ beBytes c ++ beBytes d).take 16 =
    beBytes a ++ beBytes b := by
  rw [List.append_assoc, List.append_assoc, ← List.append_assoc (beBytes a)]
  exact List.take_left' (by simp [length_beBytes])

theorem drop16 (a b c d : UInt64) : (beBytes a ++ beBytes b ++ beBytes c ++ beBytes d).drop 16 =
    beBytes c ++ beBytes d := by
  rw [List.append_assoc, List.append_assoc, ← List.append_assoc (beBytes a)]
  exact List.drop_left' (by simp [length_beBytes])

/-- **A root's two scalars** (`halves_root`): when they name a digest `r`, the half-words the four-root chain
hashes for `r` are the two scalars' words. -/
theorem halfWords_eq_scalars (s : E × E) (r : Digest) (h : rootOfHalves s = some r) :
    halfWords (toB r) = scalarBytes s.1 ++ scalarBytes s.2 := by
  have hc : s.1.limb 2 = 0 ∧ s.2.limb 2 = 0 := by
    by_contra hc
    simp only [rootOfHalves, hc, ite_false, reduceCtorEq] at h
  have hr : #v[leLane (beBytes (s.1.limb 1).lane ++ beBytes (s.1.limb 0).lane ++ beBytes (s.2.limb 1).lane ++
      beBytes (s.2.limb 0).lane) 0, leLane (beBytes (s.1.limb 1).lane ++ beBytes (s.1.limb 0).lane ++
      beBytes (s.2.limb 1).lane ++ beBytes (s.2.limb 0).lane) 1, leLane (beBytes (s.1.limb 1).lane ++
      beBytes (s.1.limb 0).lane ++ beBytes (s.2.limb 1).lane ++ beBytes (s.2.limb 0).lane) 2,
      leLane (beBytes (s.1.limb 1).lane ++ beBytes (s.1.limb 0).lane ++ beBytes (s.2.limb 1).lane ++
      beBytes (s.2.limb 0).lane) 3] = r := by
    simp only [rootOfHalves, hc, and_self, ite_true, Option.some.injEq] at h
    exact h
  rw [← hr, halfWords_of_bytes _ (by simp [length_beBytes]), take16, drop16]
  simp only [scalarBytes, hc.1, hc.2, beBytes_zero, List.append_assoc, List.replicate_append_replicate]

/-! ## The reduction -/

/-- **The two-root chain's proof** of a reduction proof: the statement's bytes `y ‖ root`, the two roots the proof's
scalars name (zero if they name none: the Statement rejects such a proof) with their out-of-domain answers, the
three values and `next`, and the circuit's commitment `index`. -/
def rootProofOf2 (index : Commitment) (stmt : Statement) (p : ReductionProof) : RootProof2 E :=
  ⟨stmt.y ++ stmt.root, toB ((rootOfHalves p.witness.root).getD default), p.witness.ood,
    toB ((rootOfHalves p.table.root).getD default), p.table.ood, (fun i => p.values.get i, p.next),
    toB index.root, index.ood⟩

/-- **The Statement's reduction is the two-root chain, then the Statement's claims**: for every lawful monad and
Keccak-256 `H`, on a proof whose two roots' scalars name digests, `reduceWithH H 22` hashes exactly what
`chainWith2` hashes over `toB ∘ H`, in the same order, and returns the two commitments and `claimsAt` at its
challenges. -/
theorem reduceWithH_eq_chain2 {m : Type → Type} [Monad m] [LawfulMonad m] (H : List UInt8 → m Digest)
    (index : Commitment) (stmt : Statement) (p : ReductionProof) (rW rT : Digest)
    (hW : rootOfHalves p.witness.root = some rW) (hT : rootOfHalves p.table.root = some rT) :
    PcsKS.VH.reduceWithH H 22 index stmt p =
      (fun ch : Chals E => (claimsAt 22 stmt ch.α ch.β ch.γ ch.t ch.ρ p.values p.next).map fun cl =>
            (⟨⟨⟨rW, p.witness.ood⟩, ⟨rT, p.table.ood⟩⟩, cl⟩ : Reduced)) <$>
        chainWith2 (pcsWire2 P) (fun l => toB <$> H l) (rootProofOf2 index stmt p) := by
  have hS : Supported 22 := by decide
  rcases p with ⟨⟨⟨w0, w1⟩, wo⟩, ⟨⟨t0, t1⟩, to'⟩, ⟨⟨vs⟩, hvs⟩, next⟩
  match vs, hvs with
  | [a0, a1, a2], _ =>
  simp only at hW hT
  simp only [PcsKS.VH.reduceWithH, hS, not_true_eq_false, ↓reduceIte,
    PcsKS.VH.startWithH, PcsKS.VH.squeezeWithH, readCommitment, hW, hT,
    Option.map_some, chainWith2, rootProofOf2, Option.getD_some, map_bind, bind_assoc, pure_bind,
    bind_map_left, map_pure, label_eq2 P]
  simp only [Chain.absorb, afterC, commitWords2, Wire2.afterValues, Wire2.valueWords,
    Bridge.toB_toList, chal_eq, word_eq, halfWords_eq_scalars _ _ hW, halfWords_eq_scalars _ _ hT,
    RootProof2.pre, RootProof2.comW, RootProof2.comT, List.flatMap_cons, List.flatMap_nil, List.nil_append,
    List.append_nil, List.cons_append, List.append_assoc]
  rfl

end PcsKS
