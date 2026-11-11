-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from this repository's `formal/EndToEnd/Bridge/Verifier.lean` (at commit abe22812: the old statement's
-- verifier is the composition's, with its early stops) to the EIP's PCS claims (`formal/SoundPcs`).
import Soundness.PcsChain

/-!
# The Statement's verifier is the deployed run's

The Statement's verifier with Keccak-256 and Keccak-f[1600] the two calls (`verifyWithH callKeccak256
callKeccakF1600`, `E2ECompleteness/PcsWithHash.lean`), on the circuit's commitment `index`:

* **`verifyWithH_eq_contD`**: on a proof whose four roots' scalars name digests, it is `SoundPcs`'s chain and six
  gated openings (`contD`, the verdict) on the converted proof (`rootProofOf4`, `restOf`): the same calls in the
  same order (`reduceWithH_eq_chain4`, `pcsOpeningWithH_eq_O`; `checkAllWith` stops at the first failure as the
  openings are gated);
* **`verifyWithH_reject`**: on another proof it rejects, whatever the calls answer.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp

namespace PcsKS

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open QuotientRpm QuotientSecurity Compose ComposePcs PcsQuotient PcsQuotient.Transcript
open WhirBridge.Pcs SoundPcs

/-! ## The claims' points -/

/-- **The claims' points have their commitments' numbers of variables**: `W`'s `m + 1`, the wiring's `m`, `H`'s
`m + 3`, `Q`'s `m + 4`, `G`'s `m + 1`, the sum's `m + 3` (`m = 24`). -/
theorem claimsAt_len_eq {stmt : Statement} {α β γ t ρ : E} {a : Vector E 4} {next qv gv : E}
    {cl : Claims} (h : claimsAt 22 stmt α β γ t ρ a next qv gv = some cl) :
    cl.witness.point.length = 25 ∧ cl.wiring.point.length = 24 ∧ cl.h.point.length = 27 ∧
      cl.q.point.length = 28 ∧ cl.g.point.length = 25 ∧ cl.sum.point.length = 27 := by
  unfold claimsAt at h
  extract_lets m w wAt theta cell x y c v gate b gamma2 gammas outside publicWeight target tau
    rows d dNext product copies denominators at h
  by_cases hd : (denominators.any fun x ↦ decide (x = 0)) = true
  · simp [hd] at h
  simp only [hd, Bool.false_eq_true, ↓reduceIte, quotientParts, Option.some.injEq] at h
  subst h
  simp (config := { zetaDelta := true }) [PcsQuotient.sumPoint, cellVars]

/-! ## The proof, converted -/

/-- The parts' two values and the six openings' proofs. -/
def restOf (proof : PcsQuotient.Proof) : Rest :=
  ⟨proof.reduction.qValue, proof.reduction.gValue, proof.openings.witness, proof.openings.wiring,
    proof.openings.h, proof.openings.q, proof.openings.g, proof.openings.sum⟩

/-- **A statement and a proof as `dExp`'s adversary outputs them** (its circuit commitment any: the setup's is
put there, `setc`). -/
def conv0 (a : Statement × PcsQuotient.Proof) : RootProof4 E × Rest :=
  (rootProofOf4 ⟨default, 0⟩ a.1 a.2.reduction, restOf a.2)

theorem setc_conv0 (index : Commitment) (a : Statement × PcsQuotient.Proof) :
    setc (toB index.root, index.ood) (conv0 a) = (rootProofOf4 index a.1 a.2.reduction, restOf a.2) := rfl

/-- The statement's bytes, read back. -/
theorem stmtOf_bytes (stmt : Statement) : stmtOf (stmt.y ++ stmt.root) = stmt := by
  obtain ⟨y, r⟩ := stmt
  unfold stmtOf
  refine congrArg₂ Statement.mk ?_ ?_
  · refine Vector.ext fun i hi => ?_
    rw [Vector.getElem_ofFn]
    show (y ++ r)[i] = y[i]
    exact Vector.getElem_append_left hi
  · refine Vector.ext fun i hi => ?_
    rw [Vector.getElem_ofFn]
    show (y ++ r)[32 + i] = r[i]
    rw [Vector.getElem_append_right (by omega) (by omega)]
    congr 1
    omega

theorem ofFn_get (a : Vector E 4) : Vector.ofFn (fun i => a.get i) = a :=
  Vector.ext fun i hi => by simp [Vector.get_eq_getElem]

/-! ## The verifier -/

theorem hash256_eq :
    (hash256 : List UInt8 → OracleComp KeccakCalls QuotientRpm.Bytes32) = fun l => toB <$> callKeccak256 l := by
  funext l
  rw [hash256, map_eq_bind_pure_comp]
  rfl

theorem optV_gate {β : Type} (V : β → OracleComp KeccakCalls Bool) (b : Bool) (w : β) :
    optV V (SoundPcs.gate b (some w)) = if b then V w else pure false := by
  cases b <;> rfl

/-- **Six gated checks are six checks stopping at the first failure.** -/
theorem gated6 (c1 c2 c3 c4 c5 c6 : OracleComp KeccakCalls Bool) :
    (c1 >>= fun b1 => (if b1 then c2 else pure false) >>= fun b2 =>
      (if b1 && b2 then c3 else pure false) >>= fun b3 =>
      (if (b1 && b2) && b3 then c4 else pure false) >>= fun b4 =>
      (if ((b1 && b2) && b3) && b4 then c5 else pure false) >>= fun b5 =>
      (if (((b1 && b2) && b3) && b4) && b5 then c6 else pure false) >>= fun b6 =>
      pure (((((b1 && b2) && b3) && b4) && b5) && b6)) =
    (c1 >>= fun b => if !b then pure false else
      c2 >>= fun b => if !b then pure false else
      c3 >>= fun b => if !b then pure false else
      c4 >>= fun b => if !b then pure false else
      c5 >>= fun b => if !b then pure false else
      c6 >>= fun b => if !b then pure false else pure true) := by
  refine bind_congr fun b1 => ?_
  cases b1
  · simp
  simp only [↓reduceIte, Bool.true_and, Bool.not_true]
  refine bind_congr fun b2 => ?_
  cases b2
  · simp
  simp only [↓reduceIte, Bool.true_and, Bool.not_true]
  refine bind_congr fun b3 => ?_
  cases b3
  · simp
  simp only [↓reduceIte, Bool.true_and, Bool.not_true]
  refine bind_congr fun b4 => ?_
  cases b4
  · simp
  simp only [↓reduceIte, Bool.true_and, Bool.not_true]
  refine bind_congr fun b5 => ?_
  cases b5
  · simp
  simp only [↓reduceIte, Bool.true_and, Bool.not_true]
  refine bind_congr fun b6 => ?_
  cases b6 <;> simp

variable (I : Instance E)

theorem claimsD_conv (index : Commitment) (stmt : Statement) (proof : PcsQuotient.Proof) (tA : Transcript)
    (ch : Chals E) :
    claimsD ⟨rootProofOf4 index stmt proof.reduction, restOf proof, tA, ch⟩ =
      claimsAt 22 stmt ch.α ch.β ch.γ ch.t ch.ρ proof.reduction.values proof.reduction.next
        proof.reduction.qValue proof.reduction.gValue := by
  unfold claimsD
  simp only [rootProofOf4, restOf, stmtOf_bytes, ofFn_get]

/-- **The Statement's verifier is the deployed run's chain and six gated openings**, on a proof whose four
roots' scalars name digests. -/
theorem verifyWithH_eq_contD (index : Commitment) (stmt : Statement) (proof : PcsQuotient.Proof)
    (rW rH rQ rG : Digest) (hW : rootOfHalves proof.reduction.witness.root = some rW)
    (hH : rootOfHalves proof.reduction.h.root = some rH) (hQ : rootOfHalves proof.reduction.q.root = some rQ)
    (hG : rootOfHalves proof.reduction.g.root = some rG) (tA : Transcript) :
    E2ECompleteness.Pcs.verifyWithH callKeccak256 callKeccakF1600 22 index stmt proof =
      Prod.snd <$> contD (pcsWire I) pcsOpen (rootProofOf4 index stmt proof.reduction, restOf proof) tA := by
  unfold E2ECompleteness.Pcs.verifyWithH contD
  rw [reduceWithH_eq_chain4 I callKeccak256 index stmt proof.reduction rW rH rQ rG hW hH hQ hG,
    bind_map_left, map_bind, hash256_eq]
  refine bind_congr fun ch => ?_
  rw [Functor.map_map]
  simp only [id_map']
  have hcd := claimsD_conv index stmt proof tA ch
  rcases hcl : claimsAt 22 stmt ch.α ch.β ch.γ ch.t ch.ρ proof.reduction.values proof.reduction.next
    proof.reduction.qValue proof.reduction.gValue with _ | cl
  · rw [hcl] at hcd
    simp [verS, inW, inσ, inH, inQ, inG, inS, hcd, optV, SoundPcs.gate]
  · rw [hcl] at hcd
    obtain ⟨l1, l2, l3, l4, l5, l6⟩ := claimsAt_len_eq hcl
    simp only [Option.map_some, Reduced.checks, E2ECompleteness.Pcs.checkAllWithH,
      pcsOpeningWithH_eq_O callKeccak256 callKeccakF1600 _ cl.witness l1,
      pcsOpeningWithH_eq_O callKeccak256 callKeccakF1600 _ cl.wiring l2,
      pcsOpeningWithH_eq_O callKeccak256 callKeccakF1600 _ cl.h l3,
      pcsOpeningWithH_eq_O callKeccak256 callKeccakF1600 _ cl.q l4,
      pcsOpeningWithH_eq_O callKeccak256 callKeccakF1600 _ cl.g l5,
      pcsOpeningWithH_eq_O callKeccak256 callKeccakF1600 _ cl.sum l6]
    simp only [verS, inW, inσ, inH, inQ, inG, inS, hcd, Option.bind_some, mkIn, l1, l2, l3, l4, l5, l6,
      dite_true, optV_gate]
    rw [← gated6]
    simp only [optV, pcsOpen, pcsVerifierO, rootProofOf4, restOf, LeanVM.Rpm.digestOfRpm_toRpm, hW, hH, hQ,
      hG, Option.getD_some]

/-- The four roots' scalars name digests. -/
def RootsOK (p : ReductionProof) : Prop :=
  (rootOfHalves p.witness.root).isSome ∧ (rootOfHalves p.h.root).isSome ∧ (rootOfHalves p.q.root).isSome ∧
    (rootOfHalves p.g.root).isSome

/-- **A proof whose roots' scalars name no digests is rejected** by the reduction, whatever the calls answer. -/
theorem reduceWithH_none (index : Commitment) (stmt : Statement) (p : ReductionProof) (h : ¬ RootsOK p) :
    ∀ o ∈ support (E2ECompleteness.Pcs.reduceWithH callKeccak256 22 index stmt p), o = none := by
  have hS : Supported 22 := by decide
  intro o ho
  simp only [E2ECompleteness.Pcs.reduceWithH, hS, not_true_eq_false, ↓reduceIte,
    E2ECompleteness.Pcs.startWithH, E2ECompleteness.Pcs.squeezeWithH, bind_assoc, pure_bind] at ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨s₀, -, ho⟩ := ho
  rcases hw : rootOfHalves p.witness.root with _ | rW
  · simpa [readCommitment, hw] using ho
  simp only [readCommitment, hw, Option.map_some] at ho
  simp only [mem_support_bind_iff] at ho
  obtain ⟨s₁, -, s₂, -, s₃, -, ho⟩ := ho
  rcases hh : rootOfHalves p.h.root with _ | rH
  · simpa [hh] using ho
  rcases hq : rootOfHalves p.q.root with _ | rQ
  · simpa [hh, hq] using ho
  rcases hg : rootOfHalves p.g.root with _ | rG
  · simpa [hh, hq, hg] using ho
  exact absurd ⟨by simp [hw], by simp [hh], by simp [hq], by simp [hg]⟩ h

/-- **A proof whose roots' scalars name no digests is rejected**, whatever the calls answer. -/
theorem verifyWithH_reject (index : Commitment) (stmt : Statement) (proof : PcsQuotient.Proof)
    (h : ¬ RootsOK proof.reduction) :
    ∀ b ∈ support (E2ECompleteness.Pcs.verifyWithH callKeccak256 callKeccakF1600 22 index stmt proof),
      b = false := by
  intro b hb
  unfold E2ECompleteness.Pcs.verifyWithH at hb
  rw [mem_support_bind_iff] at hb
  obtain ⟨o, ho, hb⟩ := hb
  rw [reduceWithH_none index stmt proof.reduction h o ho] at hb
  simpa using hb

end PcsKS
