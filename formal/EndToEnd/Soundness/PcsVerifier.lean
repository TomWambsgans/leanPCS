-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from this repository's `formal/EndToEnd/Bridge/Verifier.lean` (at commit abe22812: the old statement's
-- verifier is the composition's, with its early stops), and from its own version at `f96a7938` (six openings), to
-- the deployed protocol's three PCS openings (`formal/SoundPcs`).
import Soundness.PcsChain

/-!
# The Statement's verifier is the deployed run's

The Statement's verifier with Keccak-256 and Keccak-f[1600] the two calls (`verifyWithH callKeccak256
callKeccakF1600`, `Soundness/PcsVH.lean`), on the circuit's commitment `index`:

* **`verifyWithH_eq_contD`**: on a proof whose two roots' scalars name digests, it is `SoundPcs`'s chain and three
  gated openings (`contD`, the verdict) on the converted proof (`rootProofOf2`, `restOf`): the same calls in the
  same order (`reduceWithH_eq_chain2`, `pcsOpeningWithH_eq_O`; `checkAllWith` stops at the first failure as the
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

/-- **The claims' points have their commitments' numbers of variables**: `W`'s and the wiring's `24`, `T`'s `28`. -/
theorem claimsAt_len_eq {stmt : Statement} {α β μ t ρ : E} {v : Vector E 3} {next : E}
    {cl : Claims} (h : claimsAt 22 stmt α β μ t ρ v next = some cl) :
    cl.witness.point.length = 24 ∧ cl.wiring.point.length = 24 ∧ cl.copy.point.length = 28 :=
  PcsKS.VH.claimsAt_lengths h

/-! ## The proof, converted -/

/-- The three openings' proofs. -/
def restOf (proof : PcsQuotient.Proof) : Rest :=
  ⟨proof.openings.witness, proof.openings.wiring, proof.openings.copy⟩

/-- **A statement and a proof as `dExp`'s adversary outputs them** (its circuit commitment any: the setup's is
put there, `setc`). -/
def conv0 (a : Statement × PcsQuotient.Proof) : RootProof2 E × Rest :=
  (rootProofOf2 ⟨default, 0⟩ a.1 a.2.reduction, restOf a.2)

theorem setc_conv0 (index : Commitment) (a : Statement × PcsQuotient.Proof) :
    setc (toB index.root, index.ood) (conv0 a) = (rootProofOf2 index a.1 a.2.reduction, restOf a.2) := rfl

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

theorem ofFn_get (a : Vector E 3) : Vector.ofFn (fun i => a.get i) = a :=
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

/-- **Three gated checks are three checks stopping at the first failure.** -/
theorem gated3 (c1 c2 c3 : OracleComp KeccakCalls Bool) :
    (c1 >>= fun b1 => (if b1 then c2 else pure false) >>= fun b2 =>
      (if b1 && b2 then c3 else pure false) >>= fun b3 =>
      pure ((b1 && b2) && b3)) =
    (c1 >>= fun b => if !b then pure false else
      c2 >>= fun b => if !b then pure false else
      c3 >>= fun b => if !b then pure false else pure true) := by
  refine bind_congr fun b1 => ?_
  cases b1
  · simp
  simp only [↓reduceIte, Bool.true_and, Bool.not_true]
  refine bind_congr fun b2 => ?_
  cases b2
  · simp
  simp only [↓reduceIte, Bool.true_and, Bool.not_true]
  refine bind_congr fun b3 => ?_
  cases b3 <;> simp

variable (P : Kc3.Params E)

theorem claimsD_conv (index : Commitment) (stmt : Statement) (proof : PcsQuotient.Proof) (tA : Transcript)
    (ch : Chals E) :
    claimsD ⟨rootProofOf2 index stmt proof.reduction, restOf proof, tA, ch⟩ =
      claimsAt 22 stmt ch.α ch.β ch.γ ch.t ch.ρ proof.reduction.values proof.reduction.next := by
  unfold claimsD
  simp only [rootProofOf2, restOf, stmtOf_bytes, ofFn_get]

/-- **The Statement's verifier is the deployed run's chain and three gated openings**, on a proof whose two
roots' scalars name digests. -/
theorem verifyWithH_eq_contD (index : Commitment) (stmt : Statement) (proof : PcsQuotient.Proof)
    (rW rT : Digest) (hW : rootOfHalves proof.reduction.witness.root = some rW)
    (hT : rootOfHalves proof.reduction.table.root = some rT) (tA : Transcript) :
    PcsKS.VH.verifyWithH callKeccak256 callKeccakF1600 22 index stmt proof =
      Prod.snd <$> contD (pcsWire2 P) pcsOpen (rootProofOf2 index stmt proof.reduction, restOf proof) tA := by
  unfold PcsKS.VH.verifyWithH contD
  rw [reduceWithH_eq_chain2 P callKeccak256 index stmt proof.reduction rW rT hW hT,
    bind_map_left, map_bind, hash256_eq]
  refine bind_congr fun ch => ?_
  rw [Functor.map_map]
  simp only [id_map']
  have hcd := claimsD_conv index stmt proof tA ch
  rcases hcl : claimsAt 22 stmt ch.α ch.β ch.γ ch.t ch.ρ proof.reduction.values proof.reduction.next with
    _ | cl
  · rw [hcl] at hcd
    simp [verS, inW, inσ, inT, hcd, optV, SoundPcs.gate]
  · rw [hcl] at hcd
    obtain ⟨l1, l2, l3⟩ := claimsAt_len_eq hcl
    simp only [Option.map_some, Reduced.checks, PcsKS.VH.checkAllWithH,
      pcsOpeningWithH_eq_O callKeccak256 callKeccakF1600 _ cl.witness l1,
      pcsOpeningWithH_eq_O callKeccak256 callKeccakF1600 _ cl.wiring l2,
      pcsOpeningWithH_eq_O callKeccak256 callKeccakF1600 _ cl.copy l3]
    simp only [verS, inW, inσ, inT, hcd, Option.bind_some, mkIn, l1, l2, l3, dite_true, optV_gate]
    rw [← gated3]
    simp only [optV, pcsOpen, pcsVerifierO, rootProofOf2, restOf, LeanVM.Rpm.digestOfRpm_toRpm, hW, hT,
      Option.getD_some]

/-- The two roots' scalars name digests. -/
def RootsOK (p : ReductionProof) : Prop :=
  (rootOfHalves p.witness.root).isSome ∧ (rootOfHalves p.table.root).isSome

/-- **A proof whose roots' scalars name no digests is rejected** by the reduction, whatever the calls answer. -/
theorem reduceWithH_none (index : Commitment) (stmt : Statement) (p : ReductionProof) (h : ¬ RootsOK p) :
    ∀ o ∈ support (PcsKS.VH.reduceWithH callKeccak256 22 index stmt p), o = none := by
  have hS : Supported 22 := by decide
  intro o ho
  simp only [PcsKS.VH.reduceWithH, hS, not_true_eq_false, ↓reduceIte,
    PcsKS.VH.startWithH, PcsKS.VH.squeezeWithH, bind_assoc, pure_bind] at ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨s₀, -, ho⟩ := ho
  rcases hw : rootOfHalves p.witness.root with _ | rW
  · simpa [readCommitment, hw] using ho
  simp only [readCommitment, hw, Option.map_some] at ho
  simp only [mem_support_bind_iff] at ho
  obtain ⟨s₁, -, s₂, -, s₃, -, ho⟩ := ho
  rcases ht : rootOfHalves p.table.root with _ | rT
  · simpa [ht] using ho
  exact absurd ⟨by simp [hw], by simp [ht]⟩ h

/-- **A proof whose roots' scalars name no digests is rejected**, whatever the calls answer. -/
theorem verifyWithH_reject (index : Commitment) (stmt : Statement) (proof : PcsQuotient.Proof)
    (h : ¬ RootsOK proof.reduction) :
    ∀ b ∈ support (PcsKS.VH.verifyWithH callKeccak256 callKeccakF1600 22 index stmt proof),
      b = false := by
  intro b hb
  unfold PcsKS.VH.verifyWithH at hb
  rw [mem_support_bind_iff] at hb
  obtain ⟨o, ho, hb⟩ := hb
  rw [reduceWithH_none index stmt proof.reduction h o ho] at hb
  simpa using hb

end PcsKS
