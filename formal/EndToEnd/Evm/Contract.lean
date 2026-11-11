-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Evm.PcsOpen

/-!
# The contract accepts exactly what the Statement's verifier accepts

On the calldata of a statement and a proof (`Implementation.calldata`, `quotient.rs`'s), with the
deployed Keccak-256 and the circuit's commitment `index` in storage (`Implementation.deployed`), and
with what the block proves of declared claim `k` modelled by `pcsOpen` (the claim read as the block
reads it, then `PcsQuotient.pcsOpening` with the proof's opening `k`):

* **`evm_accepts_eq_verify`**: the contract's verdict is `PcsQuotient.verify` (`verifyWith` at
  Keccak-f[1600]) on the proof, as `Bool`s; **`evm_accepts_iff_verifyWith`**: the same, as `verifyWith`;
-/

set_option linter.unusedSectionVars false

namespace Evm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash PcsQuotient PcsQuotient.Transcript
  Implementation

theorem checkAllWith_id (l : List (Commitment × Claim × Compile.Proof)) :
    Id.run (checkAllWith (m := Id) (fun s ↦ pure (keccakF1600 s)) l) =
      l.all fun x => pcsOpening x.1 x.2.1 x.2.2 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨c, claim, pr⟩ := x
    rw [List.all_cons, ← ih]
    show (if !(pcsOpening c claim pr) then false else Id.run (checkAllWith _ l)) = _
    cases pcsOpening c claim pr <;> rfl

/-- **The Statement's verifier over Keccak-f[1600]**: the reduction, then the three openings. -/
theorem verify_eq (index : Commitment) (stmt : Statement) (proof : Proof) :
    verify 22 index stmt proof =
      match reduce 22 index stmt proof.reduction with
      | none => false
      | some r => (r.checks index proof.openings).all fun x => pcsOpening x.1 x.2.1 x.2.2 := by
  have e : verify 22 index stmt proof = match reduce 22 index stmt proof.reduction with
      | none => false
      | some r => Id.run (checkAllWith (m := Id) (fun s ↦ pure (keccakF1600 s)) (r.checks index proof.openings)) :=
    rfl
  rw [e]
  split
  · rfl
  · exact checkAllWith_id _

/-- The three claims' points have `1` to `32` coordinates (`24`, `24`, `28`). -/
theorem claims_lengths (I : Formula.Vals) :
    (Formula.claims I).witness.point.length = 24 ∧ (Formula.claims I).wiring.point.length = 24 ∧
      (Formula.claims I).copy.point.length = 28 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Formula.claims, copyPoint, Formula.u, cellVars, PcsQuotient.logRows, Formula.m]

theorem reduce_some {index : Commitment} {stmt : Statement} {p : ReductionProof} {frame : UInt8}
    {cd : List UInt8} (h : calldata stmt p frame = some cd) {r : Reduced} (hr : reduce 22 index stmt p = some r) :
    ∃ I : Formula.Vals, r.claims = Formula.claims I := by
  obtain ⟨rw, rt, hw, ht, -⟩ := calldata_some h
  rw [reduce_eq index stmt p hw ht] at hr
  set I := chainVals index stmt p
  rw [show claimsAt 22 stmt I.α I.β I.μ I.t I.ρ p.values p.next =
      claimsAt PcsQuotient.logRows I.stmt I.α I.β I.μ I.t I.ρ I.v I.next from rfl,
    Formula.claimsAt_eq] at hr
  revert hr
  split_ifs <;> intro hr <;> simp at hr
  exact ⟨I, by rw [← hr]⟩

/-- **The contract's verdict is the Statement's verifier's**: on the calldata of a statement and a proof,
with the deployed Keccak-256 and the circuit's commitment `index` in storage, and with what the block proves
of declared claim `k` the opening check `pcsOpen` with the proof's openings, the contract accepts exactly
when `PcsQuotient.verify` (`verifyWith` at Keccak-f[1600]) does. -/
theorem evm_accepts_eq_verify (index : Commitment) (stmt : Statement) (proof : Proof) (frame : UInt8)
    (cd : List UInt8) (h : calldata stmt proof.reduction frame = some cd) :
    accepts (pcsOpen proof.openings) (deployed index cd) = verify 22 index stmt proof := by
  rw [accepts_calldata _ index stmt proof.reduction frame cd h, verify_eq]
  rcases hr : reduce 22 index stmt proof.reduction with _ | r
  · rfl
  · obtain ⟨I, hI⟩ := reduce_some h hr
    obtain ⟨l0, l1, l2⟩ := claims_lengths I
    simp only [checkPairs, Reduced.checks, List.map_cons, List.map_nil, allAttested, List.all_cons,
      List.all_nil]
    rw [pcsOpen_pcsClaimBytes _ _ _ _ (by rw [hI, l0]; norm_num) (by rw [hI, l0]; norm_num),
      pcsOpen_pcsClaimBytes _ _ _ _ (by rw [hI, l1]; norm_num) (by rw [hI, l1]; norm_num),
      pcsOpen_pcsClaimBytes _ _ _ _ (by rw [hI, l2]; norm_num) (by rw [hI, l2]; norm_num)]
    rfl

/-- **`evm_accepts_eq_verify`, with the Statement's `verifyWith`** at `π = Keccak-f[1600]`. -/
theorem evm_accepts_iff_verifyWith (index : Commitment) (stmt : Statement) (proof : Proof) (frame : UInt8)
    (cd : List UInt8) (h : calldata stmt proof.reduction frame = some cd) :
    accepts (pcsOpen proof.openings) (deployed index cd) = true ↔
      Id.run (verifyWith (m := Id) (fun s ↦ pure (keccakF1600 s)) 22 index stmt proof) = true := by
  rw [evm_accepts_eq_verify index stmt proof frame cd h]
  rfl

end Evm
