-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Follows `formal/EndToEnd/Completeness/E2ECompleteness/PcsOpening.lean` of this repository at `f96a7938`
-- (`pcsOpeningWithH_eq_runProof`, `openingProgram_eq`, `runWithHash_bind`), there at a pure hash and
-- permutation, here in any lawful monad, against `formal/WhirBridge/WhirBridge/PcsOracle.lean`'s
-- `pcsVerifyWithHashO`. Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`,
-- commit 6175f1a0, MIT OR Apache-2.0): the runner `runWithHash`, `runProofWithHash`, `exists_ladder`.
import Soundness.PcsDExp
import Soundness.PcsVH
import Bridge.Chain

/-!
# The Statement's opening check is F2's

The Statement's opening check of a PCS claim, with Keccak-256 an explicit call (`pcsOpeningWithH`,
`Soundness/PcsVH.lean`), is F2's verifier reading the out-of-domain point off Keccak-256
(`WhirBridge.Pcs.pcsVerifyWithHashO`), in every lawful monad (**`pcsOpeningWithH_eq_O`**), so over the two
oracles it is `pcsVerifierO`: the same calls in the same order. The two differ in form only:

* the claim's bytes (`pcsClaimBytes_eq`: the Statement's `elementBytes` is F2's `elemBytes`), the zero public
  digest, the out-of-domain point (`oodPointWithH_eq`: `elementOf` is `elemOf` on 24 bytes);
* the root's two scalars: the Statement absorbs them, checks them, then computes the point and runs the opening
  from the commitment on; F2 checks them, computes the point, then runs the program whose first step absorbs
  them (`commitStack`); the two absorptions call no permutation (the sponge's queue is not full,
  `absorb_short`), so the calls are the same;
* the program: F2's `check` is mumbai's `verifyStackedOpening` of the Statement's two stack claims
  (`check_eq_vso`, `eqZ = eqEval`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp

namespace PcsKS

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open PcsQuotient PcsQuotient.Transcript

/-! ## Bytes -/

theorem kBytesBE_eq (a : K) : WhirBridge.Pcs.kBytesBE a = beBytes a.lane := rfl

theorem elemBytes_eq (x : E) : WhirBridge.Pcs.elemBytes x = elementBytes x := rfl

theorem flatMap_elemBytes (l : List E) :
    l.flatMap WhirBridge.Pcs.elemBytes = l.flatMap elementBytes := rfl

/-- **The claim's bytes** (`PcsClaim::encode`), transcribed twice. -/
theorem pcsClaimBytes_eq (c : Commitment) (claim : Claim) {n : ℕ} (h : claim.point.length = n) :
    pcsClaimBytes c claim = WhirBridge.Pcs.claimBytes (⟨c.root, c.ood, claim.point, claim.value, h⟩ :
      WhirBridge.Pcs.Claim1 n) := by
  subst h
  rfl

theorem oodTag_eq : PcsQuotient.oodTag = WhirBridge.Pcs.oodTag := by decide +kernel

theorem oodInput_eq (n : ℕ) (r : Digest) (j : ℕ) :
    PcsQuotient.oodInput n r j = WhirBridge.Pcs.oodInput n r j := by
  unfold PcsQuotient.oodInput WhirBridge.Pcs.oodInput
  rw [oodTag_eq]
  rfl

/-- `beWord` of eight bytes is the little-endian lane of their reverse. -/
theorem beWord_eq_leLane (bs : List UInt8) (s : ℕ) (h : s + 8 ≤ bs.length) :
    beWord bs s = leLane ((bs.drop s).take 8).reverse 0 := by
  rw [Bridge.beWord_eq bs s h, QuotientRpm.ofBe64, LeanVM.Rpm.leLane_eq_bytesLane, Nat.mul_zero,
    List.drop_zero]

/-- **`element_of`**, transcribed twice, on 24 bytes. -/
theorem elementOf_eq (bs : List UInt8) (h : bs.length = 24) :
    elementOf bs = WhirBridge.Pcs.elemOf bs := by
  unfold elementOf WhirBridge.Pcs.elemOf WhirBridge.Pcs.beK
  rw [beWord_eq_leLane bs 16 (by omega), beWord_eq_leLane bs 8 (by omega),
    beWord_eq_leLane bs 0 (by omega), List.drop_zero]

theorem length_drop_digestBytes (d : Digest) : ((digestBytes d).drop 8).length = 24 := by
  rw [List.length_drop, WhirBridge.Pcs.digestBytes_length']

/-- **The out-of-domain point**, transcribed twice, in any monad. -/
theorem oodPointWithH_eq {m : Type → Type} [Monad m] (H : Bytes → m Digest) (n : ℕ) (r : Digest) :
    PcsKS.VH.oodPointWithH H n r = WhirBridge.Pcs.oodPointM H n r := by
  unfold PcsKS.VH.oodPointWithH WhirBridge.Pcs.oodPointM
  congr 1
  funext j
  rw [oodInput_eq]
  congr 1
  funext d
  rw [elementOf_eq _ (length_drop_digestBytes d)]

/-! ## The sponge, the program -/

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m] (H : Bytes → m Digest)
  (F : KeccakState → m KeccakState)

/-- A scalar absorbed into an empty queue: no permutation. -/
theorem absorb_nil (s : KeccakState) (x : E) (t : ℕ) :
    LeanVM.Protocol.Compile.absorb F ⟨s, []⟩ x t = pure ⟨s, [(x, t)]⟩ := by
  simp [LeanVM.Protocol.Compile.absorb, LeanVM.Protocol.Compile.rateScalars]

/-- A scalar absorbed into a queue of one: no permutation. -/
theorem absorb_one (s : KeccakState) (y : E × ℕ) (x : E) (t : ℕ) :
    LeanVM.Protocol.Compile.absorb F ⟨s, [y]⟩ x t = pure ⟨s, [y, (x, t)]⟩ := by
  simp [LeanVM.Protocol.Compile.absorb, LeanVM.Protocol.Compile.rateScalars]

/-- F2's program: the root as commitment `0`, the check, accept. -/
theorem prog_eq_commit {n : ℕ} (hw : Whir.Admissible n WhirBridge.logInvRate) (z : List E)
    (x : WhirBridge.Pcs.Claim1 n) :
    WhirBridge.Pcs.prog n WhirBridge.logInvRate z x =
      Prog.commit (WhirBridge.rootHeight n WhirBridge.logInvRate) (2 ^ WhirBridge.laneFold)
        ((WhirBridge.Pcs.check n WhirBridge.logInvRate z x).bind fun _ => Prog.ret true) := by
  unfold WhirBridge.Pcs.prog
  rw [WhirBridge.commitStack_eq hw]
  rfl

theorem dot_stack (lam : E) (z : List E) (c : Commitment) (claim : Claim) :
    dot (powers lam (pcsStackClaims z c claim).length) ((pcsStackClaims z c claim).map (·.2)) =
      c.ood + lam * claim.value :=
  PcsKS.VH.dot_powers_two lam _ _

theorem dot_stack_fn (lam : E) (z : List E) (c : Commitment) (claim : Claim) :
    (fun point => dot (powers lam (pcsStackClaims z c claim).length)
        ((pcsStackClaims z c claim).map fun cl => cl.1 point)) =
      fun pt => WhirBridge.eqZ z pt + lam * WhirBridge.eqZ claim.point pt := by
  funext pt
  rw [WhirBridge.eqZ_eq_eqEval, WhirBridge.eqZ_eq_eqEval]
  exact PcsKS.VH.dot_powers_two lam _ _

/-- **F2's check is the Statement's stacked opening** of its two stack claims. -/
theorem check_eq_vso (c : Commitment) (claim : Claim) {n : ℕ} (h : claim.point.length = n) (z : List E) :
    WhirBridge.Pcs.check n WhirBridge.logInvRate z (⟨c.root, c.ood, claim.point, claim.value, h⟩ :
      WhirBridge.Pcs.Claim1 n) = verifyStackedOpening n logInvRate (pcsStackClaims z c claim) := by
  unfold WhirBridge.Pcs.check verifyStackedOpening
  refine congrArg (fun f => Prog.sampleChallenge >>= f) (funext fun lam => ?_)
  show _ = verifyWhir n logInvRate
    (dot (powers lam (pcsStackClaims z c claim).length) ((pcsStackClaims z c claim).map (·.2)))
    (fun point => dot (powers lam (pcsStackClaims z c claim).length)
        ((pcsStackClaims z c claim).map fun cl => cl.1 point))
  rw [dot_stack, dot_stack_fn]
  rfl

/-- **The Statement's opening check is F2's**, with the out-of-domain point read off the hash, in any lawful
monad. -/
theorem pcsOpeningWithH_eq_O (c : Commitment) (claim : Claim) {n : ℕ} (h : claim.point.length = n)
    (pf : Compile.Proof) :
    PcsKS.VH.pcsOpeningWithH H F c claim pf =
      WhirBridge.Pcs.pcsVerifyWithHashO H F (⟨c.root, c.ood, claim.point, claim.value, h⟩ :
        WhirBridge.Pcs.Claim1 n) pf := by
  subst h
  unfold PcsKS.VH.pcsOpeningWithH WhirBridge.Pcs.pcsVerifyWithHashO
  by_cases hr : minVars ≤ claim.point.length ∧ claim.point.length ≤ maxVars
  · have hr' : WhirBridge.Pcs.minVars ≤ claim.point.length ∧
        claim.point.length ≤ WhirBridge.Pcs.maxVars := hr
    rw [ite_eq_left hr, ite_eq_left hr']
    simp only [PcsKS.VH.pcsSpongeWithH, bind_assoc, pure_bind,
      pcsClaimBytes_eq c claim rfl]
    refine bind_congr fun iv => ?_
    have hpd : zeroDigest = WhirBridge.publicDigest := rfl
    rw [hpd]
    refine bind_congr fun seed => ?_
    rcases hs : pf.stream with _ | ⟨x0, _ | ⟨x1, rest⟩⟩
    · simp [WhirBridge.rootOf, hs]
    · simp [WhirBridge.rootOf, hs]
    · simp only [absorb_nil, absorb_one, pure_bind, WhirBridge.rootOf, hs]
      by_cases hd : digestOfScalars (x0, x1) = some c.root
      · rw [ite_eq_left hd, ite_eq_left hd, oodPointWithH_eq]
        refine bind_congr fun z => ?_
        rw [LeanVM.Protocol.Compile.runProofWithHash,
          prog_eq_commit (PcsKS.VH.admissible_of_vars hr)]
        simp only [LeanVM.Protocol.Compile.runWithHash, hs, absorb_nil, absorb_one, pure_bind, hd]
        rw [check_eq_vso c claim rfl z, PcsKS.VH.runWithHash_bind, bind_assoc, List.nil_append]
        refine bind_congr fun o => ?_
        rcases o with _ | ⟨a, s⟩
        · simp
        · simp [LeanVM.Protocol.Compile.runWithHash]
      · rw [ite_eq_right hd, ite_eq_right hd]
  · have hr' : ¬ (WhirBridge.Pcs.minVars ≤ claim.point.length ∧
        claim.point.length ≤ WhirBridge.Pcs.maxVars) := hr
    rw [ite_eq_right hr, ite_eq_right hr']

end Monad

end PcsKS
