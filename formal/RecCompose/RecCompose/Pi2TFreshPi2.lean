-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `Pi2TFresh.lean`'s `tFresh_of` at π2's staged run
-- (`RecCompose.Pi2ProbStaged`'s `pi2Staged`: `stageB`, `mid2`, `crates/leanvm/rec/src/pi2/prover.rs`'s `Q` and `t`);
-- uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0).
import RecCompose.Pi2TFresh
import RecCompose.Pi2AlphaLen

/-!
# `t`'s freshness at π2's staged run (π2v4): stage B

* **`stageB_eq`**: stage B is `Q`'s tree (`commitWithH`) and out-of-domain point (`oodPointM`: `28` hashes of `46`
  bytes, neither `32` nor `88`, `apq_oodPointM`) then a pure writer, whose `t` input is `s₃`'s bytes, `Q`'s root word
  and its answer (**`tin_stageB`**, `88` bytes).
* **`tFreshBound2 N εα = εα + (4N + 6 + treeCost μQ + μQ) / 2^256`**, the bound `Pi2AlphaG.pi2TFresh_ofG` gives from the
  run's cost and `α`'s freshness; **`tFreshBound2_le`**: below `2^-200` at `N ≤ 2^50`, `εα ≤ 2^-201`.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2G

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM LeanVM.Rpm
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom
open E2ECompleteness (ro HashOK)
open UniKeccakComplete.Prob.TFresh (HC hc_of_qc take_digestBytes)
open Pi2S Pi2K Pi2P Pi2E
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## Stage B -/

/-- `Q`'s stack at stage A's output and the triple's hashes. -/
noncomputable def qStackOf {D : RecDeployment} (C : Pi2Circuits D) (input : Vector UInt8 32) (a : StA)
    (s₁ s₂ s₃ : Digest) : Array K :=
  padStack (stackVars (C.G a.roots).logN).2.1 (qEntry (C.G a.roots).logN
    (mulX (hNovel (C.G a.roots) a.vw.2 (chalP s₁) (chalP s₂)))
    (qNovel (C.G a.roots) a.vw.2 (chalP s₁) (chalP s₂) (chalP s₃)
      (phiOn (Spec.of (D.circuitAt a.roots.pi1).circuit).core (publicScalarsOf input.toList a.vw.1) (chalP s₃)))
    (pNovel (C.G a.roots) a.vw.2) (qpNovel (C.G a.roots) a.vw.2 (chalP s₃)))

/-- **Stage B's hashes**: `Q`'s commitment, then its out-of-domain point (`oodPointM`, `ood_point`). -/
noncomputable def treeB {D : RecDeployment} (C : Pi2Circuits D) (input : Vector UInt8 32) (a : StA)
    (s₁ s₂ s₃ : Digest) : OracleComp KeccakCalls (LeanVM.Prover.Tree × List E) := do
  let qT ← E2ECompleteness.commitWithH callKeccak256 (stackVars (C.G a.roots).logN).2.1 (qStackOf C input a s₁ s₂ s₃)
  let z ← WhirBridge.Pcs.oodPointM callKeccak256 (stackVars (C.G a.roots).logN).2.1 qT.root
  return (qT, z)

/-- **Stage B's writer** after the hashes: `Q`'s root word, its out-of-domain answer. -/
noncomputable def outB {D : RecDeployment} (C : Pi2Circuits D) (input : Vector UInt8 32) (a : StA)
    (s₁ s₂ s₃ : Digest) (d : LeanVM.Prover.Tree × List E) : StB :=
  ⟨a, chalP s₁, chalP s₂, chalP s₃, qStackOf C input a s₁ s₂ s₃, d.1,
    { absorbW (absorbW (absorbW a.wr s₁) s₂) s₃ with
      stream := (absorbW (absorbW (absorbW a.wr s₁) s₂) s₃).stream ++
        (UniStatement.rootWord (UniStatement.rootHalves d.1.root)).toArray ++
        (UniComplete.scalarWire (pi2OodAt (qStackOf C input a s₁ s₂ s₃) d.2)).toArray }, d.2⟩

/-- **Stage B is `Q`'s tree and point, then a pure writer.** -/
theorem stageB_eq (D : RecDeployment) (C : Pi2Circuits D) (input : Vector UInt8 32) (a : StA) (s₁ s₂ s₃ : Digest) :
    stageB callKeccak256 D C input a s₁ s₂ s₃ =
      treeB C input a s₁ s₂ s₃ >>= fun d ↦ pure (outB C input a s₁ s₂ s₃ d) := by
  unfold stageB mid2 treeB outB qStackOf
  simp only [StateT.run_bind, StateT.run_lift, UniKeccakComplete.Prob.run_sendRoot, bind_assoc, pure_bind,
    StateT.run_pure, UniComplete.sendScalar, UniComplete.sendBytes, StateT.run_modify]

/-- **`t`'s input after stage B**: `s₃`'s bytes, then `Q`'s root word and its out-of-domain answer. -/
theorem tin_stageB {D : RecDeployment} (C : Pi2Circuits D) (input : Vector UInt8 32) (a : StA) (s₁ s₂ s₃ : Digest)
    (d : LeanVM.Prover.Tree × List E) :
    UniKeccakComplete.Prob.tInput (outB C input a s₁ s₂ s₃ d).wr = digestBytes s₃ ++
      UniStatement.rootWord (UniStatement.rootHalves d.1.root) ++
      UniComplete.scalarWire (pi2OodAt (qStackOf C input a s₁ s₂ s₃) d.2) := by
  simp [UniKeccakComplete.Prob.tInput, outB, absorbW]

theorem tin_stageB_length {D : RecDeployment} (C : Pi2Circuits D) (input : Vector UInt8 32) (a : StA)
    (s₁ s₂ s₃ : Digest) (qT : LeanVM.Prover.Tree × List E) :
    (UniKeccakComplete.Prob.tInput (outB C input a s₁ s₂ s₃ qT).wr).length = TF.tLen ∧
      (UniKeccakComplete.Prob.tInput (outB C input a s₁ s₂ s₃ qT).wr).take 32 = digestBytes s₃ := by
  rw [tin_stageB, List.append_assoc]
  refine ⟨?_, take_digestBytes _ _⟩
  rw [List.length_append, List.length_append, E2ECompleteness.length_digestBytes, UniKeccakComplete.Prob.rootWord_length,
    UniKeccakComplete.length_scalarWire]

/-! ## The named input and `t`'s freshness -/

/-- `Q`'s tree's height parameter. -/
abbrev muQ : ℕ := (stackVars 24).2.1

/-- **The out-of-domain point's queries** (`46` bytes, never `t`'s `88`) begin with nothing in particular: no
`tLen`-byte query. -/
theorem apq_oodPointM (n : ℕ) (r : Digest) (R : List Digest) :
    TF.APq (fun _ _ ↦ True) R (WhirBridge.Pcs.oodPointM callKeccak256 n r) := by
  unfold WhirBridge.Pcs.oodPointM
  generalize List.range n = l
  induction l generalizing R with
  | nil => exact .ret _ trivial
  | cons j l ih =>
    rw [List.mapM_cons]
    refine TF.APq.bind (Q₁ := fun _ _ ↦ True) (fun b R' _ ↦ (ih R').bind fun bs R'' _ ↦ .ret _ trivial) ?_
    exact .query _ _ (fun hl ↦ absurd hl (by rw [Pi2A.oodInput_length]; decide)) fun u ↦ .ret _ trivial

/-- **Stage B's hashes' `tLen`-byte queries begin with received digests** (the tree's nodes; the point asks none). -/
theorem apq_treeB {D : RecDeployment} (C : Pi2Circuits D) (input : Vector UInt8 32) (a : StA) (s₁ s₂ s₃ : Digest) :
    TF.APq (fun _ _ ↦ True) [default] (treeB C input a s₁ s₂ s₃) :=
  (TF.apq_commitWithH _ _ _ (List.mem_singleton_self _)).bind fun _ R _ ↦
    (apq_oodPointM _ _ R).bind fun _ _ _ ↦ .ret _ trivial

/-- **Stage B hashes nothing of `32` bytes.** -/
theorem hashOK32_treeB {D : RecDeployment} (C : Pi2Circuits D) (input : Vector UInt8 32) (a : StA)
    (s₁ s₂ s₃ : Digest) : HashOK (fun m ↦ m.length ≠ 32) (treeB C input a s₁ s₂ s₃) :=
  E2ECompleteness.HashOK.bind
    (UniKeccakComplete.Prob.HashOK.mono (fun m h ↦ h.1) (E2ECompleteness.hashOK_commitWithH _ _)) fun _ ↦
    E2ECompleteness.HashOK.bind (Pi2A.hashOK_oodPointM _ _ fun j ↦ by
      show (WhirBridge.Pcs.oodInput _ _ j).length ≠ 32
      rw [Pi2A.oodInput_length]
      decide) fun _ ↦ E2ECompleteness.HashOK.pure _ _

/-- **Stage B's hash count**: `Q`'s tree and its point's `μQ` hashes. -/
theorem hc_treeB {D : RecDeployment} (C : Pi2Circuits D) (Fa : Pi2Facts D C) (input : Vector UInt8 32) (a : StA)
    (s₁ s₂ s₃ : Digest) : HC (treeB C input a s₁ s₂ s₃) (E2ECompleteness.Cost.treeCost muQ + muQ) := by
  unfold treeB E2ECompleteness.Cost.treeCost
  rw [logN_G Fa]
  exact hc_of_qc ((E2ECompleteness.Cost.qc_commitWithH _ _).bind_le (fun _ ↦
    (Cost2.qc_oodPointM _ _).bind_le (fun _ ↦ E2ECompleteness.Cost.qc_pure _ 0) le_rfl) le_rfl)

/-- **`t`'s cache-hit bound**: `εα` and `(4N + 6 + |Q's tree| + |Q's point|) / 2^256`. -/
noncomputable def tFreshBound2 (N : ℕ) (εα : ℝ≥0∞) : ℝ≥0∞ :=
  εα + ((4 * N + 6 + (E2ECompleteness.Cost.treeCost muQ + muQ) : ℕ) : ℝ≥0∞) / 2 ^ 256

theorem muQ_le : muQ ≤ 40 := by decide

/-- **`t`'s bound in bits**: below `2^-200` at `N ≤ 2^50`, `εα ≤ 2^-201`. -/
theorem tFreshBound2_le {N : ℕ} {εα : ℝ≥0∞} (hN : N ≤ 2 ^ 50) (ha : εα ≤ (2 : ℝ≥0∞)⁻¹ ^ 201) :
    tFreshBound2 N εα ≤ (2 : ℝ≥0∞)⁻¹ ^ 200 := by
  have hT : E2ECompleteness.Cost.treeCost muQ ≤ 2 ^ 38 := by
    unfold E2ECompleteness.Cost.treeCost
    calc 5 * 2 ^ (muQ - 6 + 1) ≤ 2 ^ 3 * 2 ^ 35 := by
          gcongr
          · norm_num
          · have := muQ_le; omega
      _ = 2 ^ 38 := by norm_num
  have hm := muQ_le
  have hb : ((4 * N + 6 + (E2ECompleteness.Cost.treeCost muQ + muQ) : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      (2 : ℝ≥0∞)⁻¹ ^ 201 := by
    calc ((4 * N + 6 + (E2ECompleteness.Cost.treeCost muQ + muQ) : ℕ) : ℝ≥0∞) / 2 ^ 256
        ≤ ((2 ^ 55 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (201 + 55) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          gcongr
          exact_mod_cast (show 4 * N + 6 + (E2ECompleteness.Cost.treeCost muQ + muQ) ≤ 2 ^ 55 by omega)
      _ = (2 : ℝ≥0∞)⁻¹ ^ 201 := by
          rw [Nat.cast_pow, Nat.cast_ofNat]
          exact E2ECompleteness.two_pow_mul_inv_pow 55 201
  unfold tFreshBound2
  calc εα + _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 201 + (2 : ℝ≥0∞)⁻¹ ^ 201 := add_le_add ha hb
    _ = (2 : ℝ≥0∞)⁻¹ ^ 200 := by
        rw [← two_mul, show (201 : ℕ) = 1 + 200 from rfl, pow_add, ← mul_assoc, pow_one,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

end RecCompose.Pi2G

