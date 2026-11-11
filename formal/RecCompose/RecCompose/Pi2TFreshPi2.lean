-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `Pi2TFresh.lean`'s `tFresh_of` at π2's staged run
-- (`RecCompose.Pi2ProbStaged`'s `pi2Staged`: `stageB`, `mid2`, `crates/leanvm/rec/src/pi2/prover.rs`'s `Q` and `t`);
-- uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0).
import RecCompose.Pi2TFresh
import RecCompose.Pi2AlphaLen

/-!
# `Pi2TFresh`, proved from `α`'s freshness

* **`Pi2AlphaFresh D C Fa P1k εα`** (named, replacing `Pi2HashBeforeAlpha`, which a π1 prover hashing `32`-byte inputs breaks, `Pi2Chain`): in
  the two-call random-oracle model, `α`'s input (`inp`, the state after the seed and π1's public data and `W`'s root,
  `608` bytes) is already hashed after stage A with probability at most `εα`.
* **`stageB_eq`**: stage B is `Q`'s tree (`commitWithH`) and out-of-domain point (`oodPointM`: `28` hashes of `46`
  bytes, neither `32` nor `88`, `apq_oodPointM`) then a pure writer, whose `t` input is `s₃`'s bytes, `Q`'s root word
  and its answer (**`tin_stageB`**, `88` bytes).
* **`pi2TFresh_of`**: `Pi2TFresh D C Fa P1k (tFreshBound2 N εα)`, `tFreshBound2 N εα = εα + (4N + 6 + treeCost μQ + μQ) /
  2^256`, for every `P1k`, from `Pi2RunCost D C Fa P1k N` and `Pi2AlphaFresh D C Fa P1k εα`;
  **`tFreshBound2_le`**: below `2^-200` at `N ≤ 2^50`, `εα ≤ 2^-201`.
* **`recCompleteness2_pi2_staged2`**: π2's completeness from `Pi2ProbStaged`'s named facts with `Pi2HashBeforeAlpha` and
  `Pi2TFresh` replaced by `Pi2AlphaFresh`, error `delta2' N εα (tFreshBound2 N εα) εpow`; **`delta2_pi2_le2`**: below
  `2^-164` at `N ≤ 2^50`, `εα ≤ 2^-201`. **`recCompleteness_pi2_staged2_fs`**: end to end.
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
    (hNovel (C.G a.roots) a.vw.2 (chalP s₁) (chalP s₂))
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

/-- **Named: `α`'s input is fresh** (replaces `Pi2HashBeforeAlpha`, false at π1-rec3's prover, which hashes `32`-byte
inputs, `Pi2Chain`): in the two-call random-oracle model, `α`'s input (`608` bytes: the state after the seed, π1's
public data, `W`'s root) is already hashed after stage A (the setup, `P1k`, π1-rec3's graph and its openings, π2's
prover up to `W`'s root) with probability at most `εα`. -/
def Pi2AlphaFresh (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniKeccak.KeccakProof))
    (εα : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q →
    Pr{let p ← (simulateQ ro (pi2Staged D C Fa (P1k input rows q) input).A).run ∅}[
      p.2 (.inl ((pi2Staged D C Fa (P1k input rows q) input).inp p.1)) ≠ none] ≤ εα

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

/-- **`Pi2TFresh`, from the run's cost and `α`'s freshness**, for every `P1k`. -/
theorem pi2TFresh_of {D : RecDeployment} (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniKeccak.KeccakProof))
    {N : ℕ} {εα : ℝ≥0∞} (hcost : Pi2RunCost D C Fa P1k N) (hα : Pi2AlphaFresh D C Fa P1k εα) :
    Pi2TFresh D C Fa P1k (tFreshBound2 N εα) := by
  intro input rows q hfit hrel
  refine TF.tFresh_of (pi2Staged D C Fa (P1k input rows q) input) (fun a s₁ s₂ s₃ ↦ treeB C input a s₁ s₂ s₃)
    (fun a s₁ s₂ s₃ qT ↦ outB C input a s₁ s₂ s₃ qT) (fun a s₁ s₂ s₃ ↦ stageB_eq D C input a s₁ s₂ s₃)
    (fun a s₁ s₂ s₃ ↦ apq_treeB C input a s₁ s₂ s₃) (fun a s₁ s₂ s₃ ↦ hashOK32_treeB C input a s₁ s₂ s₃)
    (NT := E2ECompleteness.Cost.treeCost muQ + muQ) (fun a s₁ s₂ s₃ ↦ hc_treeB C Fa input a s₁ s₂ s₃)
    (fun a s₁ s₂ s₃ qT ↦ tin_stageB_length C input a s₁ s₂ s₃ qT) (by norm_num : (608 : ℕ) ≠ 32)
    (fun a ↦ fixLen_length 608 _) ((pi2Staged D C Fa (P1k input rows q) input).hc_A (hcost input rows q hfit hrel))
    (hα input rows q hfit hrel) |>.trans (le_of_eq ?_)
  unfold tFreshBound2
  rfl

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

/-! ## π2's completeness, `α`'s input fresh -/

/-- **The staged run's `Holds2`**, at the real deployment's facts: `holds_pi2`'s fields, `α`'s freshness for `hashA`,
`t`'s freshness proved. -/
theorem holds2_pi2 {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (P1 : Pi1Prover D)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniKeccak.KeccakProof))
    {N : ℕ} {εα : ℝ≥0∞}
    (hexp : Pi2ExperimentLe D C (pi2Facts hD C hchk) P1 P1k) (hrun : Pi2RunAt D C (pi2Facts hD C hchk) P1k)
    (hdup : Pi2RunDuplex D C (pi2Facts hD C hchk) P1k) (hcost : Pi2RunCost D C (pi2Facts hD C hchk) P1k N)
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) P1k εα)
    (hpo : Pi2Pi1Openings D C (pi2Facts hD C hchk)) (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk))
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows) (hfit : D.pi1.shape.RowsFit rows)
    (hrel : D.pi1.HonestRelation D.flock rows input q) :
    (pi2Staged D C (pi2Facts hD C hchk) (P1k input rows q) input).Holds2 D P1
      (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel) input rows q 608 (badSet2 C.G) (badT2 C.G)
      (2 ^ 25 + 36) (9 * 2 ^ 24) N εα (tFreshBound2 N εα)
      ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) where
  experiment := hexp input rows q hfit hrel
  duplex := hdup input rows q hfit hrel
  cost := hcost input rows q hfit hrel
  L_ne := by norm_num
  inp_length _ := fixLen_length 608 _
  alphaFresh := hal input rows q hfit hrel
  badCard p := card_badCopy_pi2 (pi2Facts hD C hchk) p.1 p.2.1 p.2.2
  badTCard fp := card_badT_pi2 (pi2Facts hD C hchk) fp.1.1 fp.1.2.1 fp.1.2.2 fp.2.1 fp.2.2.1 fp.2.2.2
    (nonHole_pi2 C hchk (pi2Facts hD C hchk) fp.1.1)
  tFresh := pi2TFresh_of C (pi2Facts hD C hchk) P1k hcost hal input rows q hfit hrel
  rejectGood := rejectGood_pi2 hD C (pi2Facts hD C hchk) hroots hwc hpo P1k hrun input rows q
    (hcost input rows q hfit hrel)

/-- **π2's completeness, `α`'s input fresh** (`recCompleteness2_pi2_staged` with `Pi2HashBeforeAlpha`, false at
a π1 prover hashing `32`-byte inputs, replaced by `Pi2AlphaFresh εα`, and `Pi2TFresh` proved). -/
theorem recCompleteness2_pi2_staged2 {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (P1 : Pi1Prover D)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniKeccak.KeccakProof))
    {N : ℕ} {εα : ℝ≥0∞}
    (hexp : Pi2ExperimentLe D C (pi2Facts hD C hchk) P1 P1k) (hrun : Pi2RunAt D C (pi2Facts hD C hchk) P1k)
    (hdup : Pi2RunDuplex D C (pi2Facts hD C hchk) P1k) (hcost : Pi2RunCost D C (pi2Facts hD C hchk) P1k N)
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) P1k εα)
    (hpo : Pi2Pi1Openings D C (pi2Facts hD C hchk)) (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk)) :
    RecCompleteness2 D P1 (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel)
      (delta2' N εα (tFreshBound2 N εα) ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness2_of_staged2 fun input rows q hfit hrel ↦
    ⟨_, _, _, holds2_pi2 hD C hchk hroots P1 P1k hexp hrun hdup hcost hal hpo hwc input rows q hfit hrel⟩

/-- **`δ2` in bits**, `α`'s input fresh: below `2^-164` at `N ≤ 2^50` block calls and `εα ≤ 2^-201`. -/
theorem delta2_pi2_le2 {N : ℕ} {εα : ℝ≥0∞} (hN : N ≤ 2 ^ 50) (ha : εα ≤ (2 : ℝ≥0∞)⁻¹ ^ 201) :
    delta2' N εα (tFreshBound2 N εα) ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 164 :=
  delta2'_le hN (ha.trans (E2ECompleteness.inv_pow_le_inv_pow (by norm_num))) (tFreshBound2_le hN ha) (grind_le hN)

/-- **The recursive verifier's completeness end to end**, `α`'s input fresh. -/
theorem recCompleteness_pi2_staged2_fs {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (P1 : Pi1Prover D)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniKeccak.KeccakProof))
    {N : ℕ} {εα : ℝ≥0∞}
    (hexp : Pi2ExperimentLe D C (pi2Facts hD C hchk) P1 P1k) (hrun : Pi2RunAt D C (pi2Facts hD C hchk) P1k)
    (hdup : Pi2RunDuplex D C (pi2Facts hD C hchk) P1k) (hcost : Pi2RunCost D C (pi2Facts hD C hchk) P1k N)
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) P1k εα)
    (hpo : Pi2Pi1Openings D C (pi2Facts hD C hchk)) (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk))
    (δ1 δh : ℝ≥0∞) (h1 : Pi1CompletenessKeccak D P1 δ1) (hh : Pi1HazardKeccakHonest D P1 δh) :
    RecCompletenessWith D (composeProver D P1 (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel))
      (δ1 + δh + delta2' N εα (tFreshBound2 N εα)
        ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness_end_fs D hD P1 _ _
    (recCompleteness2_pi2_staged2 hD C hchk hroots P1 P1k hexp hrun hdup hcost hal hpo hwc) δ1 δh h1 hh

end RecCompose.Pi2G

/-- info: 'RecCompose.Pi2G.pi2TFresh_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.pi2TFresh_of

/-- info: 'RecCompose.Pi2G.recCompleteness2_pi2_staged2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.recCompleteness2_pi2_staged2

/-- info: 'RecCompose.Pi2G.delta2_pi2_le2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.delta2_pi2_le2

/-- info: 'RecCompose.Pi2G.recCompleteness_pi2_staged2_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.recCompleteness_pi2_staged2_fs
