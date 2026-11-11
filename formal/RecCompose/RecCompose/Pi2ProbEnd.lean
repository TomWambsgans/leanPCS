-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π2's completeness (`formal/RecStatement`'s
-- `RecCompleteness2`) at π2v4, from `Pi2Holds3.lean`'s `recCompleteness2_of_staged3` on `Pi2ProbStaged.lean`'s staged
-- run; the algebra's counts are `Pi2HonestCount.lean`'s (`card_badCopy_le`, `card_badT_le`, `card_badRho_le`); uses
-- leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two
-- calls, their lazy random oracles, `missProb`, `rpmError`.
import RecCompose.Pi2SimCore
import RecCompose.Pi2Holds3
import RecCompose.Pi2RhoFresh
import RecCompose.Pi2HonestCount

/-!
# π2's completeness (π2v4), from the staged run

**`recCompleteness2_pi2_v4`**: `RecCompleteness2 D P1 (pi2Prover D C.G Fa.pubOf nonceFuel) (delta2V4 N εα εt)` at the
real deployment (`hD`), for π1's prover `P1` (a two-call program `P1k` over the random permutation), from:

* **proved here**: `Holds3` of `pi2Staged` at `G = GAccA` (π1's prover returned a proof the graph accepted): `α`'s
  input length (`88`), off `G` the verdict rejects (`accA_v4`, `accB_v4`, by postconditions of the code, `Holds`), the
  bad sets' counts (the copy argument's `2N |E|²`, `t`'s `10N + 1`, `ρ`'s `1`), **`ρ`'s bound** (`rhoBad_v4`:
  `Pi2RhoFresh.prEvent_rho_leG` on stage C's split at `ρ`, `stageC_eq`), the grinding (`Pi2SimCore.rejectGood_pi2`,
  the staged run at pure functions through `pi2_accepts`);
* **named** (statements about the explicit staged run, proved in `Pi2Closed` from π1's prover's named facts by the
  code's commutation, duplex shape, block count and hash census): `Pi2ExperimentLe` (the experiment as the staged
  run), `Pi2RunDuplex`, `Pi2RunCost N`, `Pi2AlphaFreshG εα` and `Pi2TFreshG εt` (`α`'s and `t`'s inputs fresh where
  the graph accepted);
* **the other helpers' inputs**: `Pi2Pi1Openings D` (π1-rec4's graph's three claims open: `pi2_accepts`' `hp3`,
  `hpi1`), `Pi2WitnessExists D C Fa` (the circuit compiler's completeness, `pi2_accepts`' `hgood`), a non-hole position
  (`t`'s count).

`delta2V4 N εα εt = delta2' N εα εt (εt + (N + 1) / 2^256 + 1 / 2^192) (N · (1 − 2^-17)^nonceFuel)`;
**`delta2V4_le`**: below `2^-164` for `N ≤ 2^50`, `εα ≤ 2^-170`, `εt ≤ 2^-171` (about `2^-164.4`: `t`'s
`(10 · 2^24 + 1) / 2^192` and the copy argument's `2^25 / 2^192` dominate).
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2G

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM LeanVM.Rpm
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open E2ECompleteness (ro Cache)
open UniKeccakComplete.Prob.TFresh (HC hc_of_qc)
open Pi2S Pi2K Pi2P Pi2E
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

variable {D : RecDeployment} (C : Pi2Circuits D) (Fa : Pi2Facts D C) (input : Vector UInt8 32)

/-- **Off `GAccA` of its stage A, stage C's verdict's first component is `false`.** -/
theorem accB_v4 (b : StB) (hb : ¬ GAccA b.a) (st : Digest) (c : Cache)
    (z : ((Bool × Bool) × ((RecSetupRoots × E) × E)) × Cache)
    (hz : z ∈ support ((simulateQ ro (stageC callKeccak256 callKeccakF1600 D C input b st)).run c)) :
    z.1.1.1 = false :=
  holds_ro_support (holds_stageC callKeccak256 callKeccakF1600 D C input b st hb) c z hz

/-- **Off `GAccA`, the tail's verdict's first component is `false`.** -/
theorem accA_v4 (P1k : OracleComp KeccakCalls (Option UniKeccak.KeccakProof)) (a : StA) (ha : ¬ GAccA a)
    (s₁ s₂ s₃ : Digest) (c : Cache) (z : (pi2Staged D C Fa P1k input).Tail × Cache)
    (hz : z ∈ support ((simulateQ ro ((pi2Staged D C Fa P1k input).tail a s₁ s₂ s₃)).run c)) :
    z.1.1.1 = false := by
  refine holds_ro_support (P := fun y : (pi2Staged D C Fa P1k input).Tail ↦ y.1.1 = false) ?_ c z hz
  unfold Pi2Staged.tail
  refine holds_bind (holds_stageB callKeccak256 D C input a s₁ s₂ s₃) fun b hb ↦
    holds_bind (holds_true _) fun st _ ↦ ?_
  exact holds_bind (holds_stageC callKeccak256 callKeccakF1600 D C input b st (by rw [hb]; exact ha))
    fun z hz' ↦ holds_pure hz'

/-! ## Stage C, split at `ρ` -/

/-- The values at `t` (`post2`'s): the `2^r` fold values, `ξ`, `s`. -/
def valsC (b : StB) (st : Digest) : List E :=
  foldValues (C.G b.a.roots).logN (C.G b.a.roots).logW (wTableB (C.G b.a.roots) b.a.vw.2) (chalP st) ++
    [xiOf (C.G b.a.roots).logN (D.circuitAt b.a.roots.pi1).setupStack b.β (chalP st),
      sOf (C.G b.a.roots).logN (pNovel (C.G b.a.roots) b.a.vw.2) (chalP st)]

/-- The stream after the values at `t`. -/
def streamC (b : StB) (st : Digest) : Array UInt8 :=
  b.wr.stream ++ ((valsC C b st).flatMap UniComplete.scalarWire).toArray

/-- **`ρ`'s input**: `t`'s answer's bytes, then the values' (`sampleW`'s). -/
def rinC (b : StB) (st : Digest) : List UInt8 :=
  digestBytes st ++ ((streamC C b st).extract b.wr.stream.size (streamC C b st).size).toList

/-- **The prover's output** at `ρ`'s answer `sr`. -/
def outC (b : StB) (st sr : Digest) : Pi2Out :=
  ⟨streamC C b st, b.a.wS, b.a.wT, b.qS, b.qT,
    ⟨publicScalarsOf input.toList b.a.vw.1, b.α, b.β, b.γ, chalP st,
      foldValues (C.G b.a.roots).logN (C.G b.a.roots).logW (wTableB (C.G b.a.roots) b.a.vw.2) (chalP st),
      xiOf (C.G b.a.roots).logN (D.circuitAt b.a.roots.pi1).setupStack b.β (chalP st),
      sOf (C.G b.a.roots).logN (pNovel (C.G b.a.roots) b.a.vw.2) (chalP st), chalP sr⟩, b.a.wP, b.qP⟩

/-- **After `ρ`**: the openings and the contract, at the prover's output. -/
noncomputable def zC (b : StB) (st sr : Digest) : OracleComp KeccakCalls (Bool × Bool) :=
  match b.a.p1 with
  | none => pure (false, false)
  | some p1 => restC callKeccak256 callKeccakF1600 D C input b p1 (outC C input b st sr)

/-- **Stage C, split at `ρ`**: where π1's prover returned a proof, `ρ`'s query, then the rest. -/
theorem stageC_eq (b : StB) (p1 : UniKeccak.KeccakProof) (hp : b.a.p1 = some p1) (st : Digest) :
    stageC callKeccak256 callKeccakF1600 D C input b st =
      callKeccak256 (rinC C b st) >>= fun sr ↦
        (fun v ↦ (v, ((b.a.roots, chalP st), chalP sr))) <$> zC C input b st sr := by
  unfold stageC zC
  rw [hp]
  simp only [post2, StateT.run_bind, UniComplete.sendScalars, UniComplete.sendBytes, StateT.run_modify,
    UniComplete.sampleW, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
    map_eq_bind_pure_comp]
  rfl

theorem rinC_length (hW : ∀ roots, (C.G roots).logW = 4) (b : StB) (st : Digest) :
    (rinC C b st).length = 464 ∧ (rinC C b st).take 32 = digestBytes st := by
  refine ⟨?_, List.take_left' (E2ECompleteness.length_digestBytes st)⟩
  unfold rinC streamC
  have hv : (valsC C b st).length = 18 := by
    unfold valsC
    rw [List.length_append, length_foldValues, hW]
    rfl
  have hb : ((valsC C b st).flatMap UniComplete.scalarWire).length = 432 := by
    rw [List.length_flatMap]
    simp only [UniKeccakComplete.length_scalarWire, List.map_const', List.sum_replicate, smul_eq_mul, hv]
  simp only [List.length_append, E2ECompleteness.length_digestBytes, Array.toList_extract, List.extract_eq_take_drop,
    List.length_take, List.length_drop, Array.size_append, List.size_toArray, hb]
  simp [hv]

/-! ## The counts -/

include Fa in
set_option exponentiation.threshold 1024 in
/-- **The copy argument's bad triples**: at most `2N |E|² = 2^25 · 2^384`. -/
theorem card_badSet2_v4 (p : Pr2) : (badSet2 C.G p).card ≤ 2 ^ 25 * 2 ^ 384 := by
  classical
  unfold badSet2
  refine (card_badCopy_le _ p.2.1 p.2.2).trans (le_of_eq ?_)
  rw [RecPiop.Circuit.N, logN_G Fa p.1, LeanVM.Protocol.card_E]
  norm_num

include Fa in
/-- **`t`'s bad points**: for a witness, off `BadCopy`, at most `10N + 1`. -/
theorem card_badT2_v4 (hnh : ∀ roots, ∃ i < (C.G roots).N, ¬ (C.G roots).IsHole i) (fp : Pr2 × E × E × E) :
    ∃ T : Finset E, T.card ≤ 10 * 2 ^ 24 + 1 ∧ ∀ t, badT2 C.G fp t → t ∈ T := by
  classical
  by_cases hw : (C.G fp.1.1).Satisfies fp.1.2.2 (RecCircuit.emb fp.1.2.1)
  · by_cases hbad : BadCopy (C.G fp.1.1) fp.1.2.1 fp.1.2.2 fp.2.1 fp.2.2.1 fp.2.2.2
    · exact ⟨∅, by simp, fun t ht ↦ absurd hbad ht.2.1⟩
    · refine ⟨_, (card_badT_le _ (Fa.valid fp.1.1) (kCircuit_toPiop _) (by rw [logN_G Fa fp.1.1]; omega) fp.1.2.1
        fp.1.2.2 hw fp.2.1 fp.2.2.1 fp.2.2.2 hbad (hnh fp.1.1)).trans (by rw [RecPiop.Circuit.N, logN_G Fa fp.1.1]),
        fun t ht ↦ ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht.2.2⟩
  · exact ⟨∅, by simp, fun t ht ↦ absurd ht.1 hw⟩

/-- **`ρ`'s bad values**: at most one. -/
theorem card_badR2_v4 (fr : RecSetupRoots × E) : ∃ T : Finset E, T.card ≤ 1 ∧ ∀ ρ, badR2 C.G fr ρ → ρ ∈ T := by
  classical
  exact ⟨_, card_badRho_le (C.G fr.1) fr.2, fun ρ h ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

/-- **The run up to `t`'s query**: its Keccak-256 queries at most the run's block calls. -/
theorem Pi2Staged.hc_pre (S : Pi2Staged) {N : ℕ} (h : Common.QueryCostAtMost S.run hashBlocks N) : HC S.pre N := by
  rw [S.run_eq_pre] at h
  exact hc_of_qc (Common.QueryCostAtMost.of_bind h)

/-! ## The named facts on freshness -/

/-- **Named: `α`'s input is fresh where the graph accepted** (v3's `Pi2Sim.alphaFresh_of`). -/
def Pi2AlphaFreshG (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniKeccak.KeccakProof))
    (εα : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q →
    Pr{let p ← (simulateQ ro (pi2Staged D C Fa (P1k input rows q) input).A).run ∅}[
      p.2 (.inl ((pi2Staged D C Fa (P1k input rows q) input).inp p.1)) ≠ none ∧ GAccA p.1] ≤ εα

/-- **Named: `t`'s input is fresh where the graph accepted** (v3's `pi2TFresh_ofG`, from `α`'s). -/
def Pi2TFreshG (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniKeccak.KeccakProof))
    (εt : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q →
    Pr{let p ← (simulateQ ro (pi2Staged D C Fa (P1k input rows q) input).pre).run ∅}[
      p.2 (.inl ((pi2Staged D C Fa (P1k input rows q) input).tin p.1.1)) ≠ none ∧ GAccA p.1.1.a] ≤ εt

/-! ## `Holds3` and π2's completeness -/

/-- **`ρ`'s bound at π2's staged run**: `εt + (N + 1) / 2^256 + 1 / 2^192`. -/
theorem rhoBad_v4 (P1k : OracleComp KeccakCalls (Option UniKeccak.KeccakProof)) {N : ℕ}
    (hcost : Common.QueryCostAtMost (pi2Staged D C Fa P1k input).run hashBlocks N) {εt : ℝ≥0∞}
    (htf : Pr{let p ← (simulateQ ro (pi2Staged D C Fa P1k input).pre).run ∅}[
      p.2 (.inl ((pi2Staged D C Fa P1k input).tin p.1.1)) ≠ none ∧ GAccA p.1.1.a] ≤ εt) :
    Pr{let z ← (simulateQ ro (pi2Staged D C Fa P1k input).run).run' ∅}[
      z.1.1.1 = true ∧ badR2 C.G z.1.2.2.1 z.1.2.2.2] ≤
      εt + (((N + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + ((1 : ℕ) : ℝ≥0∞) / 2 ^ 192) :=
  prEvent_rho_leG (pi2Staged D C Fa P1k input) (rinC C) (fun b st ↦ (b.a.roots, chalP st)) (zC C input)
    (fun b : StB ↦ GAccA b.a)
    (fun b hb st ↦ by
      obtain ⟨hs, -⟩ := hb
      obtain ⟨p1, hp⟩ := Option.isSome_iff_exists.mp hs
      exact stageC_eq C input b p1 hp st)
    (fun b st _ ↦ rinC_length C Fa.logW b st) (badR2 C.G) 1 (card_badR2_v4 C)
    (fun b hb st c z hz ↦ accB_v4 C input b hb st c z hz) (Pi2Staged.hc_pre _ hcost) htf

/-- **π2's completeness error** (π2v4) at `N` block calls, `α`'s and `t`'s freshness `εα`, `εt`: `ρ`'s
`εt + (N + 1) / 2^256 + 1 / 2^192`, the grinding `N (1 − 2^-17)^nonceFuel`. -/
noncomputable def delta2V4 (N : ℕ) (εα εt : ℝ≥0∞) : ℝ≥0∞ :=
  delta2' N εα εt (εt + (((N + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + ((1 : ℕ) : ℝ≥0∞) / 2 ^ 192))
    ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)

/-- **The staged run's `Holds3`** at π2v4. -/
theorem holds3_v4 (hD : D.Real) (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (P1 : Pi1Prover D)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniKeccak.KeccakProof))
    {N : ℕ} {εα εt : ℝ≥0∞}
    (hexp : Pi2ExperimentLe D C Fa P1 P1k) (hdup : Pi2RunDuplex D C Fa P1k)
    (hcost : Pi2RunCost D C Fa P1k N) (hal : Pi2AlphaFreshG D C Fa P1k εα) (htf : Pi2TFreshG D C Fa P1k εt)
    (hpo : Pi2Pi1Openings D) (hwc : Pi2WitnessExists D C Fa)
    (hnh : ∀ roots, ∃ i < (C.G roots).N, ¬ (C.G roots).IsHole i)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows) (hfit : D.pi1.shape.RowsFit rows)
    (hrel : D.pi1.HonestRelation D.flock rows input q) :
    (pi2Staged D C Fa (P1k input rows q) input).Holds3 D P1 (pi2Prover D C.G Fa.pubOf PcsQuotient.nonceFuel)
      input rows q 88 (badSet2 C.G) (badT2 C.G) (badR2 C.G) GAccA (fun b : StB ↦ GAccA b.a) (2 ^ 25)
      (10 * 2 ^ 24 + 1) N εα εt (εt + (((N + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + ((1 : ℕ) : ℝ≥0∞) / 2 ^ 192))
      ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) where
  experiment := hexp input rows q hfit hrel
  duplex := hdup input rows q hfit hrel
  cost := hcost input rows q hfit hrel
  L_ne := by norm_num
  inp_length _ := fixLen_length 88 _
  alphaFresh := hal input rows q hfit hrel
  accA := fun a ha s₁ s₂ s₃ c z hz ↦ accA_v4 C Fa input (P1k input rows q) a ha s₁ s₂ s₃ c z hz
  accB := fun b hb st c z hz ↦ accB_v4 C input b hb st c z hz
  badCard p := card_badSet2_v4 C Fa p
  badTCard fp := card_badT2_v4 C Fa hnh fp
  tFresh := htf input rows q hfit hrel
  rhoBad := rhoBad_v4 C Fa input (P1k input rows q) (hcost input rows q hfit hrel) (htf input rows q hfit hrel)
  rejectGood := Pi2Sim.rejectGood_pi2 hD C Fa hroots hwc hpo (P1k input rows q) input (hcost input rows q hfit hrel)

/-- **π2's completeness** (π2v4) at the real deployment: `RecCompleteness2 D P1 (pi2Prover …) (delta2V4 N εα εt)`. -/
theorem recCompleteness2_pi2_v4 (hD : D.Real) (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt)
    (P1 : Pi1Prover D)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniKeccak.KeccakProof))
    {N : ℕ} {εα εt : ℝ≥0∞}
    (hexp : Pi2ExperimentLe D C Fa P1 P1k) (hdup : Pi2RunDuplex D C Fa P1k)
    (hcost : Pi2RunCost D C Fa P1k N) (hal : Pi2AlphaFreshG D C Fa P1k εα) (htf : Pi2TFreshG D C Fa P1k εt)
    (hpo : Pi2Pi1Openings D) (hwc : Pi2WitnessExists D C Fa)
    (hnh : ∀ roots, ∃ i < (C.G roots).N, ¬ (C.G roots).IsHole i) :
    RecCompleteness2 D P1 (pi2Prover D C.G Fa.pubOf PcsQuotient.nonceFuel) (delta2V4 N εα εt) :=
  recCompleteness2_of_staged3 fun input rows q hfit hrel ↦
    ⟨_, _, _, _, _, _, holds3_v4 C Fa hD hroots P1 P1k hexp hdup hcost hal htf hpo hwc hnh input rows q hfit
      hrel⟩

/-- **`δ2` in bits** (π2v4): below `2^-164` for `N ≤ 2^50` block calls, `εα ≤ 2^-170`, `εt ≤ 2^-171`. -/
theorem delta2V4_le {N : ℕ} {εα εt : ℝ≥0∞} (hN : N ≤ 2 ^ 50) (ha : εα ≤ (2 : ℝ≥0∞)⁻¹ ^ 170)
    (ht : εt ≤ (2 : ℝ≥0∞)⁻¹ ^ 171) : delta2V4 N εα εt ≤ (2 : ℝ≥0∞)⁻¹ ^ 164 := by
  have hsmall : ∀ k, 172 ≤ k → (2 : ℝ≥0∞)⁻¹ ^ k ≤ (2 : ℝ≥0∞)⁻¹ ^ 172 := fun k hk ↦
    E2ECompleteness.inv_pow_le_inv_pow hk
  have h1 : ((N + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ (2 : ℝ≥0∞)⁻¹ ^ 172 := by
    calc ((N + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ ((2 ^ 51 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (205 + 51) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          gcongr
          exact_mod_cast (show N + 1 ≤ 2 ^ 51 by omega)
      _ = (2 : ℝ≥0∞)⁻¹ ^ 205 := by
          rw [Nat.cast_pow, Nat.cast_ofNat]
          exact E2ECompleteness.two_pow_mul_inv_pow 51 205
      _ ≤ _ := hsmall 205 (by norm_num)
  have h2 : ((1 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ (2 : ℝ≥0∞)⁻¹ ^ 172 := by
    rw [Nat.cast_one, one_div, ENNReal.inv_pow]
    exact hsmall 192 (by norm_num)
  have ht' : εt ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ 172 := by
    refine ht.trans (le_of_eq ?_)
    rw [show (172 : ℕ) = 1 + 171 from rfl, pow_add, ← mul_assoc, pow_one,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hr : εt + (((N + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + ((1 : ℕ) : ℝ≥0∞) / 2 ^ 192) ≤ (2 : ℝ≥0∞)⁻¹ ^ 170 := by
    calc _ ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ 172 + ((2 : ℝ≥0∞)⁻¹ ^ 172 + (2 : ℝ≥0∞)⁻¹ ^ 172) :=
          add_le_add ht' (add_le_add h1 h2)
      _ = 2 ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ (170 + 2) := by ring
      _ = (2 : ℝ≥0∞)⁻¹ ^ 170 := E2ECompleteness.two_pow_mul_inv_pow 2 170
  exact delta2'_le hN ha (ht.trans (E2ECompleteness.inv_pow_le_inv_pow (by norm_num))) hr (grind_le hN)

end RecCompose.Pi2G

/-- info: 'RecCompose.Pi2G.recCompleteness2_pi2_v4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.recCompleteness2_pi2_v4

/-- info: 'RecCompose.Pi2G.delta2V4_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.delta2V4_le
