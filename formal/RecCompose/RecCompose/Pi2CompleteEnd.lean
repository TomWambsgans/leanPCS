-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π2's honest prover is `crates/leanvm/rec/src/pi2/prover.rs`'s
-- (`RecCompose.Pi2Prover`), its witness the circuit compiler's (`crates/leanvm/rec/src/circuit/compile.rs`, not
-- transcribed: chosen here); the statements are `formal/RecStatement`'s (`RecCompleteness2`, `RecCompleteness`).
import RecCompose.Pi2Complete
import RecCompose.Pi2Prob
import RecCompose.Pi2HonestThm
import RecCompose.Pi2HonestCount
import RecCompose.Real
import RecCompose.End

/-!
# π2's completeness, and the recursive verifier's end to end

* **`pi2Prover D C Fa fuel : Pi2Prover`**, π2's honest prover as the recursion runs it (a Lean transcription; the
  deployed Rust prover is trusted for completeness, see `pi2Prover`): the setup's trees and π1's and π2's IVs recomputed
  over `π`, the circuit's witness and public values for π1's stream (`pi2Choice`: a choice of one satisfying the
  compiled circuit at the values' public limbs and holding π1's stream, `Pi2Good`), then
  `pi2ProveWith` (`prover.rs`'s `prove_with` and `open`, Keccak-256 the sponge over `π`, `π` for the proofs of work), its
  stream and five PCS openings after π1's three.
* **`Pi2WitnessComplete D C Fa`** (the circuit compiler's completeness; proved at the real deployment,
  `Pi2W.pi2WitnessComplete`): on a stream whose π1-rec3 graph checks hold, such a witness exists.
* **`pi2_accepts`** (proved): at a pure permutation, π2's honest prover's proof is accepted by the contract, off the bad
  challenges (π2's arithmetic passes and its claims hold, `contract_accepts`) and the proofs of work, π1's three
  openings accepted.
* **`Pi2StagedFacts`** (named: the code-level bridge of the experiment to the two-call model, `Pi2Staged.Holds` at
  `L = 608` (`α`'s input: the state and π1's two roots and 19 elements and `W`'s root), the copy argument's
  `(2^25 + 36) |E|²` bad triples (`2N + n_P`, `N = 2^24`, `n_P = 36`), `t`'s `2^27` (`8N`), `N` block calls, `εt`,
  `εpow`): its `rejectGood` is `pi2_accepts` with the grinding, its other fields the commutation, duplex shape, cost and
  lengths of the composed code (as UniComplete's `ProverSim`, `ProverDuplex`, `ProverCost`, `ProbTFresh`, `ProbGrind`
  prove them for its π1 prover).
* **`recCompleteness2_pi2`**: `RecCompleteness2 D P1 (pi2Prover D C Fa fuel) (delta2 N εt εpow)`;
  **`delta2_le`**: `delta2 N εt εpow ≤ 2^-164` for `N ≤ 2^50`, `εt ≤ 2^-200`, `εpow ≤ 2^-300`;
  **`recCompleteness_pi2_fs`**: the recursive verifier's completeness end to end with `pi2Prover`, error
  `δ1 + δh + delta2`.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2E

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open Pi2S Pi2K Pi2P
open LeanVM (rpmError)
open scoped ENNReal

/-! ## The witness -/

/-- **An honest witness and public values** for π1's stream `s` at a setup: the values match the reads, the witness
satisfies the compiled circuit at the public limbs of the values' scalars, and it holds `s`. -/
def Pi2Good (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) (roots : RecSetupRoots)
    (input : Vector UInt8 32) (s : Array UInt8) (vw : List PublicValue × (ℕ → K)) : Prop :=
  List.Forall₂ ReadMatch (D.circuitAt roots.pi1).circuit.reads vw.1 ∧
    (C.G roots).Satisfies (Fa.pubOf roots (publicScalarsOf input.toList vw.1)) (RecCircuit.emb vw.2) ∧
    D.pi1Stream vw.2 = s

/-- **The circuit compiler's completeness**: on a stream whose π1-rec3 graph checks hold, an honest witness exists.
Proved at the real deployment (`Pi2W.pi2WitnessComplete`, from the compiler's completeness checks `completeSlots`,
`completeValues`, `completeGiven`, `completeCover`), which the end theorems use; here it is the input of the
`Pi2Sim` forms that take it as an argument. -/
def Pi2WitnessComplete (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) : Prop :=
  ∀ (roots : RecSetupRoots) (input : Vector UInt8 32) (s : Array UInt8),
    pi1GraphChecks (D.pi1IvAt roots.pi1) input s = true → ∃ vw, Pi2Good D C Fa roots input s vw

open Classical in
/-- **The witness π2's prover takes**: an honest one if there is one. -/
noncomputable def pi2Choice (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) (roots : RecSetupRoots)
    (input : Vector UInt8 32) (s : Array UInt8) : List PublicValue × (ℕ → K) :=
  if h : ∃ vw, Pi2Good D C Fa roots input s vw then h.choose else ([], fun _ ↦ 0)

theorem pi2Choice_good {D : RecDeployment} {C : Pi2Circuits D} {Fa : Pi2Facts D C} {roots : RecSetupRoots}
    {input : Vector UInt8 32} {s : Array UInt8} (h : ∃ vw, Pi2Good D C Fa roots input s vw) :
    Pi2Good D C Fa roots input s (pi2Choice D C Fa roots input s) := by
  unfold pi2Choice
  split
  next h' => exact h'.choose_spec
  next h' => exact absurd h h'

/-! ## The prover -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- **π2's honest prover** over `H`, `F`: the setup's trees, the IV, the witness, `pi2ProveWith` (`W`'s and `Q`'s
out-of-domain points read off `H`, `WhirBridge.Pcs.oodPointM H`), π1's openings first. -/
noncomputable def pi2ProverWith (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) (fuel : ℕ)
    (input : Vector UInt8 32) (p1 : UniKeccak.KeccakProof) : m (Option RecProof) := do
  let trees ← Pi2H.setupTreesWithH H F D
  let iv ← Pi2H.ivOfH H D trees.roots
  let vw := pi2Choice D C Fa trees.roots input p1.stream
  let c := D.circuitAt trees.roots.pi1
  let res ← pi2ProveWith H F fuel (C.G trees.roots) (WhirBridge.Pcs.oodPointM H) c.circuit c.setupStack trees.pi2 iv
    input.toList vw.1 vw.2
  return res.map fun x ↦ ⟨x.1, p1.c1, p1.c2, p1.setup, x.2.w, x.2.setup, x.2.qId, x.2.qPush, x.2.qSum⟩

end With

/-- **π2's honest prover in the random-permutation model**: Keccak-256 the sponge over `π`, `π` itself for WHIR's
proofs of work.

The deployed Rust prover is trusted for completeness; this Lean prover is a transcription (`Pi2Prover.lean`, after
`prover.rs`), compared with the Rust on the circuit compiler's example at `2^9`, `2^10` positions only (setup, `W`, `Q`
roots and the stream; `RecComposeTest/Pi2Prover.lean`), not on π2's real circuit. Its witness is not the Rust's witness
generation but `Classical.choose` among the `Pi2Good` witnesses (`pi2Choice`), which exist by
`Pi2W.pi2WitnessComplete`. -/
noncomputable def pi2Prover (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) (fuel : ℕ) : Pi2Prover :=
  pi2ProverWith (keccak256With queryPermutation) queryPermutation D C Fa fuel

/-! ## The core: the honest proof is accepted -/

/-- **The prover's run at a pure permutation**: the stream, then the five openings at the arithmetic's claims. -/
theorem pi2ProveWith_run (Hk : List UInt8 → Digest) (F : KeccakState → Id KeccakState) (fuel : ℕ)
    (G : RecPiop.Circuit E) (zf : ℕ → Digest → List E) (view : Circuit) (setupStack : Array K)
    (setupTree : LeanVM.Prover.Tree) (iv input : List UInt8) (values : List PublicValue) (w : ℕ → K) :
    Id.run (pi2ProveWith (m := Id) (Pure.pure ∘ Hk) F fuel G (pureZ zf) view setupStack setupTree iv input values w) =
      let out := proverOut Hk G zf view setupStack iv input values w
      let o := (Spec.of view).core.run out.inputs
      (PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel (stackVars G.logN).1 out.wPoint out.wTree out.wStack
        o.witnessPoint o.fold).bind fun a ↦
      (PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel (stackVars G.logN).2.2
        (UniKeccakComplete.pcsZ (stackVars G.logN).2.2 setupTree.root) setupTree
        (padStack (stackVars G.logN).2.2 fun i ↦ setupStack.getD i 0) o.setupPoint out.inputs.ξ).bind fun b ↦
      (PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel (stackVars G.logN).2.1 out.qPoint out.qTree out.qStack
        o.quotientPoint o.quotientValue).bind fun c ↦
      (PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel (stackVars G.logN).2.1 out.qPoint out.qTree out.qStack
        o.pushesPoint o.pushesValue).bind fun d ↦
      (PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel (stackVars G.logN).2.1 out.qPoint out.qTree out.qStack
        o.sumPoint o.sumValue).bind fun e ↦
      some (out.stream, ⟨a, b, c, d, e⟩) := rfl

/-- **π2's honest prover at a pure permutation**: `pi2ProveWith` at the setup's trees, the contract's IV and the witness
it takes, π1's openings first. -/
theorem pi2ProverWith_run (Hk : List UInt8 → Digest) (F : KeccakState → Id KeccakState) (D : RecDeployment)
    (C : Pi2Circuits D) (Fa : Pi2Facts D C) (fuel : ℕ) (input : Vector UInt8 32) (p1 : UniKeccak.KeccakProof) :
    Id.run (pi2ProverWith (m := Id) (Pure.pure ∘ Hk) F D C Fa fuel input p1) =
      let trees := Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)
      (Id.run (pi2ProveWith (m := Id) (Pure.pure ∘ Hk) F fuel (C.G trees.roots) (pureZ (pi2Z Hk))
        (D.circuitAt trees.roots.pi1).circuit (D.circuitAt trees.roots.pi1).setupStack trees.pi2
        (ivOf D Hk trees.roots) input.toList (pi2Choice D C Fa trees.roots input p1.stream).1
        (pi2Choice D C Fa trees.roots input p1.stream).2)).map
        fun x ↦ ⟨x.1, p1.c1, p1.c2, p1.setup, x.2.w, x.2.setup, x.2.qId, x.2.qPush, x.2.qSum⟩ := by
  unfold pi2ProverWith
  rw [oodPointM_id_eq]
  rfl

/-- The setup's table has `2^(m+1)` words. -/
theorem setupStack_size (c : Pi2Circuit) : c.setupStack.size = 2 ^ (c.circuit.logN + 1) := by
  unfold Pi2Circuit.setupStack
  simp [UniKeccakComplete.AlgC.bCoefficients_size, pow_succ, mul_two]

/-- **π2's claims on the stacks, as the PCS openings evaluate them**: `Pi2ClaimsHold` (`mleStk`) on stacks of `2^24`
and `2^28` words is `StackClaimsHold` (`stackEval`), the setup's on its table padded to `2^25` words. -/
theorem stackClaims_of_pi2Claims (D : RecDeployment) (roots : RecSetupRoots) (inp : Inputs E) (wStack qStack : Array K)
    (hview : (D.circuitAt roots.pi1).circuit = Data.circuit)
    (hw : wStack.size = 2 ^ 24) (hq : qStack.size = 2 ^ 28)
    (h : Pi2ClaimsHold D roots inp (fun j ↦ wStack.getD j 0) (fun j ↦ qStack.getD j 0)) :
    StackClaimsHold ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp) inp.ξ wStack qStack
      (padStack 25 fun i ↦ (D.circuitAt roots.pi1).setupStack.getD i 0) := by
  have hlogN : (D.circuitAt roots.pi1).circuit.logN = 24 := by rw [hview]; rfl
  obtain ⟨lW, lS, lQ, lP, lSum⟩ := run_points_length (Spec.of (D.circuitAt roots.pi1).circuit).core
    (by rw [hview]; rfl) (by rw [hview]; rfl) inp
  unfold Pi2ClaimsHold ClaimOn at h
  simp only [hlogN, Pi2W.stackVars_24] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Pi2W.stackEval_eq_mleStk _ _ (by rw [hw, lW]), lW]; exact h1
  · rw [Pi2W.stackEval_eq_mleStk _ _ (by rw [hq, lQ]), lQ]; exact h2
  · rw [Pi2W.stackEval_eq_mleStk _ _ (by rw [hq, lP]), lP]; exact h3
  · rw [Pi2W.stackEval_eq_mleStk _ _ (by rw [hq, lSum]), lSum]; exact h4
  · rw [Pi2W.stackEval_eq_mleStk _ _ (by rw [Pi2W.padStack_size, lS]), lS]
    rw [Pi2W.mleStk_congr (c' := fun j ↦ (D.circuitAt roots.pi1).setupStack.getD j 0)
      (fun j hj ↦ by simp only [padStack_getD, hj, ↓reduceIte])]
    exact h5

/-- **π2's honest proof is accepted** at a pure permutation `F` (Keccak-256 `Hk`): for the witness the prover takes
(an honest one, `hgood`), if the prover returns a proof, π2's arithmetic on its inputs passes and its claims hold on its
stacks (off the bad challenges, `halg`), and π1's three openings are accepted (`hpi1`), the contract accepts. -/
theorem pi2_accepts (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (F : KeccakState → Id KeccakState) (Hk : List UInt8 → Digest)
    (fuel : ℕ) (input : Vector UInt8 32) (p1 : UniKeccak.KeccakProof)
    (hgood : Pi2Good D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream
      (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream))
    (hGN : (C.G (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots).logN = 24)
    (hrow : Data.circuit.logRow = (C.G (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots).logW)
    (proof : RecProof)
    (hp : Id.run (pi2ProverWith (m := Id) (Pure.pure ∘ Hk) F D C Fa fuel input p1) = some proof)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt)
    (hbad : let trees := Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)
      let vw := pi2Choice D C Fa trees.roots input p1.stream
      let out := outOf D Hk trees.roots (C.G trees.roots) (pi2Z Hk) input vw.1 vw.2
      ¬ BadCopy (C.G trees.roots) vw.2 (Fa.pubOf trees.roots (publicScalarsOf input.toList vw.1))
        out.inputs.α out.inputs.β out.inputs.γ)
    (ht : let trees := Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)
      let vw := pi2Choice D C Fa trees.roots input p1.stream
      let out := outOf D Hk trees.roots (C.G trees.roots) (pi2Z Hk) input vw.1 vw.2
      ¬ BadT (C.G trees.roots) vw.2 out.inputs.α out.inputs.β out.inputs.γ out.inputs.t)
    (hpi1 : ∃ ops, pi1OpsOf D (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input
        proof.stream = some ops ∧
      Id.run (Pi2H.openSeqH (m := Id) (Pure.pure ∘ Hk) F ops proof) = true) :
    (Id.run (Pi2H.contractWithH (m := Id) (Pure.pure ∘ Hk) F D
      (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input proof)).1 = true := by
  simp only at hbad ht
  -- the prover's run
  have hres := hp
  rw [pi2ProverWith_run] at hres
  simp only at hres
  rw [pi2ProveWith_run] at hres
  simp only at hres
  rw [hGN, Pi2W.stackVars_24] at hres
  simp only at hres
  set trees := Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D) with htrees
  set vw := pi2Choice D C Fa trees.roots input p1.stream with hvw
  have hview : (D.circuitAt trees.roots.pi1).circuit = Data.circuit := hD.1 _
  have hlogN : (D.circuitAt trees.roots.pi1).circuit.logN = 24 := by rw [hview]; rfl
  obtain ⟨hmatch, hwS, -⟩ := hgood
  have hmatch' := hmatch
  rw [hview] at hmatch
  -- the algebra (`pi2_honest`), at the prover's inputs and stacks
  obtain ⟨-, -, -, -, -, -, -, -, -, hi, hwsk, hqsk⟩ := runWith_honest Hk (C.G trees.roots) (pi2Z Hk)
    (D.circuitAt trees.roots.pi1).circuit (D.circuitAt trees.roots.pi1).setupStack (ivOf D Hk trees.roots)
    input.toList vw.1 vw.2 hmatch' (by rw [hview]; exact hrow)
  have halg := pi2_honest Fa (pi2SetupColumns_of_real hD C hroots) trees.roots vw.2
    (publicScalarsOf input.toList vw.1) _ _ _ _
    (outOf D Hk trees.roots (C.G trees.roots) (pi2Z Hk) input vw.1 vw.2).inputs.ρ hwS hbad ht
  -- the setup's commitment, of its padded table
  set sS := padStack 25 fun i ↦ (D.circuitAt trees.roots.pi1).setupStack.getD i 0 with hsS
  have htree : trees.pi2 = E2ECompleteness.commitWithH (m := Id) (Pure.pure ∘ Hk) 25 sS := by
    show Pi2H.setupTreeWithH (Pure.pure ∘ Hk) (D.circuitAt trees.roots.pi1) = _
    unfold Pi2H.setupTreeWithH
    rw [hlogN, Pi2W.stackVars_24]
    exact (Pi2W.commitWithH_padStack _ (by norm_num) _).symm
  have hroot2 : trees.roots.pi2 = (E2ECompleteness.commitWithH (m := Id) (Pure.pure ∘ Hk) 25 sS).root := by
    rw [← htree]; rfl
  have hood2 : trees.roots.pi2Ood = UniKeccakComplete.pcsOod 25 sS trees.roots.pi2 := by
    show (D.circuitAt trees.roots.pi1).setupOod trees.pi2.root = _
    rw [Pi2W.setupOod_eq _ _ (by rw [setupStack_size, hlogN, Pi2W.stackVars_24])]
    simp only [hlogN, Pi2W.stackVars_24]
    rfl
  generalize hW : PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel 24 _ _ _ _ _ = rW at hres
  generalize hS : PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel 25 _ _ _ _ _ = rS at hres
  generalize hQ1 : PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel 28 _ _ _ _
    ((Spec.of _).core.run _).quotientValue = rQ1 at hres
  generalize hQ2 : PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel 28 _ _ _ _
    ((Spec.of _).core.run _).pushesValue = rQ2 at hres
  generalize hQ3 : PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel 28 _ _ _ _
    ((Spec.of _).core.run _).sumValue = rQ3 at hres
  rcases rW with _ | pW
  · simp at hres
  rcases rS with _ | pS
  · simp at hres
  rcases rQ1 with _ | pQ1
  · simp at hres
  rcases rQ2 with _ | pQ2
  · simp at hres
  rcases rQ3 with _ | pQ3
  · simp at hres
  simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hres
  subst hres
  have hwsz : (outOf D Hk trees.roots (C.G trees.roots) (pi2Z Hk) input vw.1 vw.2).wStack.size = 2 ^ 24 := by
    rw [hwsk, hGN]; exact Pi2W.padStack_size _ _
  have hqsz : (outOf D Hk trees.roots (C.G trees.roots) (pi2Z Hk) input vw.1 vw.2).qStack.size = 2 ^ 28 := by
    rw [hqsk, hGN]; exact Pi2W.padStack_size _ _
  refine contract_accepts D F Hk trees.roots (C.G trees.roots) hview hGN hrow (by rw [hD.2.1]; rfl) sS
    (Pi2W.padStack_size _ _) hroot2 hood2 input vw.1 vw.2 hmatch fuel p1.c1 p1.c2 p1.setup pW pS pQ1 pQ2 pQ3
    ⟨by rw [hi]; exact halg.1, stackClaims_of_pi2Claims D trees.roots _ _ _ hview hwsz hqsz ?_⟩
    hW (by rw [← htree]; exact hS) hQ1 hQ2 hQ3 hpi1
  have h2 := halg.2
  convert h2 using 2
  all_goals first
    | exact hi
    | (rw [hwsk]; rfl)
    | (rw [hqsk]; rfl)

/-! ## π2's completeness -/

/-- **π2's completeness error**: the copy argument's `(2^25 + 36) |E|²` bad triples (`2N`, π2v3), `t`'s `9 · 2^24`
bad points (`9N`), `N` block calls, `t`'s cache hit `εt`, the proofs of work `εpow`. -/
noncomputable def delta2 (N : ℕ) (εt εpow : ℝ≥0∞) : ℝ≥0∞ := deltaStaged (2 ^ 25 + 36) (9 * 2 ^ 24) N εt εpow

/-! ## The algebra's counts at π2's numbers -/

set_option exponentiation.threshold 1024 in
open Classical in
/-- **The copy argument's bad triples at π2's circuit** (`lean-pi2-alg`'s `card_badCopy_le` at `N = 2^24`): at most
`(2^25 + 36) |E|²`, `Holds.badCard`'s `M`. -/
theorem card_badCopy_pi2 {D : RecDeployment} {C : Pi2Circuits D} (Fa : Pi2Facts D C) (roots : RecSetupRoots)
    (w : ℕ → K) (pub : ℕ → List E) :
    (Finset.univ.filter fun v : E × E × E ↦ BadCopy (C.G roots) w pub v.1 v.2.1 v.2.2).card ≤
      (2 ^ 25 + 36) * 2 ^ 384 := by
  refine (card_badCopy_le _ w pub).trans ?_
  rw [RecPiop.Circuit.N, logN_G Fa roots, LeanVM.Protocol.card_E]
  calc 2 * 2 ^ 24 * (2 ^ 192) ^ 2 = 2 ^ 25 * 2 ^ 384 := by ring
    _ ≤ (2 ^ 25 + 36) * 2 ^ 384 := Nat.mul_le_mul_right _ (by omega)

open Classical in
/-- **`t`'s bad points at π2's circuit** (`card_badT_le` at `N = 2^24`): for a witness, off `BadCopy`, at most
`9 · 2^24`, `Holds.badTCard`'s `ct`, for `badT` the event `Satisfies ∧ ¬ BadCopy ∧ BadT`. -/
theorem card_badT_pi2 {D : RecDeployment} {C : Pi2Circuits D} (Fa : Pi2Facts D C) (roots : RecSetupRoots)
    (w : ℕ → K) (pub : ℕ → List E) (α β γ : E) (hnh : ∃ i < (C.G roots).N, ¬ (C.G roots).IsHole i) :
    ∃ T : Finset E, T.card ≤ 9 * 2 ^ 24 ∧
      ∀ t, ((C.G roots).Satisfies pub (RecCircuit.emb w) ∧ ¬ BadCopy (C.G roots) w pub α β γ ∧
        BadT (C.G roots) w α β γ t) → t ∈ T := by
  by_cases hw : (C.G roots).Satisfies pub (RecCircuit.emb w)
  · by_cases hbad : BadCopy (C.G roots) w pub α β γ
    · exact ⟨∅, by simp, fun t ht ↦ absurd hbad ht.2.1⟩
    · refine ⟨_, (card_badT_le _ (Fa.valid roots) (kCircuit_toPiop _) (by rw [logN_G Fa roots]; omega) w pub hw
        α β γ hbad hnh).trans (by rw [RecPiop.Circuit.N, logN_G Fa roots]), fun t ht ↦ ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht.2.2⟩
  · exact ⟨∅, by simp, fun t ht ↦ absurd ht.1 hw⟩

/-- **Named input: π2's completeness experiment in the two-call model** (`Pi2Staged.Holds` at `α`'s input of `608`
bytes, the copy argument's bad triples `(2^25 + 36) |E|²`, `t`'s `9 · 2^24` per prior, `N` block calls, `εt`, `εpow`), for
every honest statement: the code-level bridge. Its `rejectGood` is `pi2_accepts` (proved) with the proofs of work's
grinding; its `badCard`, `badTCard` the algebra's counts (`lean-pi2-alg`: `card_badCopy_le`, `card_badT_le`); the rest
(the experiment as the staged two-call run with P1, the graph's check, `pi2Prover` and the contract; its duplex shape;
its cost; nothing of length `32` or `608` hashed before `α`; `t`'s input fresh) the commutation, duplex and cost lemmas
of the composed code, as UniComplete proves them for π1 (`ProverSim`, `ProverDuplex`, `ProverCost`, `ProbTFresh`). -/
def Pi2StagedFacts (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) (P1 : Pi1Prover D) (fuel N : ℕ)
    (εt εpow : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q →
      ∃ (S : Pi2Staged) (Bad : S.ρ → Finset (E × E × E)) (badT : S.τ → E → Prop),
        S.Holds D P1 (pi2Prover D C Fa fuel) input rows q 608 Bad badT (2 ^ 25 + 36) (9 * 2 ^ 24) N εt εpow

/-- **π2's completeness**: `RecCompleteness2 D P1 (pi2Prover D C Fa fuel) (delta2 N εt εpow)`. -/
theorem recCompleteness2_pi2 {D : RecDeployment} {C : Pi2Circuits D} {Fa : Pi2Facts D C} {P1 : Pi1Prover D}
    {fuel N : ℕ} {εt εpow : ℝ≥0∞} (h : Pi2StagedFacts D C Fa P1 fuel N εt εpow) :
    RecCompleteness2 D P1 (pi2Prover D C Fa fuel) (delta2 N εt εpow) :=
  recCompleteness2_of_staged h

/-- **`δ2` in bits**: below `2^-164` for at most `2^50` block calls, `εt ≤ 2^-200` and `εpow ≤ 2^-300` (the copy
argument's `2^-166`, `t`'s `9 · 2^-168`, the rest below `2^-170` each). -/
theorem delta2_le {N : ℕ} {εt εpow : ℝ≥0∞} (hN : N ≤ 2 ^ 50) (ht : εt ≤ (2 : ℝ≥0∞)⁻¹ ^ 200)
    (hp : εpow ≤ (2 : ℝ≥0∞)⁻¹ ^ 300) : delta2 N εt εpow ≤ (2 : ℝ≥0∞)⁻¹ ^ 164 := by
  set x : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ 170 with hx
  have hsmall : ∀ k, 170 ≤ k → (2 : ℝ≥0∞)⁻¹ ^ k ≤ x := fun k hk ↦ E2ECompleteness.inv_pow_le_inv_pow hk
  have ha : (1 : ℝ≥0∞) / 2 ^ 256 ≤ x := by
    rw [ENNReal.div_eq_inv_mul, mul_one, ENNReal.inv_pow]
    exact hsmall 256 (by norm_num)
  have hb : ((2 ^ 25 + 36 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ 2 ^ 4 * x := by
    calc ((2 ^ 25 + 36 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ 2 ^ 26 * (2 : ℝ≥0∞)⁻¹ ^ (166 + 26) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          gcongr
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 166 := E2ECompleteness.two_pow_mul_inv_pow 26 166
      _ = 2 ^ 4 * x := (E2ECompleteness.two_pow_mul_inv_pow 4 166).symm
  have hc : ((9 * 2 ^ 24 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ 36 * x := by
    refine le_of_eq ?_
    calc ((9 * 2 ^ 24 : ℕ) : ℝ≥0∞) / 2 ^ 192 = 9 * (2 ^ 24 * (2 : ℝ≥0∞)⁻¹ ^ (168 + 24)) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow]
          push_cast
          ring
      _ = 9 * (2 : ℝ≥0∞)⁻¹ ^ 168 := by rw [E2ECompleteness.two_pow_mul_inv_pow 24 168]
      _ = 9 * (2 ^ 2 * x) := by rw [hx, E2ECompleteness.two_pow_mul_inv_pow 2 168]
      _ = 36 * x := by ring
  have hd : εt ≤ x := ht.trans (hsmall 200 (by norm_num))
  have he : εpow ≤ x := hp.trans (hsmall 300 (by norm_num))
  have hf : rpmError N ≤ x := by
    calc rpmError N ≤ rpmError (2 ^ 50) := by
          unfold rpmError
          gcongr
      _ = 2 ^ (50 * 2) * (2 : ℝ≥0∞)⁻¹ ^ (408 + 50 * 2) := by
          rw [rpmError, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
      _ = (2 : ℝ≥0∞)⁻¹ ^ 408 := E2ECompleteness.two_pow_mul_inv_pow _ 408
      _ ≤ x := hsmall 408 (by norm_num)
  unfold delta2 deltaStaged
  calc _ ≤ (x + 2 ^ 4 * x) + (x + 36 * x) + x + x :=
        add_le_add (add_le_add (add_le_add (add_le_add ha hb) (add_le_add hd hc)) he) hf
    _ = 56 * x := by ring
    _ ≤ 2 ^ 6 * x := by gcongr; norm_num
    _ = (2 : ℝ≥0∞)⁻¹ ^ 164 := by rw [hx]; exact E2ECompleteness.two_pow_mul_inv_pow 6 164

/-- **The recursive verifier's completeness end to end, with π2's honest prover**: for π1-rec3's prover `P1`, under π2's
staged facts (named), π1-rec3's completeness at Keccak-f[1600] and its honest proofs' hazard (the Fiat–Shamir heuristic,
named), the composed prover's proof is rejected with probability at most `δ1 + δh + delta2 N εt εpow`. -/
theorem recCompleteness_pi2_fs (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1 : Pi1Prover D) (fuel N : ℕ) (εt εpow : ℝ≥0∞) (h2 : Pi2StagedFacts D C Fa P1 fuel N εt εpow) (δ1 δh : ℝ≥0∞)
    (h1 : Pi1CompletenessKeccak D P1 δ1) (hh : Pi1HazardKeccakHonest D P1 δh) :
    RecCompletenessWith D (composeProver D P1 (pi2Prover D C Fa fuel)) (δ1 + δh + delta2 N εt εpow) :=
  recCompleteness_end_fs D hD P1 (pi2Prover D C Fa fuel) _ (recCompleteness2_pi2 h2) δ1 δh h1 hh

end RecCompose.Pi2E

/-- info: 'RecCompose.Pi2E.pi2_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2E.pi2_accepts

/-- info: 'RecCompose.Pi2E.recCompleteness2_pi2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2E.recCompleteness2_pi2

/-- info: 'RecCompose.Pi2E.card_badCopy_pi2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2E.card_badCopy_pi2

/-- info: 'RecCompose.Pi2E.card_badT_pi2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2E.card_badT_pi2

/-- info: 'RecCompose.Pi2E.delta2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2E.delta2_le

/-- info: 'RecCompose.Pi2E.recCompleteness_pi2_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2E.recCompleteness_pi2_fs
