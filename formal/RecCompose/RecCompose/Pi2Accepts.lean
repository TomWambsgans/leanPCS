-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π2's honest prover is `crates/leanvm/rec/src/pi2/prover.rs`'s
-- (`RecCompose.Pi2Prover`); the statements are `formal/RecStatement`'s.
import RecCompose.Pi2ProverRec
import RecCompose.Pi2HonestThm
import RecCompose.Real

/-!
# π2's honest proof is accepted, at a pure permutation (π2v4)

* **`stackClaims_of_pi2Claims`**: `Pi2ClaimsHold` (`mleStk`, the tables' layer) on stacks of `2^24` and `2^28` words is
  `StackClaimsHold` (`stackEval`, what the PCS openings evaluate), the setup's on its table padded to `2^25` words.
* **`pi2_accepts`**: at the real deployment, a pure permutation `F` (Keccak-256 `Hk`), for the witness π2's prover takes
  (an honest one, `hgood`: the values match the reads, the frame words the declared claims' Keccak-256s), if the prover
  returns a proof, the challenges it drew are off `BadCopy`, `BadT` and `BadRho`, π1's claims as the graph makes them
  are three (`hp3`) and their openings with π1's opening proofs accept (`hpi1`), then the contract accepts: π2's algebra
  holds (`pi2_honest`) and `Pi2Complete.contract_accepts` applies.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2E

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open Pi2S Pi2K

theorem setupStack_size (c : Pi2Circuit) : c.setupStack.size = 2 ^ (c.circuit.logN + 1) := by
  rw [size_setupStack, pow_succ]
  ring

/-- **π2's claims on the stacks, as the PCS openings evaluate them**: `Pi2ClaimsHold` (`mleStk`) on stacks of `2^24`
and `2^28` words is `StackClaimsHold` (`stackEval`), the setup's on its table padded to `2^25` words. -/
theorem stackClaims_of_pi2Claims (D : RecDeployment) (roots : RecSetupRoots) (inp : Inputs E) (wStack qStack : Array K)
    (hview : (D.circuitAt roots.pi1).circuit = Data.circuit)
    (hw : wStack.size = 2 ^ 24) (hq : qStack.size = 2 ^ 28)
    (h : Pi2ClaimsHold D roots inp (fun j ↦ wStack.getD j 0) (fun j ↦ qStack.getD j 0)) :
    StackClaimsHold ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp) inp.ξ wStack qStack
      (padStack 25 fun i ↦ (D.circuitAt roots.pi1).setupStack.getD i 0) := by
  have hlogN : (D.circuitAt roots.pi1).circuit.logN = 24 := by rw [hview]; rfl
  obtain ⟨lW, lS, lQ, lP⟩ := run_points_length (Spec.of (D.circuitAt roots.pi1).circuit).core
    (by rw [hview]; rfl) (by rw [hview]; rfl) inp
  unfold Pi2ClaimsHold ClaimOn at h
  simp only [hlogN, Pi2W.stackVars_24] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Pi2W.stackEval_eq_mleStk _ _ (by rw [hw, lW]), lW]; exact h1
  · rw [Pi2W.stackEval_eq_mleStk _ _ (by rw [hq, lQ]), lQ]; exact h2
  · rw [Pi2W.stackEval_eq_mleStk _ _ (by rw [hq, lP]), lP]; exact h3
  · rw [Pi2W.stackEval_eq_mleStk _ _ (by rw [Pi2W.padStack_size, lS]), lS]
    rw [Pi2W.mleStk_congr (c' := fun j ↦ (D.circuitAt roots.pi1).setupStack.getD j 0)
      (fun j hj ↦ by simp only [padStack_getD, hj, ↓reduceIte])]
    exact h4

/-- **π2's honest proof is accepted** at a pure permutation `F` (Keccak-256 `Hk`), at the real deployment: for the
witness the prover takes (an honest one, `hgood`), if the prover returns a proof, its challenges are off `BadCopy`,
`BadT` (`t`) and `BadRho` (`ρ`), π1's claims as the graph makes them are three (`hp3`) and their openings with π1's
proofs accept (`hpi1`), the contract accepts. -/
theorem pi2_accepts (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (F : KeccakState → Id KeccakState) (Hk : List UInt8 → Digest)
    (fuel : ℕ) (input : Vector UInt8 32) (p1 : UniKeccak.KeccakProof)
    (hgood : let trees := Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)
      let claims := pi1ClaimsOf D trees.roots.pi1 input p1.stream
      Pi2Good D C.G Fa.pubOf trees.roots input p1.stream claims
        (pi2Choice D C.G Fa.pubOf trees.roots input p1.stream claims))
    (hp3 : (pi1ClaimsOf D (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots.pi1 input
      p1.stream).length = 3)
    (hGN : (C.G (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots).logN = 24)
    (hrow : Data.circuit.logRow = (C.G (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots).logW)
    (proof : RecProof)
    (hp : Id.run (pi2ProverWith (m := Id) (Pure.pure ∘ Hk) F D C.G Fa.pubOf fuel input p1) = some proof)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt)
    (hbad : let trees := Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)
      let claims := pi1ClaimsOf D trees.roots.pi1 input p1.stream
      let vw := pi2Choice D C.G Fa.pubOf trees.roots input p1.stream claims
      let out := outOf D Hk trees.roots (C.G trees.roots) (pi2Z Hk) input vw.1 vw.2
      ¬ BadCopy (C.G trees.roots) vw.2 (Fa.pubOf trees.roots (publicScalarsOf input.toList vw.1))
        out.inputs.α out.inputs.β out.inputs.γ)
    (ht : let trees := Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)
      let claims := pi1ClaimsOf D trees.roots.pi1 input p1.stream
      let vw := pi2Choice D C.G Fa.pubOf trees.roots input p1.stream claims
      let out := outOf D Hk trees.roots (C.G trees.roots) (pi2Z Hk) input vw.1 vw.2
      ¬ BadT (C.G trees.roots) vw.2 out.inputs.α out.inputs.β out.inputs.γ out.inputs.t)
    (hρ : let trees := Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)
      let claims := pi1ClaimsOf D trees.roots.pi1 input p1.stream
      let vw := pi2Choice D C.G Fa.pubOf trees.roots input p1.stream claims
      let out := outOf D Hk trees.roots (C.G trees.roots) (pi2Z Hk) input vw.1 vw.2
      ¬ BadRho (C.G trees.roots) out.inputs.t out.inputs.ρ)
    (hpi1 : Id.run (Pi2H.pcsOpenWordsH (m := Id) (Pure.pure ∘ Hk) F ((pi1ClaimsOf D (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots.pi1 input p1.stream).getD 0 []) p1.c1) = true ∧
      Id.run (Pi2H.pcsOpenWordsH (m := Id) (Pure.pure ∘ Hk) F ((pi1ClaimsOf D (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots.pi1 input p1.stream).getD 1 []) p1.c2) = true ∧
      Id.run (Pi2H.pcsOpenWordsH (m := Id) (Pure.pure ∘ Hk) F ((pi1ClaimsOf D (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots.pi1 input p1.stream).getD 2 []) p1.setup) = true) :
    (Id.run (Pi2H.contractWithH (m := Id) (Pure.pure ∘ Hk) F D
      (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input proof)).1 = true := by
  simp only at hgood hbad ht hρ
  -- the prover's run
  have hres := hp
  rw [pi2ProverWith_run] at hres
  simp only at hres
  rw [pi2ProveWith_run] at hres
  simp only at hres
  rw [hGN, Pi2W.stackVars_24] at hres
  simp only at hres
  set trees := Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D) with htrees
  set claims := pi1ClaimsOf D trees.roots.pi1 input p1.stream with hclaims
  set vw := pi2Choice D C.G Fa.pubOf trees.roots input p1.stream claims with hvw
  have hview : (D.circuitAt trees.roots.pi1).circuit = Data.circuit := hD.1 _
  have hlogN : (D.circuitAt trees.roots.pi1).circuit.logN = 24 := by rw [hview]; rfl
  obtain ⟨hmatch, hwS, -⟩ := hgood
  have hmatch' := hmatch
  rw [hview] at hmatch
  -- the algebra (`pi2_honest`), at the prover's inputs and stacks
  obtain ⟨-, -, -, -, -, -, -, -, -, hi, hwsk, hqsk⟩ := runWith_honest Hk (C.G trees.roots) (pi2Z Hk)
    (D.circuitAt trees.roots.pi1).circuit (D.circuitAt trees.roots.pi1).setupStack (ivOf D Hk trees.roots)
    input.toList vw.1 vw.2 (frameOf claims) hmatch' (by rw [hview]; exact hrow)
  have halg := pi2_honest Fa (pi2SetupColumns_of_real hD C hroots) trees.roots vw.2
    (publicScalarsOf input.toList vw.1) _ _ _ _
    (outOf D Hk trees.roots (C.G trees.roots) (pi2Z Hk) input vw.1 vw.2).inputs.ρ hwS hbad ht hρ
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
  rcases rW with _ | pW
  · simp at hres
  rcases rS with _ | pS
  · simp at hres
  rcases rQ1 with _ | pQ1
  · simp at hres
  rcases rQ2 with _ | pQ2
  · simp at hres
  simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hres
  subst hres
  have hwsz : (outOf D Hk trees.roots (C.G trees.roots) (pi2Z Hk) input vw.1 vw.2).wStack.size = 2 ^ 24 := by
    rw [hwsk, hGN]; exact Pi2W.padStack_size _ _
  have hqsz : (outOf D Hk trees.roots (C.G trees.roots) (pi2Z Hk) input vw.1 vw.2).qStack.size = 2 ^ 28 := by
    rw [hqsk, hGN]; exact Pi2W.padStack_size _ _
  refine contract_accepts D F Hk trees.roots (C.G trees.roots) hview hGN hrow (by rw [hD.2.1]; rfl) sS
    (Pi2W.padStack_size _ _) hroot2 hood2 input vw.1 vw.2 claims hp3 hmatch fuel p1.c1 p1.c2 p1.setup pW pS pQ1 pQ2
    ⟨by rw [hi]; exact halg.1, stackClaims_of_pi2Claims D trees.roots _ _ _ hview hwsz hqsz ?_⟩
    hW (by rw [← htree]; exact hS) hQ1 hQ2 hpi1
  have h2 := halg.2
  convert h2 using 2
  all_goals first
    | exact hi
    | (rw [hwsk]; rfl)
    | (rw [hqsk]; rfl)

end RecCompose.Pi2E

/-- info: 'RecCompose.Pi2E.pi2_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2E.pi2_accepts
