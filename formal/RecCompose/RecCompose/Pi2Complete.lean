-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The contract is `formal/RecStatement`'s
-- (`Security.lean`: `contractWith`, `pcsOpenAt`, `pi1OpsOf`); π2's honest prover `RecCompose.Pi2Prover`'s; the joint
-- run `Pi2CompleteSync`'s, the calls' decodings `Pi2CompleteCalls`', the honest openings `Pi2Whir`'s.
import RecCompose.Pi2CompleteSync
import RecCompose.Pi2CompleteCalls
import RecCompose.Couplings
import RecCompose.CallsPure
import RecCompose.Pi2Whir

/-!
# The contract accepts π2's honest proof off the bad challenges

**`contract_accepts`** (the core of π2's completeness, at one permutation): over a pure permutation `F` (Keccak-256 the
sponge over it, `Hk`), at the deployment's circuit (`Data.circuit`: its three reads the frame's payloads `0, 1, 2`, no
π1 claim encoded, `D.pi1Calls = []`), the contract (`RecDeployment.contractWith`) accepts the proof whose stream π2's
honest prover writes (`proverOut`, at the contract's IV, the frame words its values' words), whose declared π1 claims
`pi1Claims` (three) are those the values' frame words hash (`ReadMatch (frameOf pi1Claims)`), and whose seven openings
are π1's three and the honest prover's four, when

* π2's arithmetic on the prover's inputs passes (`all ≠ 0`) and its four claims hold on the prover's stacks
  (`StackClaimsHold`: each value the stack's multilinear extension at its point): the algebra, off the bad challenges;
* the four PCS openings exist (no proof of work failed);
* the three declared π1 claims are accepted with π1's opening proofs (`pcsOpenWordsH`).

The steps: π2's verifier reads the prover's stream back, its frame words the declared claims' Keccak-256s
(`runWith_honest`), so its arithmetic is the prover's and its check passes; no claim is encoded, the declared ones are
three (`encodedDeclared`), so the claims are seven; `W`'s, the setup's and `Q`'s two decode (`claimOfWords_claim`) to
the roots the prover committed (the stream's root bytes, `rootOfWord_rootWord_rootHalves`; the setup's the
deployment's), their out-of-domain answers (the stream's, `runWith_honest`; the setup's the deployment's) and the
prover's claims, and the PCS check accepts the honest openings of true claims (`W`'s and `Q`'s by the oracle-point
check `pcsOpenKOH`, at `Hk`'s point `pi2Z Hk` where the prover answered and opened, `proverOut_points`,
`pi2PcsOpenO_honest`; the setup's at the deployed point, `pi2PcsOpen_honest`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2K

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open Pi2S Pi2C

/-! ## The stream's offsets -/

theorem foldl_rootsAt (reads : List Read) : ∀ acc : List ℕ × ℕ,
    (reads.foldl (fun (acc : List ℕ × ℕ) rd ↦ (if rd = .root then acc.1 ++ [acc.2] else acc.1, acc.2 + rd.bytes))
        acc).1.length = acc.1.length + (reads.filter (· = .root)).length ∧
      (reads.foldl (fun (acc : List ℕ × ℕ) rd ↦ (if rd = .root then acc.1 ++ [acc.2] else acc.1, acc.2 + rd.bytes))
        acc).2 = acc.2 + (reads.map Read.bytes).sum := by
  induction reads with
  | nil => intro acc; simp
  | cons rd rs ih =>
    intro acc
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih _
    refine ⟨?_, ?_⟩
    · rw [h1]
      by_cases hr : rd = .root
      · simp [hr]; omega
      · simp [hr]
    · rw [h2]; simp; omega

/-- **`W`'s and `Q`'s roots' offsets**: after the public data. -/
theorem rootsAt_offsets (reads : List Read) :
    (rootsAt reads).getD (rootReads reads) 0 = (reads.map Read.bytes).sum ∧
      (rootsAt reads).getD (rootReads reads + 1) 0 = (reads.map Read.bytes).sum + 56 := by
  obtain ⟨h1, h2⟩ := foldl_rootsAt reads ([], 0)
  unfold rootsAt rootReads
  simp only at h1 h2 ⊢
  rw [List.length_nil, zero_add] at h1
  rw [zero_add] at h2
  constructor
  · rw [← h1, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, h2]; rfl
  · rw [← h1, List.getD_append_right _ _ _ _ (by omega), show _ + 1 - _ = 1 by omega, h2]; rfl

theorem publicWire_length (frameAt : ℕ → List UInt8) : ∀ (reads : List Read) (values : List PublicValue),
    List.Forall₂ (ReadMatch frameAt) reads values →
    (publicWire (reads.zip values)).length = (reads.map Read.bytes).sum
  | [], [], .nil => rfl
  | .root :: rs, .root b :: vs, .cons _ h => by
    have := publicWire_length frameAt rs vs h
    simp only [publicWire, List.zip_cons_cons, List.flatMap_cons, List.length_append, List.map_cons,
      List.sum_cons] at this ⊢
    rw [this]
    simp [publicBytes, Read.bytes]
  | .scalar :: rs, .scalar x :: vs, .cons _ h => by
    have := publicWire_length frameAt rs vs h
    simp only [publicWire, List.zip_cons_cons, List.flatMap_cons, List.length_append, List.map_cons,
      List.sum_cons] at this ⊢
    rw [this]
    simp [publicBytes, Read.bytes]
  | .frame p :: rs, .word b :: vs, .cons _ h => by
    have := publicWire_length frameAt rs vs h
    simp only [publicWire, List.zip_cons_cons, List.flatMap_cons, List.length_append, List.map_cons,
      List.sum_cons] at this ⊢
    rw [this]
    simp [publicBytes, Read.bytes]
  | .integer _ :: _, _ :: _, .cons hm _ => by cases hm
  | .narrow :: _, _ :: _, .cons hm _ => by cases hm
  | .root :: _, .integer _ :: _, .cons hm _ => by cases hm
  | .root :: _, .scalar _ :: _, .cons hm _ => by cases hm
  | .root :: _, .word _ :: _, .cons hm _ => by cases hm
  | .scalar :: _, .integer _ :: _, .cons hm _ => by cases hm
  | .scalar :: _, .root _ :: _, .cons hm _ => by cases hm
  | .scalar :: _, .word _ :: _, .cons hm _ => by cases hm
  | .frame _ :: _, .integer _ :: _, .cons hm _ => by cases hm
  | .frame _ :: _, .root _ :: _, .cons hm _ => by cases hm
  | .frame _ :: _, .scalar _ :: _, .cons hm _ => by cases hm

/-! ## The arithmetic's points -/

theorem run_points_length (S : CoreSpec E) (hN : S.logN = 24) (hR : S.logRow = 4) (inp : Inputs E) :
    (S.run inp).witnessPoint.length = 24 ∧ (S.run inp).setupPoint.length = 25 ∧
      (S.run inp).quotientPoint.length = 28 ∧ (S.run inp).pushesPoint.length = 28 := by
  simp [CoreSpec.run, digitsList, hN, hR, padded, stackVars]

/-! ## Loops -/

theorem forIn_and_true {γ : Type} (f : γ → Bool → Id (ForInStep Bool)) (g : γ → Bool)
    (hf : ∀ x b, f x b = pure (ForInStep.yield (b && g x))) :
    ∀ (l : List γ) (b : Bool), (∀ x ∈ l, g x = true) → Id.run (forIn l b f) = b
  | [], b, _ => rfl
  | x :: l, b, h => by
    rw [List.forIn_cons, hf, pure_bind, h x List.mem_cons_self, Bool.and_true]
    exact forIn_and_true f g hf l b fun y hy ↦ h y (List.mem_cons_of_mem _ hy)

/-- A postcondition of a computation in `Id` from its value. -/
theorem holds_id_of {α : Type} {X : Id α} {P : α → Prop} (h : P X.run) : Holds X P := by
  unfold Holds
  show ((X.run, P X.run) : α × Prop) = (X.run, True)
  rw [eq_true h]

/-! ## The core -/

theorem list3_eq_getD {α : Type} (l : List α) (h : l.length = 3) (d : α) : l = [l.getD 0 d, l.getD 1 d, l.getD 2 d] := by
  match l, h with
  | [_, _, _], _ => rfl

/-- The contract's IV at a pure permutation. -/
abbrev ivOf (D : RecDeployment) (Hk : List UInt8 → Digest) (roots : RecSetupRoots) : List UInt8 :=
  Id.run (Pi2H.ivOfH (m := Id) (Pure.pure ∘ Hk) D roots)

/-- **π2's honest prover's output** at the setup's commitments, the contract's IV. -/
abbrev outOf (D : RecDeployment) (Hk : List UInt8 → Digest) (roots : RecSetupRoots)
    (G : RecPiop.Circuit E) (zf : ℕ → Digest → List E) (input : Vector UInt8 32) (values : List PublicValue)
    (w : ℕ → K) : Pi2Out :=
  proverOut Hk G zf (D.circuitAt roots.pi1).circuit (D.circuitAt roots.pi1).setupStack (ivOf D Hk roots) input.toList
    values w

/-- **π2's four claims hold on the stacks** (each claim's value the stack's multilinear extension at its point,
`stackEval`): `W`'s, `Q`'s identity and pushes' claims, the setup's. -/
def StackClaimsHold (o : Out E) (ξ : E) (wStack qStack sStack : Array K) : Prop :=
  UniComplete.stackEval wStack o.witnessPoint = o.fold ∧
    UniComplete.stackEval qStack o.quotientPoint = o.quotientValue ∧
    UniComplete.stackEval qStack o.pushesPoint = o.pushesValue ∧
    UniComplete.stackEval sStack o.setupPoint = ξ

/-- **The honest PCS opening of a claim on `W` or `Q` is accepted** by the oracle-point check (`pcsOpenKOH`, the
point read off `Hk`): the proof `pcsProveZH` makes at the point `pi2Z Hk n root` (pure `Hk`, `F`; `23 ≤ n ≤ 28`, a
stack of `2^n` words). -/
theorem pi2PcsOpenO_honest (Hk : List UInt8 → Digest) (F : KeccakState → KeccakState) (fuel : ℕ) {n : ℕ}
    (h1 : 23 ≤ n) (h2 : n ≤ 28) (stack : Array K) (hs : stack.size = 2 ^ n) (pt : List E) (hpt : pt.length = n)
    {π : Compile.Proof}
    (hπ : PcsZ.pcsProveZH (m := Id) Hk F fuel n (pi2Z Hk n (E2ECompleteness.commitWithH (m := Id) Hk n stack).root)
      (E2ECompleteness.commitWithH (m := Id) Hk n stack) stack pt (UniComplete.stackEval stack pt) = some π) :
    Pi2H.pcsOpenKOH (m := Id) (Pure.pure ∘ Hk) (fun s ↦ pure (F s)) n
      (E2ECompleteness.commitWithH (m := Id) Hk n stack).root
      (pi2OodAt stack (pi2Z Hk n (E2ECompleteness.commitWithH (m := Id) Hk n stack).root)) pt
      (UniComplete.stackEval stack pt) π = true := by
  rw [Pi2H.pcsOpenKOH_id Hk _ n _ _ _ _ _ hpt]
  exact PcsZ.pcsVerify_pcsProveZH Hk F fuel h1 h2 (WhirBridge.Pcs.oodPointWith Hk n) stack hs pt hpt hπ

/-- `frameReads` of the deployment's reads: the frame's payloads `0, 1, 2`. -/
theorem frameReads_data : frameReads Data.circuit.reads = [0, 1, 2] := rfl

/-- **No claim encoded, three declared**: the contract's check of the declared π1 claims passes on three. -/
theorem encodedDeclared_data (declared : List (List (List UInt8))) (h : declared.length = 3) :
    encodedDeclared Data.circuit [] declared = true := by
  unfold encodedDeclared
  rw [frameReads_data, h]
  simp

/-- **The contract accepts π2's honest proof**, at a pure permutation, off the bad challenges and proofs of work, the
declared π1 claims accepted: at the deployment's circuit (three frame reads, no π1 claim encoded), the setup's
commitment that of its stack `sStack` (`2^25` words), the values' frame words the declared claims' Keccak-256s, the
four PCS openings the honest prover's (`pcsProveZH`: `W`'s and `Q`'s at the points `pi2Z Hk` the contract reads off
`Hk`, the setup's at the deployed point) of true claims. -/
theorem contract_accepts (D : RecDeployment) (F : KeccakState → Id KeccakState) (Hk : List UInt8 → Digest)
    (roots : RecSetupRoots) (G : RecPiop.Circuit E)
    (hview : (D.circuitAt roots.pi1).circuit = Data.circuit) (hGN : G.logN = 24) (hrow : Data.circuit.logRow = G.logW)
    (hcalls0 : D.pi1Calls = []) (sStack : Array K) (hsS : sStack.size = 2 ^ 25)
    (hroot2 : roots.pi2 = (E2ECompleteness.commitWithH (m := Id) (Pure.pure ∘ Hk) 25 sStack).root)
    (hood2 : roots.pi2Ood = UniKeccakComplete.pcsOod 25 sStack roots.pi2)
    (input : Vector UInt8 32) (values : List PublicValue) (w : ℕ → K)
    (pi1Claims : List (List (List UInt8))) (hp3 : pi1Claims.length = 3)
    (hmatch : List.Forall₂ (ReadMatch (frameOf pi1Claims)) Data.circuit.reads values) (fuel : ℕ)
    (c1 c2 cf pW pS pQ1 pQ2 : Compile.Proof)
    (halg : ((Spec.of (D.circuitAt roots.pi1).circuit).core.run
        (outOf D Hk roots G (pi2Z Hk) input values w).inputs).all ≠ 0 ∧
      StackClaimsHold ((Spec.of (D.circuitAt roots.pi1).circuit).core.run
          (outOf D Hk roots G (pi2Z Hk) input values w).inputs)
        (outOf D Hk roots G (pi2Z Hk) input values w).inputs.ξ
        (outOf D Hk roots G (pi2Z Hk) input values w).wStack
        (outOf D Hk roots G (pi2Z Hk) input values w).qStack sStack)
    (hW : let out := outOf D Hk roots G (pi2Z Hk) input values w
      let o := (Spec.of (D.circuitAt roots.pi1).circuit).core.run out.inputs
      PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel 24 out.wPoint out.wTree out.wStack o.witnessPoint o.fold =
        some pW)
    (hS : let out := outOf D Hk roots G (pi2Z Hk) input values w
      let o := (Spec.of (D.circuitAt roots.pi1).circuit).core.run out.inputs
      PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel 25
        (UniKeccakComplete.pcsZ 25 (E2ECompleteness.commitWithH (m := Id) (Pure.pure ∘ Hk) 25 sStack).root)
        (E2ECompleteness.commitWithH (m := Id) (Pure.pure ∘ Hk) 25 sStack) sStack o.setupPoint out.inputs.ξ = some pS)
    (hQ1 : let out := outOf D Hk roots G (pi2Z Hk) input values w
      let o := (Spec.of (D.circuitAt roots.pi1).circuit).core.run out.inputs
      PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel 28 out.qPoint out.qTree out.qStack o.quotientPoint
        o.quotientValue = some pQ1)
    (hQ2 : let out := outOf D Hk roots G (pi2Z Hk) input values w
      let o := (Spec.of (D.circuitAt roots.pi1).circuit).core.run out.inputs
      PcsZ.pcsProveZH (m := Id) (Pure.pure ∘ Hk) F fuel 28 out.qPoint out.qTree out.qStack o.pushesPoint
        o.pushesValue = some pQ2)
    (hpi1 : Id.run (Pi2H.pcsOpenWordsH (m := Id) (Pure.pure ∘ Hk) F (pi1Claims.getD 0 []) c1) = true ∧
      Id.run (Pi2H.pcsOpenWordsH (m := Id) (Pure.pure ∘ Hk) F (pi1Claims.getD 1 []) c2) = true ∧
      Id.run (Pi2H.pcsOpenWordsH (m := Id) (Pure.pure ∘ Hk) F (pi1Claims.getD 2 []) cf) = true) :
    (Id.run (Pi2H.contractWithH (m := Id) (Pure.pure ∘ Hk) F D roots input
      ⟨(outOf D Hk roots G (pi2Z Hk) input values w).stream, pi1Claims, c1, c2, cf, pW, pS, pQ1, pQ2⟩)).1 =
      true := by
  have hlogN : (D.circuitAt roots.pi1).circuit.logN = 24 := by rw [hview]; rfl
  obtain ⟨r, hr, hinp, -, hout, hoods, hstr, hwt, hqt, -, hwsk, hqsk⟩ := runWith_honest Hk G (pi2Z Hk)
    (D.circuitAt roots.pi1).circuit (D.circuitAt roots.pi1).setupStack (ivOf D Hk roots) input.toList values w
    (frameOf pi1Claims) (by rw [hview]; exact hmatch) (by rw [hview]; exact hrow)
  obtain ⟨hwp, hqp⟩ := proverOut_points Hk G (pi2Z Hk)
    (D.circuitAt roots.pi1).circuit (D.circuitAt roots.pi1).setupStack (ivOf D Hk roots) input.toList values w
    (frameOf pi1Claims) (by rw [hview]; exact hmatch) (by rw [hview]; exact hrow)
  simp only at hW hS hQ1 hQ2
  generalize hout_def : outOf D Hk roots G (pi2Z Hk) input values w = out at halg hW hS hQ1 hQ2 ⊢
  have hr' : (Pi2H.runWithH (m := Id) (Pure.pure ∘ Hk) (Spec.of (D.circuitAt roots.pi1).circuit) (ivOf D Hk roots)
      input.toList (frameOf pi1Claims) out.stream).result = .ok r := by rw [← hout_def]; exact hr
  have hinp' : r.inputs = out.inputs := by rw [← hout_def]; exact hinp
  have hv : stackVars G.logN = (24, 28, 25) := by rw [hGN]; rfl
  rw [hv] at hoods hwt hqt hwsk hqsk hstr hwp hqp
  have hoods' : r.oods = (pi2OodAt out.wStack (pi2Z Hk 24 out.wTree.root),
      pi2OodAt out.qStack (pi2Z Hk 28 out.qTree.root)) := by
    rw [← hout_def]; exact hoods
  have hwp' : out.wPoint = pi2Z Hk 24 out.wTree.root := by rw [← hout_def]; exact hwp
  have hqp' : out.qPoint = pi2Z Hk 28 out.qTree.root := by rw [← hout_def]; exact hqp
  have hstr' : out.stream.toList = publicWire ((D.circuitAt roots.pi1).circuit.reads.zip values) ++
      UniStatement.rootWord (UniStatement.rootHalves out.wTree.root) ++
      UniComplete.scalarWire (pi2OodAt out.wStack (pi2Z Hk 24 out.wTree.root)) ++
      UniStatement.rootWord (UniStatement.rootHalves out.qTree.root) ++
      UniComplete.scalarWire (pi2OodAt out.qStack (pi2Z Hk 28 out.qTree.root)) ++
      (out.inputs.a ++ [out.inputs.ξ, out.inputs.s]).flatMap UniComplete.scalarWire := by rw [← hout_def]; exact hstr
  have hwt' : out.wTree = E2ECompleteness.commitWithH (m := Id) (Pure.pure ∘ Hk) 24 out.wStack := by
    rw [← hout_def]; exact hwt
  have hqt' : out.qTree = E2ECompleteness.commitWithH (m := Id) (Pure.pure ∘ Hk) 28 out.qStack := by
    rw [← hout_def]; exact hqt
  have hwsz : out.wStack.size = 2 ^ 24 := by
    rw [← hout_def, hwsk]; exact Pi2W.padStack_size _ _
  have hqsz : out.qStack.size = 2 ^ 28 := by
    rw [← hout_def, hqsk]; exact Pi2W.padStack_size _ _
  clear hr hinp hstr hwt hqt hoods hwsk hqsk hwp hqp hout_def
  have hro : r.out = (Spec.of (D.circuitAt roots.pi1).circuit).core.run out.inputs := by rw [hout, hinp']
  -- the contract
  refine holds_id (P := fun x : Bool × List (List (List UInt8)) ↦ x.1 = true) ?_
  unfold Pi2H.contractWithH
  refine holds_bind (Q := fun iv ↦ iv = ivOf D Hk roots) (holds_id_of rfl) fun iv hiv ↦ ?_
  subst hiv
  refine holds_bind (Q := fun oc ↦ oc.result = .ok r) (holds_id_of hr') fun oc hoc ↦ ?_
  have hacc : oc.accepts = true := by
    unfold Outcome.accepts
    rw [hoc]
    show (r.out.all != 0) = true
    rw [hro]
    simpa using halg.1
  split
  · rename_i e he
    rw [hoc] at he
    cases he
  rename_i r' hr''
  rw [hoc] at hr''
  cases hr''
  simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hpl : pi1CallsWith D.pi1Calls roots.pi1 = [] := by simp [pi1CallsWith, hcalls0]
  rw [hpl, hcalls0, hview]
  simp only [List.length_nil, List.take_zero, List.drop_zero, encodedDeclared_data pi1Claims hp3, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  have hlen : (pi1Claims ++ pcsCalls Data.circuit [] (digestBytes roots.pi2) roots.pi2Ood out.stream r).length = 7 := by
    rw [List.length_append, pcsCalls_length, hp3]; rfl
  simp only [hlen, ne_eq, not_true_eq_false, ↓reduceIte]
  refine holds_bind (Q := fun ok ↦ ok = true) (holds_id_of ?_) fun ok hok ↦ holds_pure hok
  -- π2's four
  have hcr : (D.circuitAt roots.pi1).circuit.reads = Data.circuit.reads := by rw [hview]
  have hpw := publicWire_length (frameOf pi1Claims) _ _ hmatch
  obtain ⟨hoffW, hoffQ⟩ := rootsAt_offsets Data.circuit.reads
  have hrootW : streamWord out.stream ((rootsAt Data.circuit.reads).getD (rootReads Data.circuit.reads) 0) =
      UniStatement.rootWord (UniStatement.rootHalves out.wTree.root) := by
    rw [hoffW, ← hpw]
    refine streamWord_of out.stream _ _
      (UniComplete.scalarWire (pi2OodAt out.wStack (pi2Z Hk 24 out.wTree.root)) ++
      UniStatement.rootWord (UniStatement.rootHalves out.qTree.root) ++
      UniComplete.scalarWire (pi2OodAt out.qStack (pi2Z Hk 28 out.qTree.root)) ++
      (out.inputs.a ++ [out.inputs.ξ, out.inputs.s]).flatMap UniComplete.scalarWire) ?_ (length_rootWord _)
    rw [hstr', hcr]
    simp only [List.append_assoc]
  have hrootQ : streamWord out.stream ((rootsAt Data.circuit.reads).getD (rootReads Data.circuit.reads + 1) 0) =
      UniStatement.rootWord (UniStatement.rootHalves out.qTree.root) := by
    rw [hoffQ, ← hpw]
    have := streamWord_of out.stream (publicWire (Data.circuit.reads.zip values) ++
      UniStatement.rootWord (UniStatement.rootHalves out.wTree.root) ++
      UniComplete.scalarWire (pi2OodAt out.wStack (pi2Z Hk 24 out.wTree.root)))
      (UniStatement.rootWord (UniStatement.rootHalves out.qTree.root))
      (UniComplete.scalarWire (pi2OodAt out.qStack (pi2Z Hk 28 out.qTree.root)) ++
        (out.inputs.a ++ [out.inputs.ξ, out.inputs.s]).flatMap UniComplete.scalarWire)
      (by rw [hstr', hcr]; simp only [List.append_assoc]) (length_rootWord _)
    have hl : (publicWire (Data.circuit.reads.zip values) ++
        UniStatement.rootWord (UniStatement.rootHalves out.wTree.root) ++
        UniComplete.scalarWire (pi2OodAt out.wStack (pi2Z Hk 24 out.wTree.root))).length =
        (publicWire (Data.circuit.reads.zip values)).length + 56 := by
      simp only [List.length_append, length_rootWord, UniKeccakComplete.length_scalarWire]
    rwa [hl] at this
  obtain ⟨lW, lS, lQ, lP⟩ := run_points_length (Spec.of (D.circuitAt roots.pi1).circuit).core
    (by rw [hview]; rfl) (by rw [hview]; rfl) out.inputs
  obtain ⟨hcW, hcQ, hcP, hcS⟩ := halg.2
  have hdecW := claimOfWords_claim _ (length_rootWord (UniStatement.rootHalves out.wTree.root)) r.oods.1 r.witness
  have hdecS := claimOfWords_claim (digestBytes roots.pi2) (Pi1Decode.length_digestBytes _) roots.pi2Ood r.setup
  have hdecQ := claimOfWords_claim _ (length_rootWord (UniStatement.rootHalves out.qTree.root)) r.oods.2 r.quotient
  have hdecP := claimOfWords_claim _ (length_rootWord (UniStatement.rootHalves out.qTree.root)) r.oods.2 r.pushes
  -- the seven claims listed
  have h3 := list3_eq_getD pi1Claims hp3 []
  unfold pcsCalls
  simp only [hrootW, hrootQ, List.map_nil, List.nil_append]
  rw [h3]
  simp only [RecProof.openings, List.cons_append, List.nil_append, List.zip_cons_cons, List.zip_nil_left]
  refine forIn_and_true _
    (fun x ↦ Id.run (Pi2H.pcsOpenWordsH (m := Id) (Pure.pure ∘ Hk) F x.1 x.2))
    (fun x b ↦ by obtain ⟨_, _⟩ := x; rfl) _ true ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hpi1.1
  · exact hpi1.2.1
  · exact hpi1.2.2
  · -- `W`
    simp only [List.cons_append, List.nil_append] at hdecW ⊢
    rw [Pi2H.pcsOpenWordsH_eq (Pure.pure ∘ Hk) F _ _ _ hdecW]
    unfold Pi2H.openAtH
    simp only [rootOfWord_rootWord_rootHalves, hoods', Reduced.witness, hro, lW, show oodRead 24 = true from rfl,
      ↓reduceIte]
    rw [← hcW]
    have h := pi2PcsOpenO_honest Hk F fuel (n := 24) (by norm_num) (by norm_num) out.wStack hwsz
      _ lW (π := pW) (by rw [hwp', hwt', ← hcW] at hW; exact hW)
    rw [hwt']
    exact h
  · -- the setup
    simp only [List.cons_append, List.nil_append] at hdecS ⊢
    rw [Pi2H.pcsOpenWordsH_eq (Pure.pure ∘ Hk) F _ _ _ hdecS]
    unfold Pi2H.openAtH
    simp only [rootOfWord_digestBytes, Reduced.setup, hro, lS, hinp', show oodRead 25 = false from rfl,
      Bool.false_eq_true, ↓reduceIte]
    rw [← hcS, hood2, hroot2]
    exact Pi2W.pi2PcsOpen_honest Hk F fuel (n := 25) (by norm_num) (by norm_num) sStack hsS _ lS
      (by rw [← hcS] at hS; exact hS)
  · -- `Q`'s identity
    simp only [List.cons_append, List.nil_append] at hdecQ ⊢
    rw [Pi2H.pcsOpenWordsH_eq (Pure.pure ∘ Hk) F _ _ _ hdecQ]
    unfold Pi2H.openAtH
    simp only [rootOfWord_rootWord_rootHalves, hoods', Reduced.quotient, hro, lQ, show oodRead 28 = true from rfl,
      ↓reduceIte]
    rw [← hcQ]
    have h := pi2PcsOpenO_honest Hk F fuel (n := 28) (by norm_num) (by norm_num) out.qStack hqsz
      _ lQ (π := pQ1) (by rw [hqp', hqt', ← hcQ] at hQ1; exact hQ1)
    rw [hqt']
    exact h
  · -- `Q`'s pushes
    simp only [List.cons_append, List.nil_append] at hdecP ⊢
    rw [Pi2H.pcsOpenWordsH_eq (Pure.pure ∘ Hk) F _ _ _ hdecP]
    unfold Pi2H.openAtH
    simp only [rootOfWord_rootWord_rootHalves, hoods', Reduced.pushes, hro, lP, show oodRead 28 = true from rfl,
      ↓reduceIte]
    rw [← hcP]
    have h := pi2PcsOpenO_honest Hk F fuel (n := 28) (by norm_num) (by norm_num) out.qStack hqsz
      _ lP (π := pQ2) (by rw [hqp', hqt', ← hcP] at hQ2; exact hQ2)
    rw [hqt']
    exact h

end RecCompose.Pi2K

/-- info: 'RecCompose.Pi2K.pi2PcsOpenO_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2K.pi2PcsOpenO_honest

/-- info: 'RecCompose.Pi2K.contract_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2K.contract_accepts
