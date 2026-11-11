-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecCompose.Couplings
import RecCompose.CallsPure
import RecCompose.CompleteCouplings
import UniKeccakComplete.K.Reference

/-!
# The Keccak π1-rec3's verifier's openings are the contract's: `Pi1OpeningsAgree`, proved

`pi1OpeningsAgree`: on a stream the Keccak π1-rec3's graph accepts with the contract's π1 openings `ops`, off the merge
hazard (the graph being the Keccak π1-rec3's verifier there, `Pi1GraphIsVerifierK`), the Keccak π1-rec3's verifier at
Keccak-f[1600] with the recursive proof's three π1 opening proofs is, as a computation, the contract's three π1
openings `openSeq` of `ops`.

* the graph's outputs are the verifier's (`Pi1GraphIsVerifierK`, `RecGraphKeccak.verifierOutputsWithK`): the run
  accepts (its zeros vanish), and its claims are `UniKeccak.pcsClaimWordsK`' words of its openings, three point claims
  in `commitments` order (**`Pi1RunOpenings`**, proved in `RunOpenings.lean`), which decode (`decode_pcsClaimWordsK`)
  to the verifier's commitments, points and values; `Pi1GraphAccepts` makes `ops`' points and values these, and `C1`'s
  and `C2`'s roots and answers theirs (the matrices' check passes by `Pi1RunShape`);
* the setup's commitment in `ops` is the contract's decoding of the deployment's constants `digestBytes F`,
  `elementWord f(z)` (`rootOfWord_digestBytes`, `Pi1Decode.elementOfWord_elementWord`), when π1's third call starts with
  two constants, and the contract's points have the verifier's stacks' variables `stackVarsK` (`27`, `26`, `23`), by
  the calls' word counts (**`Pi1CallsShape`**, named; `Data.pi1Calls`' `pi1CallsShape_data`; `contract_ops`), so the
  contract's openings at the points' lengths are the verifier's at `stackVarsK`.
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open scoped ENNReal

/-! ## The named facts -/

/-- **The Keccak π1-rec3's run's openings** (a fact of `UniKeccak.reduceWithK`'s code, named here, proved in
`RunOpenings.lean`: `pi1RunOpenings`): a run of the Keccak π1-rec3's verifier at the reference shape that returns a
result has three point claims, without a bit-slice claim, in `commitments` order (`batchK` at the point-claim ABI, one
opening per commitment, and each commitment has a relation). -/
def Pi1RunOpenings : Prop :=
  ∀ (iv publicInput : List UInt8) (stream : Array UInt8) (r : UniStatement.Reduced),
    (UniKeccak.runK4 RecGraphKeccak.Pi1.keccak128 iv publicInput stream UniKeccak.keccakRec4 .point).result = .ok r →
      ∃ pt1 v1 pt2 v2 pt3 v3, r.openings = [(.c1, .point pt1 v1 none), (.c2, .point pt2 v2 none),
        (.setup, .point pt3 v3 none)]

/-- **π1's calls' shape**: three calls of `stackVarsK + 3` words at the reference shape (the root, the out-of-domain
answer, the point, the value: `30`, `29`, `26`), the third (the setup's) naming its root and answer as constants (which
the contract replaces by the setup's, `pi1CallsWith`). -/
def Pi1CallsShape (D : RecDeployment) : Prop :=
  D.pi1Calls.map List.length =
      UniStatement.commitments.map (fun c ↦ UniKeccak.stackVarsK RecGraphKeccak.Pi1.keccak128 c + 3) ∧
    ∃ w1 w2 rest, D.pi1Calls.getD 2 [] = CallWord.const w1 :: CallWord.const w2 :: rest

/-- The real deployment's calls have that shape. -/
theorem pi1CallsShape_data (D : RecDeployment) (h : D.pi1Calls = Data.pi1Calls) : Pi1CallsShape D := by
  rw [Pi1CallsShape, h]
  refine ⟨?_, _, _, _, rfl⟩
  have e : RecGraphKeccak.Pi1.keccak128 = UniKeccakSound.keccakRefShape := rfl
  simp only [UniStatement.commitments, List.map_cons, List.map_nil, e, UniKeccakComplete.reference_stackVars_c1,
    UniKeccakComplete.reference_stackVars_c2, UniKeccakComplete.reference_stackVars_setup]
  rfl

/-! ## Bytes -/

/-- **The contract's setup root word names the setup's root** (a PCS claim's root field: the digest's bytes). -/
theorem rootOfWord_digestBytes (f : Digest) : rootOfWord (digestBytes f) = f := digestOfBytes32_digestBytes f

/-! ## Decoding -/

/-- `mapM` in `Option` of three. -/
theorem mapM_three {α β : Type} (f : α → Option β) (a b c : α) (ys : List β)
    (h : [a, b, c].mapM f = some ys) : ∃ x y z, ys = [x, y, z] ∧ f a = some x ∧ f b = some y ∧ f c = some z := by
  simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.pure_def] at h
  cases ha : f a with
  | none => simp [ha] at h
  | some x =>
    cases hb : f b with
    | none => simp [ha, hb] at h
    | some y =>
      cases hc : f c with
      | none => simp [ha, hb, hc] at h
      | some z =>
        simp only [ha, hb, hc, Option.bind_some, Option.some.injEq] at h
        exact ⟨x, y, z, h.symm, rfl, rfl, rfl⟩

/-- **A claim's root and answer words, decoded.** -/
theorem claimOfWords_cons (r o : List UInt8) (ws : List (List UInt8)) (x : Pi1Opening)
    (h : claimOfWords (r :: o :: ws) = some x) : x.1 = rootOfWord r ∧ elementOfWord o = some x.2.1 := by
  unfold claimOfWords at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨root, hr, oodW, ho, valueW, -, h⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hr
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at ho
  subst hr ho
  split at h
  · exact absurd h (by simp)
  · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ood, hood, pt, -, value, -, rfl⟩ := h
    exact ⟨rfl, hood⟩

/-- `pi1CallsWith` keeps each call's word count. -/
theorem pi1CallsWith_lengths (calls : List (List CallWord)) (roots : UniKeccak.SetupRootsK) :
    (pi1CallsWith calls roots).map List.length = calls.map List.length := by
  unfold pi1CallsWith
  rw [List.map_map]
  refine List.map_congr_left fun call _ ↦ ?_
  simp only [Function.comp_apply]
  split <;> simp_all

/-- **The contract's π1 openings, from π1's calls' shape**: three, their points of `stackVarsK` coordinates (`27`, `26`,
`23`), the third's commitment the setup's. -/
theorem contract_ops (D : RecDeployment) (hC : Pi1CallsShape D) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (stream : Array UInt8) (ops : List Pi1Opening) (hops : pi1OpsOf D roots input stream = some ops) :
    ∃ o0 o1 o2, ops = [o0, o1, o2] ∧
      o0.2.2.1.length = UniKeccak.stackVarsK RecGraphKeccak.Pi1.keccak128 .c1 ∧
      o1.2.2.1.length = UniKeccak.stackVarsK RecGraphKeccak.Pi1.keccak128 .c2 ∧
      o2.2.2.1.length = UniKeccak.stackVarsK RecGraphKeccak.Pi1.keccak128 .setup ∧
      o2.1 = roots.pi1.f ∧ o2.2.1 = roots.pi1.fOod := by
  obtain ⟨hl, w1, w2, rest, hw⟩ := hC
  obtain ⟨a, b, c, hcl⟩ : ∃ a b c, D.pi1Calls = [a, b, c] := by
    have := congrArg List.length hl
    simp only [List.length_map, UniStatement.commitments, List.length_cons, List.length_nil] at this
    match D.pi1Calls, this with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  rw [hcl] at hw hl
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hw
  subst hw
  simp only [List.map_cons, List.map_nil, UniStatement.commitments, List.cons.injEq, and_true] at hl
  obtain ⟨la, lb, lc⟩ := hl
  have hpl := pi1CallsWith_lengths D.pi1Calls roots.pi1
  rw [hcl] at hpl
  unfold pi1OpsOf at hops
  simp only at hops
  split at hops
  · exact absurd hops (by simp)
  · rename_i r2 _
    unfold contractPi1Openings at hops
    have h3 : (pi1CallsWith D.pi1Calls roots.pi1).length = 3 := by
      rw [hcl]
      have := congrArg List.length hpl
      simpa using this
    rw [pcsCalls_take _ _ _ _ _ _ h3] at hops
    rw [hcl] at hops

    set a' := (pi1CallsWith [a, b, CallWord.const w1 :: CallWord.const w2 :: rest] roots.pi1).getD 0 []
    set b' := (pi1CallsWith [a, b, CallWord.const w1 :: CallWord.const w2 :: rest] roots.pi1).getD 1 []
    have he : pi1CallsWith [a, b, CallWord.const w1 :: CallWord.const w2 :: rest] roots.pi1 =
        [a', b', .const (digestBytes roots.pi1.f) :: .const (UniStatement.elementWord roots.pi1.fOod) :: rest] := by
      simp only [a', b', pi1CallsWith, List.map_cons, List.map_nil]
      rfl
    rw [he] at hops hpl
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpl
    obtain ⟨la', lb', -⟩ := hpl
    simp only [List.map_cons, List.map_nil] at hops
    obtain ⟨x, y, z, rfl, hx, hy, hz⟩ := mapM_three _ _ _ _ _ hops
    refine ⟨x, y, z, rfl, ?_, ?_, ?_, ?_⟩
    · rw [Pi1Decode.claimOfWords_length _ _ hx, List.length_map, la', la]; rfl
    · rw [Pi1Decode.claimOfWords_length _ _ hy, List.length_map, lb', lb]; rfl
    · rw [Pi1Decode.claimOfWords_length _ _ hz]
      simp only [List.length_cons, List.length_map] at lc ⊢
      omega
    · obtain ⟨hr, ho⟩
 := claimOfWords_cons _ _ _ _ hz
      simp only [callWord, Pi1Decode.elementOfWord_elementWord, Option.some.injEq] at ho hr

      exact ⟨hr.trans (rootOfWord_digestBytes _), ho.symm⟩

/-! ## The theorem -/

/-- **`Pi1OpeningsAgree`**, at the reference shape, from π1-rec3's run's shape and openings and π1's calls' shape. -/
theorem pi1OpeningsAgree (D : RecDeployment) (hD : D.pi1.shape = RecGraphKeccak.Pi1.keccak128) (hS : Pi1RunShape)
    (hO : Pi1RunOpenings) (hC : Pi1CallsShape D) : Pi1OpeningsAgree D := by
  intro hgv roots input proof s ops hops hga hz
  obtain ⟨o0, o1, o2, rfl, hl0, hl1, hl2, hf, hfo⟩ := contract_ops D hC roots input proof.stream ops hops
  obtain ⟨out, gops, hout, hzs, -, hg, hpts, hroot⟩ := hga
  have hge := hgv LeanVM.Semantics.keccakF1600 (D.pi1IvAt roots.pi1) input s hz
  have hiv : D.pi1IvAt roots.pi1 = pi1Iv RecGraphKeccak.Pi1.keccak128 D.pi1.programIv roots.pi1 := by
    unfold RecDeployment.pi1IvAt; rw [hD]
  rw [hiv] at hge hout
  set iv := pi1Iv RecGraphKeccak.Pi1.keccak128 D.pi1.programIv roots.pi1 with hivd
  set o := UniKeccak.runK RecGraphKeccak.Pi1.keccak128 iv input.toList s UniKeccak.keccakRec3 .point with ho
  have hgo : RecGraph.evalGraphDeployed RecGraphKeccak.Pi1.pi1GraphK iv input.toList s =
      match o.result with
      | .ok r => some ⟨UniKeccak.pcsClaimWordsK keccakRefRoots r, o.chan.zeros.toList, []⟩
      | .error _ => none := hge
  rw [hgo] at hout
  cases hres : o.result with
  | error e =>
    rw [hres] at hout
    exact absurd hout (by simp)
  | ok r =>
    rw [hres] at hout
    have hout' := (Option.some.inj hout).symm
    subst hout'
    obtain ⟨hmat, -⟩ := hS iv input.toList s r hres
    obtain ⟨pt1, v1, pt2, v2, pt3, v3, hro⟩ := hO iv input.toList s r hres
    simp only at hg
    rw [decode_pcsClaimWordsK _ r pt1 pt2 pt3 v1 v2 v3 hro, Option.some.injEq] at hg
    subst hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, List.take] at hpts hroot
    obtain ⟨e0, e1, e2⟩ := hpts
    obtain ⟨r0, r1⟩ := hroot
    -- The run accepts.
    have hacc : o.accepts = true := by
      unfold UniStatement.Outcome.accepts
      rw [hres, ← Array.all_toList]
      simp only [Bool.true_and, List.all_eq_true, beq_iff_eq]
      exact fun z hz ↦ hzs z hz
    rcases o0 with ⟨a0, b0, q0⟩
    rcases o1 with ⟨a1, b1, q1⟩
    rcases o2 with ⟨a2, b2, q2⟩
    simp only [Prod.mk.injEq] at hf hfo r0 r1 e0 e1 e2 hl0 hl1 hl2
    obtain ⟨rfl, rfl⟩ := r0
    obtain ⟨rfl, rfl⟩ := r1
    subst hf hfo e0 e1 e2
    unfold pi1KeccakVerifierWith openSeq openAt
    simp only [RecProof.pi1Proof]
    have hres' : (UniKeccak.runK RecGraphKeccak.Pi1.keccak128 (pi1Iv RecGraphKeccak.Pi1.keccak128 D.pi1.programIv
        roots.pi1) input.toList s UniKeccak.keccakRec3 .point).result = .ok r := hres
    have hacc' : (UniKeccak.runK RecGraphKeccak.Pi1.keccak128 (pi1Iv RecGraphKeccak.Pi1.keccak128 D.pi1.programIv
        roots.pi1) input.toList s UniKeccak.keccakRec3 .point).accepts = true := hacc
    simp only [hD, hacc', hres', Bool.not_true, Bool.false_eq_true, ite_false, hro]
    have hcm : (List.map (fun x ↦ x.1) [(UniStatement.Commitment.c1, UniStatement.Opening.point pt1 v1 none),
        (UniStatement.Commitment.c2, UniStatement.Opening.point pt2 v2 none),
        (UniStatement.Commitment.setup, UniStatement.Opening.point pt3 v3 none)] == UniStatement.commitments) = true :=
      rfl
    have hs1 : oodRead (UniKeccak.stackVarsK RecGraphKeccak.Pi1.keccak128 UniStatement.Commitment.c1) = false := by
      rw [show RecGraphKeccak.Pi1.keccak128 = UniKeccakSound.keccakRefShape from rfl,
        UniKeccakComplete.reference_stackVars_c1]
      rfl
    have hs2 : oodRead (UniKeccak.stackVarsK RecGraphKeccak.Pi1.keccak128 UniStatement.Commitment.c2) = false := by
      rw [show RecGraphKeccak.Pi1.keccak128 = UniKeccakSound.keccakRefShape from rfl,
        UniKeccakComplete.reference_stackVars_c2]
      rfl
    have hs3 : oodRead (UniKeccak.stackVarsK RecGraphKeccak.Pi1.keccak128 UniStatement.Commitment.setup) = false := by
      rw [show RecGraphKeccak.Pi1.keccak128 = UniKeccakSound.keccakRefShape from rfl,
        UniKeccakComplete.reference_stackVars_setup]
      rfl
    simp only [hcm, hmat, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.forIn_cons, List.forIn_nil,
      bind_assoc, pure_bind, Bool.true_and, List.getD_cons_zero, List.getD_cons_succ, UniKeccak.commitOfK,
      UniKeccak.KeccakProof.openingOf, hl0, hl1, hl2, hs1, hs2, hs3]

end RecCompose

/-- info: 'RecCompose.pi1OpeningsAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi1OpeningsAgree
