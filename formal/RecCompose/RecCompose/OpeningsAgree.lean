-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecCompose.Couplings
import RecCompose.CallsPure
import RecCompose.Pi1Words
import UniKeccakComplete.K.Reference
import RecCompose.ClaimBytes
import RecGraphKeccak.Sim.AtSetup4

/-!
# π1-rec4's verifier's openings are the contract's: `Pi1OpeningsAgree`, proved

`pi1OpeningsAgree`: on a stream π1-rec4's graph at π1's setup commitment accepts, its claims' encodings the declared
ones' (`claimCollision` empty), decoded `ops`, off the merge hazard, π1-rec4's verifier at Keccak-f[1600] with the
recursive proof's three π1 opening proofs is, as a computation, the contract's three π1 openings `openSeq` of `ops`.

* the graph at π1's setup commitment is π1-rec4's verifier there (`RecGraphKeccak.Sim.pi1GraphIsVerifierK4At`, no
  hypothesis): the run accepts (its zeros vanish) and the graph's claims are `UniKeccak.pcsClaimWordsK`' words of its
  openings at that commitment, three point claims in `commitments` order (`Pi1RunOpenings`), which decode
  (`decode_pcsClaimWordsK`) to the verifier's commitments, points and values;
* the declared claims have the graph's claims' encodings, and both decode, so they are the same claims
  (`ClaimBytes.claimOfWords_eq_of_pcsClaimBytes`): `ops` are the verifier's openings;
* the points have the verifier's stacks' variables `stackVarsK` (`27`, `26`, `23`): the graph's calls are the emitted
  graph's (`GraphsAgreeK4`, evaluated), of `30`, `29`, `26` words, 32 bytes each (`call_bytes_length`).
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open scoped ENNReal

/-- **π1-rec4's run's openings** (`RunOpenings.lean`: `pi1RunOpenings`): a run of π1-rec4's verifier at the reference
shape that returns a result has three point claims, without a bit-slice claim, in `commitments` order. -/
def Pi1RunOpenings : Prop :=
  ∀ (iv publicInput : List UInt8) (stream : Array UInt8) (r : UniStatement.Reduced),
    (UniKeccak.runK4 RecGraphKeccak.Pi1.keccak128 iv publicInput stream UniKeccak.keccakRec4 .point).result = .ok r →
      ∃ pt1 v1 pt2 v2 pt3 v3, r.openings = [(.c1, .point pt1 v1 none), (.c2, .point pt2 v2 none),
        (.setup, .point pt3 v3 none)]

/-! ## Bytes -/

/-- **The contract's setup root word names the setup's root** (a PCS claim's root field: the digest's bytes). -/
theorem rootOfWord_digestBytes (f : Digest) : rootOfWord (digestBytes f) = f := digestOfBytes32_digestBytes f

theorem length_beBytes32 (w : ℕ) : (RecGraph.beBytes32 w).length = 32 := by simp [RecGraph.beBytes32]

/-- A word of the emitted graph's calls is 32 bytes on a stream of the graph's length. -/
def WordFits (streamLen : ℕ) : RecGraph.Word → Bool
  | .node _ => true
  | .const _ => true
  | .stream at_ => decide (at_ + 32 ≤ streamLen)

theorem wordBytes_length {s : Array UInt8} {vals : Array RecGraph.Value} {w : RecGraph.Word}
    (hw : WordFits s.size w = true) : (RecGraph.wordBytes s vals w).length = 32 := by
  cases w with
  | node id => simp [RecGraph.wordBytes, Pi1Decode.length_elementWord]
  | const c => exact length_beBytes32 c
  | stream a =>
    simp only [WordFits, decide_eq_true_eq] at hw
    simp only [RecGraph.wordBytes, Array.length_toList, Array.size_extract]
    omega

theorem call_bytes_length {s : Array UInt8} {vals : Array RecGraph.Value} (call : List RecGraph.Word)
    (h : ∀ w ∈ call, WordFits s.size w = true) : (call.flatMap (RecGraph.wordBytes s vals)).length = 32 * call.length := by
  induction call with
  | nil => simp
  | cons w ws ih =>
    rw [List.flatMap_cons, List.length_append, wordBytes_length (h w (by simp)),
      ih fun v hv ↦ h v (by simp [hv]), List.length_cons]
    ring

theorem atSetupCall_length (roots : UniKeccak.SetupRootsK) (call : List RecGraph.Word) :
    (RecGraphKeccak.atSetupCall roots call).length = call.length := by
  unfold RecGraphKeccak.atSetupCall
  split <;> simp

theorem atSetupCall_fits (roots : UniKeccak.SetupRootsK) (n : ℕ) (call : List RecGraph.Word)
    (h : ∀ w ∈ call, WordFits n w = true) : ∀ w ∈ RecGraphKeccak.atSetupCall roots call, WordFits n w = true := by
  unfold RecGraphKeccak.atSetupCall
  split
  · rename_i a b rest
    intro w hw
    simp only [List.mem_cons] at hw
    rcases hw with rfl | rfl | hw
    · rfl
    · rfl
    · exact h w (by simp [hw])
  · exact h

/-- The emitted graph's calls: `30`, `29`, `26` words, each 32 bytes on a stream of its length. -/
theorem emitted_calls :
    RecGraphKeccak.Emitted.graph.calls.map List.length = [30, 29, 26] ∧
      ∀ call ∈ RecGraphKeccak.Emitted.graph.calls, ∀ w ∈ call,
        WordFits RecGraphKeccak.Emitted.graph.streamLen w = true := by
  decide

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

theorem claimOfWords_of_decodePi1Call {call : List UInt8} {x : Pi1Opening} (h : decodePi1Call call = some x) :
    claimOfWords (words32 call) = some x := by
  unfold decodePi1Call at h
  split at h
  · exact absurd h (by simp)
  · exact h

/-- **No collision**: `claimCollision` empty, the graph's claims' encodings are the declared ones'. -/
theorem encodings_of_no_collision {g : RecGraph.Graph} {iv1 : List UInt8} {input : Vector UInt8 32} {s : Array UInt8}
    {ds : List (List (List UInt8))} {out : RecGraph.Outputs}
    (hout : RecGraph.evalGraphDeployed g iv1 input.toList s = some out)
    (h : claimCollision g iv1 input s ds = ([], [])) :
    ∀ j < ds.length, pcsClaimBytes (words32 (out.calls.getD j [])) = pcsClaimBytes (ds.getD j []) := by
  unfold claimCollision at h
  rw [hout] at h
  simp only at h
  split at h
  · rename_i j hj
    have hne : pcsClaimBytes (words32 (out.calls.getD j [])) ≠ [] := by simp [pcsClaimBytes]
    exact absurd (congrArg Prod.fst h) hne
  · rename_i hn
    intro j hj
    have := List.find?_eq_none.mp hn j (List.mem_range.mpr hj)
    simpa using this

/-! ## The theorem -/

/-- **`Pi1OpeningsAgree`**, at the reference shape: from π1-rec4's run's shape and openings, the graph at every setup
commitment being the verifier there (`RecGraphKeccak.Sim.pi1GraphIsVerifierK4At`), and the Lean recording being the
emitted graph (`GraphsAgreeK4`, evaluated: the claims' word counts). -/
theorem pi1OpeningsAgree (D : RecDeployment) (hD : D.pi1.shape = RecGraphKeccak.Pi1.keccak128) (hS : Pi1RunShape)
    (hO : Pi1RunOpenings) (hg : RecGraphKeccak.GraphsAgreeK4) : Pi1OpeningsAgree D := by
  intro _ roots input proof s ops hops hga hcol hz
  obtain ⟨out, hout, hzs, -, hlen, -⟩ := hga
  have hge := RecGraphKeccak.Sim.pi1GraphIsVerifierK4At roots.pi1 LeanVM.Semantics.keccakF1600 (D.pi1IvAt roots.pi1)
    input s hz
  have henc := encodings_of_no_collision hout hcol
  have hiv : D.pi1IvAt roots.pi1 = pi1Iv RecGraphKeccak.Pi1.keccak128 D.pi1.programIv roots.pi1 := by
    unfold RecDeployment.pi1IvAt; rw [hD]
  rw [hiv] at hge hout
  set iv := pi1Iv RecGraphKeccak.Pi1.keccak128 D.pi1.programIv roots.pi1 with hivd
  set o := UniKeccak.runK4 RecGraphKeccak.Pi1.keccak128 iv input.toList s UniKeccak.keccakRec4 .point with ho
  -- the graph's outputs as the evaluation computes them: each call 32 bytes a word
  have hgraph := hout
  unfold pi1GraphAt RecGraph.evalGraphDeployed RecGraph.evalGraph at hgraph
  have hgo : RecGraph.evalGraphDeployed (pi1GraphAt roots.pi1) iv input.toList s =
      match o.result with
      | .ok r => some ⟨UniKeccak.pcsClaimWordsK roots.pi1 r, o.chan.zeros.toList, []⟩
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
    have hdec := decode_pcsClaimWordsK roots.pi1 r pt1 pt2 pt3 v1 v2 v3 hro
    -- the calls' byte lengths from the emitted graph's word counts
    have hsz : s.size = RecGraphKeccak.Emitted.graph.streamLen := by
      by_contra hne
      rw [show (RecGraphKeccak.graphAtSetup RecGraphKeccak.Pi1.pi1GraphK4 roots.pi1).streamLen =
        RecGraphKeccak.Emitted.graph.streamLen by rw [← hg]; rfl] at hgraph
      simp [hne] at hgraph
    -- the claims' bytes are the graph's calls' words, 32 bytes each
    have hcalls : ∃ vals, UniKeccak.pcsClaimWordsK roots.pi1 r =
        (RecGraphKeccak.graphAtSetup RecGraphKeccak.Pi1.pi1GraphK4 roots.pi1).calls.map
          (·.flatMap (RecGraph.wordBytes s vals)) := by
      have hsz' : s.size = (RecGraphKeccak.graphAtSetup RecGraphKeccak.Pi1.pi1GraphK4 roots.pi1).streamLen := by
        rw [hsz, ← hg]; rfl
      simp only [hsz', ite_true] at hgraph
      exact ⟨_, (congrArg RecGraph.Outputs.calls (Option.some.inj hgraph)).symm⟩
    obtain ⟨vals, hcalls⟩ := hcalls
    have hcl : (RecGraphKeccak.graphAtSetup RecGraphKeccak.Pi1.pi1GraphK4 roots.pi1).calls =
        RecGraphKeccak.Emitted.graph.calls.map (RecGraphKeccak.atSetupCall roots.pi1) := by
      rw [← hg]; rfl
    obtain ⟨hcnt, hfit⟩ := emitted_calls
    have hlens := congrArg (List.map List.length) hcalls
    rw [hcl, List.map_map, List.map_map] at hlens
    have hlens' : (RecGraphKeccak.Emitted.graph.calls.map fun call ↦
        ((RecGraphKeccak.atSetupCall roots.pi1 call).flatMap (RecGraph.wordBytes s vals)).length) =
        [32 * 30, 32 * 29, 32 * 26] := by
      rw [show [32 * 30, 32 * 29, 32 * 26] = (RecGraphKeccak.Emitted.graph.calls.map List.length).map (32 * ·) by
        rw [hcnt]; rfl, List.map_map]
      refine List.map_congr_left fun call hc ↦ ?_
      simp only [Function.comp_apply]
      rw [call_bytes_length _ (atSetupCall_fits roots.pi1 _ call fun w hw ↦ by rw [hsz]; exact hfit call hc w hw),
        atSetupCall_length]
    simp only [Function.comp_def] at hlens
    rw [hlens'] at hlens
    unfold UniKeccak.pcsClaimWordsK at hlens
    rw [hro] at hlens
    simp only [List.map_cons, List.map_nil, List.length_append, Pi1Decode.length_elementWord, List.length_flatMap,
      List.cons.injEq, and_true] at hlens
    obtain ⟨l1, l2, l3⟩ := hlens
    simp only [UniKeccak.rootBytesK, UniKeccakComplete.length_rootWord, Pi1Decode.length_digestBytes,
      List.map_const', List.sum_replicate, smul_eq_mul] at l1 l2 l3
    have hl1 : pt1.length = 27 := by omega
    have hl2 : pt2.length = 26 := by omega
    have hl3 : pt3.length = 23 := by omega
    -- the declared claims are the graph's
    have hd3 : proof.pi1Claims.length = 3 := by
      rw [← hlen]; simp [UniKeccak.pcsClaimWordsK, hro]
    have henc' : ∀ j < 3, pcsClaimBytes (words32 ((UniKeccak.pcsClaimWordsK roots.pi1 r).getD j [])) =
        pcsClaimBytes (proof.pi1Claims.getD j []) := fun j hj ↦ henc j (by rw [hd3]; exact hj)
    clear henc
    obtain ⟨d0, d1, d2, hds⟩ : ∃ a b c, proof.pi1Claims = [a, b, c] := by
      match proof.pi1Claims, hd3 with
      | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
    rw [hds] at hops henc'
    obtain ⟨x0, x1, x2, rfl, hx0, hx1, hx2⟩ := mapM_three _ _ _ _ _ hops
    unfold UniKeccak.pcsClaimWordsK at hdec henc'
    rw [hro] at hdec henc'
    simp only [List.map_cons, List.map_nil] at hdec henc'
    obtain ⟨g0, g1, g2, hgs, hg0, hg1, hg2⟩ := mapM_three _ _ _ _ _ hdec
    simp only [List.cons.injEq, and_true] at hgs
    obtain ⟨rfl, rfl, rfl⟩ := hgs
    have e0 := claimOfWords_eq_of_pcsClaimBytes hx0 (claimOfWords_of_decodePi1Call hg0) (henc' 0 (by simp)).symm
    have e1 := claimOfWords_eq_of_pcsClaimBytes hx1 (claimOfWords_of_decodePi1Call hg1) (henc' 1 (by simp)).symm
    have e2 := claimOfWords_eq_of_pcsClaimBytes hx2 (claimOfWords_of_decodePi1Call hg2) (henc' 2 (by simp)).symm
    subst e0 e1 e2
    -- the run accepts
    have hacc : o.accepts = true := by
      unfold UniStatement.Outcome.accepts
      rw [hres, ← Array.all_toList]
      simp only [Bool.true_and, List.all_eq_true, beq_iff_eq]
      exact fun z hz ↦ hzs z hz
    unfold pi1KeccakVerifierWith openSeq openAt
    simp only [RecProof.pi1Proof]
    have hres' : (UniKeccak.runK4 RecGraphKeccak.Pi1.keccak128 (pi1Iv RecGraphKeccak.Pi1.keccak128 D.pi1.programIv
        roots.pi1) input.toList s pi1Variant .point).result = .ok r := hres
    have hacc' : (UniKeccak.runK4 RecGraphKeccak.Pi1.keccak128 (pi1Iv RecGraphKeccak.Pi1.keccak128 D.pi1.programIv
        roots.pi1) input.toList s pi1Variant .point).accepts = true := hacc
    simp only [hD, hacc', hres', Bool.not_true, Bool.false_eq_true, ite_false, hro]
    have hcm : (List.map (fun x ↦ x.1) [(UniStatement.Commitment.c1, UniStatement.Opening.point pt1 v1 none),
        (UniStatement.Commitment.c2, UniStatement.Opening.point pt2 v2 none),
        (UniStatement.Commitment.setup, UniStatement.Opening.point pt3 v3 none)] == UniStatement.commitments) = true :=
      rfl
    have e1' : UniKeccak.stackVarsK RecGraphKeccak.Pi1.keccak128 UniStatement.Commitment.c1 = pt1.length := by
      rw [hl1, show RecGraphKeccak.Pi1.keccak128 = UniKeccakSound.keccakRefShape from rfl,
        UniKeccakComplete.reference_stackVars_c1]
    have e2' : UniKeccak.stackVarsK RecGraphKeccak.Pi1.keccak128 UniStatement.Commitment.c2 = pt2.length := by
      rw [hl2, show RecGraphKeccak.Pi1.keccak128 = UniKeccakSound.keccakRefShape from rfl,
        UniKeccakComplete.reference_stackVars_c2]
    have e3' : UniKeccak.stackVarsK RecGraphKeccak.Pi1.keccak128 UniStatement.Commitment.setup = pt3.length := by
      rw [hl3, show RecGraphKeccak.Pi1.keccak128 = UniKeccakSound.keccakRefShape from rfl,
        UniKeccakComplete.reference_stackVars_setup]
    have hs1 : oodRead pt1.length = false := by rw [hl1]; rfl
    have hs2 : oodRead pt2.length = false := by rw [hl2]; rfl
    have hs3 : oodRead pt3.length = false := by rw [hl3]; rfl
    simp only [hcm, hmat, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.forIn_cons, List.forIn_nil,
      bind_assoc, pure_bind, Bool.true_and, List.getD_cons_zero, List.getD_cons_succ, UniKeccak.commitOfK,
      UniKeccak.KeccakProof.openingOf, e1', e2', e3', hs1, hs2, hs3]

end RecCompose

/-- info: 'RecCompose.pi1OpeningsAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi1OpeningsAgree
