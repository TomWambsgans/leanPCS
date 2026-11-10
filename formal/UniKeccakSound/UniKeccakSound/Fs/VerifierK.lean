-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `UniSound/FsVerifier.lean` (`uniVerifierBridge_of_walk`,
-- whose generic lemmas are reused) and π1-rec3's `Rec3/FsVerifier3.lean` (three calls) for the Keccak verifier,
-- `formal/UniKeccak`'s `verifyWithK` (the loop over the openings, then no matrices' claim).
import UniKeccakSound.Fs.WalkK
import UniKeccakSound.Code.Link
import UniSound.FsVerifier

/-!
# The Keccak verifier bridge from the walk

**`uniVerifierBridgeK_of_walk`**: `UniVerifierBridgeK` (`CoupleK.lean`) from the walk's two halves (`UniWalkK`,
`UniWalkRejectK`, `WalkK.lean`) and the code-level link's roots, **`UniOutRootsK`** (`Code/Link.lean`: the chain
program's result names the roots of rounds `0` and `nF + 1`, on every transcript), as `UniSound`'s:

* a stream of another length is rejected by the walk; on a stream of the main line's length the walk is the chain
  over Keccak-256, the same chain the composed verifier runs first (`UniSound.simulateQ_verU`);
* per challenges: if `uAccBK` is `false` `verifyWithK` rejects; else its result is `uOutK`, and the rest of
  `verifyWithK` (`restRK`: the loop `stepRK` over the result's openings, then no matrices' claim, any claim
  rejecting) accepts only on a result of the main line's shape (`GoodRK`: three point claims without a bit slice on
  `C1`, `C2`, the setup, each of its stack's variables, and no matrices' claim: `restRK_good`); on such a result it
  is the **three** PCS openings one after the other (`restRK_unroll`), each `pcsOpenC` answered over `π`
  (`pcsOpenK_eq`), on the composed openings' claims (the roots `root_at`, the out-of-domain answers the result's), so
  it accepts at most as often as the three composed openings all do, and its acceptance gives `uniCheckK`.
-/

namespace UniKeccakSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement UniSound UniKeccak
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.setupStackK UniKeccak.setupOodK

/-! ## `verifyWithK` after the run -/

section Rest

variable (shape : UniStatement.Shape) (roots : SetupRootsK) (proof : KeccakProof)

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- The loop's step over the result's openings. -/
def stepRK (r : Reduced) : Commitment × UniStatement.Opening → Bool → m (ForInStep Bool) :=
  fun x ok => match x with
    | (c, opening) => match opening with
      | .point pt value none => do
          let b ← pcsOpenK F (stackVarsK shape c) (commitOfK roots r c).1 (commitOfK roots r c).2 pt value
            (proof.openingOf c)
          pure (ForInStep.yield (ok && b))
      | _ => pure (ForInStep.yield false)

/-- **`verifyWithK` after the run**, on its result: the loop, then no matrices' claim. -/
def restRK (r : Reduced) : m Bool :=
  forIn r.openings (r.openings.map (·.1) == commitments) (stepRK shape roots proof F r) >>= fun ok =>
    if r.matrices.isSome then pure false else pure ok

/-- **`verifyWithK` is the run, then `restRK`** on an accepting run's result. -/
theorem verifyWithK_eq_rest [LawfulMonad m] (iv : List UInt8) (input : Vector UInt8 32) :
    verifyWithK F shape keccakMain iv roots input proof =
      ((fun o : UniStatement.Outcome => (o.accepts, o.result)) <$>
          runWithK F shape iv input.toList proof.stream keccakMain .point) >>= fun p =>
        if !p.1 then pure false else
          match p.2 with
          | .error _ => pure false
          | .ok r => restRK shape roots proof F r := by
  rw [bind_map_left]
  rfl

end Rest

/-! ## What an accepting `restRK` needs -/

section Support

variable (shape : UniStatement.Shape) (roots : SetupRootsK) (proof : KeccakProof)
variable {ι : Type} {spec : OracleSpec.{0, 0} ι} (F : KeccakState → OracleComp spec KeccakState)

/-- **A PCS opening rejects a point of another length**, before any query. -/
theorem pcsOpenK_len (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E) (p : Compile.Proof) :
    ∀ b ∈ support (pcsOpenK F n root ood pt v p), b = true → pt.length = n := by
  intro b hb hbt
  by_contra hne
  unfold pcsOpenK at hb
  rw [dite_eq_right_iff.mpr (fun h => absurd h hne)] at hb
  rw [support_pure, Set.mem_singleton_iff] at hb
  rw [hb] at hbt
  exact Bool.false_ne_true hbt

theorem stepRK_point (r : Reduced) (c : Commitment) (pt : List E) (v : E) (ok : Bool) :
    stepRK shape roots proof F r (c, .point pt v none) ok =
      pcsOpenK F (stackVarsK shape c) (commitOfK roots r c).1 (commitOfK roots r c).2 pt v (proof.openingOf c) >>=
        fun b => pure (ForInStep.yield (ok && b)) := rfl

theorem stepRK_other (r : Reduced) (c : Commitment) (o : UniStatement.Opening)
    (ho : ∀ pt v, o ≠ .point pt v none) (ok : Bool) :
    stepRK shape roots proof F r (c, o) ok = pure (ForInStep.yield false) := by
  rcases o with _ | ⟨pt, v, _ | _⟩
  · rfl
  · exact absurd rfl (ho pt v)
  · rfl

/-- **An accepting loop** started from `ok`, and met only point claims without a bit slice, each of its stack's
variables. -/
theorem forIn_stepRK_true (r : Reduced) :
    ∀ (l : List (Commitment × UniStatement.Opening)) (ok : Bool),
      ∀ b ∈ support (forIn l ok (stepRK shape roots proof F r)), b = true →
        ok = true ∧ ∀ x ∈ l, ∃ pt v, x.2 = .point pt v none ∧ pt.length = stackVarsK shape x.1
  | [], ok, b, hb, hbt => by
    rw [List.forIn_nil, support_pure, Set.mem_singleton_iff] at hb
    subst hb
    exact ⟨hbt, by simp⟩
  | (c, o) :: l, ok, b, hb, hbt => by
    rw [List.forIn_cons, mem_support_bind_iff] at hb
    obtain ⟨y, hy, hb⟩ := hb
    by_cases ho : ∃ pt v, o = .point pt v none
    · obtain ⟨pt, v, rfl⟩ := ho
      rw [stepRK_point, mem_support_bind_iff] at hy
      obtain ⟨b1, hb1, hy⟩ := hy
      rw [support_pure, Set.mem_singleton_iff] at hy
      subst hy
      obtain ⟨h1, h2⟩ := forIn_stepRK_true r l (ok && b1) b hb hbt
      rw [Bool.and_eq_true] at h1
      refine ⟨h1.1, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨pt, v, rfl, pcsOpenK_len F _ _ _ _ _ _ b1 hb1 h1.2⟩
      · exact h2 x hx
    · rw [stepRK_other _ _ _ _ _ _ _ (fun pt v h => ho ⟨pt, v, h⟩), support_pure,
        Set.mem_singleton_iff] at hy
      subst hy
      exact absurd (forIn_stepRK_true r l false b hb hbt).1 (by simp)

/-- **The main line's result**: three point claims without a bit slice, on `C1`, `C2` and the setup, each of its
stack's variables, and no matrices' claim. -/
def GoodRK (r : Reduced) : Prop :=
  ∃ (p1 : List E) (v1 : E) (p2 : List E) (v2 : E) (p3 : List E) (v3 : E),
    r.openings = [(.c1, .point p1 v1 none), (.c2, .point p2 v2 none),
      (.setup, .point p3 v3 none)] ∧ r.matrices = none ∧
    p1.length = stackVarsK shape .c1 ∧ p2.length = stackVarsK shape .c2 ∧ p3.length = stackVarsK shape .setup

/-- **`restRK` accepts only on the main line's result.** -/
theorem restRK_good (r : Reduced) :
    ∀ b ∈ support (restRK shape roots proof F r), b = true → GoodRK shape r := by
  intro b hb hbt
  rw [restRK, mem_support_bind_iff] at hb
  obtain ⟨ok, hok, hb⟩ := hb
  have hmc : r.matrices = none ∧ ok = true := by
    rcases h : r.matrices with _ | mc
    · rw [h] at hb
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, support_pure,
        Set.mem_singleton_iff] at hb
      subst hb
      exact ⟨rfl, hbt⟩
    · rw [h] at hb
      simp only [Option.isSome_some, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hb
      subst hb
      exact absurd hbt (by simp)
  obtain ⟨hmc, hokt⟩ := hmc
  subst hokt
  obtain ⟨hc, hall⟩ := forIn_stepRK_true shape roots proof F r _ _ _ hok rfl
  rw [beq_iff_eq] at hc
  rcases hl : r.openings with _ | ⟨⟨c₁, o₁⟩, _ | ⟨⟨c₂, o₂⟩, _ | ⟨⟨c₃, o₃⟩, _ | ⟨_, _⟩⟩⟩⟩ <;>
    rw [hl] at hc hall <;> simp [commitments] at hc
  obtain ⟨rfl, rfl, rfl⟩ := hc
  obtain ⟨p1, v1, e1, l1⟩ := hall _ List.mem_cons_self
  obtain ⟨p2, v2, e2, l2⟩ := hall _ (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨p3, v3, e3, l3⟩ := hall _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    List.mem_cons_self))
  simp only at e1 e2 e3
  subst e1 e2 e3
  exact ⟨p1, v1, p2, v2, p3, v3, hl, hmc, l1, l2, l3⟩

/-- **On the main line's result, `restRK` is the three PCS openings**, one after the other. -/
theorem restRK_unroll (r : Reduced) (p1 : List E) (v1 : E) (p2 : List E) (v2 : E) (p3 : List E)
    (v3 : E) (ho : r.openings = [(.c1, .point p1 v1 none), (.c2, .point p2 v2 none),
      (.setup, .point p3 v3 none)]) (hm : r.matrices = none) :
    restRK shape roots proof F r = seqAnd
      [pcsOpenK F (stackVarsK shape .c1) (rootOf r.roots.1) r.oods.1 p1 v1 proof.c1,
        pcsOpenK F (stackVarsK shape .c2) (rootOf r.roots.2) r.oods.2 p2 v2 proof.c2,
        pcsOpenK F (stackVarsK shape .setup) roots.f roots.fOod p3 v3 proof.setup] true := by
  have hc : (r.openings.map (·.1) == commitments) = true := by
    rw [ho]
    rfl
  rw [restRK, hc, ho, hm]
  simp only [List.forIn_cons, List.forIn_nil, stepRK_point, bind_assoc, pure_bind,
    seqAnd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  rfl

end Support

/-! ## The three openings -/

theorem sim_gopsRun_cons {γ : Type} (view : UPf → FSt × List (RMsg E)) (o : GOp UPf E Stk)
    (os : List (GOp UPf E Stk)) (π : UPf) (ch : List (List E))
    (g : List Bool → OracleComp KeccakCalls γ) :
    simulateQ keccakCallsOverQueryPermutation (gopsRun view (o :: os) π ch >>= g) =
      simulateQ keccakCallsOverQueryPermutation (GOp.run view o π ch) >>= fun b =>
        simulateQ keccakCallsOverQueryPermutation (gopsRun view os π ch >>= fun bs => g (b :: bs)) := by
  rw [gopsRun, bind_assoc, simulateQ_bind]
  simp only [bind_map_left]

theorem sim_gopsRun_nil {γ : Type} (view : UPf → FSt × List (RMsg E)) (π : UPf)
    (ch : List (List E)) (g : List Bool → OracleComp KeccakCalls γ) :
    simulateQ keccakCallsOverQueryPermutation
        (gopsRun view ([] : List (GOp UPf E Stk)) π ch >>= g) =
      simulateQ keccakCallsOverQueryPermutation (g []) := by
  rw [gopsRun, pure_bind]

/-- **An opening accepting at most as often as an equal one**, over the lazily sampled permutation, for
continuations ordered as accepting implies accepting. -/
theorem eq_le_rpm {β γ : Type} (x x' : OracleComp KeccakCalls Bool)
    (k₁ : Bool → OracleComp Common.RandomPermutationOracles β)
    (k₂ : Bool → OracleComp Common.RandomPermutationOracles γ) (E₁ : β → Prop) (E₂ : γ → Prop)
    (hx : x' = x)
    (h0 : ∀ s, Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles (k₁ false)).run' s}[
      E₁ y] = 0)
    (h1 : ∀ s, Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles (k₁ true)).run' s}[
      E₁ y] ≤ Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles (k₂ true)).run' s}[E₂ y])
    (s : Common.PermutationEdges KeccakState) :
    Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles
        (simulateQ keccakCallsOverQueryPermutation x >>= k₁)).run' s}[E₁ y] ≤
      Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles
        (simulateQ keccakCallsOverQueryPermutation x' >>= k₂)).run' s}[E₂ y] := by
  subst hx
  have hk : ∀ b s, Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles (k₁ b)).run' s}[
      E₁ y] ≤ Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles (k₂ b)).run' s}[E₂ y] := by
    intro b s
    cases b
    · rw [h0 s]
      exact bot_le
    · exact h1 s
  exact Soundness.mono_bind _ _ _ _ _ _ hk s

/-- **THE KECCAK VERIFIER BRIDGE**, from the walk (`UniWalkK`, `UniWalkRejectK`) and the chain program's roots
(`UniOutRootsK`). -/
theorem uniVerifierBridgeK_of_walk (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (Fl : KFlockSound F κ keccakMain) (nV V : ℕ) (C : UniCodeK D Fl nV V) (hs : UniShapesK D)
    (hW : UniWalkK D Fl nV V C) (hR : UniWalkRejectK D Fl nV V) (hO : UniOutRootsK D Fl C) :
    UniVerifierBridgeK D Fl nV V C hs := by
  intro π s
  rw [verifyWithK_eq_rest]
  by_cases hlen : π.proof.stream.size = uLenK Fl nV V
  swap
  · -- a stream of another length: the walk rejects
    refine (le_of_eq (Soundness.zero_of_support _ _ _ (fun b hb => ?_) s)).trans zero_le
    rw [mem_support_bind_iff] at hb
    obtain ⟨p, hp, hb⟩ := hb
    rw [support_map] at hp
    obtain ⟨o, ho, rfl⟩ := hp
    simp only [hR π hlen o ho, Bool.not_false, ↓reduceIte, support_pure,
      Set.mem_singleton_iff] at hb
    simp [hb]
  -- the walk is the chain; both sides run it first
  rw [show (kpOf π).stream = π.proof.stream from rfl, hW Common.queryPermutation π hlen, bind_map_left,
    simulateQ_verU]
  refine mono_bind_supp _ _ _ _ _ _ (fun ch hch s => ?_) s
  obtain ⟨hfits, hlch⟩ := doneFits_of_mem_chain (uRoundsK Fl nV V) π ch _ hch
  dsimp only
  cases hacc : uAccBK D Fl nV V C π ch
  · -- the walk's verdict rejects
    rw [ite_eq_left (show (!false) = true from rfl), Soundness.zero_pure _ false _ (by simp) s]
    exact zero_le
  rw [ite_eq_right (show ¬ ((!true) = true) by decide)]
  have hz : (C.prog (uStK Fl nV V π).1 (uStK Fl nV V π).2).ZerosVanish
      (uDone (uRoundsK Fl nV V) π ch) (uTailK (uRoundsK Fl nV V) π) :=
    (@of_decide_eq_true _ (Classical.propDecidable _) hacc).2
  by_cases hg : GoodRK D.shape (uOutK D Fl nV V C π ch)
  swap
  · -- not the main line's result: `verifyWithK` rejects
    refine (le_of_eq (Soundness.zero_of_support _ _ _ (fun b hb hbt => ?_) s)).trans zero_le
    exact hg (restRK_good D.shape (skOf D π.roots) (kpOf π) Common.queryPermutation _ b hb hbt)
  obtain ⟨p1, v1, p2, v2, p3, v3, ho, hm, l1, l2, l3⟩ := hg
  have hwf : WellFormedK D (uOutK D Fl nV V C π ch) := by
    refine ⟨by rw [ho]; rfl, ?_, ?_, ?_, hm⟩
    · simp [claimsOf, ho]; exact l1
    · simp [claimsOf, ho]; exact l2
    · simp [claimsOf, ho]; exact l3
  have hcheck : uniCheckK D Fl nV V C π ch := ⟨hfits, hz, hwf⟩
  -- the point claims
  have hwo : (uOutK D Fl nV V C π ch).openings.map Prod.fst = commitments := by rw [ho]; rfl
  have e1 : ptvK (uOutK D Fl nV V C π ch) .c1 = (p1, v1) := ptvK_of_mem (bs := none) hwo (by rw [ho]; simp)
  have e2 : ptvK (uOutK D Fl nV V C π ch) .c2 = (p2, v2) := ptvK_of_mem (bs := none) hwo (by rw [ho]; simp)
  have e3 : ptvK (uOutK D Fl nV V C π ch) .setup = (p3, v3) := ptvK_of_mem (bs := none) hwo (by rw [ho]; simp)
  -- the rounds' roots
  have hroots : (uOutK D Fl nV V C π ch).roots =
      (((uDone (uRoundsK Fl nV V) π ch).getD 0 default).1.1.getD default,
        ((uDone (uRoundsK Fl nV V) π ch).getD (Fl.prog.rounds.length + 1) default).1.1.getD default) :=
    hO _ _ _ _
  have hr1 : ofB (((msgK (uView (uRoundsK Fl nV V)) π 0).1).getD (Vector.replicate 32 0)) =
      rootOf (uOutK D Fl nV V C π ch).roots.1 := by
    rw [hroots]
    exact root_at _ π ch 0 (by rw [length_uniRounds]; omega) hlch (by
      rw [uniRounds_getD_zero])
  have hr2 : ofB (((msgK (uView (uRoundsK Fl nV V)) π (Fl.prog.rounds.length + 1)).1).getD
      (Vector.replicate 32 0)) = rootOf (uOutK D Fl nV V C π ch).roots.2 := by
    rw [hroots]
    exact root_at _ π ch _ (by rw [length_uniRounds]; omega) hlch (by
      rw [uniRounds_getD_c2])
  -- `verifyWithK`'s three PCS openings, answered over `π`
  rw [restRK_unroll D.shape (skOf D π.roots) (kpOf π) Common.queryPermutation _ p1 v1 p2 v2 p3 v3 ho hm,
    pcsOpenK_eq, pcsOpenK_eq, pcsOpenK_eq]
  -- the composed side's three openings
  unfold uOpsK uniOpsK
  -- C1
  rw [seqAnd_cons, sim_gopsRun_cons]
  refine eq_le_rpm _ _ _ _ _ _ ?_ (fun s => ?_) (fun s => ?_) s
  · show verK D Fl nV V C 0 _ π ch = _
    unfold verK oodK
    simp only [comK]
    rw [e1]
    simp only [GOp.root, opK]
    rw [hr1]
    rfl
  · refine Soundness.zero_of_support _ _ _ (fun x hx => ?_) s
    rw [seqAnd_false _ x hx]
    exact Bool.false_ne_true
  -- C2
  rw [seqAnd_cons, sim_gopsRun_cons]
  refine eq_le_rpm _ _ _ _ _ _ ?_ (fun s => ?_) (fun s => ?_) s
  · show verK D Fl nV V C 1 _ π ch = _
    unfold verK oodK
    simp only [comK]
    rw [e2]
    simp only [GOp.root, opK]
    rw [hr2]
    rfl
  · refine Soundness.zero_of_support _ _ _ (fun x hx => ?_) s
    rw [seqAnd_false _ x hx]
    exact Bool.false_ne_true
  -- the setup
  rw [seqAnd_cons, sim_gopsRun_cons]
  refine eq_le_rpm _ _ _ _ _ _ ?_ (fun s => ?_) (fun s => ?_) s
  · show verK D Fl nV V C 2 _ π ch = _
    unfold verK oodK
    simp only [comK]
    rw [e3]
    rw [show GOp.root (uView (uRoundsK Fl nV V))
        (opK Fl nV V C hs 2 (by decide) (.setup (fun π => toB π.roots.bytecode) (colFK D))) π =
        toB π.roots.bytecode from rfl, Soundness.ofB_toB_root]
    rfl
  · refine Soundness.zero_of_support _ _ _ (fun x hx => ?_) s
    rw [seqAnd_false _ x hx]
    exact Bool.false_ne_true
  -- every opening accepted
  rw [seqAnd, sim_gopsRun_nil, simulateQ_pure]
  refine Soundness.le_pure _ _ _ _ _ (fun _ => ⟨hcheck, fun k hk => ?_⟩) s
  have hk3 : k < 3 := hk
  interval_cases k <;> rfl

end UniKeccakSound

/-- info: 'UniKeccakSound.uniVerifierBridgeK_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniVerifierBridgeK_of_walk
