-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `UniSound/FsVerifier.lean` (`uniVerifierBridge_of_walk`,
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
  `C1`, `C2`, the setup, each of its Keccak layout word's variables, and no matrices' claim: `restRK_good`); on such
  a result it is the **three** calls one after the other (`restRK_unroll`), each F2's `ourVerifierEarly` on the plain
  layout of `2^23 ..= 2^28` words (`pcsOpen_eq_earlyK`), on the composed openings' inputs, so it accepts at most as
  often as the three `ourVerifier`s all do (`UniSound.early_le_rpm`), and its acceptance gives `uniCheckK`.
-/

namespace UniKeccakSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement UniSound UniKeccak
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.layoutWordsK UniKeccak.setupStackK

/-! ## `verifyWithK` after the run -/

section Rest

variable (shape : UniStatement.Shape) (roots : SetupRoots) (proof : KeccakProof)

/-- A commitment's call: its root, its Keccak layout word, its opening proof. -/
def callOfRK (r : Reduced) : Commitment → Digest × List UInt8 × Compile.Proof
  | .c1 => (rootOf r.roots.1, (layoutWordsK shape).getD 0 [], proof.c1)
  | .c2 => (rootOf r.roots.2, (layoutWordsK shape).getD 1 [], proof.c2)
  | .setup => (roots.bytecode, (layoutWordsK shape).getD 2 [], proof.setup)

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- The loop's step over the result's openings. -/
def stepRK (r : Reduced) : Commitment × UniStatement.Opening → Bool → m (ForInStep Bool) :=
  fun x ok => match x with
    | (c, opening) => match opening with
      | .point pt value none => match callOfRK shape roots proof r c with
        | (root, word, p) => do
          let b ← pcsOpenWith F (layoutWordVars word) root [⟨pt, value⟩] p
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

variable (shape : UniStatement.Shape) (roots : SetupRoots) (proof : KeccakProof)
variable {ι : Type} {spec : OracleSpec.{0, 0} ι} (F : KeccakState → OracleComp spec KeccakState)

theorem stepRK_point (r : Reduced) (c : Commitment) (pt : List E) (v : E) (ok : Bool) :
    stepRK shape roots proof F r (c, .point pt v none) ok =
      pcsOpenWith F (layoutWordVars (callOfRK shape roots proof r c).2.1)
          (callOfRK shape roots proof r c).1 [⟨pt, v⟩] (callOfRK shape roots proof r c).2.2 >>=
        fun b => pure (ForInStep.yield (ok && b)) := by
  cases c <;> rfl

theorem stepRK_other (r : Reduced) (c : Commitment) (o : UniStatement.Opening)
    (ho : ∀ pt v, o ≠ .point pt v none) (ok : Bool) :
    stepRK shape roots proof F r (c, o) ok = pure (ForInStep.yield false) := by
  rcases o with _ | ⟨pt, v, _ | _⟩
  · rfl
  · exact absurd rfl (ho pt v)
  · rfl

/-- **An accepting loop** started from `ok`, and met only point claims without a bit slice, each of its layout
word's variables. -/
theorem forIn_stepRK_true (r : Reduced) :
    ∀ (l : List (Commitment × UniStatement.Opening)) (ok : Bool),
      ∀ b ∈ support (forIn l ok (stepRK shape roots proof F r)), b = true →
        ok = true ∧ ∀ x ∈ l, ∃ pt v, x.2 = .point pt v none ∧
          pt.length = layoutWordVars (callOfRK shape roots proof r x.1).2.1
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
      · exact ⟨pt, v, rfl, pcsOpen_len F _ _ _ _ _ b1 hb1 h1.2⟩
      · exact h2 x hx
    · rw [stepRK_other _ _ _ _ _ _ _ (fun pt v h => ho ⟨pt, v, h⟩), support_pure,
        Set.mem_singleton_iff] at hy
      subst hy
      exact absurd (forIn_stepRK_true r l false b hb hbt).1 (by simp)

/-- **The main line's result**: three point claims without a bit slice, on `C1`, `C2` and the setup, each of its
Keccak layout word's variables, and no matrices' claim. -/
def GoodRK (r : Reduced) : Prop :=
  ∃ (p1 : List E) (v1 : E) (p2 : List E) (v2 : E) (p3 : List E) (v3 : E),
    r.openings = [(.c1, .point p1 v1 none), (.c2, .point p2 v2 none),
      (.setup, .point p3 v3 none)] ∧ r.matrices = none ∧
    p1.length = layoutWordVars ((layoutWordsK shape).getD 0 []) ∧
    p2.length = layoutWordVars ((layoutWordsK shape).getD 1 []) ∧
    p3.length = layoutWordVars ((layoutWordsK shape).getD 2 [])

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

/-- **On the main line's result, `restRK` is the three calls**, one after the other. -/
theorem restRK_unroll (r : Reduced) (p1 : List E) (v1 : E) (p2 : List E) (v2 : E) (p3 : List E)
    (v3 : E) (ho : r.openings = [(.c1, .point p1 v1 none), (.c2, .point p2 v2 none),
      (.setup, .point p3 v3 none)]) (hm : r.matrices = none) :
    restRK shape roots proof F r = seqAnd
      [pcsOpenWith F (layoutWordVars ((layoutWordsK shape).getD 0 [])) (rootOf r.roots.1)
          [⟨p1, v1⟩] proof.c1,
        pcsOpenWith F (layoutWordVars ((layoutWordsK shape).getD 1 [])) (rootOf r.roots.2)
          [⟨p2, v2⟩] proof.c2,
        pcsOpenWith F (layoutWordVars ((layoutWordsK shape).getD 2 [])) roots.bytecode
          [⟨p3, v3⟩] proof.setup] true := by
  have hc : (r.openings.map (·.1) == commitments) = true := by
    rw [ho]
    rfl
  rw [restRK, hc, ho, hm]
  simp only [List.forIn_cons, List.forIn_nil, stepRK_point, bind_assoc, pure_bind,
    seqAnd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  rfl

end Support

/-! ## The three openings -/

/-- **`PCS_OPEN` is F2's opening with the Statement's early stop**, on the plain layout of `23 … 28` variables, its
two calls answered over `π`. -/
theorem pcsOpen_eq_earlyK (v : ℕ) (h1 : 23 ≤ v) (h2 : v ≤ 28) (root : Digest)
    (x : Stmt (plainL v).stacking) (cs : List PcsQuotient.Claim)
    (hx : x.claims = cs.map Bridge.claimTr) (p : Compile.Proof) :
    pcsOpenWith Common.queryPermutation v root cs p =
      simulateQ keccakCallsOverQueryPermutation
        (Soundness.ourVerifierEarly (plainL v) logInvRate ((root, x), p)) := by
  rw [pcsOpenWith, Bridge.openingWith_eq_ourVerifier' Common.queryPermutation (plainLayout v)
    (plainL v) (Bridge.layoutTr_ofChunks_zero v v v (2 ^ v)) (Or.inl rfl)
    (admissible_k h1 h2) root x cs hx p, Bridge.keccakCallsWith_queryPermutation]

/-! ## The bridge -/

section Bridge

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain) (nV V : ℕ)
  (C : UniCodeK D Fl nV V)

/-- The claims of the opening of a layout word's variables, its one claim. -/
theorem claims_uClK (k : ℕ) (pt : List E) (v : E) (hl : pt.length = wvK D k) :
    (uClK D k [⟨pt, v⟩]).claims = [(⟨pt, v⟩ : PcsQuotient.Claim)].map Bridge.claimTr :=
  mkStmt_claims _ _ _ (by simp) fun c hc => by
    rw [List.mem_singleton] at hc
    subst hc
    exact hl

theorem wellFormedK_of_good (r : Reduced) (p1 : List E) (v1 : E) (p2 : List E) (v2 : E)
    (p3 : List E) (v3 : E)
    (ho : r.openings = [(.c1, .point p1 v1 none), (.c2, .point p2 v2 none),
      (.setup, .point p3 v3 none)]) (hm : r.matrices = none)
    (l1 : p1.length = wvK D 0) (l2 : p2.length = wvK D 1) (l3 : p3.length = wvK D 2) :
    WellFormedK D r := by
  refine ⟨by rw [ho]; rfl, ?_, ?_, ?_, hm⟩
  · simp [claimsOf, ho, l1]
  · simp [claimsOf, ho, l2]
  · simp [claimsOf, ho, l3]

end Bridge

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
    exact hg (restRK_good D.shape π.roots (kpOf π) Common.queryPermutation _ b hb hbt)
  obtain ⟨p1, v1, p2, v2, p3, v3, ho, hm, l1, l2, l3⟩ := hg
  have l1' : p1.length = wvK D 0 := l1
  have l2' : p2.length = wvK D 1 := l2
  have l3' : p3.length = wvK D 2 := l3
  have hcheck : uniCheckK D Fl nV V C π ch :=
    ⟨hfits, hz, wellFormedK_of_good D _ p1 v1 p2 v2 p3 v3 ho hm l1' l2' l3'⟩
  -- the claims
  have hx1 : (cl1K D Fl nV V C π ch).claims = [(⟨p1, v1⟩ : PcsQuotient.Claim)].map Bridge.claimTr := by
    rw [cl1K, show claimsOf (uOutK D Fl nV V C π ch) .c1 = [⟨p1, v1⟩] by simp [claimsOf, ho]]
    exact claims_uClK D 0 p1 v1 l1'
  have hx2 : (cl2K D Fl nV V C π ch).claims = [(⟨p2, v2⟩ : PcsQuotient.Claim)].map Bridge.claimTr := by
    rw [cl2K, show claimsOf (uOutK D Fl nV V C π ch) .c2 = [⟨p2, v2⟩] by simp [claimsOf, ho]]
    exact claims_uClK D 1 p2 v2 l2'
  have hx3 : (cl3K D Fl nV V C π ch).claims = [(⟨p3, v3⟩ : PcsQuotient.Claim)].map Bridge.claimTr := by
    rw [cl3K, show claimsOf (uOutK D Fl nV V C π ch) .setup = [⟨p3, v3⟩] by simp [claimsOf, ho]]
    exact claims_uClK D 2 p3 v3 l3'
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
  -- `verifyWithK`'s three calls, F2's early-stop openings
  rw [restRK_unroll D.shape π.roots (kpOf π) Common.queryPermutation _ p1 v1 p2 v2 p3 v3 ho hm,
    show layoutWordVars ((layoutWordsK D.shape).getD 0 []) = wvK D 0 from rfl,
    show layoutWordVars ((layoutWordsK D.shape).getD 1 []) = wvK D 1 from rfl,
    show layoutWordVars ((layoutWordsK D.shape).getD 2 []) = wvK D 2 from rfl,
    pcsOpen_eq_earlyK (wvK D 0) (hs.lo 0 (by decide)) (hs.hi 0 (by decide)) _ _ _ hx1,
    pcsOpen_eq_earlyK (wvK D 1) (hs.lo 1 (by decide)) (hs.hi 1 (by decide)) _ _ _ hx2,
    pcsOpen_eq_earlyK (wvK D 2) (hs.lo 2 (by decide)) (hs.hi 2 (by decide)) _ _ _ hx3]
  -- the composed side's three openings
  unfold uOpsK uniOpsK
  -- C1
  rw [seqAnd_cons, sim_opsRun_cons]
  refine early_le_rpm _ _ _ _ _ _ _ _ ?_ (fun s => ?_) (fun s => ?_) s
  · exact Prod.ext (Prod.ext hr1 rfl) rfl
  · refine Soundness.zero_of_support _ _ _ (fun x hx => ?_) s
    rw [seqAnd_false _ x hx]
    exact Bool.false_ne_true
  -- C2
  rw [seqAnd_cons, sim_opsRun_cons]
  refine early_le_rpm _ _ _ _ _ _ _ _ ?_ (fun s => ?_) (fun s => ?_) s
  · exact Prod.ext (Prod.ext hr2 rfl) rfl
  · refine Soundness.zero_of_support _ _ _ (fun x hx => ?_) s
    rw [seqAnd_false _ x hx]
    exact Bool.false_ne_true
  -- the setup
  rw [seqAnd_cons, sim_opsRun_cons]
  refine early_le_rpm _ _ _ _ _ _ _ _ ?_ (fun s => ?_) (fun s => ?_) s
  · exact Prod.ext (Prod.ext (Soundness.ofB_toB_root _) rfl) rfl
  · refine Soundness.zero_of_support _ _ _ (fun x hx => ?_) s
    rw [seqAnd_false _ x hx]
    exact Bool.false_ne_true
  -- every opening accepted
  rw [seqAnd, sim_opsRun_nil, simulateQ_pure]
  refine Soundness.le_pure _ _ _ _ _ (fun _ => ⟨hcheck, fun k hk => ?_⟩) s
  have hk3 : k < 3 := hk
  interval_cases k <;> rfl

end UniKeccakSound

/-- info: 'UniKeccakSound.uniVerifierBridgeK_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniVerifierBridgeK_of_walk
