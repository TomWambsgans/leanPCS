-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The Keccak main line's `Fs/VerifierK.lean` at π1-rec3's
-- shape (`verifyWithK … keccakRec3`), as `UniSound/Rec3/FsVerifier3.lean`.
import UniKeccakSound.Fs.WalkK3
import UniKeccakSound.Fs.VerifierK
import UniKeccakSound.Code.Link3

/-!
# The Keccak verifier bridge at π1-rec3's shape, from the walk

**`uniVerifierBridgeK3_of_walk`**: `UniVerifierBridgeK3` from `UniWalkK3`, `UniWalkRejectK3` and the code-level
link's roots (`UniOutRootsK3`, `Code/Link3.lean`), as `VerifierK.lean`'s: `verifyWithK` after the run is the main
line's `restRK` (the variant enters the run only: `verifyWithK_eq_rest3`), accepting only on `GoodRK`, then the three
calls (`restRK_unroll`), each F2's early-stop opening (`pcsOpen_eq_earlyK`).
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

/-- **`verifyWithK` is the run, then `restRK`** on an accepting run's result. -/
theorem verifyWithK_eq_rest3 [LawfulMonad m] (iv : List UInt8) (input : Vector UInt8 32) :
    verifyWithK F shape keccakRec3 iv roots input proof =
      ((fun o : UniStatement.Outcome => (o.accepts, o.result)) <$>
          runWithK F shape iv input.toList proof.stream keccakRec3 .point) >>= fun p =>
        if !p.1 then pure false else
          match p.2 with
          | .error _ => pure false
          | .ok r => restRK shape roots proof F r := by
  rw [bind_map_left]
  rfl

end Rest

/-- **THE KECCAK VERIFIER BRIDGE**, from the walk (`UniWalkK3`, `UniWalkRejectK3`) and the chain program's roots
(`UniOutRootsK3`). -/
theorem uniVerifierBridgeK3_of_walk (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (nV np : ℕ) (C : UniCodeK3 D F3 nV np) (hs : UniShapesK D)
    (hW : UniWalkK3 D F3 nV np C) (hR : UniWalkRejectK3 D F3 nV np) (hO : UniOutRootsK3 D F3 C) :
    UniVerifierBridgeK3 D F3 nV np C hs := by
  intro π s
  rw [verifyWithK_eq_rest3]
  by_cases hlen : π.proof.stream.size = uLenK3 F3 nV np
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
  obtain ⟨hfits, hlch⟩ := doneFits_of_mem_chain (uRoundsK3 F3 nV np) π ch _ hch
  dsimp only
  cases hacc : uAccBK3 D F3 nV np C π ch
  · -- the walk's verdict rejects
    rw [ite_eq_left (show (!false) = true from rfl), Soundness.zero_pure _ false _ (by simp) s]
    exact zero_le
  rw [ite_eq_right (show ¬ ((!true) = true) by decide)]
  have hz : (C.prog (uStK3 F3 nV np π).1 (uStK3 F3 nV np π).2).ZerosVanish
      (uDone (uRoundsK3 F3 nV np) π ch) (uTailK (uRoundsK3 F3 nV np) π) :=
    (@of_decide_eq_true _ (Classical.propDecidable _) hacc).2
  by_cases hg : GoodRK D.shape (uOutK3 D F3 nV np C π ch)
  swap
  · -- not π1-rec3's result: `verifyWithK` rejects
    refine (le_of_eq (Soundness.zero_of_support _ _ _ (fun b hb hbt => ?_) s)).trans zero_le
    exact hg (restRK_good D.shape (skOf D π.roots) (kpOf π) Common.queryPermutation _ b hb hbt)
  obtain ⟨p1, v1, p2, v2, p3, v3, ho, hm, l1, l2, l3⟩ := hg
  have hwf : WellFormedK D (uOutK3 D F3 nV np C π ch) := by
    refine ⟨by rw [ho]; rfl, ?_, ?_, ?_, hm⟩
    · simp [claimsOf, ho]; exact l1
    · simp [claimsOf, ho]; exact l2
    · simp [claimsOf, ho]; exact l3
  have hcheck : uniCheckK3 D F3 nV np C π ch := ⟨hfits, hz, hwf⟩
  -- the point claims
  have hwo : (uOutK3 D F3 nV np C π ch).openings.map Prod.fst = commitments := by rw [ho]; rfl
  have e1 : ptvK (uOutK3 D F3 nV np C π ch) .c1 = (p1, v1) := ptvK_of_mem (bs := none) hwo (by rw [ho]; simp)
  have e2 : ptvK (uOutK3 D F3 nV np C π ch) .c2 = (p2, v2) := ptvK_of_mem (bs := none) hwo (by rw [ho]; simp)
  have e3 : ptvK (uOutK3 D F3 nV np C π ch) .setup = (p3, v3) := ptvK_of_mem (bs := none) hwo (by rw [ho]; simp)
  -- the rounds' roots
  have hroots : (uOutK3 D F3 nV np C π ch).roots =
      (((uDone (uRoundsK3 F3 nV np) π ch).getD 0 default).1.1.getD default,
        ((uDone (uRoundsK3 F3 nV np) π ch).getD (F3.prog.rounds.length + 1) default).1.1.getD default) :=
    hO _ _ _ _
  have hr1 : ofB (((msgK (uView (uRoundsK3 F3 nV np)) π 0).1).getD (Vector.replicate 32 0)) =
      rootOf (uOutK3 D F3 nV np C π ch).roots.1 := by
    rw [hroots]
    exact root_at _ π ch 0 (by rw [length_rec3Rounds]; omega) hlch (by
      rw [rec3Rounds_zero])
  have hr2 : ofB (((msgK (uView (uRoundsK3 F3 nV np)) π (F3.prog.rounds.length + 1)).1).getD
      (Vector.replicate 32 0)) = rootOf (uOutK3 D F3 nV np C π ch).roots.2 := by
    rw [hroots]
    exact root_at _ π ch _ (by rw [length_rec3Rounds]; omega) hlch (by
      rw [rec3Rounds_c2])
  -- `verifyWithK`'s three PCS openings, answered over `π`
  rw [restRK_unroll D.shape (skOf D π.roots) (kpOf π) Common.queryPermutation _ p1 v1 p2 v2 p3 v3 ho hm,
    pcsOpenK_eq, pcsOpenK_eq, pcsOpenK_eq]
  -- the composed side's three openings
  unfold uOpsK3 uniOpsK3
  -- C1
  rw [seqAnd_cons, sim_gopsRun_cons]
  refine eq_le_rpm _ _ _ _ _ _ ?_ (fun s => ?_) (fun s => ?_) s
  · show verK3 D F3 nV np C 0 _ π ch = _
    unfold verK3 oodK3
    simp only [comK]
    rw [e1]
    simp only [GOp.root, opK3]
    rw [hr1]
    rfl
  · refine Soundness.zero_of_support _ _ _ (fun x hx => ?_) s
    rw [seqAnd_false _ x hx]
    exact Bool.false_ne_true
  -- C2
  rw [seqAnd_cons, sim_gopsRun_cons]
  refine eq_le_rpm _ _ _ _ _ _ ?_ (fun s => ?_) (fun s => ?_) s
  · show verK3 D F3 nV np C 1 _ π ch = _
    unfold verK3 oodK3
    simp only [comK]
    rw [e2]
    simp only [GOp.root, opK3]
    rw [hr2]
    rfl
  · refine Soundness.zero_of_support _ _ _ (fun x hx => ?_) s
    rw [seqAnd_false _ x hx]
    exact Bool.false_ne_true
  -- the setup
  rw [seqAnd_cons, sim_gopsRun_cons]
  refine eq_le_rpm _ _ _ _ _ _ ?_ (fun s => ?_) (fun s => ?_) s
  · show verK3 D F3 nV np C 2 _ π ch = _
    unfold verK3 oodK3
    simp only [comK]
    rw [e3]
    rw [show GOp.root (uView (uRoundsK3 F3 nV np))
        (opK3 F3 nV np C hs 2 (by decide) (.setup (fun π => toB π.roots.bytecode) (colFK D))) π =
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

/-- info: 'UniKeccakSound.uniVerifierBridgeK3_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniVerifierBridgeK3_of_walk
