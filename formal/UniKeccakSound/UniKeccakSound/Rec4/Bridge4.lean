-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The statements are `Fs/WalkK3.lean`'s, `Fs/CoupleK3.lean`'s,
-- `Fs/GameK3.lean`'s and `FinalK3.lean`'s (`FsLayer128K3`) for π1-rec4's verifier in the rate model.
import UniKeccakSound.Rec4.FsOps4
import UniKeccakSound.Rec4.RpmRate
import UniKeccakSound.Fs.LayerK3

/-!
# π1-rec4's Fiat–Shamir layer: the statements

π1-rec4's composed verifier reads Keccak-256's rate (`Compose.KeccakCallsR`): the wide chain over `hashR` (each
round's digest and tail), then the three openings, which read the digest only (`liftR`).

* **`hashRP P`**: Keccak-256 over the permutation `P` as the rate model answers it (`hashR` simulated over the
  permutation is `hashRP Common.queryPermutation`);
* **`verWR`**, **`uVerIvK4`**: the composed verifier, and with the contract's IV (`ivInputK4`: the variant's bytes at
  `keccakRec4`);
* **`UniWalkK4`**, **`UniWalkRejectK4`**, **`UniOutRootsK4`**: the deployed walk (`runWithK4`) is the wide chain on
  streams of π1-rec4's length (`uLen4`) and rejects the others; the chain program names the roots at rounds `0` and
  `28 + κ`;
* **`UniVerifierBridgeK4`**, **`UniExtractBridgeK4`**, **`UniGameLeVK4`**: the coupling's facts and the coupling, of
  `keccakSoundnessExperiment4` with the random-permutation game whose verifier reads the rate (`rpmGameSR`);
* **`FsLayer128K4`**: the Fiat–Shamir layer at `≥ 128` bits for π1-rec4.
-/

namespace UniKeccakSound.Rec4

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement UniSound UniKeccak LeanVM.Semantics
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.setupStackK UniKeccak.setupOodK

/-! ## Keccak-256 over a permutation, as the rate model answers it -/

/-- **Keccak-256 over `P` read as the rate model reads it**: the digest's bytes and the tail. -/
def hashRP {m : Type → Type} [Monad m] (P : KeccakState → m KeccakState) (x : List UInt8) :
    m (Bytes32 × TailP) :=
  (fun st => (toB (digestOfState st), tailOfState st)) <$> keccak256StateWith P x

theorem simulateQ_hashR (x : List UInt8) :
    simulateQ keccakCallsROverQueryPermutation (Compose.hashR x) = hashRP Common.queryPermutation x := by
  rw [Compose.hashR, Compose.callKeccak256R, simulateQ_bind, simulateQ_spec_query]
  simp only [simulateQ_pure]
  show (rateOfState <$> keccak256StateWith Common.queryPermutation x) >>= _ = _
  rw [bind_map_left, hashRP, map_eq_bind_pure_comp]
  rfl

/-! ## The composed verifier -/

section Ver

variable {St M : Type} (W : ChainSpecW E St) (view : UPf → St × List (RMsg E)) (ops : List (GOp UPf E M))

/-- **The composed verifier in the rate model**: the wide chain over Keccak-256's rate, then the openings (on the
digest). -/
def verWR (π : UPf) : OracleComp KeccakCallsR (List (List E) × List Bool) :=
  W.chain Compose.hashR (view π).1 (view π).2 >>= fun ch =>
    simulateQ liftR (gopsRun view ops π ch) >>= fun b => pure (ch, b)

end Ver

/-- **The Keccak contract IV's input at π1-rec4** (`contractIvKWith` at `keccakRec4`). -/
def ivInputK4 (D : KDeployment) (roots : SetupRootsK) : List UInt8 :=
  ivTag ++ D.programIv ++ digestBytes roots.f ++ elementBytes24 roots.fOod ++
    shapeBytes D.shape ++ variantBytesK keccakRec4

/-- **The IV as the composed verifier computes it**: one Keccak-256 call of its input. -/
def ivKCK4 (D : KDeployment) (π : UPf) : OracleComp KeccakCalls Bytes32 := hash256 (ivInputK4 D (skOf D π.roots))

section Verifier

variable (D : KDeployment) (κ nV np : ℕ) (C : UniCodeK4 D κ nV np) (hs : UniShapesK D)

/-- **The composed verifier with the IV** (rate model): the Keccak contract's IV, then the wide chain and the three
openings on the proof carrying it. -/
noncomputable def uVerIvK4 (π : UPf) : OracleComp KeccakCallsR (Bytes32 × (List (List E) × List Bool)) :=
  simulateQ liftR (ivKCK4 D π) >>= fun iv => (fun v => (iv, v)) <$>
    verWR (uSpec4 κ nV np) (uView4 κ nV np) (uOps4 D κ nV np C hs) (setIv iv π)

/-- **The stream's length π1-rec4 reads**: the row counts' `24` bytes, the rounds' messages, the tail's three
scalars. -/
def uLen4 : ℕ := 24 + roundsBytes (rec4Rounds κ nV np) + 24 * 3

/-- **The walk accepts**: the row counts' range checks vanish, and every value the chain program requires zero
does. -/
def UAcc4 (π : UPf) (ch : List (List E)) : Prop :=
  (∀ z ∈ countZeros D.shape.heights (uSt4 κ nV np π).2, z = 0) ∧
    (C.prog (uSt4 κ nV np π).1 (uSt4 κ nV np π).2).ZerosVanish (uDone4 κ nV np π ch) (uTail4 κ nV np π)

open Classical in
/-- `UAcc4` as a verdict. -/
noncomputable def uAccB4 (π : UPf) (ch : List (List E)) : Bool := decide (UAcc4 D κ nV np C π ch)

/-- **WALK** (π1-rec4): on a stream of π1-rec4's length, in every lawful monad and over every permutation, the
deployed walk's verdict and result are the wide chain's challenges (over Keccak-256's rate, `hashRP P`) read by
`uAccB4` and the chain program's result `uOut4`. -/
def UniWalkK4 : Prop :=
  ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (P : KeccakState → m KeccakState) (π : UPf),
    π.proof.stream.size = uLen4 κ nV np →
      (fun o : UniStatement.Outcome => (o.accepts, o.result)) <$>
          runWithK4 P D.shape π.iv.toList π.input.toList π.proof.stream keccakRec4 .point =
        (fun ch => (uAccB4 D κ nV np C π ch,
            (Except.ok (uOut4 D κ nV np C π ch) : Except UniError Reduced))) <$>
          (uSpec4 κ nV np).chain (hashRP P) (uView4 κ nV np π).1 (uView4 κ nV np π).2

/-- **WALK REJECTS** (π1-rec4): on a stream of any other length, every outcome of the deployed walk rejects. -/
def UniWalkRejectK4 : Prop :=
  ∀ π : UPf, π.proof.stream.size ≠ uLen4 κ nV np →
    ∀ o ∈ support (runWithK4 Common.queryPermutation D.shape π.iv.toList π.input.toList
      π.proof.stream keccakRec4 .point), o.accepts = false

/-- **The chain program's result names the roots the transcript carries** at rounds `0` (`C1`) and `28 + κ`
(`C2`). -/
def UniOutRootsK4 : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (done : Done) (tl : List E),
    ((C.prog input rows).out done tl).roots =
      ((done.getD 0 default).1.1.getD default, (done.getD (28 + κ) default).1.1.getD default)

/-- **VERIFIER** (π1-rec4): from any state of the lazily sampled permutation, `verifyWithK4` on a proof accepts at
most as often as the composed verifier (rate model, over the permutation) passes `uniCheck4` with every opening
accepting. -/
def UniVerifierBridgeK4 : Prop :=
  ∀ (π : UPf) (s : Common.PermutationEdges KeccakState),
    Pr{let b ← (simulateQ Common.lazyRandomPermutationOracles
        (verifyWithK4 Common.queryPermutation D.shape keccakRec4 π.iv.toList (skOf D π.roots) π.input
          (kpOf π))).run' s}[b = true] ≤
      Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles
          (simulateQ keccakCallsROverQueryPermutation
            (verWR (uSpec4 κ nV np) (uView4 κ nV np) (uOps4 D κ nV np C hs) π))).run' s}[
        uniCheck4 D κ nV np C π v.1 ∧ ∀ k < (uOps4 D κ nV np C hs).length, v.2.getD k false = true]

/-- **EXTRACTOR READING** (π1-rec4): a candidate stack of `C1`'s root that the composed extractor reads off the
setup's log and a permutation transcript, satisfying the Keccak VM's relation at the proof's statement, makes
`uniExtractorK` find a stack satisfying it. -/
def UniExtractBridgeK4 (F : KeccakVm.KeccakFlockSpec) : Prop :=
  ∀ (t : LeanVM.Prover.Tree) (T : Common.OracleQueryLog) (z : UPf × (List (List E) × List Bool)) (q : Stk),
    some q ∈ extractorK (fun i => (uniTcK hs i).commit) (uView4 κ nV np)
        (z, Soundness.treeTr t ++ evalTr (permutationQueries T)) →
      RelK F D (uSt4 κ nV np z.1) q →
        ∃ q', uniExtractorK F D z.1.input (PcsQuotient.Tree.evaluations t) T (kpOf z.1) = some q' ∧
          D.Relation F (kpOf z.1).rows z.1.input q'

/-- **The coupling** (π1-rec4): the Keccak experiment's break is at most as likely as the random-permutation game's
whose verifier reads Keccak-256's rate (`rpmGameSR`), of the setup's tree, the adversary (`uAdvK`) and the composed
verifier with the IV (`uVerIvK4`). -/
def UniGameLeVK4 (F : KeccakVm.KeccakFlockSpec) : Prop :=
  ∀ A : KAdversary,
    Pr{let z ← keccakSoundnessExperiment4 D A}[KBreaksKnowledgeSoundness F D (uniExtractorK F D) z] ≤
      Pr{let z ← Common.runWithRandomPermutation
          (rpmGameSR (uSetupK D hs) (uFixK D) (uAdvK D A) (uVerIvK4 D κ nV np C hs))}[
        UniBreaksRel4 D κ nV np C hs F (ivOut z.1, z.2.1 ++ evalTr (permutationQueries z.2.2))]

end Verifier

/-- **The Fiat–Shamir layer at `≥ 128` bits at π1-rec4**: every round-by-round sound protocol on its rounds, errors
at most `e`, first state the Keccak VM's relation, last state from the checks with true claims (on the transcript
opened with `C2`'s root at round `28 + κ`), makes the deployed Keccak verifier at `keccakRec4` knowledge sound for
`uniExtractorK F D` with the bound `uniBound128 e`. -/
def FsLayer128K4 (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (κ nV np : ℕ) (C : UniCodeK4 D κ nV np) : Prop :=
  ∀ (R : RbrPiop (rec4Rounds κ nV np) USt Stk) (e : ℝ≥0∞), (∀ j, R.err j ≤ e) →
    (∀ s c m, R.pre s [] (some c, m) → RelK F D s c) →
    (∀ (s : USt) done tl c1 c2, DoneFits (rec4Rounds κ nV np) done → tl.length = 3 →
      (C.prog s.1 s.2).ZerosVanish done tl → ClaimsHoldK D ((C.prog s.1 s.2).out done tl) c1 c2 →
        ∃ p m ch, openedOf (27 + κ) c1 c2 done = p ++ [(m, ch)] ∧ R.post s p m ch) →
    UniKnowledgeSoundnessKeccakRec4 F D (uniBound128 e)

end UniKeccakSound.Rec4
