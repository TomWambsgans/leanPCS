-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the two calls `KeccakCalls` and their simulation lemmas (`implH`, `implF`, `simulateQ_queryH`), and
-- `formal/EndToEnd/Completeness/E2ECompleteness/WithHash.lean`'s `simulateQ_openingWithH`, `simulateQ_commitWithH`.
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/VerifierHSim.lean`.
import UniKeccakComplete.K.VerifierH
import UniKeccakComplete.K.PcsProver

/-!
# The univariate verifier commutes with simulation

The H-copies of `VerifierH.lean` over the two calls (`m := OracleComp KeccakCalls`, `H := callKeccak256`,
`F := callKeccakF1600`) commute with any simulation `impl`: **`simulateQ_verifierWithH`**,
**`simulateQ_setupTreeKWithH`**, as WithHash's `simulateQ_verifyWithH`, `simulateQ_commitWithH`.

The verifier runs in the channel's monad `ChanM m = ExceptT UniError (StateT Chan m)`, with loops (`forIn`) over
lists and ranges. So the commutation is proved once for **any monad morphism** (`Morph`: a map of computations
that keeps `pure` and `bind`), of which `simulateQ impl` is one (`Morph.sim`):

* `Morph.chan` lifts a morphism `m → n` to the channel's monads (the state and the error pass through), and keeps
  `pure`, `bind`, `get`, `set`, `modify`, `throw`, the lift of `m`, `<$>`, `if` and the loops (`chan_…`);
* every function of the verifier commutes with it, the hash `H` becoming `φ ∘ H` (`chan_sampleH`, …,
  `chan_reduceWithH`; the Statement's non-hashing helpers keep their form, `chan_nextScalar`, …);
* at the monad's level, the run, the IV and, given that the opening commutes (`hopen`, which WithHash proves for
  `simulateQ`), the verifier (`app_runWithH`, `app_verifyWithH`, **`app_verifierWithH`**).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH simulateQ_queryF)
open UniStatement

namespace UniKeccakComplete

/-- **A monad morphism**: a map of computations keeping `pure` and `bind`. -/
structure Morph (m n : Type → Type) [Monad m] [Monad n] where
  app : {α : Type} → m α → n α
  app_pure : ∀ {α : Type} (a : α), app (pure a) = pure a
  app_bind : ∀ {α β : Type} (x : m α) (f : α → m β), app (x >>= f) = app x >>= fun a ↦ app (f a)

namespace Morph

section Basic

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (φ : Morph m n)

/-- **The morphism on the channel's monad**: the state and the error pass through. -/
def chan {α : Type} (x : ChanM m α) : ChanM n α :=
  ExceptT.mk fun c ↦ φ.app (x.run.run c)

omit [Monad n] [LawfulMonad n] in
theorem chan_ext {α : Type} {x y : ChanM n α} (h : ∀ c, x.run.run c = y.run.run c) : x = y := funext h

omit [LawfulMonad m] [LawfulMonad n] in
theorem chan_run {α : Type} (x : ChanM m α) (c : Chan) : (φ.chan x).run.run c = φ.app (x.run.run c) := rfl

theorem app_map {α β : Type} (f : α → β) (x : m α) : φ.app (f <$> x) = f <$> φ.app x := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, φ.app_bind]
  simp only [Function.comp_def, φ.app_pure]

omit [LawfulMonad m] [LawfulMonad n] in
theorem app_ite {α : Type} (c : Prop) [Decidable c] (x y : m α) :
    φ.app (if c then x else y) = if c then φ.app x else φ.app y := by
  split <;> rfl

omit [LawfulMonad m] [LawfulMonad n] in
/-- A loop over a list. -/
theorem app_forIn_list {α β : Type} (l : List α) (b : β) (f : α → β → m (ForInStep β)) :
    φ.app (forIn l b f) = forIn l b fun a s ↦ φ.app (f a s) := by
  induction l generalizing b with
  | nil => exact φ.app_pure b
  | cons a l ih =>
    simp only [List.forIn_cons, φ.app_bind]
    congr 1
    funext s
    cases s with
    | done b => exact φ.app_pure b
    | yield b => exact ih b

omit [LawfulMonad m] [LawfulMonad n] in
theorem chan_pure {α : Type} (a : α) : φ.chan (pure a : ChanM m α) = pure a :=
  chan_ext fun c ↦ φ.app_pure (Except.ok a, c)

omit [LawfulMonad m] [LawfulMonad n] in
theorem chan_bind {α β : Type} (x : ChanM m α) (f : α → ChanM m β) :
    φ.chan (x >>= f) = φ.chan x >>= fun a ↦ φ.chan (f a) := by
  refine chan_ext fun c ↦ ?_
  simp only [chan_run, ExceptT.run_bind, StateT.run_bind, φ.app_bind]
  congr 1
  funext p
  obtain ⟨e, s⟩ := p
  cases e with
  | error e => exact φ.app_pure _
  | ok a => rfl

theorem chan_get : φ.chan (get : ChanM m Chan) = get := by
  refine chan_ext fun c ↦ ?_
  show φ.app ((Except.ok <$> (get : StateT Chan m Chan)).run c) =
    (Except.ok <$> (get : StateT Chan n Chan)).run c
  simp only [StateT.run_map, StateT.run_get, app_map, φ.app_pure]

theorem chan_set (s : Chan) : φ.chan (set s : ChanM m PUnit) = set s := by
  refine chan_ext fun c ↦ ?_
  show φ.app ((Except.ok <$> (set s : StateT Chan m PUnit)).run c) =
    (Except.ok <$> (set s : StateT Chan n PUnit)).run c
  simp only [StateT.run_map, StateT.run_set, app_map, φ.app_pure]

theorem chan_modify (f : Chan → Chan) : φ.chan (modify f : ChanM m PUnit) = modify f := by
  refine chan_ext fun c ↦ ?_
  show φ.app ((Except.ok <$> (modifyGet (fun s ↦ (PUnit.unit, f s)) : StateT Chan m PUnit)).run c) =
    (Except.ok <$> (modifyGet (fun s ↦ (PUnit.unit, f s)) : StateT Chan n PUnit)).run c
  simp only [StateT.run_map, StateT.run_modifyGet, app_map, φ.app_pure]

omit [LawfulMonad m] [LawfulMonad n] in
theorem chan_throw {α : Type} (e : UniError) : φ.chan (throw e : ChanM m α) = throw e := by
  refine chan_ext fun c ↦ ?_
  simp [chan_run, φ.app_pure]

theorem chan_lift {α : Type} (y : m α) : φ.chan (monadLift y : ChanM m α) = monadLift (φ.app y) := by
  refine chan_ext fun c ↦ ?_
  show φ.app ((Except.ok <$> (monadLift y : StateT Chan m α)).run c) =
    (Except.ok <$> (monadLift (φ.app y) : StateT Chan n α)).run c
  simp only [StateT.run_map, StateT.run_monadLift, monadLift_self, app_map, φ.app_bind, φ.app_pure]

theorem chan_map {α β : Type} (f : α → β) (x : ChanM m α) : φ.chan (f <$> x) = f <$> φ.chan x := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, chan_bind]
  simp only [Function.comp_def, chan_pure]

omit [LawfulMonad m] [LawfulMonad n] in
theorem chan_ite {α : Type} (c : Prop) [Decidable c] (x y : ChanM m α) :
    φ.chan (if c then x else y) = if c then φ.chan x else φ.chan y := by
  split <;> rfl

omit [LawfulMonad m] [LawfulMonad n] in
/-- A loop over a list. -/
theorem chan_forIn_list {α β : Type} (l : List α) (b : β) (f : α → β → ChanM m (ForInStep β)) :
    φ.chan (forIn l b f) = forIn l b fun a s ↦ φ.chan (f a s) := by
  induction l generalizing b with
  | nil => exact chan_pure φ b
  | cons a l ih =>
    simp only [List.forIn_cons, chan_bind]
    congr 1
    funext s
    cases s with
    | done b => exact chan_pure φ b
    | yield b => exact ih b

omit [LawfulMonad m] [LawfulMonad n] in
/-- A loop over a range. -/
theorem chan_forIn_range {β : Type} (r : Std.Legacy.Range) (b : β) (f : ℕ → β → ChanM m (ForInStep β)) :
    φ.chan (forIn r b f) = forIn r b fun a s ↦ φ.chan (f a s) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range', chan_forIn_list]

/-! ### The Statement's channel helpers keep their form -/

theorem chan_takeBytes (k : ℕ) : φ.chan (takeBytes (m := m) k) = takeBytes k := by
  unfold takeBytes
  simp only [chan_bind, chan_get]
  congr 1; funext c
  split
  · simp only [chan_bind, chan_set, chan_pure]
  · exact chan_throw φ _

theorem chan_nextScalar : φ.chan (nextScalar (m := m)) = nextScalar := by
  simp only [nextScalar, chan_bind, chan_takeBytes, chan_pure]

theorem chan_nextInteger (bytes : ℕ) : φ.chan (nextInteger (m := m) bytes) = nextInteger bytes := by
  simp only [nextInteger, chan_bind, chan_takeBytes, chan_pure]

theorem chan_nextScalars (count : ℕ) : φ.chan (nextScalars (m := m) count) = nextScalars count := by
  simp only [nextScalars, chan_bind, chan_forIn_range, chan_nextScalar, chan_pure]

theorem chan_nextRoot : φ.chan (nextRoot (m := m)) = nextRoot := by
  simp only [nextRoot, chan_bind, chan_takeBytes, chan_pure]

theorem chan_requireZero (value : E) : φ.chan (requireZero (m := m) value) = requireZero value := by
  simp only [requireZero, chan_modify]

theorem chan_finish : φ.chan (finish (m := m)) = finish := by
  unfold finish
  simp only [chan_bind, chan_get]
  congr 1; funext c
  split
  · exact chan_pure φ _
  · exact chan_throw φ _

theorem chan_roundPoly (count : ℕ) (claim : E) (e : Option E) :
    φ.chan (roundPoly (m := m) count claim e) = roundPoly count claim e := by
  unfold roundPoly
  split <;> simp only [chan_bind, chan_nextScalar, chan_nextScalars, chan_pure]

theorem chan_countBits (heights : List ℕ) : φ.chan (countBits (m := m) heights) = countBits heights := by
  simp only [countBits, chan_bind, chan_forIn_list, chan_nextInteger, chan_requireZero, chan_pure]

theorem chan_tablePart (t : Table) (logHeight : ℕ) (weights : Array E) (beta : E) (w : List E) :
    φ.chan (tablePart (m := m) t logHeight weights beta w) = tablePart t logHeight weights beta w := by
  simp only [tablePart, chan_bind, chan_forIn_list, chan_nextScalar, chan_pure, chan_ite]

end Basic

/-! ### The verifier's functions -/

section Verifier

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (φ : Morph m n)
  (H : List UInt8 → m Digest)

theorem chan_sampleH : φ.chan (sampleH H) = sampleH fun x ↦ φ.app (H x) := by
  simp only [sampleH, chan_bind, chan_get, chan_lift, chan_set, chan_pure]

theorem chan_samplesH (count : ℕ) :
    φ.chan (samplesH H count) = samplesH (fun x ↦ φ.app (H x)) count := by
  simp only [samplesH, chan_bind, chan_forIn_range, chan_sampleH, chan_pure]

theorem chan_sumcheckH (claim : E) (count : ℕ) (equalities : List (Option E)) :
    φ.chan (sumcheckH H claim count equalities) = sumcheckH (fun x ↦ φ.app (H x)) claim count equalities := by
  simp only [sumcheckH, chan_bind, chan_forIn_list, chan_roundPoly, chan_sampleH, chan_pure]

theorem chan_sampleNarrowH : φ.chan (sampleNarrowH H) = sampleNarrowH fun x ↦ φ.app (H x) := by
  simp only [sampleNarrowH, chan_bind, chan_get, chan_lift, chan_set, chan_pure]

theorem chan_sampleDrawnH (narrow : Bool) :
    φ.chan (sampleDrawnH H narrow) = sampleDrawnH (fun x ↦ φ.app (H x)) narrow := by
  cases narrow
  · exact chan_sampleH φ H
  · exact chan_sampleNarrowH φ H

theorem chan_drawRunH (fs : FsShape) (count : ℕ) :
    φ.chan (drawRunH H fs count) = drawRunH (fun x ↦ φ.app (H x)) fs count := by
  cases fs <;> simp only [drawRunH, chan_samplesH, chan_ite, chan_pure, chan_bind, chan_sampleH]

theorem chan_sumcheckDrawnH (claim : E) (count : ℕ) (equalities : List (Option E)) (narrow : Bool) :
    φ.chan (sumcheckDrawnH H claim count equalities narrow) =
      sumcheckDrawnH (fun x ↦ φ.app (H x)) claim count equalities narrow := by
  simp only [sumcheckDrawnH, chan_bind, chan_forIn_list, chan_roundPoly, chan_sampleDrawnH, chan_pure]

/-- The pair's round polynomial only reads. -/
theorem chan_pairRoundPoly (degree : ℕ) (claim : E) :
    φ.chan (pairRoundPoly (m := m) degree claim) = pairRoundPoly degree claim := by
  simp only [pairRoundPoly, chan_bind, chan_nextScalars, chan_pure]

theorem chan_sumcheckPairsDrawnH (claim : E) (degree vars : ℕ) (narrow : Bool) :
    φ.chan (sumcheckPairsDrawnH H claim degree vars narrow) =
      sumcheckPairsDrawnH (fun x ↦ φ.app (H x)) claim degree vars narrow := by
  simp only [sumcheckPairsDrawnH, chan_bind, chan_forIn_range, chan_pairRoundPoly, chan_sampleDrawnH, chan_pure,
    chan_ite, chan_sumcheckDrawnH]

theorem chan_zerocheckFsH (logN k : ℕ) (fs : FsShape) :
    φ.chan (Flock.zerocheckFsH H logN k fs) = Flock.zerocheckFsH (fun x ↦ φ.app (H x)) logN k fs := by
  simp only [Flock.zerocheckFsH, chan_bind, chan_drawRunH, chan_ite, chan_nextScalars, chan_sampleH, chan_pure,
    chan_sumcheckH, chan_nextScalar]

theorem chan_ringEndH (variant : UniStatement.Flock.Variant) (s : List E) :
    φ.chan (Flock.ringEndH H variant s) = Flock.ringEndH (fun x ↦ φ.app (H x)) variant s := by
  simp only [Flock.ringEndH, chan_bind, chan_samplesH, chan_pure]

theorem chan_frontKH (logN : ℕ) (v : UniKeccak.KeccakVariant) :
    φ.chan (frontKH H logN v) = frontKH (fun x ↦ φ.app (H x)) logN v := by
  simp only [frontKH, chan_bind, chan_zerocheckFsH, chan_sampleH, chan_sumcheckH, chan_pure, chan_nextScalars]

theorem chan_verifyWalkedKH (logN : ℕ) (v : UniKeccak.KeccakVariant) :
    φ.chan (verifyWalkedKH H logN v) = verifyWalkedKH (fun x ↦ φ.app (H x)) logN v := by
  simp only [verifyWalkedKH, chan_bind, chan_frontKH, chan_requireZero, chan_ringEndH, chan_pure]

set_option linter.unusedSimpArgs false in
theorem chan_batchKH (fs : FsShape) (combined : List (Commitment × Combined))
    (layouts : List (Commitment × StackLayout)) (ringMap : Option (List E)) :
    φ.chan (batchKH H fs combined layouts ringMap) = batchKH (fun x ↦ φ.app (H x)) fs combined layouts ringMap := by
  cases fs <;>
    simp only [batchKH, chan_bind, chan_sampleH, chan_sumcheckPairsDrawnH, chan_sumcheckDrawnH,
      chan_nextScalars, chan_nextScalar, chan_pure, pure_bind, chan_ite, chan_requireZero]

/-- Push the morphism through the walk's binds (the lemmas above). -/
macro "chan_pushK" : tactic => `(tactic| simp only [chan_bind, chan_ite, chan_throw, chan_pure, chan_countBits,
  chan_nextRoot, chan_drawRunH, chan_sampleH, chan_verifyWalkedKH, chan_forIn_list, chan_tablePart, chan_nextScalar,
  chan_batchKH, pure_bind])

/-- The walk's closing tactic: push the morphism through the binds, then strip the common prefix of binds and split
the matches the pushing stopped at, pushing again inside, until both sides agree. -/
macro "chan_closeK" : tactic => `(tactic| (chan_pushK; repeat (first
  | with_reducible rfl
  | (with_reducible refine bind_congr fun _ ↦ ?_)
  | split
  | chan_pushK)))

/-- **The Keccak walk commutes with the morphism**, at every variant and claims mode. -/
theorem chan_reduceWithKH (shape : UniStatement.Shape) (publicWords : List E) (v : UniKeccak.KeccakVariant) (mode : ClaimsMode) :
    φ.chan (reduceWithKH H shape publicWords v mode) =
      reduceWithKH (fun x ↦ φ.app (H x)) shape publicWords v mode := by
  unfold reduceWithKH
  chan_closeK

/-! ### The run, the IV, the verifier -/

omit [LawfulMonad m] [LawfulMonad n] in
theorem app_seedWithH (iv publicInput : List UInt8) :
    φ.app (seedWithH H iv publicInput) = seedWithH (fun x ↦ φ.app (H x)) iv publicInput := rfl

theorem app_runWithKH (shape : UniStatement.Shape) (iv publicInput : List UInt8) (stream : Array UInt8)
    (v : UniKeccak.KeccakVariant) (mode : ClaimsMode) :
    φ.app (runWithKH H shape iv publicInput stream v mode) =
      runWithKH (fun x ↦ φ.app (H x)) shape iv publicInput stream v mode := by
  simp only [runWithKH, φ.app_bind, app_seedWithH, φ.app_pure, ← chan_run φ, chan_bind, chan_reduceWithKH,
    chan_finish, chan_pure]

omit [LawfulMonad m] [LawfulMonad n] in
theorem app_contractIvKWithH (s : UniStatement.Shape) (v : UniKeccak.KeccakVariant) (programIv : List UInt8)
    (roots : UniKeccak.SetupRootsK) :
    φ.app (contractIvKWithH H s v programIv roots) = contractIvKWithH (fun x ↦ φ.app (H x)) s v programIv roots := by
  simp only [contractIvKWithH, φ.app_bind, φ.app_pure]

omit [LawfulMonad m] [LawfulMonad n] in
theorem app_ivWithH (D : UniKeccak.KDeployment) (v : UniKeccak.KeccakVariant) (roots : UniKeccak.SetupRootsK) :
    φ.app (KDeployment.ivWithH H D v roots) =
      KDeployment.ivWithH (fun x ↦ φ.app (H x)) D v roots :=
  app_contractIvKWithH φ H _ _ _ _

variable (F : KeccakState → m KeccakState)

omit [LawfulMonad m] [LawfulMonad n] in
/-- A claim's opening commutes with a monad morphism that commutes with the PCS check. -/
theorem app_pcsOpenKH
    (hopen : ∀ (n : ℕ) (zOf : Digest → Vector E n) (x : WhirBridge.Pcs.Claim1 n)
      (proof : LeanVM.Protocol.Compile.Proof),
      φ.app (WhirBridge.Pcs.pcsVerifyWithHash H F zOf x proof) =
        WhirBridge.Pcs.pcsVerifyWithHash (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) zOf x proof)
    (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E) (p : LeanVM.Protocol.Compile.Proof) :
    φ.app (pcsOpenKH H F n root ood pt v p) = pcsOpenKH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) n root ood pt v p := by
  unfold pcsOpenKH
  split
  · exact hopen _ _ _ _
  · exact φ.app_pure _

/-- **The Keccak verifier commutes with a monad morphism that commutes with the PCS check** (`hopen`,
`simulateQ_pcsVerify` for `simulateQ`). -/
theorem app_verifyWithKH
    (hopen : ∀ (n : ℕ) (zOf : Digest → Vector E n) (x : WhirBridge.Pcs.Claim1 n)
      (proof : LeanVM.Protocol.Compile.Proof),
      φ.app (WhirBridge.Pcs.pcsVerifyWithHash H F zOf x proof) =
        WhirBridge.Pcs.pcsVerifyWithHash (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) zOf x proof)
    (shape : UniStatement.Shape) (v : UniKeccak.KeccakVariant) (iv : List UInt8) (roots : UniKeccak.SetupRootsK)
    (publicInput : Vector UInt8 32) (proof : UniKeccak.KeccakProof) :
    φ.app (verifyWithKH H F shape v iv roots publicInput proof) =
      verifyWithKH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) shape v iv roots publicInput proof := by
  simp only [verifyWithKH, φ.app_bind, app_runWithKH]
  congr 1; funext o
  split
  · exact φ.app_pure _
  · split
    · exact φ.app_pure _
    · simp only [φ.app_bind, app_forIn_list]
      congr 1
      · congr 1; funext x s
        split
        · simp only [φ.app_bind, φ.app_pure, app_pcsOpenKH φ H F hopen]
        · exact φ.app_pure _
      · funext s
        split <;> exact φ.app_pure _

/-- **The deployed Keccak verifier commutes with a monad morphism that commutes with the opening.** -/
theorem app_verifierWithH
    (hopen : ∀ (n : ℕ) (zOf : Digest → Vector E n) (x : WhirBridge.Pcs.Claim1 n)
      (proof : LeanVM.Protocol.Compile.Proof),
      φ.app (WhirBridge.Pcs.pcsVerifyWithHash H F zOf x proof) =
        WhirBridge.Pcs.pcsVerifyWithHash (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) zOf x proof)
    (D : UniKeccak.KDeployment) (v : UniKeccak.KeccakVariant) (roots : UniKeccak.SetupRootsK) (input : Vector UInt8 32)
    (proof : UniKeccak.KeccakProof) :
    φ.app (KDeployment.verifierWithH H F D v roots input proof) =
      KDeployment.verifierWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) D v roots input proof := by
  simp only [KDeployment.verifierWithH, φ.app_bind, app_ivWithH, app_verifyWithKH φ H F hopen]

end Verifier

end Morph

end UniKeccakComplete

/-! ## Over the two calls: `simulateQ` -/

namespace UniKeccakComplete

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

/-- **`simulateQ impl` is a monad morphism**, for any oracles. -/
def Morph.sim {ι : Type} {spec : OracleSpec.{0, 0} ι} {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl spec r) : Morph (OracleComp spec) r :=
  ⟨fun x ↦ simulateQ impl x, fun a ↦ simulateQ_pure impl a, fun x f ↦ simulateQ_bind impl x f⟩

theorem Morph.sim_H : (fun x ↦ (Morph.sim impl).app (callKeccak256 x)) = implH impl :=
  funext fun x ↦ simulateQ_queryH impl x

theorem Morph.sim_F : (fun s ↦ (Morph.sim impl).app (callKeccakF1600 s)) = implF impl :=
  funext fun s ↦ simulateQ_queryF impl s

/-- **The deployed Keccak verifier over the two calls commutes with any simulation.** -/
theorem simulateQ_verifierWithH (D : UniKeccak.KDeployment) (v : UniKeccak.KeccakVariant) (roots : UniKeccak.SetupRootsK)
    (input : Vector UInt8 32) (proof : UniKeccak.KeccakProof) :
    simulateQ impl (KDeployment.verifierWithH callKeccak256 callKeccakF1600 D v roots input proof) =
      KDeployment.verifierWithH (implH impl) (implF impl) D v roots input proof := by
  have h := Morph.app_verifierWithH (Morph.sim impl) callKeccak256 callKeccakF1600
    (fun n zOf x proof ↦ by
      rw [Morph.sim_H, Morph.sim_F]
      exact simulateQ_pcsVerify impl zOf x proof) D v roots input proof
  rw [Morph.sim_H, Morph.sim_F] at h
  exact h

/-- **The setup over the two calls commutes with any simulation.** -/
theorem simulateQ_setupTreeKWithH (D : UniKeccak.KDeployment) :
    simulateQ impl (setupTreeKWithH callKeccak256 callKeccakF1600 D) =
      setupTreeKWithH (implH impl) (implF impl) D := by
  simp only [setupTreeKWithH, E2ECompleteness.simulateQ_commitWithH]

end Commute

end UniKeccakComplete

/-- info: 'UniKeccakComplete.simulateQ_verifierWithH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.simulateQ_verifierWithH

/-- info: 'UniKeccakComplete.simulateQ_setupTreeKWithH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.simulateQ_setupTreeKWithH

/-- info: 'UniKeccakComplete.Morph.app_verifierWithH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.Morph.app_verifierWithH
