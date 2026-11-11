-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `formal/Compose/Compose/Rpm.lean` of this repository (`map_wiredExp`, `le_wiredExp`: the
-- deterministic adversary's experiment, the event on its cache, bounded by the composition's run) to the
-- deployed run of the EIP's PCS claims (`formal/SoundPcs`, `dExp`).
import Soundness.PcsRpm
import SoundPcs
import Soundness.TreeLog

/-!
# The two-oracle game is bounded by the deployed run

`rpm_le_romG` (`PcsRpm.lean`) ends at a two-oracle game: the setup `S`, one deterministic adversary `A'`, the
verifier `V` from the cache they leave, the event holding of every transcript of that cache. Here it is bounded
by `SoundPcs`'s deployed run `dExp` (the setup `setupPcs`, the adversary, the chain, the claims, the three
openings), for a setup whose output `setupPcs` reads (`hS : setup' = φ <$> S`) and an adversary converted to
`dExp`'s (`conv`):

* `verS`, **`map_dExp`**: what `BreaksD` reads of `dExp`'s outcome (the protocol state and the verdict) is the
  adversary's run, logged, the chain, then the three gated openings (`verS`), the stages' logs dropped;
* **`le_dExp`**: given, for every outcome of the setup and the adversary and every cache it may leave, that the
  verifier's event from that cache is at most as likely as `BreaksD`'s after the chain and the openings on the
  converted proof with any transcript of the cache as the adversary's log (`hcmp`), the game is bounded by
  `dExp`'s `BreaksD`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace PcsKS

open Compose ComposePcs QuotientRpm QuotientSecurity LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Protocol.Compile LeanVM.Parameters WhirBridge WhirBridge.Pcs SoundPcs

variable {P : Kc3.Params E} (W : Wire2 P) (O : OpenSpec)

/-! ## The three gated openings -/

/-- **The three openings**, each run only if the ones before accepted (`dExp`'s stages, logs dropped). -/
def verS (a : S0) : OracleComp KeccakCalls Bool :=
  optV (O.V 24) (inW a) >>= fun b1 =>
  optV (O.V 24) (SoundPcs.gate b1 (inσ a)) >>= fun b2 =>
  optV (O.V 28) (SoundPcs.gate (b1 && b2) (inT a)) >>= fun b3 =>
  pure ((b1 && b2) && b3)

/-- A stage followed by a continuation that does not read its log. -/
theorem stage_bind {α γ : Type} (pre : OracleComp KeccakCalls α) (V : α → OracleComp KeccakCalls Bool)
    (K : α × Bool → OracleComp KeccakCalls γ) :
    (stage pre V >>= fun z => K z.1) = pre >>= fun a => V a >>= fun b => K (a, b) := by
  unfold stage
  rw [bind_logged_fst _ [] (fun z => K z.1) K (fun _ => rfl)]
  simp only [bind_assoc, bind_map_left]

/-- What `BreaksD` reads of an outcome of `dExp`: the protocol state and the verdict. -/
def projD (z : X3) : S0 × Bool := (z.s, z.ok)

/-- One more gated opening, as a stage, its log dropped. -/
theorem map_stage_gate {α : Type} (e : OracleComp KeccakCalls α) (s : α → S0) (ok : α → Bool) (n : ℕ)
    (inp : S0 → Option (Claim1 n × Proof)) :
    (fun z : (α × Bool) × Transcript => (s z.1.1, ok z.1.1 && z.1.2)) <$>
        stage e (fun x => optV (O.V n) (SoundPcs.gate (ok x) (inp (s x)))) =
      ((fun x => (s x, ok x)) <$> e) >>= fun p =>
        (fun b => (p.1, p.2 && b)) <$> optV (O.V n) (SoundPcs.gate p.2 (inp p.1)) := by
  rw [map_eq_bind_pure_comp]
  change (stage e _ >>= fun z => (fun w : α × Bool =>
    (pure (s w.1, ok w.1 && w.2) : OracleComp KeccakCalls (S0 × Bool))) z.1) = _
  rw [stage_bind e _ (fun w : α × Bool =>
    (pure (s w.1, ok w.1 && w.2) : OracleComp KeccakCalls (S0 × Bool))), bind_map_left]
  refine bind_congr fun x => ?_
  rw [map_eq_bind_pure_comp]
  rfl

/-- The first opening, as a stage, its log dropped. -/
theorem map_stage_first (A : OracleComp KeccakCalls (RootProof2 E × Rest)) :
    (fun z : X1 => (X1.s z, X1.ok z)) <$> e1 W O A =
      DA2 W A >>= fun a => (fun b => (a, b)) <$> optV (O.V 24) (inW a) := by
  unfold e1
  rw [map_eq_bind_pure_comp]
  change (stage (DA2 W A) _ >>= fun z => (fun w : S0 × Bool =>
    (pure (w.1, w.2) : OracleComp KeccakCalls (S0 × Bool))) z.1) = _
  rw [stage_bind]
  refine bind_congr fun a => ?_
  rw [map_eq_bind_pure_comp]
  rfl

/-- **The stages' logs past the adversary's are not read**: what `BreaksD` reads of `dExp` is the adversary
and the chain (`DA2`), then the three gated openings. -/
theorem map_dExp (A : OracleComp KeccakCalls (RootProof2 E × Rest)) :
    projD <$> dExp W O A = DA2 W A >>= fun a => (fun ok => (a, ok)) <$> verS O a := by
  have h3 := map_stage_gate O (e2 W O A) X2.s X2.ok 28 inT
  have h2 := map_stage_gate O (e1 W O A) X1.s X1.ok 24 inσ
  have h1 := map_stage_first W O A
  have e3 : projD <$> dExp W O A = (fun z : X3 => (X2.s z.1.1, X2.ok z.1.1 && z.1.2)) <$>
      stage (e2 W O A) (fun x => optV (O.V 28) (SoundPcs.gate (X2.ok x) (inT (X2.s x)))) := rfl
  have e2' : (fun x : X2 => (X2.s x, X2.ok x)) <$> e2 W O A =
      (fun z : X2 => (X1.s z.1.1, X1.ok z.1.1 && z.1.2)) <$>
        stage (e1 W O A) (fun x => optV (O.V 24) (SoundPcs.gate (X1.ok x) (inσ (X1.s x)))) := rfl
  rw [e3, h3, e2', h2, h1]
  simp only [verS, bind_assoc, map_eq_bind_pure_comp, Function.comp_def, pure_bind]

/-! ## The bound -/

/-- The protocol state after the chain, and the three gated openings, on a proof and a log. -/
def contD (po : RootProof2 E × Rest) (tA : Transcript) : OracleComp KeccakCalls (S0 × Bool) :=
  chainWith2 W hash256 po.1 >>= fun ch =>
    (fun ok => ((⟨po.1, po.2, tA, ch⟩ : S0), ok)) <$> verS O ⟨po.1, po.2, tA, ch⟩

/-- The proof the verifier reads: the adversary's, with the setup's commitment. -/
def setc (c : Bytes32 × E) (po : RootProof2 E × Rest) : RootProof2 E × Rest :=
  ({ po.1 with ir := c.1, io := c.2 }, po.2)

/-- `BreaksD` on what it reads. -/
def BreaksDP (cW : TableCode P.Msg₁) (z : S0 × Bool) : Prop :=
  z.2 = true ∧ ∀ g ∈ adversaryExtractor2 cW z.1.tA z.1.π, ¬ P.Sat (W.decode z.1.π.stmt) (P.cells g.1)

theorem breaksD_iff (cW : TableCode P.Msg₁) (z : X3) : BreaksD W cW z ↔ BreaksDP W cW (projD z) :=
  Iff.rfl

theorem DA2_bind {γ : Type} (A : OracleComp KeccakCalls (RootProof2 E × Rest))
    (k : S0 → OracleComp KeccakCalls γ) :
    DA2 W A >>= k = loggedKC A >>= fun pt =>
      chainWith2 W hash256 pt.1.1 >>= fun ch => k ⟨pt.1.1, pt.1.2, pt.2, ch⟩ := by
  simp only [DA2, bind_assoc, pure_bind]

variable {σ₀ α : Type}

/-- **The two-oracle game is bounded by the deployed run**: for a setup `S` whose output `setupPcs q₀`
reads (`hS`), an adversary `A'` whose output `conv0` converts, and a verifier `V` whose event from any cache
is at most as likely as `BreaksD`'s after the chain and the openings on the converted proof with the setup's
commitment, any transcript of that cache as the adversary's log (`hcmp`). -/
theorem le_dExp (cW : TableCode P.Msg₁) (S : OracleComp KeccakCalls σ₀) (φ : σ₀ → Bytes32 × E)
    (q₀ : Column 24) (hS : setupPcs q₀ = φ <$> S) (conv0 : α → RootProof2 E × Rest)
    (A' : OracleComp KeccakCalls α) (V : σ₀ → α → OracleComp KeccakCalls Bool)
    (Ev : σ₀ → α → Bool → Transcript → Prop)
    (hcmp : ∀ x a (c : KeccakCalls.QueryCache) (tA : Transcript), Consistent tA c →
      Pr{let v ← (simulateQ randomOracle (V x a)).run' c}[Ev x a v tA] ≤
        Pr{let z ← (simulateQ randomOracle (contD W O (setc (φ x) (conv0 a)) tA)).run' c}[
          BreaksDP W cW z]) :
    Pr{let y ← (simulateQ randomOracle (S >>= fun x => (x, ·) <$> A')).run ∅ >>= gLG V}[
        BreaksCG Ev y] ≤
      Pr{let z ← (simulateQ randomOracle
          (dExp W O (withSetup2 (setupPcs q₀) (fun _ => conv0 <$> A')))).run' ∅}[BreaksD W cW z] := by
  set X := S >>= fun x => (x, ·) <$> A' with hX
  have hA : withSetup2 (setupPcs q₀) (fun _ => conv0 <$> A') =
      (fun p : σ₀ × α => setc (φ p.1) (conv0 p.2)) <$> X := by
    rw [withSetup2, hS, hX, bind_map_left, map_bind]
    refine bind_congr fun x => ?_
    simp only [Functor.map_map]
    rfl
  -- The deployed run, on what `BreaksD` reads.
  have hR : Pr{let z ← (simulateQ randomOracle
      (dExp W O (withSetup2 (setupPcs q₀) (fun _ => conv0 <$> A')))).run' ∅}[BreaksD W cW z] =
      Pr{let z ← (simulateQ randomOracle (loggedKC X)).run ∅ >>= fun q =>
        (simulateQ randomOracle (contD W O (setc (φ q.1.1.1) (conv0 q.1.1.2)) q.1.2)).run' q.2}[
          BreaksDP W cW z] := by
    have e1 : Pr{let z ← (simulateQ randomOracle
        (dExp W O (withSetup2 (setupPcs q₀) (fun _ => conv0 <$> A')))).run' ∅}[BreaksD W cW z] =
        Pr{let z ← (simulateQ randomOracle (projD <$>
          dExp W O (withSetup2 (setupPcs q₀) (fun _ => conv0 <$> A')))).run' ∅}[BreaksDP W cW z] := by
      have h : (simulateQ randomOracle (projD <$>
          dExp W O (withSetup2 (setupPcs q₀) (fun _ => conv0 <$> A')))).run' ∅ =
          projD <$> (simulateQ randomOracle
            (dExp W O (withSetup2 (setupPcs q₀) (fun _ => conv0 <$> A')))).run' ∅ := by
        rw [simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map,
          Functor.map_map]
      rw [h, prEvent_map]
      rfl
    rw [e1, map_dExp, DA2_bind, hA, Soundness.loggedKC_map, bind_map_left, simulateQ_bind,
      StateT.run'_eq, StateT.run_bind, map_bind]
    simp only [StateT.run'_eq]
    rfl
  -- The game, through the logged run.
  have hL : (simulateQ randomOracle X).run ∅ >>= gLG V =
      (simulateQ randomOracle (loggedKC X)).run ∅ >>= fun q => gLG V (q.1.1, q.2) := by
    rw [← map_run_loggedKC X [] ∅, bind_map_left]
    rfl
  rw [hR, hL]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun q hq => ?_
  have hcons : Consistent q.1.2 q.2 := consistent_run_loggedKC X [] ∅ consistent_nil q hq
  rw [gLG, prEvent_map]
  exact (prEvent_mono _ _ _ fun v hv => hv q.1.2 hcons).trans (hcmp _ _ _ _ hcons)

end PcsKS
