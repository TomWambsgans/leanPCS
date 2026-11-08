-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the two calls `KeccakCalls` and their simulation (`implH`, `implF`), through `ProbHyp.lean`'s hypotheses.
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/FlockCost.lean` (its commutation half).
import UniKeccakComplete.K.FlockProver
import UniKeccakComplete.K.ProbHyp

/-!
# Flock's honest prover commutes with every monad morphism

The probability layer takes Flock's prover as a parameter (`FlockProverH`) and names the facts it uses of it. Here
the commutation is proved of the honest one, **`flockProveH`** (`FlockP.flockProve`, `FlockProver.lean`: one prover
for both variants, `keccakMain` and `keccakRec3`):

* **`flockCommutes_flockProveH : FlockCommutes flockProveH`**: it commutes with every monad morphism, the hash
  becoming `φ ∘ H` (`FlockP.wr_flockProve`, piece by piece: the run of draws `wr_drawW` (one by one on the main
  line, one challenge and its squares otherwise), the zerocheck's rounds `wr_zcRounds`, the skip `wr_skipW`, the
  zerocheck `wr_zerocheckW`, the lincheck's `11` rounds `wr_lcRounds`, the front `wr_frontW` (the slices always
  sent), the ring map `wr_ringEndW`), with `Morph.wr`'s lemmas (`ProverSim.lean`);
* the probability layer's three hypotheses from it (`ProbHyp.lean`'s `…_of_flock`): **`Prob.proverCommutes_flockProveH`**,
  **`Prob.proverDuplex_flockProveH`**, **`Prob.flockSimCommutes_flockProveH`**.

Decision (recorded): the lemmas are generic in the monads, no lawfulness asked (`Morph.wr_bind`, `wr_pure`, `wr_ite`,
`wr_sampleW`, `wr_samplesW`, `wr_sendScalar(s)` do not use it); the recursions (`zcRounds`, `lcRounds`) by the same
recursion.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open UniStatement

set_option autoImplicit false

namespace UniKeccakComplete.FlockP

open UniComplete

open UniStatement.Flock

section Commute

variable {m n : Type → Type} [Monad m] [Monad n] (φ : Morph m n) (H : List UInt8 → m Digest)

/-- **A run of draws commutes** (one by one, or one challenge and its squares). -/
theorem wr_drawW (fs : FsShape) (count : ℕ) :
    φ.wr (drawW H fs count) = drawW (fun x ↦ φ.app (H x)) fs count := by
  cases fs <;> simp only [drawW, Morph.wr_samplesW, Morph.wr_ite, Morph.wr_bind, Morph.wr_sampleW, Morph.wr_pure]

/-- **The zerocheck's rounds commute.** -/
theorem wr_zcRounds : ∀ (r : List E) (claim : E) (a b c : Array E),
    φ.wr (zcRounds H r claim a b c) = zcRounds (fun x ↦ φ.app (H x)) r claim a b c
  | [], _, _, _, _ => by simp only [zcRounds, Morph.wr_pure]
  | _ :: rest, _, _, _, _ => by
    simp only [zcRounds, Morph.wr_bind, Morph.wr_sendScalar, Morph.wr_sampleW, Morph.wr_pure, wr_zcRounds rest]

/-- **The lincheck's rounds commute.** -/
theorem wr_lcRounds : ∀ (k : ℕ) (claim : E) (w z : Array E),
    φ.wr (lcRounds H k claim w z) = lcRounds (fun x ↦ φ.app (H x)) k claim w z
  | 0, _, _, _ => by simp only [lcRounds, Morph.wr_pure]
  | k + 1, _, _, _ => by
    simp only [lcRounds, Morph.wr_bind, Morph.wr_sendScalar, Morph.wr_sampleW, Morph.wr_pure, wr_lcRounds k]

theorem wr_skipW (k : ℕ) (r : List E) (wit : Wit) :
    φ.wr (skipW H k r wit) = skipW (fun x ↦ φ.app (H x)) k r wit := by
  simp only [skipW, Morph.wr_ite, Morph.wr_bind, Morph.wr_sendScalars, Morph.wr_sampleW, Morph.wr_pure]

theorem wr_zerocheckW (logN k : ℕ) (fs : FsShape) (wit : Wit) :
    φ.wr (zerocheckW H logN k fs wit) = zerocheckW (fun x ↦ φ.app (H x)) logN k fs wit := by
  simp only [zerocheckW, Morph.wr_bind, wr_drawW, wr_skipW, wr_zcRounds, Morph.wr_sendScalar, Morph.wr_pure]

theorem wr_frontW (logN : ℕ) (v : UniKeccak.KeccakVariant) (q : Array K) :
    φ.wr (frontW H logN v q) = frontW (fun x ↦ φ.app (H x)) logN v q := by
  simp only [frontW, Morph.wr_bind, wr_zerocheckW, Morph.wr_sampleW, wr_lcRounds, Morph.wr_sendScalars,
    Morph.wr_pure]

theorem wr_ringEndW (s : List E) : φ.wr (ringEndW H s) = ringEndW (fun x ↦ φ.app (H x)) s := by
  simp only [ringEndW, Morph.wr_bind, Morph.wr_samplesW, Morph.wr_pure]

/-- **Flock's honest prover commutes with every monad morphism**, the hash becoming `φ ∘ H`. -/
theorem wr_flockProve (logN : ℕ) (v : UniKeccak.KeccakVariant) (q : Array K) :
    φ.wr (flockProve H logN v q) = flockProve (fun x ↦ φ.app (H x)) logN v q := by
  simp only [flockProve, Morph.wr_bind, wr_frontW, wr_ringEndW, Morph.wr_pure]

end Commute

end UniKeccakComplete.FlockP

namespace UniKeccakComplete

open UniComplete

/-- **Flock's honest prover** as the probability layer's parameter (`FlockProverH`). -/
def flockProveH : FlockProverH := fun H ↦ FlockP.flockProve H

/-- **Flock's honest prover commutes with every monad morphism** (`ProverSim.lean`'s `FlockCommutes`). -/
theorem flockCommutes_flockProveH : FlockCommutes flockProveH := by
  intro m n _ _ _ _ φ H logN variant words
  exact FlockP.wr_flockProve φ H logN variant words

/-- **Flock's honest prover only hashes** (`ProverDuplex.lean`'s `FlockHashOnly`). -/
theorem flockHashOnly_flockProveH : FlockHashOnly flockProveH :=
  flockHashOnly_of_commutes flockProveH flockCommutes_flockProveH

namespace Prob

theorem proverCommutes_flockProveH (D : UniKeccak.KDeployment) : ProverCommutes flockProveH D :=
  proverCommutes_of_flock flockCommutes_flockProveH D

theorem proverDuplex_flockProveH (D : UniKeccak.KDeployment) : ProverDuplex flockProveH D :=
  proverDuplex_of_flock flockCommutes_flockProveH D

theorem flockSimCommutes_flockProveH : FlockSimCommutes flockProveH :=
  flockSimCommutes_of_commutes flockCommutes_flockProveH

end Prob

end UniKeccakComplete

/-! ## Axioms -/

/-- info: 'UniKeccakComplete.flockCommutes_flockProveH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.flockCommutes_flockProveH

/-- info: 'UniKeccakComplete.Prob.proverCommutes_flockProveH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Prob.proverCommutes_flockProveH

/-- info: 'UniKeccakComplete.Prob.proverDuplex_flockProveH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Prob.proverDuplex_flockProveH

/-- info: 'UniKeccakComplete.Prob.flockSimCommutes_flockProveH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Prob.flockSimCommutes_flockProveH
