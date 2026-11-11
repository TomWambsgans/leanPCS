-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Compose.Claims
import Compose.Rpm
import QuotientSecurity.Deployed
import PcsQuotient.Circuit

/-!
# The definitions of `Soundness.Defs` that the leanVM line shares

Moved here from `Soundness/Defs.lean` (names unchanged), so that the leanVM line (`UniSound`,
`UniKeccakSound`, `RecCompose`) does not import the membership protocol's soundness layer:

* `eLimbs`: a field element as its three limbs, low first, each a 64-bit lane;
* `ourVerifierEarly`: an opening with the first stop (no root, rejected before any query);
* `treeTr`: a tree's Keccak-256 evaluations as a transcript of Compose's.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp
open scoped ENNReal

namespace Soundness

open QuotientRpm QuotientSecurity Compose Compose.Reduce LeanVM LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile WhirBridge

/-! ## The limbs -/

/-- A field element as its three limbs, low first, each a 64-bit lane (`F192`'s `(c0, c1, c2)`). -/
def eLimbs : E ≃ Limbs where
  toFun x := ((x.limb 0).lane, (x.limb 1).lane, (x.limb 2).lane)
  invFun l := E.ofLimbs (K.ofLane l.1) (K.ofLane l.2.1) (K.ofLane l.2.2)
  left_inv x := by
    simp only
    have h : ∀ a : K, K.ofLane a.lane = a := fun _ => rfl
    rw [h, h, h, ofLimbs_limb]
  right_inv l := by
    obtain ⟨a, b, c⟩ := l
    have h : ∀ w : UInt64, (K.ofLane w).lane = w := fun _ => rfl
    simp only [limb_ofLimbs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, h]

/-! ## The verifier with early stops -/

/-- **An opening with the Statement's first stop**: a proof whose scalar stream holds fewer than two
scalars (no root) is rejected before any query (`PcsQuotient.openingWith` reads the root first);
otherwise `opening::verify` (`ourVerifier`), which rejects it too, after its seed. -/
def ourVerifierEarly (L : Layout) (R : ℕ) (w : (Digest × Stmt L.stacking) × Proof) :
    OracleComp KeccakCalls Bool :=
  match w.2.stream with
  | _ :: _ :: _ => ourVerifier L R w
  | _ => pure false

/-! ## The setup's log -/

/-- The setup tree's Keccak-256 evaluations as a transcript of Compose's (inputs, 32-byte
answers). -/
def treeTr (t : LeanVM.Prover.Tree) : Transcript :=
  (PcsQuotient.Tree.evaluations t).map fun e => (e.1, toB e.2)

end Soundness

/-- info: 'Soundness.eLimbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Soundness.eLimbs

/-- info: 'Soundness.ourVerifierEarly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Soundness.ourVerifierEarly

/-- info: 'Soundness.treeTr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Soundness.treeTr
