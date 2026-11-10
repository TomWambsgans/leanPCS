-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The Keccak main line's `Fs/OpsK.lean` at π1-rec3's shape
-- (`keccakRec3`, `rec3Rounds`), as `UniSound/Rec3/FsOps3.lean` is the main line's `FsOps.lean`.
import UniKeccakSound.FinalK3
import UniKeccakSound.Fs.OpsK
import UniSound.Rec3.FsOps3

/-!
# The Keccak verifier at π1-rec3's shape: its three openings and its check

`OpsK.lean`'s openings, check and `good`s at π1-rec3's rounds (`rec3Rounds`, code-level link `UniCodeK3`): the proof
the chain reads (`UPf`, `upOf`, `kpOf`), the tail (`uTailK`), the shapes (`UniShapesK`, `shapeKK`), the decoders
(`uniTcK`), the statements (`uClK`) and the well-formedness (`WellFormedK`) are the main line's, unchanged; only the
rounds differ (`uRoundsK3`, `uOutK3`, `uniCheckK3`, `cl1K3 … cl3K3`, `uniOpsK3`, `uniGoodK3`, `uniGoodSK3`).
-/

namespace UniKeccakSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement UniSound UniKeccak
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.layoutWordsK UniKeccak.setupStackK

/-! ## The verifier's openings -/

section Ops

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3) (nV np : ℕ)
  (C : UniCodeK3 D F3 nV np)

/-- π1-rec3's rounds. -/
abbrev uRoundsK3 : List RoundSpec := rec3Rounds F3.prog.rounds nV np 1

/-- The PIOP's statement a proof announces. -/
def uStK3 (π : UPf) : USt := ustOf (uView (uRoundsK3 F3 nV np) π).1

/-- **The chain program's result** on a proof and challenges (the tail: three scalars). -/
def uOutK3 (π : UPf) (ch : List (List E)) : Reduced :=
  (C.prog (uStK3 F3 nV np π).1 (uStK3 F3 nV np π).2).out (uDone (uRoundsK3 F3 nV np) π ch)
    (uTailK (uRoundsK3 F3 nV np) π)

/-- **The verifier's check** (what an accepting run satisfies). -/
def uniCheckK3 (π : UPf) (ch : List (List E)) : Prop :=
  DoneFits (uRoundsK3 F3 nV np) (uDone (uRoundsK3 F3 nV np) π ch) ∧
    (C.prog (uStK3 F3 nV np π).1 (uStK3 F3 nV np π).2).ZerosVanish (uDone (uRoundsK3 F3 nV np) π ch)
      (uTailK (uRoundsK3 F3 nV np) π) ∧
    WellFormedK D (uOutK3 D F3 nV np C π ch)

/-- `C1`'s claims. -/
def cl1K3 (π : UPf) (ch : List (List E)) : Stmt (plainL (wvK D 0)).stacking :=
  uClK D 0 (claimsOf (uOutK3 D F3 nV np C π ch) .c1)

/-- `C2`'s claims. -/
def cl2K3 (π : UPf) (ch : List (List E)) : Stmt (plainL (wvK D 1)).stacking :=
  uClK D 1 (claimsOf (uOutK3 D F3 nV np C π ch) .c2)

/-- The setup's claims. -/
def cl3K3 (π : UPf) (ch : List (List E)) : Stmt (plainL (wvK D 2)).stacking :=
  uClK D 2 (claimsOf (uOutK3 D F3 nV np C π ch) .setup)

variable {D} in
/-- **The Keccak verifier's three openings**: `C1` and `C2` (rounds `0`, `nF + 1`), the setup's stack (the setup's
root), each its one claim. -/
noncomputable def uniOpsK3 (hs : UniShapesK D) (qF : LeanVM.Protocol.Column (wvK D 2)) :
    List (WhirOp UPf E Stk) :=
  [⟨shapeKK hs 0 (by decide), cl1K3 D F3 nV np C, fun π => π.proof.c1,
      .round 0 fun q => rdTab (tabOf _ q)⟩,
    ⟨shapeKK hs 1 (by decide), cl2K3 D F3 nV np C, fun π => π.proof.c2,
      .round (F3.prog.rounds.length + 1) fun q => rdTab (tabOf _ q)⟩,
    ⟨shapeKK hs 2 (by decide), cl3K3 D F3 nV np C, fun π => π.proof.setup,
      .setup (fun π => toB π.roots.bytecode) qF⟩]

/-- **A candidate is good**: at `C1`'s and `C2`'s rounds, a stack satisfying its opening's claims. -/
def uniGoodK3 (i : ℕ) (π : UPf) (ch : List (List E)) (c : Option Stk) : Prop :=
  if i = 0 then ∃ q, c = some q ∧
      ∀ cl ∈ (cl1K3 D F3 nV np C π ch).claims, mleStk q (wvK D 0) cl.point = cl.value
  else if i = F3.prog.rounds.length + 1 then ∃ q, c = some q ∧
      ∀ cl ∈ (cl2K3 D F3 nV np C π ch).claims, mleStk q (wvK D 1) cl.point = cl.value
  else True

/-- **The setup's stack is good**: the setup's honest stack satisfies its opening's claims. -/
def uniGoodSK3 (π : UPf) (ch : List (List E)) : Prop :=
  ∀ cl ∈ (cl3K3 D F3 nV np C π ch).claims,
    mleStk (fun i => (setupStackK D.prog D.shape).getD i 0) (wvK D 2) cl.point = cl.value

end Ops

end UniKeccakSound
