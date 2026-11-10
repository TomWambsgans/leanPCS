-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The Keccak main line's `Fs/OpsK.lean` at π1-rec3's shape
-- (`keccakRec3`, `rec3Rounds`), as `UniSound/Rec3/FsOps3.lean` is the main line's `FsOps.lean`.
import UniKeccakSound.FinalK3
import UniKeccakSound.Fs.OpsK
import UniSound.Rec3.FsOps3

/-!
# The Keccak verifier at π1-rec3's shape: its three openings and its check

`OpsK.lean`'s openings, check and `good`s at π1-rec3's rounds (`rec3Rounds`, code-level link `UniCodeK3`): the proof
the chain reads (`UPf`, `upOf`, `kpOf`), the tail (`uTailK`), the shapes (`UniShapesK`, `shapeKK`), the decoders
(`uniTcK`), the point claims (`ptvK`) and the well-formedness (`WellFormedK`) are the main line's, unchanged; only
the rounds differ (`uRoundsK3`, `uOutK3`, `uniCheckK3`, `oodK3`, `holdsK3`, `verK3`, `opK3`, `uniOpsK3`, `uniGoodK3`,
`uniGoodSK3`).
-/

namespace UniKeccakSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement UniSound UniKeccak
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.setupStackK UniKeccak.setupOodK

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

/-- **The `k`-th commitment's out-of-domain answer**: `C1`'s and `C2`'s as the run read them, the setup's the
setup stack's at the setup's root (`setupOodK`, the deployment's constant). -/
def oodK3 (π : UPf) (ch : List (List E)) : Commitment → E
  | .c1 => (uOutK3 D F3 nV np C π ch).oods.1
  | .c2 => (uOutK3 D F3 nV np C π ch).oods.2
  | .setup => setupOodK D π.roots.bytecode

/-- **What the `k`-th opening's claim says of a stack**: its point has the stack's variables and the plain layout's
table evaluation there is its value (the point claim of its PCS claim; its out-of-domain claim is not used). -/
def holdsK3 (k : ℕ) (π : UPf) (ch : List (List E)) (q : Column (plainL (wvK D k)).logN) : Prop :=
  (ptvK (uOutK3 D F3 nV np C π ch) (comK k)).1.length = wvK D k ∧
    (plainL (wvK D k)).tableEval q (ptvK (uOutK3 D F3 nV np C π ch) (comK k)).1 =
      (ptvK (uOutK3 D F3 nV np C π ch) (comK k)).2

/-- **The `k`-th opening's verifier**, at the root it reads: the PCS claim's opening (`pcsOpenC`) of its point claim
on the commitment `(root, ood)`, with its opening proof. -/
def verK3 (k : ℕ) (r : Digest) (π : UPf) (ch : List (List E)) : OracleComp KeccakCalls Bool :=
  pcsOpenC (wvK D k) r (oodK3 D F3 nV np C π ch (comK k)) (ptvK (uOutK3 D F3 nV np C π ch) (comK k)).1
    (ptvK (uOutK3 D F3 nV np C π ch) (comK k)).2 ((kpOf π).openingOf (comK k))

variable {D} in
/-- **The `k`-th opening** on what it opens (`t`). -/
noncomputable def opK3 (hs : UniShapesK D) (k : ℕ) (hk : k < 3) (t : Tgt UPf Stk (shapeKK hs k hk).L.logN) :
    GOp UPf E Stk :=
  ⟨(shapeKK hs k hk).L.logN, (shapeKK hs k hk).R, (shapeKK hs k hk).adm, holdsK3 D F3 nV np C k,
    verK3 D F3 nV np C k, 10122, fun _ _ _ => isTotalQueryBound_pcsOpenC _ _ _ _ _ _,
    fun _ _ _ => duplexVm_pcsOpenC _ _ _ _ _ _, t⟩

variable {D} in
/-- **The Keccak verifier's three openings**: `C1` and `C2` (rounds `0`, `nF + 1`), the setup's stack (the setup's
root), each its PCS claim. -/
noncomputable def uniOpsK3 (hs : UniShapesK D) (qF : LeanVM.Protocol.Column (wvK D 2)) :
    List (GOp UPf E Stk) :=
  [opK3 F3 nV np C hs 0 (by decide) (.round 0 fun q => rdTab (tabOf _ q)),
    opK3 F3 nV np C hs 1 (by decide) (.round (F3.prog.rounds.length + 1) fun q => rdTab (tabOf _ q)),
    opK3 F3 nV np C hs 2 (by decide) (.setup (fun π => toB π.roots.bytecode) qF)]

/-- **A candidate is good**: at `C1`'s and `C2`'s rounds, a stack satisfying its PCS claim's point claim. -/
def uniGoodK3 (i : ℕ) (π : UPf) (ch : List (List E)) (c : Option Stk) : Prop :=
  if i = 0 then ∃ q, c = some q ∧
      mleStk q (wvK D 0) (ptvK (uOutK3 D F3 nV np C π ch) .c1).1 = (ptvK (uOutK3 D F3 nV np C π ch) .c1).2
  else if i = F3.prog.rounds.length + 1 then ∃ q, c = some q ∧
      mleStk q (wvK D 1) (ptvK (uOutK3 D F3 nV np C π ch) .c2).1 = (ptvK (uOutK3 D F3 nV np C π ch) .c2).2
  else True

/-- **The setup's stack is good**: the setup's honest stack satisfies its PCS claim's point claim. -/
def uniGoodSK3 (π : UPf) (ch : List (List E)) : Prop :=
  mleStk (fun i => (setupStackK D.prog D.shape).getD i 0) (wvK D 2) (ptvK (uOutK3 D F3 nV np C π ch) .setup).1 =
    (ptvK (uOutK3 D F3 nV np C π ch) .setup).2

end Ops

end UniKeccakSound
