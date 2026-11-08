-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The main line's `UniSound/FsOps.lean` and π1-rec3's
-- `UniSound/Rec3/FsOps3.lean` for the Keccak verifier (`formal/UniKeccak`'s `verifyWithK`: three `PCS_OPEN` calls).
import UniKeccakSound.FsK
import UniKeccakSound.Fs.Whir23

/-!
# The Keccak verifier's three openings, its check, and the proof the chain reads

`UniSound/FsOps.lean`'s openings for the Keccak verifier's main line (`uniOpsK`): `C1` (round `0`'s root) and `C2`
(round `nF + 1`'s), opened by the computable decoder (`uniTcK`, `tableCode` of their shapes, the candidates read back
as stacks, `rdTab`), and the setup's stack `F` at the setup's root, each a plain layout (`plainL v`: one chunk of
`2^v` words, `PCS_OPEN`'s layout) at its Keccak layout word's variables (`wvK`, `layoutWordsK`), opened at
`plainShapeK` (`Whir23.lean`: `2^23 ..= 2^28` words). No `A0`, `B0` openings.

* **The proof the chain reads is `UniSound.UPf`** (the input, a `UniProof`, the transcript's IV, the setup's roots):
  a Keccak proof is a `UniProof` whose `A0`, `B0` opening proofs are never read (`upOf`, `kpOf`: `kpOf ⟨…, upOf p, …⟩
  = p` by `rfl`), so the chain's statement and messages (`uView`, `uDone`) and every lemma about them are
  `UniSound`'s, at the main line's rounds (`uniRounds`); the tail is three scalars (`uTailK`, as π1-rec3's `uTail3`).
* **`UniShapesK`**: the three layout words name `23 … 28` variables, `C1`'s and `C2`'s at least `24` (their roots'
  lists at most `largeList ≤ 9952`, the chain's list term).
* **The check** (`uniCheckK`): the transcript completes the rounds, every value the chain program requires zero is,
  and its result is well formed (`WellFormedK`: one point claim per commitment, of its layout word's variables, no
  matrices' claim).
* **`good`** (`uniGoodK`) and **`goodS`** (`uniGoodSK`: the setup's honest stack `setupStackK` satisfies its claim).
-/

namespace UniKeccakSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement UniSound UniKeccak
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.layoutWordsK UniKeccak.setupStackK

/-! ## The Keccak proof as the chain reads it -/

/-- **A Keccak proof as a `UniProof`**: the stream and the three opening proofs; `A0`'s and `B0`'s slots hold the
setup's proof (never read). -/
def upOf (p : KeccakProof) : UniProof := ⟨p.stream, p.c1, p.c2, p.setup, p.setup, p.setup⟩

/-- **The Keccak proof a `UniProof` carries**: its stream and its first three opening proofs. -/
def kpOf (π : UPf) : KeccakProof := ⟨π.proof.stream, π.proof.c1, π.proof.c2, π.proof.setup⟩

theorem kpOf_upOf (input : Vector UInt8 32) (p : KeccakProof) (iv : Vector UInt8 32) (roots : SetupRoots) :
    kpOf ⟨input, upOf p, iv, roots⟩ = p := rfl

/-- **The Keccak verifier's tail**: the three scalars after the rounds (the stacks' values at the batch's point). -/
def uTailK (rounds : List RoundSpec) (π : UPf) : List E :=
  (List.range 3).map fun k => scalarAt π.proof.stream (24 + roundsBytes rounds + 24 * k)

@[simp] theorem length_uTailK (rounds : List RoundSpec) (π : UPf) : (uTailK rounds π).length = 3 := by
  simp [uTailK]

/-! ## The layout words and the shapes -/

/-- A Keccak layout word's variables (`layoutWordVars` of `layoutWordsK`): `C1`, `C2`, the setup. -/
def wvK (D : KDeployment) (k : ℕ) : ℕ := layoutWordVars ((layoutWordsK D.shape).getD k [])

/-- **The Keccak deployment's stacks fit WHIR's certified window**: the three layout words name `23 … 28` variables,
`C1`'s and `C2`'s at least `24`. -/
structure UniShapesK (D : KDeployment) : Prop where
  lo : ∀ k < 3, 23 ≤ wvK D k
  hi : ∀ k < 3, wvK D k ≤ 28
  c1 : 24 ≤ wvK D 0
  c2 : 24 ≤ wvK D 1

/-- The `k`-th opening's shape. -/
@[reducible] noncomputable def shapeKK {D : KDeployment} (hs : UniShapesK D) (k : ℕ) (hk : k < 3) :
    WhirShape :=
  plainShapeK (wvK D k) (hs.lo k hk) (hs.hi k hk)

/-! ## The verifier's openings -/

section Ops

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain) (nV V : ℕ)
  (C : UniCodeK D Fl nV V)

/-- The main line's rounds. -/
abbrev uRoundsK : List RoundSpec := uniRounds Fl.prog.rounds nV V

/-- The PIOP's statement a proof announces. -/
def uStK (π : UPf) : USt := ustOf (uView (uRoundsK Fl nV V) π).1

/-- **The chain program's result** on a proof and challenges (the tail: three scalars). -/
def uOutK (π : UPf) (ch : List (List E)) : Reduced :=
  (C.prog (uStK Fl nV V π).1 (uStK Fl nV V π).2).out (uDone (uRoundsK Fl nV V) π ch)
    (uTailK (uRoundsK Fl nV V) π)

/-- **The result is well formed**: one opening per commitment, in order, its point claims of its Keccak layout
word's variables, and no matrices' claim. -/
def WellFormedK (r : Reduced) : Prop :=
  r.openings.map Prod.fst = commitments ∧
    (∀ c ∈ claimsOf r .c1, c.point.length = wvK D 0) ∧
    (∀ c ∈ claimsOf r .c2, c.point.length = wvK D 1) ∧
    (∀ c ∈ claimsOf r .setup, c.point.length = wvK D 2) ∧
    r.matrices = none

/-- **The verifier's check** (what an accepting run satisfies). -/
def uniCheckK (π : UPf) (ch : List (List E)) : Prop :=
  DoneFits (uRoundsK Fl nV V) (uDone (uRoundsK Fl nV V) π ch) ∧
    (C.prog (uStK Fl nV V π).1 (uStK Fl nV V π).2).ZerosVanish (uDone (uRoundsK Fl nV V) π ch)
      (uTailK (uRoundsK Fl nV V) π) ∧
    WellFormedK D (uOutK D Fl nV V C π ch)

/-- The `k`-th opening's statement on its plain layout. -/
def uClK (k : ℕ) (cs : List WhirBridge.Claim) : Stmt (plainL (wvK D k)).stacking :=
  mkStmt _ (extra_plainL _) cs

/-- `C1`'s claims. -/
def cl1K (π : UPf) (ch : List (List E)) : Stmt (plainL (wvK D 0)).stacking :=
  uClK D 0 (claimsOf (uOutK D Fl nV V C π ch) .c1)

/-- `C2`'s claims. -/
def cl2K (π : UPf) (ch : List (List E)) : Stmt (plainL (wvK D 1)).stacking :=
  uClK D 1 (claimsOf (uOutK D Fl nV V C π ch) .c2)

/-- The setup's claims. -/
def cl3K (π : UPf) (ch : List (List E)) : Stmt (plainL (wvK D 2)).stacking :=
  uClK D 2 (claimsOf (uOutK D Fl nV V C π ch) .setup)

variable {D} in
/-- **The Keccak verifier's three openings**: `C1` and `C2` (rounds `0`, `nF + 1`), the setup's stack (the setup's
root), each its one claim. -/
noncomputable def uniOpsK (hs : UniShapesK D) (qF : LeanVM.Protocol.Column (wvK D 2)) :
    List (WhirOp UPf E Stk) :=
  [⟨shapeKK hs 0 (by decide), cl1K D Fl nV V C, fun π => π.proof.c1,
      .round 0 fun q => rdTab (tabOf _ q)⟩,
    ⟨shapeKK hs 1 (by decide), cl2K D Fl nV V C, fun π => π.proof.c2,
      .round (Fl.prog.rounds.length + 1) fun q => rdTab (tabOf _ q)⟩,
    ⟨shapeKK hs 2 (by decide), cl3K D Fl nV V C, fun π => π.proof.setup,
      .setup (fun π => toB π.roots.bytecode) qF⟩]

/-- **A candidate is good**: at `C1`'s and `C2`'s rounds, a stack satisfying its opening's claims. -/
def uniGoodK (i : ℕ) (π : UPf) (ch : List (List E)) (c : Option Stk) : Prop :=
  if i = 0 then ∃ q, c = some q ∧
      ∀ cl ∈ (cl1K D Fl nV V C π ch).claims, mleStk q (wvK D 0) cl.point = cl.value
  else if i = Fl.prog.rounds.length + 1 then ∃ q, c = some q ∧
      ∀ cl ∈ (cl2K D Fl nV V C π ch).claims, mleStk q (wvK D 1) cl.point = cl.value
  else True

/-- **The setup's stack is good**: the setup's honest stack satisfies its opening's claims. -/
def uniGoodSK (π : UPf) (ch : List (List E)) : Prop :=
  ∀ cl ∈ (cl3K D Fl nV V C π ch).claims,
    mleStk (fun i => (setupStackK D.prog D.shape).getD i 0) (wvK D 2) cl.point = cl.value

end Ops

variable {D : KDeployment} in
/-- **The decoders**: `C1`'s (round `0`) and `C2`'s, `tableCode` of their shapes. -/
noncomputable def uniTcK (hs : UniShapesK D) (i : ℕ) : TableCode Stk :=
  if i = 0 then tableCode (shapeKK hs 0 (by decide)).L (shapeKK hs 0 (by decide)).R
      (shapeKK hs 0 (by decide)).adm rdTab
  else tableCode (shapeKK hs 1 (by decide)).L (shapeKK hs 1 (by decide)).R
      (shapeKK hs 1 (by decide)).adm rdTab

end UniKeccakSound
