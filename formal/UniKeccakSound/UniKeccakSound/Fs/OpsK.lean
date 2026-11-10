-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The main line's `UniSound/FsOps.lean` and π1-rec3's
-- `UniSound/Rec3/FsOps3.lean` for the Keccak verifier (`formal/UniKeccak`'s `verifyWithK`: three claims' openings).
import UniKeccakSound.FsK
import UniKeccakSound.Fs.PcsOpK

/-!
# The Keccak verifier's three openings, its check, and the proof the chain reads

`UniSound/FsOps.lean`'s openings for the Keccak verifier's main line (`uniOpsK`): `C1` (round `0`'s root) and `C2`
(round `nF + 1`'s), opened by the computable decoder (`uniTcK`, `tableCode` of their shapes, the candidates read back
as stacks, `rdTab`), and the setup's stack `F` at the setup's root, each a plain layout (`plainL v`: one chunk of
`2^v` words, the claims' layout) at its Keccak layout word's variables (`wvK`, `layoutWordsK`), opened at
`plainShapeK` (`Whir23.lean`: `2^23 ..= 2^28` words).

* **The proof the chain reads is `UniSound.UPf`** (the input, a `UniProof`, the transcript's IV, the setup's roots):
  a Keccak proof is a `UniProof` (`upOf`, `kpOf`: `kpOf ⟨…, upOf p, …⟩ = p` by `rfl`), so the chain's statement
  and messages (`uView`, `uDone`) and every lemma about them are `UniSound`'s, at the main line's rounds
  (`uniRounds`); the tail is three scalars (`uTailK`, as π1-rec3's `uTail3`).
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
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.setupStackK UniKeccak.setupOodK

/-! ## The Keccak proof as the chain reads it -/

/-- **A Keccak proof as a `UniProof`**: the stream and the three opening proofs. -/
def upOf (p : KeccakProof) : UniProof := ⟨p.stream, p.c1, p.c2, p.setup⟩

/-- **The Keccak proof a `UniProof` carries**: its stream and its first three opening proofs. -/
def kpOf (π : UPf) : KeccakProof := ⟨π.proof.stream, π.proof.c1, π.proof.c2, π.proof.setup⟩

theorem kpOf_upOf (input : Vector UInt8 32) (p : KeccakProof) (iv : Vector UInt8 32) (roots : SetupRoots) :
    kpOf ⟨input, upOf p, iv, roots⟩ = p := rfl

/-- **The Keccak verifier's tail**: the three scalars after the rounds (the stacks' values at the batch's point). -/
def uTailK (rounds : List RoundSpec) (π : UPf) : List E :=
  (List.range 3).map fun k => scalarAt π.proof.stream (24 + roundsBytes rounds + 24 * k)

@[simp] theorem length_uTailK (rounds : List RoundSpec) (π : UPf) : (uTailK rounds π).length = 3 := by
  simp [uTailK]

/-- **The setup commitment of a setup root** at a deployment: the root and the setup stack's out-of-domain answer
there (`setupOodK`; `KDeployment.setupRoots t = skOf D ⟨t.root⟩`). -/
def skOf (D : KDeployment) (r : SetupRoots) : SetupRootsK := ⟨r.bytecode, setupOodK D r.bytecode⟩

theorem setupRoots_skOf (D : KDeployment) (t : LeanVM.Prover.Tree) : D.setupRoots t = skOf D ⟨t.root⟩ := rfl

/-! ## The stacks' variables and the shapes -/

/-- The commitment of index `k`: `C1`, `C2`, the setup. -/
def comK : ℕ → Commitment
  | 0 => .c1
  | 1 => .c2
  | _ => .setup

/-- A Keccak commitment's stack variables (`stackVarsK`, its PCS claim's `n`): `C1`, `C2`, the setup. -/
def wvK (D : KDeployment) (k : ℕ) : ℕ := stackVarsK D.shape (comK k)

/-- **The Keccak deployment's stacks fit WHIR's certified window**: the three stacks have `23 … 28` variables,
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
abbrev uRoundsK : List RoundSpec := uniRounds Fl.prog.rounds nV V 1

/-- The PIOP's statement a proof announces. -/
def uStK (π : UPf) : USt := ustOf (uView (uRoundsK Fl nV V) π).1

/-- **The chain program's result** on a proof and challenges (the tail: three scalars). -/
def uOutK (π : UPf) (ch : List (List E)) : Reduced :=
  (C.prog (uStK Fl nV V π).1 (uStK Fl nV V π).2).out (uDone (uRoundsK Fl nV V) π ch)
    (uTailK (uRoundsK Fl nV V) π)

/-- **The result is well formed**: one opening per commitment, in order, its point claims of its stack's
variables, and no matrices' claim. -/
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

/-- **A commitment's point claim in a result**: the point and the value of its opening, if a point claim. -/
def ptvK (r : Reduced) (c : Commitment) : List E × E :=
  match r.openings.lookup c with
  | some (.point pt v _) => (pt, v)
  | _ => ([], 0)

/-- **The `k`-th commitment's out-of-domain answer**: `C1`'s and `C2`'s as the run read them, the setup's the
setup stack's at the setup's root (`setupOodK`, the deployment's constant). -/
def oodK (π : UPf) (ch : List (List E)) : Commitment → E
  | .c1 => (uOutK D Fl nV V C π ch).oods.1
  | .c2 => (uOutK D Fl nV V C π ch).oods.2
  | .setup => setupOodK D π.roots.bytecode

/-- **What the `k`-th opening's claim says of a stack**: its point has the stack's variables and the plain layout's
table evaluation there is its value (the point claim of its PCS claim; its out-of-domain claim is not used). -/
def holdsK (k : ℕ) (π : UPf) (ch : List (List E)) (q : Column (plainL (wvK D k)).logN) : Prop :=
  (ptvK (uOutK D Fl nV V C π ch) (comK k)).1.length = wvK D k ∧
    (plainL (wvK D k)).tableEval q (ptvK (uOutK D Fl nV V C π ch) (comK k)).1 =
      (ptvK (uOutK D Fl nV V C π ch) (comK k)).2

/-- **The `k`-th opening's verifier**, at the root it reads: the PCS claim's opening (`pcsOpenC`) of its point claim
on the commitment `(root, ood)`, with its opening proof. -/
def verK (k : ℕ) (r : Digest) (π : UPf) (ch : List (List E)) : OracleComp KeccakCalls Bool :=
  pcsOpenC (wvK D k) r (oodK D Fl nV V C π ch (comK k)) (ptvK (uOutK D Fl nV V C π ch) (comK k)).1
    (ptvK (uOutK D Fl nV V C π ch) (comK k)).2 ((kpOf π).openingOf (comK k))

variable {D} in
/-- **The `k`-th opening** on what it opens (`t`). -/
noncomputable def opK (hs : UniShapesK D) (k : ℕ) (hk : k < 3) (t : Tgt UPf Stk (shapeKK hs k hk).L.logN) :
    GOp UPf E Stk :=
  ⟨(shapeKK hs k hk).L.logN, (shapeKK hs k hk).R, (shapeKK hs k hk).adm, holdsK D Fl nV V C k,
    verK D Fl nV V C k, 10122, fun _ _ _ => isTotalQueryBound_pcsOpenC _ _ _ _ _ _,
    fun _ _ _ => duplexVm_pcsOpenC _ _ _ _ _ _, t⟩

variable {D} in
/-- **The Keccak verifier's three openings**: `C1` and `C2` (rounds `0`, `nF + 1`), the setup's stack (the setup's
root), each its PCS claim. -/
noncomputable def uniOpsK (hs : UniShapesK D) (qF : LeanVM.Protocol.Column (wvK D 2)) :
    List (GOp UPf E Stk) :=
  [opK Fl nV V C hs 0 (by decide) (.round 0 fun q => rdTab (tabOf _ q)),
    opK Fl nV V C hs 1 (by decide) (.round (Fl.prog.rounds.length + 1) fun q => rdTab (tabOf _ q)),
    opK Fl nV V C hs 2 (by decide) (.setup (fun π => toB π.roots.bytecode) qF)]

/-- **A candidate is good**: at `C1`'s and `C2`'s rounds, a stack satisfying its PCS claim's point claim. -/
def uniGoodK (i : ℕ) (π : UPf) (ch : List (List E)) (c : Option Stk) : Prop :=
  if i = 0 then ∃ q, c = some q ∧
      mleStk q (wvK D 0) (ptvK (uOutK D Fl nV V C π ch) .c1).1 = (ptvK (uOutK D Fl nV V C π ch) .c1).2
  else if i = Fl.prog.rounds.length + 1 then ∃ q, c = some q ∧
      mleStk q (wvK D 1) (ptvK (uOutK D Fl nV V C π ch) .c2).1 = (ptvK (uOutK D Fl nV V C π ch) .c2).2
  else True

/-- **The setup's stack is good**: the setup's honest stack satisfies its PCS claim's point claim. -/
def uniGoodSK (π : UPf) (ch : List (List E)) : Prop :=
  mleStk (fun i => (setupStackK D.prog D.shape).getD i 0) (wvK D 2) (ptvK (uOutK D Fl nV V C π ch) .setup).1 =
    (ptvK (uOutK D Fl nV V C π ch) .setup).2

end Ops

variable {D : KDeployment} in
/-- **The decoders**: `C1`'s (round `0`) and `C2`'s, `tableCode` of their shapes. -/
noncomputable def uniTcK (hs : UniShapesK D) (i : ℕ) : TableCode Stk :=
  if i = 0 then tableCode (shapeKK hs 0 (by decide)).L (shapeKK hs 0 (by decide)).R
      (shapeKK hs 0 (by decide)).adm rdTab
  else tableCode (shapeKK hs 1 (by decide)).L (shapeKK hs 1 (by decide)).R
      (shapeKK hs 1 (by decide)).adm rdTab

end UniKeccakSound
