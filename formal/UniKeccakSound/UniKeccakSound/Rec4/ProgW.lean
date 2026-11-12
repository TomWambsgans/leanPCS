-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Extends `formal/UniSound/UniSound/Prog.lean`'s chain
-- programs to π1-rec4's transcript (`UniStatement.sampleWide`, `formal/UniStatement/UniStatement/Rec.lean`).
import UniSound.Prog
import UniStatement.Rec

/-!
# Wide chain programs: π1-rec4's rounds

π1-rec4's verifier (`UniKeccak.reduceWithK4`) reads the stream and draws challenges as π1-rec3's does, but every
round's challenges come from **one** Keccak-256 call (`sampleWide`: challenge `0` `sample`'s, the others the rate's),
and `C2`'s call absorbs the slices **before** `C2`'s root. A **wide chain program** (`ChainProgW`) is a chain program
(`ChainProg`: rounds, zeros, tail, result) with, for each round, the number of its scalars read before its root
(`pv`, by the round's index); its canonical channel program (`ChainProgW.runW`) reads, round by round, those scalars,
the root (if the round has one), the round's other scalars, requires its zeros, and draws `sampleWide F (ns + 1)`.

The transcript (`Done`), the fit (`DoneFits`) and the zeros (`ChainProg.ZerosVanish`) are `ChainProg`'s: a round's
message is its root and all its scalars, in order.
-/

namespace UniSound

open LeanVM.Parameters LeanVM.Semantics UniStatement

/-- **A wide chain program**: a chain program, and the number of each round's scalars read before its root. -/
structure ChainProgW (α : Type) extends ChainProg α where
  pv : ℕ → ℕ

namespace ChainProgW

variable {α : Type} (P : ChainProgW α)

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- The rounds from `rs` on, after the transcript `done`: each round's scalars before its root, its root, its other
scalars, its zeros, its wide draw. -/
def runRoundsW : List Compose.RoundSpec → Done → ChanM m Done
  | [], done => pure done
  | s :: rs, done => do
    let pre ← nextScalars (m := m) (P.pv done.length)
    let root ← if s.root then some <$> nextRoot (m := m) else pure none
    let post ← nextScalars (m := m) (s.nv - P.pv done.length)
    ChainProg.requireZeros (P.zeros done (root, pre ++ post))
    let chs ← sampleWide F (s.ns + 1)
    runRoundsW rs (done ++ [((root, pre ++ post), chs)])

/-- **The canonical channel program** of `P` over `F`: its rounds, its tail, its result. -/
def runW : ChanM m α := do
  let done ← P.runRoundsW F P.rounds []
  let tl ← nextScalars (m := m) P.tail
  ChainProg.requireZeros (P.tailZeros done tl)
  return P.out done tl

end With

end ChainProgW

end UniSound
