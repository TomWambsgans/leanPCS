-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here.
import ZK.PcsAdds

/-!
# The phase's tracked queries, written out

`squeezeF` of a message of one, two or three blocks, followed by a continuation, is that many nested tracked
queries (`squeezeF_bind_one`, `_two`, `_three`); an out-of-domain coordinate is one (`keccakF_bind_one`).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open PcsQuotient.Transcript
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open FProg

variable {A α β γ : Type}

theorem FProg.bind_assoc (P : FProg A α) (g : α → FProg A β) (f : β → FProg A γ) :
    (P.bind g).bind f = P.bind fun x ↦ (g x).bind f := by
  induction P with
  | ret a => rfl
  | step m k ih => simp only [FProg.bind, ih]
  | q x k ih => simp only [FProg.bind, ih]

/-- The zero state. -/
abbrev zeroSt : KeccakState := Vector.replicate 25 0

theorem keccakF_bind_one (data : List UInt8) (h : data.length / rate = 0) (f : Digest → FProg A β) :
    (keccakF data).bind f = .q (blockIn zeroSt (padBlock data)) fun y ↦ f (digestOf y) := by
  simp only [keccakF, h, FProg.bind_assoc]
  rfl

theorem keccakF_bind_two (data : List UInt8) (h : data.length / rate = 1) (f : Digest → FProg A β) :
    (keccakF data).bind f = .q (blockIn zeroSt (data.take rate)) fun y ↦
      .q (blockIn y (padBlock (data.drop rate))) fun y' ↦ f (digestOf y') := by
  simp only [keccakF, h, FProg.bind_assoc]
  rfl

theorem keccakF_bind_three (data : List UInt8) (h : data.length / rate = 2) (f : Digest → FProg A β) :
    (keccakF data).bind f = .q (blockIn zeroSt (data.take rate)) fun y ↦
      .q (blockIn y ((data.drop rate).take rate)) fun y' ↦
        .q (blockIn y' (padBlock ((data.drop rate).drop rate))) fun y'' ↦ f (digestOf y'') := by
  simp only [keccakF, h, FProg.bind_assoc]
  rfl

/-- The chain's message. -/
def chainMsg (c : Chain) : List UInt8 := digestBytes c.state ++ c.pending.flatMap scalarBytes

theorem squeezeF_bind (c : Chain) (f : E × Chain → FProg A β) :
    (squeezeF c).bind f = (keccakF (chainMsg c)).bind fun st ↦ f (challengeOf st, ⟨st, []⟩) := by
  simp only [squeezeF, FProg.bind_assoc]
  rfl

end PcsQuotient.EndToEnd
