-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md and AGENTS.md.
import RecCompose.RealDeployment

/-!
# The real deployment's checks, evaluated

`rec-real-check` (compiled code; no kernel evaluation) evaluates the run-checked `Prop`s of
`RecCompose/RealDeployment.lean` for the Keccak VM's π1-rec3 at 128 signatures (the compiler on
`RecGraphKeccak.Emitted.graph`), each as the very expression it names:

* `DigestChecked`: its left side at `pi2CircuitOf refCompiled.circuit`, which is `realPi2 Data.pi1Iv` (`realPi2_ref`,
  `rfl`; the digest `RecDeployment.Real` names, of the Lean compiler's `σ`, `κ` at π1's reference IV), against
  `Data.digest`;
* `IvChecked` at three 32-byte IVs: `ivCheck iv` at π1's reference IV (`Data.pi1Iv`), the zero IV and the all-ones IV
  (the compile, `viewCheck`, `streamAgree` with the reference IV's circuit);
* with `--setup`: also `SetupRootChecked`, its left side likewise (the WHIR commitment of the `2^25`-word setup
  table) against `Data.setupRoot`; with `--setup-only`, that alone.

Closed-term extraction is off, so that nothing is computed at initialization but `refCompiled`.
-/

set_option compiler.extract_closed false

open RecCompose RecStatement LeanVM.Protocol.KeccakHash

def hexOf (b : List UInt8) : String :=
  String.join (b.map fun x ↦
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    if s.length = 1 then "0" ++ s else s)

def flush : IO Unit := do (← IO.getStdout).flush

def ivs : List (String × String × List UInt8) :=
  [("ref", "pi1 reference IV", Data.pi1Iv), ("zero", "zero IV", List.replicate 32 0),
    ("ones", "all-ones IV", List.replicate 32 0xff)]

/-- `rec-real-check [ref] [zero] [ones] [--no-digest] [--setup | --setup-only]`: without an IV named, all three. Each
line carries the time since the start when it is printed (the compiler may move a computation before the clock read
that precedes it, so the per-check times can read `0`; the times since the start cannot). -/
def main (args : List String) : IO UInt32 := do
  let setup := args.contains "--setup" || args.contains "--setup-only"
  let only := args.contains "--setup-only"
  let named := ivs.filter fun x ↦ args.contains x.1
  let chosen := if named.isEmpty then ivs else named
  let start ← IO.monoMsNow
  let since : IO Nat := do return (← IO.monoMsNow) - start
  let mut ok := true
  IO.println s!"reference IV: {refCompiled.circuit.kappa.size} kappa entries, {refCompiled.circuit.ports.size} ports, \
    logN {refCompiled.circuit.logN} (at {← since} ms)"
  flush
  if !only then
    if !args.contains "--no-digest" then
      let d := Id.run ((pi2CircuitOf refCompiled.circuit).digestWith (m := Id)
        fun x ↦ pure (LeanVM.Semantics.keccakF1600 x))
      let b := decide (d = Data.digest)
      IO.println s!"DigestChecked: {b} (digest {hexOf d}, Data.digest {hexOf Data.digest}; at {← since} ms)"
      flush
      ok := ok && b
    for (_, label, iv) in chosen do
      let v := ivCheck iv
      IO.println s!"IvChecked at the {label} ({iv.length} bytes): ivCheck {v} (at {← since} ms)"
      flush
      ok := ok && v
  if setup then
    let r := digestBytes (Id.run ((pi2CircuitOf refCompiled.circuit).setupTreeWith (m := Id)
      fun x ↦ pure (LeanVM.Semantics.keccakF1600 x))).root
    let b := decide (r = Data.setupRoot)
    IO.println s!"SetupRootChecked: {b} (root {hexOf r}, Data.setupRoot {hexOf Data.setupRoot}; at {← since} ms)"
    flush
    ok := ok && b
  IO.println s!"rec-real-check: {if ok then "every check evaluated holds" else "a check FAILS"} (at {← since} ms)"
  return if ok then 0 else 1
