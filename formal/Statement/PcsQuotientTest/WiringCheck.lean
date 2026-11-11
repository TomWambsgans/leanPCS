-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: the runner of `E2ECompleteness.Pcs.H.WiringCheck` (formal/EndToEnd/Completeness/E2ECompleteness/PcsHBad.lean).
import PcsQuotient

/-!
# The evaluated check on the deployed wiring table

`E2ECompleteness.completeness_end` assumes `WiringCheck`: the deployed circuit's wiring table
(`(membership logRows).wiringTable`, the coefficients of `σ`'s points in the novel basis) has entry `2^24 − 1` zero
and entry `2^24 − 2` nonzero. This runner computes the table with the Statement's own definitions (compiled) and
prints the two entries' words and the verdict; it exits with code `1` if the check fails.

```sh
lake exe membership-wiring-check
```
-/

open PcsQuotient

def main : IO UInt32 := do
  let wt := (membership logRows).wiringTable
  let top := (wt.getD (2 ^ 24 - 1) 0).lane
  let sub := (wt.getD (2 ^ 24 - 2) 0).lane
  IO.println s!"wiring table: {wt.size} words"
  IO.println s!"entry 2^24 - 1: {top}"
  IO.println s!"entry 2^24 - 2: {sub}"
  if top == 0 && sub != 0 then
    IO.println "WiringCheck: holds"
    return 0
  else
    IO.println "WiringCheck: FAILS"
    return 1
