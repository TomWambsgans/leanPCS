-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Kc3.Protocol
import Kc3.Pole
import Kc3.Cells
import Kc3.RoundOne
import Kc3.RoundTwo
import Kc3.Conic
import Kc3.RoundThree
import Kc3.States
import Kc3.Cantor

/-!
# `Kc3`: the deployed membership reduction (`pcs-quotient-kc3`) as polynomials (F1)

The reduction of `docs/membership/PROTOCOL.md` with its tables read as the polynomials they hold, and its three
challenges' soundness:

| File | What |
|---|---|
| `Protocol.lean` | `Params` (a circuit's geometry, wiring, pins, random rows, `hSum`), the two messages, the identity `X Z q + d d' P + X R`, `Accepts`, the states, `E1`, `D2`, `roundError` |
| `Pole.lean` | **the pole lemma** (`card_pole_le`) and the first challenge's count, generically (`card_round1_core`) |
| `Cells.lean` | the polynomials on the cells; `Z g` there is the gate's or the pin's error (`errAt_row`, `errAt_pin`, `errAt_other`) |
| `RoundOne.lean` | **the sum by the layout** (`consistent_sum`) and **`card_round1_le`**: at most `E1 q² = 8 n q²` triples `(α, β, μ)` |
| `RoundTwo.lean` | the identity's degree at most `4 n − 1`; **`card_round2_le`**: at most `D2 = 4 n` points `t` |
| `Conic.lean` | the witness claim's conic: the claim is the three values' (`conic_identity`), the conic spans its plane (`conicCoeffs_ne_zero`), **`card_conic_le`** |
| `RoundThree.lean` | with the true values the copy claim is the identity at `t` (`consistentAt_of_accepts`); **`card_round3_le`**: at most `3` values `ρ` |
| `States.lean` | the rounds as states (`card_state₂_le`, `card_state₄_le`, `card_state₆_le`), `round₁_le`, `round₂_le`, `round₃_le`, `roundError_deployed` (`2^-165` at `n = 2^24`, `q = 2^192`) |
| `Cantor.lean` | **`Params.ofCantor`**: the instance on a Cantor basis, `hSum` proved (`sum_cells_eq_zero`) |
-/

/-- info: 'Kc3.Params.card_round1_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kc3.Params.card_round1_le

/-- info: 'Kc3.Params.card_round2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kc3.Params.card_round2_le

/-- info: 'Kc3.Params.card_round3_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kc3.Params.card_round3_le

/-- info: 'Kc3.Params.card_state₂_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kc3.Params.card_state₂_le

/-- info: 'Kc3.Params.card_state₄_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kc3.Params.card_state₄_le

/-- info: 'Kc3.Params.card_state₆_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kc3.Params.card_state₆_le

/-- info: 'Kc3.Params.round₁_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kc3.Params.round₁_le

/-- info: 'Kc3.Params.round₂_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kc3.Params.round₂_le

/-- info: 'Kc3.Params.round₃_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kc3.Params.round₃_le

/-- info: 'Kc3.Params.roundError_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kc3.Params.roundError_deployed

/-- info: 'Kc3.Params.ofCantor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kc3.Params.ofCantor
