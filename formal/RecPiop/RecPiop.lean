-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecPiop.Circuit
import RecPiop.LogUp
import RecPiop.Copy
import RecPiop.Dataflow
import RecPiop.Indicator
import RecPiop.Identity
import RecPiop.Sum
import RecPiop.Fold
import RecPiop.Ports
import RecPiop.Rounds
import RecPiop.Numbers
import RecPiop.Vanishing
import RecPiop.SumDeg
import RecPiop.Layout

/-!
# RecPiop: the soundness of π2's PIOP, generic over circuits

π2 is the outer proof of the recursive EVM verifier (`crates/leanvm/rec`, `PI2.md`, `SPEC-REC.md` §2.3, §12), here
**π2v4** (transcript `leanvm-rec-pi2v4`: the ports out of the copy argument, `P` committed in `Q` with its
definition, `q` below `2N`, on the EIP's plain point claims, `Q`'s two claims: the identity's, whose layout forces the
copy sum, and the pushes' after `ρ`; the setup as `κ`, `κ + σ` claimed at `β`, `ξ = κ(t) + βσ(t)` and `s = P(t)` sent,
no `h(t)`). Its copy argument carries the computation over the internal positions: every non-hole pulls
`(w(ω_i), ω_i)` and pushes `(P(ω_i) + κ(ω_i), σ(ω_i))`, `P = P_v = w + Σ_{p internal} I_p (E_p + w)` on `V_m`; the
holes carry the ports, by the term `T = Σ_{port pairs} I_p (E_p + Φ_k)`. Everything here is generic in the layout
(any `N`, row width, regions, blocks, `σ`, `κ`, ports, any `Φ` taking the public fingerprints at the holes).

1. **The circuit** (`RecPiop.Circuit`): `Circuit` (regions of `Forward | Expr | Port` roles, the
   `Expr` formulas of degree at most two, aligned blocks, `σ`, `κ`, the ports); `Valid`, decided
   by `validate` (`validate_eq_true_iff`; `pi2::circuit::Circuit::validate` and
   `spec::Circuit::check_shape`: no formula reads a hole, `κ` only at expression slots, `σ` a
   bijection onto the non-holes and the ports' tags); `Satisfies`, the relation.
2. **The copy argument and the ports in characteristic two** (`RecPiop.LogUp`, `RecPiop.Copy`):
   * set-based logUp: the log-derivative sum of a family of (value, tag) pairs is zero as a
     rational function exactly when every pair is even (`cleared_eq_zero_iff`); **with poles**: plus one term
     `c_k/(d(a_k) d(b_k))` per hole, the poles apart from the family's pairs, it is zero as a rational function
     exactly when the family is even and every `c_k` zero, and otherwise at most `(|s| + 2|H| − 1)·|F|` points
     `(α, β)` make it zero with nonzero denominators (`clearedP_ne_zero`, `card_poles_eq_zero_le`);
   * every internal tag twice, so mod 2 is equality (`eq_of_even_of_pair`, `copy_of_even`);
   * the identity gives the sum with poles (`logSum_of_copyOK`): at a non-hole `h = 1/d_pull + 1/d_push`, at the
     hole of port `j` `h = c_j/(d(a_j) d(b_j))`, `c_j = E_p + F_j` the ports' term; **`card_copyOK_le`**,
     **`prob_copyOK_le`**: a witness that does not satisfy the circuit reaches the state after `α, β, γ` with
     probability at most `(4N − 1 + Σ_j d_j)/|F|`; the ports' `d_j` are `0` (three limbs) and `1` (four limbs) for
     limbs in `K` (`RecPiop.Ports`, `bind_elem`, `bind_root`).
3. **The quotient identities** (`RecPiop.Indicator`, `RecPiop.Identity`, `RecPiop.Layout`): the (block, role)
   indicators, one on their coset, zero on the rest of `V_m`, of degree at most `N − 2^s` (`ind_eval_mem`,
   `ind_eval_not_mem`, `natDegree_ind_le`); the internal pushes with `κ` take the push values on `V_m`, `1_S` the
   holes, `T` the ports' term (`pushPolyV_eval`, `holePoly_eval`, `tPoly_eval`); with `P`'s definition
   `P + P_v + q_P Z_V`, the copy identity evaluates on `V_m` to the copy argument's (`idPoly_eval_omega`).
   **π2v4's layout** (`RecPiop.Layout`, `PI2.md` §7): the identity's claim reads `I = D² H + x Z_V D A + x² Z_V³ G +
   x D R` (`iPoly`, `H = x h` one slot, `G` the prover's slot), of degree at most `5N − 1` (`natDegree_iPoly_le`);
   **`copyOK4_of_iPoly`**: `I = 0` and the definition give `CopyOK4` (`D(0) ≠ 0` forces `H(0) = 0`, `h = H/x` below
   `N − 1`, `Σ_V h = 0` by `sum_eval_eq_zero_of_natDegree_lt` (`RecPiop.SumDeg`: only `x^(N−1)` has a nonzero sum over
   an `F_2`-subspace of `N` points, by Lagrange's interpolation), and `h D + R = 0` on `V_m`); Schwartz–Zippel in `t`
   (`card_iPoly_eval_eq_zero_le`); `Z_V` is the digit `w_m`, what the verifier evaluates (`zV_eq_digitPoly`,
   `zV_eval_eq`, `RecPiop.Vanishing`).
4. **The dataflow lemma** (`RecPiop.Dataflow`): the copy constraints are the witness being a
   fixed point of the circuit's dataflow (`copy_iff_flow`, `satisfies_iff`): expression slots
   (`expr_slot`), constants (`constant_slot`), forward chains (`forward_slot`,
   `forward_chain`, `expr_chain`), and the pushes never read a hole (`push_congr_off_holes`).
5. **The rounds** (`RecPiop.Rounds`, `RecPiop.Fold`): `piop`, π2's PIOP in `Compose.Piop`'s form for any chain with
   π2's rounds (`W` → `α, β, γ`; `Q` → `t`; the fold values, `ξ` and `s` → `ρ`; the claims), its errors proved:
   `(4N − 1 + Σ_j d_j)/|F|` (`card_copyOK4_le`: the copy argument with the vanishing denominators), `(5N − 1)/|F|`,
   `(2^r + 1)/|F|` (`sound_zero`, `sound_one`, `sound_two`; `W`'s fold binds the fold values, `card_foldAt_eq_le`;
   with them and `ξ` right, `Q`'s pushes' claim is a polynomial of degree 2 in `ρ`, nonzero unless `s = P(t)`, `P`'s
   definition at `t` and `S(t) = 0`, and then the identity's claim is `I(t) = 0`, `card_qClaim_le`). In bits at
   `N = 2^24`, `r = 4`, `|F| = 2^192`, times the lists `L_W = 9,952`, `L_Q = 3,564` (`RecPiop.Numbers`): 152.7, 140.6,
   162.8.

**Left to the next layers** (named, not assumed here): the tables' layer `Model` (`W`'s candidate's
polynomial and fold values with `cells_fold`, `Q`'s `H`, `q`, `G`, `P`, `q_P`, `S`, the setup's polynomials, the ports'
`Φ_k` with their values at the holes, the identity's claim's constant `Y³`), the binding hypothesis `hbind` for the candidates
(limbs in `K`: `Ports`), the verifier's arithmetic (the indicators' closed form `w_m/(Ẑ_s(t) + Ẑ_s(c_p))`, `Φ_k` by
rows, the fold's siblings), and the Fiat–Shamir layer and the openings (ListChainU's `hlink`: the openings'
claims give `Post2`).

The build fails if a headline theorem's axioms grow beyond Lean's three standard ones.
-/

/-- info: 'RecPiop.Circuit.validate_eq_true_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.validate_eq_true_iff

/-- info: 'RecPiop.Circuit.push_gamma' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.push_gamma

/-- info: 'RecPiop.card_logSum_eq_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.card_logSum_eq_zero_le

/-- info: 'RecPiop.prob_logSum_eq_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.prob_logSum_eq_zero_le

/-- info: 'RecPiop.cleared_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.cleared_eq_zero_iff

/-- info: 'RecPiop.eq_of_even_of_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.eq_of_even_of_pair

/-- info: 'RecPiop.Circuit.card_entries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.card_entries_le

/-- info: 'RecPiop.Circuit.copy_of_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.copy_of_even

/-- info: 'RecPiop.Circuit.logSum_of_copyOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.logSum_of_copyOK

/-- info: 'RecPiop.Circuit.card_copyOK_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.card_copyOK_le

/-- info: 'RecPiop.Circuit.prob_copyOK_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.prob_copyOK_le

/-- info: 'RecPiop.Circuit.copy_iff_flow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.copy_iff_flow

/-- info: 'RecPiop.Circuit.satisfies_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.satisfies_iff

/-- info: 'RecPiop.Circuit.expr_slot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.expr_slot

/-- info: 'RecPiop.Circuit.constant_slot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.constant_slot

/-- info: 'RecPiop.Circuit.forward_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.forward_slot

/-- info: 'RecPiop.Circuit.forward_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.forward_chain

/-- info: 'RecPiop.Circuit.expr_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.expr_chain

/-- info: 'RecPiop.Circuit.push_congr_off_holes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.push_congr_off_holes

/-- info: 'RecPiop.Circuit.flow_congr_off_holes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.flow_congr_off_holes

/-- info: 'RecPiop.Points.ofCantor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Points.ofCantor

/-- info: 'RecPiop.Circuit.ind_eval_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.ind_eval_mem

/-- info: 'RecPiop.Circuit.ind_eval_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.ind_eval_not_mem

/-- info: 'RecPiop.Circuit.natDegree_ind_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.natDegree_ind_le

/-- info: 'RecPiop.Circuit.exists_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.exists_pair

/-- info: 'RecPiop.Circuit.pair_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.pair_unique

/-- info: 'RecPiop.Circuit.holePoly_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.holePoly_eval

/-- info: 'RecPiop.Circuit.idPoly_eval_omega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.idPoly_eval_omega

/-- info: 'RecPiop.Circuit.copyOK_of_idPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.copyOK_of_idPoly

/-- info: 'RecPiop.Circuit.natDegree_idPoly_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.natDegree_idPoly_le

/-- info: 'RecPiop.Circuit.card_idPoly_eval_eq_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.card_idPoly_eval_eq_zero_le

/-- info: 'RecPiop.Circuit.pushPolyV_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.pushPolyV_eval

/-- info: 'RecPiop.Circuit.natDegree_pushPolyV_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.natDegree_pushPolyV_le

/-- info: 'RecPiop.SetupPolys.ofInterpolate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.SetupPolys.ofInterpolate

/-- info: 'RecPiop.sum_tablePoly_omega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.sum_tablePoly_omega

/-- info: 'RecPiop.card_foldAt_eq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.card_foldAt_eq_le

/-- info: 'RecPiop.Circuit.bind_elem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.bind_elem

/-- info: 'RecPiop.Circuit.bind_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.bind_root

/-- info: 'RecPiop.pre_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.pre_post

/-- info: 'RecPiop.sound_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.sound_zero

/-- info: 'RecPiop.sound_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.sound_one

/-- info: 'RecPiop.sound_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.sound_two

/-- info: 'RecPiop.piop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.piop

/-- info: 'RecPiop.bits_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.bits_copy

/-- info: 'RecPiop.bits_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.bits_t

/-- info: 'RecPiop.bits_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.bits_rho

/-- info: 'RecPiop.Circuit.zV_eq_digitPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.zV_eq_digitPoly

/-- info: 'RecPiop.Circuit.zV_eval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.zV_eval_eq

/-- info: 'RecPiop.card_poles_eq_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.card_poles_eq_zero_le

/-- info: 'RecPiop.clearedP_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.clearedP_ne_zero

/-- info: 'RecPiop.Circuit.tPoly_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.tPoly_eval

/-- info: 'RecPiop.Circuit.natDegree_defPoly_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.natDegree_defPoly_le

/-- info: 'RecPiop.card_pushComb_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.card_pushComb_le

/-- info: 'RecPiop.Circuit.card_qClaim_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.card_qClaim_le

/-- info: 'RecPiop.Circuit.card_copyOK4_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.card_copyOK4_le

/-- info: 'RecPiop.Circuit.copyOK4_of_iPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.copyOK4_of_iPoly

/-- info: 'RecPiop.Circuit.card_iPoly_eval_eq_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.card_iPoly_eval_eq_zero_le

/-- info: 'RecPiop.sum_eval_eq_zero_of_natDegree_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.sum_eval_eq_zero_of_natDegree_lt

/-- info: 'RecPiop.Circuit.qClaim_of_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.qClaim_of_eval
