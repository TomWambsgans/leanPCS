-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Transcribed from `crates/leanvm/rec/src/pi2/verifier.rs`
-- (`SpecPair`, `Group`, `PortTerm`, `Spec`, `Spec::of`, `is_zero`, `normalised_constants`) and
-- `crates/leanvm/rec/src/pi2/circuit.rs` (`coset_constants`, `vanishing`, `pair_constants`, `Circuit::max_gamma`),
-- π2v2's PIOP, as π2v4 (`leanvm-rec-pi2v4`, main `7e6d353c`) keeps it. The Cantor basis is `formal/UniStatement`'s (`beta`, `point`).
import RecStatement.Basic
import RecStatement.Core

/-!
# What the verifier is built from (`Spec::of`)

From the circuit (`Circuit`, the data the Rust emits), the verifier's constants, computed here as the Rust
computes them, in `K`:

* the blocks' vanishing polynomials `Z_{U_s}` of `U_s = span(β_r, …, β_{r+s−1})` (`r` the rows' log):
  `Z_{U_0}(x) = x`, `Z_{U_s} = Z_{U_{s−1}}² + e_s Z_{U_{s−1}}`, `e_s = Z_{U_{s−1}}(β_{r+s−1})`
  (`cosetConstants`, `vanishing`);
* each pair's `Ẑ_s(c_p) = Z_{U_s}(c_p) / Π_{j ≤ s} e_j`, `c_p = ω_{first_row · 2^r + role}` (`pairConstants`), and the
  normalised recursion's constants `c_s = Π_{j < s} e_j / e_s` (`normalisedConstants`): `Ẑ_s = Ẑ_{s−1} + c_s Ẑ_{s−1}²`;
* the **groups**: the pairs of one role, one pull flag and one formula (equal as values), in first appearance;
* **the ports' `Φ`** (`phiOf`): the public terms of nonzero value (`PublicTerm.isZero`: no terms, no nonzero
  constant), each as its hole's row and its value, grouped by its hole's role in first appearance (`Φ_k(x) =
  Σ_J F_J w_m(x)/(w_r(x) + ω_{y_J})`, `PI2.md` §1); the zero ports (π1's zero checks, their padding) are in no `Φ`;
* `maxGamma`, the highest power of `γ` a coefficient takes; `ports`, the public terms' count.
-/

namespace RecStatement

open LeanVM.Parameters UniStatement

/-- `vanishing(x, e, s)`: `Z_{U_s}(x)`, by `z ↦ z² + e_j z` for `j < s`. -/
def vanishing (x : K) (e : List K) (s : ℕ) : K := vanishingF x e s

/-- **`coset_constants(r, count)`**: `e_1 … e_count`, `e_s = Z_{U_{s−1}}(β_{r+s−1})`. -/
def cosetConstants (r count : ℕ) : List K := cosetConstantsF (fun s ↦ beta.getD (r + s) 0) count

/-- **`pair_constants(pair, r, e)`**: `Z_{U_s}(c_p)` and `Π_{j < s} e_j`, `c_p = ω_{first_row · 2^r + role}`. -/
def pairConstants (p : Pair) (r : ℕ) (e : List K) : K × K :=
  (vanishing (point (p.firstRow * 2 ^ r + p.role)) e p.logRows, (e.take p.logRows).foldl (· * ·) 1)

/-- **`normalised_constants(e)`**: `c_s = Π_{j < s} e_j / e_s`. -/
def normalisedConstants (e : List K) : List K := normalisedConstantsF e

/-- A pair as the verifier needs it (`SpecPair`): its block's rows' log `s` and `Ẑ_s(c_p)`. -/
structure SpecPair where
  logRows : ℕ
  z : K
  deriving DecidableEq, Repr, Inhabited

/-- **A group** (`Group`): the pairs of one role, one pull flag and one formula. -/
structure Group where
  role : ℕ
  formula : Formula
  pulls : Bool
  pairs : List ℕ
  deriving DecidableEq, Repr, Inhabited

/-- **What the verifier is built from** (`Spec`). -/
structure Spec where
  logN : ℕ
  logRow : ℕ
  pairs : List SpecPair
  groups : List Group
  /-- The pull-less pairs (the holes). -/
  pullLess : List ℕ
  /-- `c_1, …`: `Ẑ_s = Ẑ_{s−1} + c_s Ẑ_{s−1}²`. -/
  c : List K
  reads : List Read
  /-- The ports of nonzero value by role: `(k, [(y_J, F_J)])`, the hole's row and the port's value. -/
  phi : List (ℕ × List (ℕ × Lin))
  /-- The public terms' count. -/
  ports : ℕ
  maxGamma : ℕ
  deriving Inhabited

/-- The highest power of `γ` in a linear form (`max_gamma`'s `lin`). -/
def Lin.maxGamma (l : Lin) : ℕ :=
  ((l.terms.map fun t ↦ t.1.gamma) ++ (l.constant.map (·.gamma)).toList).foldl max 0

/-- **`Circuit::max_gamma`**: over the formulas (a product's coefficient's power plus its two forms') and the public
terms. -/
def Circuit.maxGamma (c : Circuit) : ℕ :=
  let formulas := c.formulas.map fun f ↦
    ((f.products.map fun (k, a, b) ↦ k.gamma + a.maxGamma + b.maxGamma) ++ [f.lin.maxGamma]).foldl max 0
  (formulas ++ c.publicTerms.map (·.value.maxGamma)).foldl max 0

/-- The groups: each pair joins the first group of its role, pull flag and formula, or starts one. -/
def groupsOf (c : Circuit) : List Group :=
  (List.range c.pairs.length).foldl (fun gs i ↦
    let p := c.pairs.getD i default
    let f := c.formulas.getD p.formula default
    match gs.findIdx? (fun g ↦ g.role = p.role ∧ g.pulls = p.pulls ∧ g.formula = f) with
    | some j => gs.modify j fun g ↦ { g with pairs := g.pairs ++ [i] }
    | none => gs ++ [⟨p.role, f, p.pulls, [i]⟩]) []

/-- **`is_zero`**: a term of value zero (no terms, no constant or a zero one): a zero check, its padding. -/
def PublicTerm.isZero (t : PublicTerm) : Bool :=
  t.value.terms.isEmpty && t.value.constant.all fun c ↦ c.c0 == 0 && c.c1 == 0 && c.c2 == 0

/-- **The ports' `Φ`** (`Spec::of`'s `phi`): each public term of nonzero value, its hole's row and its value, added
to its hole's role's list (`at % 2^r`, `at / 2^r`), the roles in first appearance. -/
def phiOf (c : Circuit) : List (ℕ × List (ℕ × Lin)) :=
  (List.range c.publicTerms.length).foldl (fun acc j ↦
    let term := c.publicTerms.getD j default
    if term.isZero then acc
    else
      let at' := c.holes.getD j 0
      let role := at' % 2 ^ c.logRow
      let port : ℕ × Lin := (at' / 2 ^ c.logRow, term.value)
      match acc.findIdx? (·.1 = role) with
      | some i => acc.modify i fun kt ↦ (kt.1, kt.2 ++ [port])
      | none => acc ++ [(role, [port])]) []

/-- **`Spec::of(circuit)`** (the circuit's validity, which the Rust asserts, is not checked here). -/
def Spec.of (c : Circuit) : Spec :=
  let (m, r) := (c.logN, c.logRow)
  let e := cosetConstants r (m - r)
  { logN := m
    logRow := r
    pairs := c.pairs.map fun p ↦
      let (z, norm) := pairConstants p r e
      ⟨p.logRows, z * norm⁻¹⟩
    groups := groupsOf c
    pullLess := (List.range c.pairs.length).filter fun i ↦ !(c.pairs.getD i default).pulls
    c := normalisedConstants e
    reads := c.reads
    phi := phiOf c
    ports := c.publicTerms.length
    maxGamma := c.maxGamma }

/-- The scalars the proof sends after the roots (`Spec::values`): the `2^r` fold values, `ξ` and `s`. -/
def Spec.values (s : Spec) : ℕ := 2 ^ s.logRow + 2

/-- The largest block (`Spec::max_log_rows`). -/
def Spec.maxLogRows (s : Spec) : ℕ := (s.pairs.map (·.logRows)).foldl max 0

end RecStatement
