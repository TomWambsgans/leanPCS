-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Transcribed from `crates/leanvm/rec/src/pi2/verifier.rs`
-- (`reduce`'s arithmetic after the transcript: `coeff`, `lin`, `formula`, the digits, the row's cells by the
-- siblings' fold, the blocks' `Ẑ_s(t)`, the groups' fractions, the ports' `Φ_k` by rows, the internal pushes' and the
-- ports' fractions, the identity, the one inversion, the claims), π2v4 (`leanvm-rec-pi2v4`, main 7e6d353c: `Q`'s two
-- claims, the copy sum from `Q`'s layout; `stack_vars`). `sq` is
-- `formal/QuotientSecurity`'s (`Cantor.lean`).
import Mathlib.Algebra.Field.Basic
import QuotientSecurity.Cantor

/-!
# The verifier's arithmetic at `t`, over any field (π2v4)

`pi2::verifier::reduce` after it has read the stream and drawn its challenges: a function of the public scalars,
`α, β, γ, t`, the fold values `a_k`, `ξ`, `s` and `ρ`, **generic in the field** as the Rust is generic in its
`Scalar` (the deployed verifier runs it on `E`, `RecStatement.Verifier`; the lemmas, `RecStatement.Lemmas`, prove
what it computes over any field of characteristic two). Every intermediate value is a field of `Out`, in the Rust's
order (`PI2.md` §2, steps 1–7):

1. the digits `w_0 … w_m`, `w_{l+1} = w_l² + w_l` (`sq`);
2. the row's cells `v_c` by the siblings' fold (`cellsList`, `PI2.md` §9 lever 3a: the odd child is the even one
   plus the difference);
3. `Ẑ_s(t)` for every block size (`zHat`), each group's indicators summed as one fraction `N_g/D_g`
   (`fraction`), `w_m` factored out;
4. the ports' `Φ_k(t)/w_m = G_n/G_d = Σ_J F_J/(w_r + ω_{y_J})` for each port role (`phiFrac`);
5. the internal pushes' `A/B` over the pulling groups and the ports' `R_n/R_d = Σ_g (N_g/D_g)(E_g + Δ + Φ_k)` over
   the pull-less ones (`pushSums`), `Δ = d_pull + d_push`, `d_pull = α + v_0 + βt`, `d_push = α + s + ξ`;
6. `D_n`, `num_1`, `num_3`; `Y_1 = c_h + t w_m`, `Y_2 = c_h + t w_m²`, `Y_3 = 1 + ρ (1 + w_m)`; the one inversion of
   `R_d Y_1 Y_2 · B · w_m · Y_3 · c_h D_n`; the digits' inverses down from `1/w_m`;
7. the claims, each a point of its stack (`stackVars`; past the table's coordinates, zeros): `W` at
   `(ρ, ρ², …, w_r, …, w_{m−1})` (`foldAt`'s value), the setup at `(w_0, …, w_{m−1}, β)`, `Q` at `(u_0, …, u_{m−1},
   z_0, z_1, y_0, y_1)`, `z_0 = t w_m/Y_1`, `z_1 = t w_m²/Y_2` (the identity's: `H + a q + a r_1 G` and, by `Y³`,
   `P + a q_P + a r_1 S`, `a = t w_m/c_h`, `r_1 = a w_m`), and at `(u_0, …, u_{m−1}, ρ, z'_1, 1, 1)`, `z'_1 = ρ w_m/Y_3`
   (the pushes': `P + a' q_P + a' r'_1 S`, `a' = ρ/(1 + ρ)`, `r'_1 = a' w_m`). No sum claim (`PI2.md` §7).

**Deviations, none changing a value**: the Rust skips a product by a coefficient equal to one and, for a one-pair
group, its numerator `1` (here the products are taken: `1 · x = x`); `γ^g` is read from the list of powers as the
Rust's `gammas[g]` (for `g = 0` the Rust takes the value itself, `gammas[0] = 1`); the inverse is the field's (the
Rust's is the norm's, `RecStatement.Inverse`, the same value); a port role's fraction of no term (which the Rust's
`Spec::of` never makes, and which would panic) is `(0, 1)`.
-/

namespace RecStatement

open QuotientSecurity

variable {F : Type} [Field F]

/-! ## The circuit's formulas over `F` -/

/-- **A coefficient over `F`**: a value times `γ^gamma`. -/
structure CoeffF (F : Type) where
  value : F
  gamma : ℕ

/-- **A linear form over `F`**: `Σ coefficient · cell` plus a constant. -/
structure LinF (F : Type) where
  terms : List (CoeffF F × ℕ)
  constant : Option (CoeffF F)

/-- **A formula over `F`**: a linear form plus products of two linear forms. -/
structure FormulaF (F : Type) where
  lin : LinF F
  products : List (CoeffF F × LinF F × LinF F)

/-- **A group over `F`**: its role, its formula, whether it pulls, its pairs. -/
structure GroupF (F : Type) where
  role : ℕ
  formula : FormulaF F
  pulls : Bool
  pairs : List ℕ

/-- `coeff(c, gammas)`: the value times `γ^gamma`, read from the powers. -/
def CoeffF.eval (gs : List F) (c : CoeffF F) : F := c.value * gs.getD c.gamma 0

/-- `lin(l, cell, gammas)`. -/
def LinF.eval (gs : List F) (cell : ℕ → F) (l : LinF F) : F :=
  l.terms.foldl (fun acc t ↦ acc + t.1.eval gs * cell t.2) (match l.constant with
    | none => 0
    | some c => c.eval gs)

/-- `formula(f, cell, gammas)`. -/
def FormulaF.eval (gs : List F) (cell : ℕ → F) (f : FormulaF F) : F :=
  f.products.foldl (fun acc p ↦ acc + p.1.eval gs * (p.2.1.eval gs cell * p.2.2.eval gs cell))
    (f.lin.eval gs cell)

/-- `powers(γ, n)`: `[1, γ, …, γ^(n−1)]`. -/
def powersList (γ : F) (n : ℕ) : List F := (List.range n).map (γ ^ ·)

/-! ## The verifier's constants over `F` -/

/-- **What the arithmetic is built from**, over `F`: the shape, the pairs (`(s, Ẑ_s(c_p))`), the groups, the
normalised recursion's constants, the ports of nonzero value by role (`(k, [(y_J, F_J)])`: the hole's row and the
port's value), the highest power of `γ`, the extension's coordinates `(y_0, y_1)` and scale `s`, and the points
`ω`. -/
structure CoreSpec (F : Type) where
  logN : ℕ
  logRow : ℕ
  pairs : List (ℕ × F)
  groups : List (GroupF F)
  c : List F
  phi : List (ℕ × List (ℕ × LinF F))
  maxGamma : ℕ
  y0 : F
  y1 : F
  scale : F
  /-- `Y³`, limb code `3`'s weight at `(y_0, y_1)` over the scale (`F192::Y` cubed). -/
  yCube : F
  ω : ℕ → F

/-- The largest block's rows' log. -/
def CoreSpec.maxLogRows (S : CoreSpec F) : ℕ := (S.pairs.map (·.1)).foldl max 0

/-- **What the transcript gives the arithmetic**: the public scalars and the proof's values and challenges. -/
structure Inputs (F : Type) where
  scalars : List F
  α : F
  β : F
  γ : F
  t : F
  a : List F
  ξ : F
  s : F
  ρ : F

/-! ## The steps -/

/-- **The digits** `w_0(t), …, w_{count−1}(t)`, `w_l = s^l(t)`. -/
def digitsList (t : F) (count : ℕ) : List F := (List.range count).map fun l ↦ sq^[l] t

/-- One level of the row's fold (`PI2.md` §9 lever 3a): each parent `k`, at `z = w_l + ω(2k)`, gives its even
child `p_j + z (p_j + p_{j+half})` and its odd child, the even one plus the difference `p_j + p_{j+half}`. -/
def foldLevel (ω : ℕ → F) (w : List F) (l : ℕ) (layer : List (List F)) : List (List F) :=
  let half := 2 ^ l
  (List.range layer.length).flatMap fun k ↦
    let parent := layer.getD k []
    let z := w.getD l 0 + ω (2 * k)
    let d := (List.range half).map fun j ↦ parent.getD j 0 + parent.getD (j + half) 0
    let even := (List.range half).map fun j ↦ parent.getD j 0 + z * d.getD j 0
    let odd := (List.range half).map fun j ↦ even.getD j 0 + d.getD j 0
    [even, odd]

/-- **The row's cells** `v_c = w(t + ω_c)` from the fold values, the top variable folded first. -/
def cellsList (ω : ℕ → F) (w : List F) (r : ℕ) (a : List F) : List F :=
  ((List.range r).reverse.foldl (fun layer l ↦ foldLevel ω w l layer) [a]).map (·.getD 0 0)

/-- **`Ẑ_s(x)`**: `Ẑ_0(x) = x`, `Ẑ_{s+1}(x) = Ẑ_s(x) + c_{s+1} Ẑ_s(x)²`. -/
def zHat (c : List F) : ℕ → F → F
  | 0, x => x
  | s + 1, x => zHat c s x + c.getD s 0 * (zHat c s x * zHat c s x)

/-- **`vanishing(x, e, s)`**: `Z_{U_s}(x)` by `z ↦ z² + e_j z` for `j < s` (`pi2::circuit::vanishing`). -/
def vanishingF (x : F) (e : List F) (s : ℕ) : F :=
  (List.range s).foldl (fun z j ↦ z * z + e.getD j 0 * z) x

/-- **`coset_constants`**: `e_s = Z_{U_s}(b_s)` for `s < count`, `b` the subspace's basis (`β_{r+s}`). -/
def cosetConstantsF (b : ℕ → F) (count : ℕ) : List F :=
  (List.range count).foldl (fun e s ↦ e ++ [vanishingF (b s) e s]) []

/-- **`normalised_constants(e)`**: `c_s = Π_{j < s} e_j / e_s`. -/
def normalisedConstantsF (e : List F) : List F :=
  (e.foldl (fun (acc : List F × F) x ↦ (acc.1 ++ [acc.2 * x⁻¹], acc.2 * x)) ([], 1)).1

/-- **A sum of inverses as one fraction**: `Σ 1/x_i = N/D` by `N ← N x + D`, `D ← D x`, from `(1, x_0)`. -/
def fraction : List F → F × F
  | [] => (0, 1)
  | x :: xs => xs.foldl (fun nd y ↦ (nd.1 * y + nd.2, nd.2 * y)) (1, x)

/-- Each group's indicators' denominators `Ẑ_s(t) + Ẑ_s(c_p)`, `Ẑ_s(t)` read from `zt`. -/
def groupDens (S : CoreSpec F) (zt : List F) (g : GroupF F) : List F :=
  g.pairs.map fun p ↦ let q := S.pairs.getD p (0, 0); zt.getD q.1 0 + q.2

/-- `x` squared `i` times: `x^(2^i)`. -/
def sqIter (x : F) (i : ℕ) : F := (fun y ↦ y * y)^[i] x

/-- **A port role's `Φ_k(t)/w_m` as one fraction** `G_n/G_d = Σ_J F_J/(w_r + ω_{y_J})`: from the first term
`(F_0, w_r + ω_{y_0})`, `N ← N x + D F`, `D ← D x`. -/
def phiFrac (ω : ℕ → F) (gs pubs : List F) (wr : F) : List (ℕ × LinF F) → F × F
  | [] => (0, 1)
  | (y, l) :: rest => rest.foldl (fun nd yl ↦
      (nd.1 * (wr + ω yl.1) + nd.2 * yl.2.eval gs (fun c ↦ pubs.getD c 0), nd.2 * (wr + ω yl.1)))
      (l.eval gs (fun c ↦ pubs.getD c 0), wr + ω y)

/-- `add` of the pushes' fractions: `(a, b) ↦ (a d + b X, b d)`, or the first term `(X, d)`. -/
def addFrac : Option (F × F) → F → F → Option (F × F)
  | some (a, b), x, d => some (a * d + b * x, b * d)
  | none, x, d => some (x, d)

/-- **One group's step of the pushes' sums**: a pulling group adds `N_g X/D_g` to `A/B` (`X = E_g(v_{c ⊕ k_g}) +
v_0`; one pair, `X/d`); a pull-less group adds `N_g X/(D_g G_d)` to `R_n/R_d`, `X = (E_g + Δ) G_d + w_m G_n` for its
role's `Φ`, `E_g + Δ` (and `D_g`) for a role of no port of nonzero value. -/
def pushStep (gs cells : List F) (v0 delta : F) (wPhi : List (ℕ × F × F))
    (acc : Option (F × F) × Option (F × F)) (gf : GroupF F × (F × F)) : Option (F × F) × Option (F × F) :=
  let g := gf.1
  let nd := gf.2
  let e := g.formula.eval gs (fun c ↦ cells.getD (c ^^^ g.role) 0)
  let single := g.pairs.length = 1
  if g.pulls then
    let value := e + v0
    (addFrac acc.1 (if single then value else nd.1 * value) nd.2, acc.2)
  else
    let vd : F × F := match wPhi.find? (·.1 = g.role) with
      | some (_, n, d) => ((e + delta) * d + n, nd.2 * d)
      | none => (e + delta, nd.2)
    (acc.1, addFrac acc.2 (if single then vd.1 else nd.1 * vd.1) vd.2)

/-- **The internal pushes' sum and the ports'** `(A, B, R_n, R_d)` (`pushStep` over the groups). -/
def pushSums (S : CoreSpec F) (gs cells : List F) (v0 delta : F) (wPhi : List (ℕ × F × F))
    (fracs : List (F × F)) : F × F × F × F :=
  let r := (S.groups.zip fracs).foldl (pushStep gs cells v0 delta wPhi) (none, none)
  ((r.1.map (·.1)).getD 0, (r.1.map (·.2)).getD 1, (r.2.map (·.1)).getD 0, (r.2.map (·.2)).getD 1)

/-- **The stacks' variables** (`stack_vars`): `W` `m`, `Q` `m + 4` (sixteen slots of `2^m`), the setup `m + 1`, each
at least `24` (`MIN_CERTIFIED_STACK`) from `m = 20` (`CERTIFIED_FROM`), else at least `15` (`MIN_LOG_STACK`). -/
def stackVars (m : ℕ) : ℕ × ℕ × ℕ :=
  let least := if 20 ≤ m then 24 else 15
  (max m least, max (m + 4) least, max (m + 1) least)

/-- A point resized to a stack's variables (`resize(vars, 0)`): zeros past the table's coordinates. -/
def padded (p : List F) (vars : ℕ) : List F := (p ++ List.replicate vars 0).take vars

/-- **Every value the arithmetic computes**, in the Rust's order. -/
structure Out (F : Type) where
  digits : List F
  cells : List F
  zt : List F
  groupFracs : List (F × F)
  phis : List (ℕ × F × F)
  num : F
  den : F
  rNum : F
  rDen : F
  dPull : F
  dPush : F
  delta : F
  ch : F
  tz : F
  y1 : F
  y2 : F
  y3 : F
  dN : F
  num1 : F
  num3 : F
  p1 : F
  p2 : F
  p3 : F
  p4 : F
  p5 : F
  cd : F
  all : F
  invAll : F
  invP5 : F
  invY3 : F
  invP4 : F
  invZ : F
  invP3 : F
  invP2 : F
  invY2 : F
  invP1 : F
  invY1 : F
  wInvs : List F
  z0 : F
  z1 : F
  zp1 : F
  quotientValue : F
  pushesValue : F
  uList : List F
  rhos : List F
  fold : F
  witnessPoint : List F
  quotientPoint : List F
  pushesPoint : List F
  setupPoint : List F

/-- `1/w_l = (1 + w_l)/w_{l+1}` down from `1/w_top`: the list `1/w_0, …, 1/w_top`. -/
def wInvsList (w : List F) (top : ℕ) (invTop : F) : List F :=
  (List.range top).reverse.foldl (fun acc l ↦ ((1 + w.getD l 0) * acc.headD 0) :: acc) [invTop]

/-- `W`'s fold at `(ρ, ρ², …)`: `fold_j ← fold_j + ρ^(2^l) (fold_j + fold_{j+half})`, the top variable first. -/
def foldW (rhos : List F) (r : ℕ) (a : List F) : F :=
  ((List.range r).reverse.foldl (fun cur l ↦
    (List.range (2 ^ l)).map fun j ↦ cur.getD j 0 + rhos.getD l 0 * (cur.getD j 0 + cur.getD (j + 2 ^ l) 0)) a).getD 0 0

/-- **The arithmetic** (`reduce` after the transcript). -/
def CoreSpec.run (S : CoreSpec F) (inp : Inputs F) : Out F :=
  let m := S.logN
  let r := S.logRow
  let t := inp.t
  let w := digitsList t (m + 1)
  let cells := cellsList S.ω w r inp.a
  let v0 := cells.getD 0 0
  let zt := (List.range (S.maxLogRows + 1)).map fun s ↦ zHat S.c s t
  let fracs := S.groups.map fun g ↦ fraction (groupDens S zt g)
  let gs := powersList inp.γ (S.maxGamma + 1)
  let wm := w.getD m 0
  let phis := S.phi.map fun kt ↦ (kt.1, phiFrac S.ω gs inp.scalars (w.getD r 0) kt.2)
  let dPull := inp.α + v0 + inp.β * t
  let dPush := inp.α + inp.s + inp.ξ
  let delta := dPull + dPush
  let wPhi := phis.map fun knd ↦ (knd.1, wm * knd.2.1, knd.2.2)
  let (num, den, rNum, rDen) := pushSums S gs cells v0 delta wPhi fracs
  let ch := dPull * dPush
  let tz := t * wm
  let y1 := ch + tz
  let y2 := ch + tz * wm
  let y3 := 1 + inp.ρ + inp.ρ * wm
  let dN := (inp.α + v0 + inp.ξ) * den + wm * num
  let num1 := delta * rDen + wm * rNum
  let num3 := dN + dPush * den
  let p1 := rDen * y1
  let p2 := p1 * y2
  let p3 := p2 * den
  let p4 := p3 * wm
  let p5 := p4 * y3
  let cd := ch * dN
  let all := p5 * cd
  let invAll := all⁻¹
  let invP5 := invAll * cd
  let invY3 := invP5 * p4
  let invP4 := invP5 * y3
  let invZ := invP4 * p3
  let invP3 := invP4 * wm
  let invP2 := invP3 * den
  let invY2 := invP2 * p1
  let invP1 := invP2 * y2
  let invY1 := invP1 * rDen
  let wInvs := wInvsList w m invZ
  let z0 := tz * invY1
  let z1 := tz * wm * invY2
  let zp1 := inp.ρ * wm * invY3
  let quotientValue := S.scale * t * ch * (t * (num1 * den) + S.yCube * (rDen * (ch * (inp.s * den) + t * num3))) *
    invP4
  let pushesValue := t * (1 + inp.ρ) * ((1 + inp.ρ) * (wm * (inp.s * den)) + inp.ρ * num3) * (invP5 * p2) * invZ
  let uList := (List.range m).map fun l ↦ 1 + wInvs.getD l 0 + wInvs.getD (l + 1) 0
  let vars := stackVars m
  let rhos := (List.range r).map fun l ↦ sqIter inp.ρ l
  { digits := w
    cells := cells
    zt := zt
    groupFracs := fracs
    phis := phis
    num := num
    den := den
    rNum := rNum
    rDen := rDen
    dPull := dPull
    dPush := dPush
    delta := delta
    ch := ch
    tz := tz
    y1 := y1
    y2 := y2
    y3 := y3
    dN := dN
    num1 := num1
    num3 := num3
    p1 := p1
    p2 := p2
    p3 := p3
    p4 := p4
    p5 := p5
    cd := cd
    all := all
    invAll := invAll
    invP5 := invP5
    invY3 := invY3
    invP4 := invP4
    invZ := invZ
    invP3 := invP3
    invP2 := invP2
    invY2 := invY2
    invP1 := invP1
    invY1 := invY1
    wInvs := wInvs
    z0 := z0
    z1 := z1
    zp1 := zp1
    quotientValue := quotientValue
    pushesValue := pushesValue
    uList := uList
    rhos := rhos
    fold := foldW rhos r inp.a
    witnessPoint := padded (rhos ++ (w.drop r).take (m - r)) vars.1
    quotientPoint := padded (uList ++ [z0, z1, S.y0, S.y1]) vars.2.1
    pushesPoint := padded (uList ++ [inp.ρ, zp1, 1, 1]) vars.2.1
    setupPoint := padded (w.take m ++ [inp.β]) vars.2.2 }

end RecStatement
