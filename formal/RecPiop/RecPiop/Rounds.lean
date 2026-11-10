-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The round-by-round form is
-- `formal/Compose/Compose/ListChainK.lean`'s `Piop`, as `formal/UniSound/UniSound/Piop.lean` builds it
-- for the univariate PIOP; the counting of uniform draws is `formal/UniSound/UniSound/Prob.lean`'s,
-- for any field.
import RecPiop.Identity
import RecPiop.Fold
import RecPiop.Vanishing
import Compose.ListChainK

/-!
# π2's PIOP, round by round (π2v3)

π2's rounds as the chain sees them (`pi2Rounds`; `PI2.md` §2):

| round | message | challenges |
|---|---|---|
| `0` | `W`'s root and out-of-domain answer | `α, β, γ` |
| `1` | `Q`'s root and out-of-domain answer | `t` |
| `2` | the `2^r` fold values `a_k`, `ξ = κ(t) + βσ(t)` and `s = P(t)` | `ρ` |

then the claims (no challenge follows; π2v3): `W`'s fold at `ρ`; `Q`'s three: the identity's at `(u, ρ', y_0, y_1)`
(the copy identity at `t`, weighing `P` and `q_P` too), the pushes' at `(u, ρ, 1, 1)` (`P(t) = s` and `P`'s definition
at `t`, combined by `ρ`, drawn after `s`) and the top coefficient (`Σ_V h`); the setup's at `β`.

**The candidates** (`Model`): a candidate of `W`'s root stands for the witness's polynomial `w`
(degree below `N`) and the true fold values `A_k(t)` at every `t`, with the verifier's cells from
them the row's cells `w(t + ω_c)` (`cells_fold`: the `B` basis, the tables' layer); a candidate of
`Q`'s root stands for `P`, `S` (below `N`), `h`, `q` and `q_P` (below `2N`); the setup's polynomials `σ`, `κ` are
fixed (`L = 1`), and so are the ports' `Φ_k` (any polynomials below `N` taking the public fingerprints at the
holes, `phi_eval`) and the identity's claim's weight `c` of `P`'s slots (`idC`, the limbs' `c_3`).

**`Q`'s empty slots** (`PI2.md` §2, "The empty slots are not constrained, and need not be"): `Q`'s commitment is its
plain sixteen-slot stack, so the prover also chooses slots `1, 5, 9` (`h`'s second digit `h_1`) and `12` (`S`, at
`P`'s limb code and kind, digit `0`); the honest prover leaves them zero. The claims then read `h = h_0 + Z_V h_1`
(below `2N`, `Σ_V h = Σ_V h_0`: `hP` is that `h`) and `P`'s share as `P(t) + S(t)/Z_V(t)`: at the challenge `t`,
`P`'s effective polynomial is `pEff = P + S(t)/Z_V(t)` (a constant shift, `t` fixed), and `Post1` and `Post2` are
stated with it.

**The states** (`pre`, `post`, for a statement `s` with public limbs `pubOf s`):

* before round `0`: **the relation** of `W`'s candidate (`Rel`: `Satisfies`, the copy constraints
  and the public ports);
* after `α, β, γ`: **`CopyOK`** (some `h` meets the identity on `V_m` and sums to zero);
* before `t`: **both identities zero as polynomials** for `Q`'s candidate, `Σ_V h = 0` (`Pre1`);
* after `t`: `t ∉ V_m`, **both identities zero at `t`** with `P`'s effective polynomial `pEff` (`P + S(t)/Z_V(t)`),
  and `Σ_V h = 0` (`Post1`);
* before `ρ`: the state after `t`;
* after `ρ`: **the claims hold** (`Post2`): `Σ_V h = 0`, the setup's claim `ξ = κ(t) + βσ(t)`, `Q`'s identity and
  pushes' claims (`QClaim`, with the verifier's `d_pull`, `d_push = α + s + ξ`, `1_S`, `T`, `P_v` from the fold values,
  `ξ`, `s`, and `P`'s share `P(t) + S(t)/Z_V(t)`), and `W`'s fold at `ρ` (`foldAt`).

**The errors** (`err`, each proved, `piop`'s `sound`): round `0` `(4N − 1 + Σ_j d_j)/|F|`
(`Circuit.card_copyOK_le`), round `1` `(4N − 1)/|F|`: for `S = 0` the identities' degrees (`h` below `2N`,
`Circuit.card_idPoly_eval_eq_zero_le`), for `S ≠ 0` the nonzero polynomial `Z_V·def + S` of degree at most `4N − 1`,
which `P`'s definition at `t` with `pEff` makes vanish (`Circuit.card_defPoly_shift_le`: were it zero, `Z_V`, of
degree `N`, would divide `S`, below `N`); round `2` `2^r/|F|`: `W`'s fold binds the fold values but for `2^r − 1`
points (`card_foldAt_eq_le`), and with them and `ξ` right the pushes' claim is a nonzero line in `ρ` unless
`s = pEff(t)` and `P`'s definition holds at `t`, and then the identity's claim is the identity at `t`
(`card_qClaim_le`, applied to `pEff`). ListChainU multiplies round
`j`'s by the candidate lists of the roots of rounds `0..j`: `L_W`, `L_W L_Q`, `L_W L_Q`.

**`d_j`** (`hbind`, a hypothesis of `piop`): port `j`'s bad `γ` for limbs that differ;
`RecPiop.Ports` gives `0` (three limbs) and `1` (four limbs) for limbs in `K`.
-/

set_option linter.unusedSectionVars false

namespace RecPiop

open Finset Polynomial OracleComp
open scoped ENNReal

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F]

/-! ## Uniform draws by counting -/

section Draws

variable [Fintype F] [SampleableType F]

theorem draws_succ (n : ℕ) : Compose.draws F (n + 1) =
    ($ᵗ F : ProbComp F) >>= fun a => Compose.draws F n >>= fun l => pure (a :: l) := rfl

/-- **`n` uniform challenges by counting.** -/
theorem prEvent_draws_card : ∀ (n : ℕ) (P : List F → Prop) [DecidablePred P],
    Pr{let c ← Compose.draws F n}[P c] =
      ((univ.filter fun v : Fin n → F => P (List.ofFn v)).card : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞) ^ n
  | 0, P, _ => by
    simp only [Compose.draws, pow_zero, div_one]
    rw [prEvent_pure]
    by_cases h : P []
    · simp only [h, ite_true]
      have : (univ.filter fun v : Fin 0 → F => P (List.ofFn v)) = univ :=
        filter_true_of_mem fun v _ => by simpa [List.ofFn_zero] using h
      rw [this, card_univ]
      simp
    · simp only [h, ite_false]
      have : (univ.filter fun v : Fin 0 → F => P (List.ofFn v)) = ∅ :=
        filter_false_of_mem fun v _ => by simpa [List.ofFn_zero] using h
      rw [this]
      simp
  | n + 1, P, _ => by
    classical
    rw [draws_succ]
    have e1 : Pr{let c ← (($ᵗ F : ProbComp F) >>= fun a => Compose.draws F n >>= fun l =>
        pure (a :: l))}[P c] =
        ∑ a : F, Pr{let x ← ($ᵗ F : ProbComp F)}[x = a] *
          Pr{let c ← (Compose.draws F n >>= fun l => pure (a :: l))}[P c] :=
      prEvent_bind_eq_sum_fintype _ _ _
    rw [e1]
    have e2 : ∀ a : F, Pr{let c ← (Compose.draws F n >>= fun l => pure (a :: l))}[P c] =
        ((univ.filter fun v : Fin n → F => P (a :: List.ofFn v)).card : ℝ≥0∞) /
          (Fintype.card F : ℝ≥0∞) ^ n := by
      intro a
      rw [← prEvent_draws_card n (fun l => P (a :: l))]
      simp only [bind_pure_comp, prEvent_map]
    simp only [e2, SampleableType.prEvent_uniformSample_eq_singleton]
    rw [← Finset.mul_sum, ← ENNReal.sum_div]
    have hc : ∑ a : F, ((univ.filter fun v : Fin n → F => P (a :: List.ofFn v)).card : ℝ≥0∞) =
        ((univ.filter fun v : Fin (n + 1) → F => P (List.ofFn v)).card : ℝ≥0∞) := by
      rw [← Nat.cast_sum]
      congr 1
      rw [← Finset.card_sigma]
      refine Finset.card_bij (fun x _ => Fin.cons x.1 x.2) (fun x hx => ?_) (fun x hx y hy h => ?_)
        (fun v hv => ?_)
      · simp only [mem_sigma, mem_univ, mem_filter, true_and] at hx ⊢
        rw [List.ofFn_succ]
        simpa using hx
      · obtain ⟨a, v⟩ := x
        obtain ⟨b, w⟩ := y
        simp only at h
        have h1 := congrFun h 0
        simp only [Fin.cons_zero] at h1
        subst h1
        have h2 : v = w := funext fun i => by simpa using congrFun h i.succ
        subst h2
        rfl
      · refine ⟨⟨v 0, Fin.tail v⟩, ?_, Fin.cons_self_tail v⟩
        simp only [mem_sigma, mem_univ, mem_filter, true_and] at hv ⊢
        rw [List.ofFn_succ] at hv
        exact hv
    rw [hc, pow_succ, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.mul_inv
      (Or.inl (pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)))
      (Or.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))]
    ring

/-- An event on `n + 1` challenges of at most `c · |F|^n` tuples has probability at most
`c / |F|`. -/
theorem prEvent_draws_le_of_card (n : ℕ) (P : List F → Prop) [DecidablePred P] (c : ℕ)
    (h : (univ.filter fun v : Fin (n + 1) → F => P (List.ofFn v)).card ≤ c * Fintype.card F ^ n) :
    Pr{let x ← Compose.draws F (n + 1)}[P x] ≤ (c : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  rw [prEvent_draws_card]
  have hE : (Fintype.card F : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hEt : (Fintype.card F : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc ((univ.filter fun v : Fin (n + 1) → F => P (List.ofFn v)).card : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞) ^ (n + 1)
      ≤ ((c * Fintype.card F ^ n : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ (n + 1) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr h) _
    _ = (c : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
        rw [Nat.cast_mul, Nat.cast_pow, pow_succ, mul_comm (c : ℝ≥0∞),
          ENNReal.mul_div_mul_left _ _ (pow_ne_zero _ hE) (ENNReal.pow_ne_top hEt)]

theorem getD_ofFn {n : ℕ} (v : Fin n → F) (i : ℕ) (hi : i < n) :
    (List.ofFn v).getD i 0 = v ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- Three challenges counted as triples. -/
theorem card_fin3_le (P : List F → Prop) [DecidablePred P] (Q : F × F × F → Prop)
    [DecidablePred Q] (h : ∀ v : Fin 3 → F, P (List.ofFn v) → Q (v 0, v 1, v 2)) :
    (univ.filter fun v : Fin 3 → F => P (List.ofFn v)).card ≤ (univ.filter Q).card := by
  refine Finset.card_le_card_of_injOn (fun v => (v 0, v 1, v 2)) (fun v hv => ?_)
    (fun v _ w _ hvw => ?_)
  · rw [Finset.mem_coe, Finset.mem_filter] at hv ⊢
    exact ⟨Finset.mem_univ _, h v hv.2⟩
  · simp only [Prod.mk.injEq] at hvw
    funext i
    fin_cases i
    · exact hvw.1
    · exact hvw.2.1
    · exact hvw.2.2

/-- One challenge counted as a point. -/
theorem card_fin1_le (P : List F → Prop) [DecidablePred P] (Q : F → Prop) [DecidablePred Q]
    (h : ∀ v : Fin 1 → F, P (List.ofFn v) → Q (v 0)) :
    (univ.filter fun v : Fin 1 → F => P (List.ofFn v)).card ≤ (univ.filter Q).card := by
  refine Finset.card_le_card_of_injOn (fun v => v 0) (fun v hv => ?_) (fun v _ w _ hvw => ?_)
  · rw [Finset.mem_coe, Finset.mem_filter] at hv ⊢
    exact ⟨Finset.mem_univ _, h v hv.2⟩
  · funext i
    fin_cases i
    exact hvw

end Draws

/-! ## The rounds, the candidates, the verifier at `t` -/

/-- **π2's rounds**: `W`'s commitment (its root, then its out-of-domain answer) then `α, β, γ`; `Q`'s then `t`; the
`2^r` fold values, `ξ` and `s`, then `ρ`. -/
def pi2Rounds (r : ℕ) : List Compose.RoundSpec :=
  [⟨true, 1, 2⟩, ⟨true, 1, 0⟩, ⟨false, 2 ^ r + 2, 0⟩]

/-- **The verifier's row cells at `t`** from the fold values: `v_x = Σ_k a_k eq(k, z)`,
`z_l = w_l(t) + ω_{x >> l}` (`PI2.md` §2 step 2; the sibling trick of §9 lever 3a computes the
same). -/
def cellsOf (r : ℕ) (ω : ℕ → F) (a : ℕ → F) (t : F) (x : ℕ) : F :=
  ∑ k ∈ range (2 ^ r), a k * ∏ l ∈ range r,
    (if k.testBit l then QuotientSecurity.sq^[l] t + ω (x >>> l)
      else 1 + (QuotientSecurity.sq^[l] t + ω (x >>> l)))

theorem cellsOf_congr (r : ℕ) (ω : ℕ → F) {a a' : ℕ → F} (h : ∀ k < 2 ^ r, a k = a' k)
    (t : F) (x : ℕ) : cellsOf r ω a t x = cellsOf r ω a' t x :=
  Finset.sum_congr rfl fun k hk => by rw [h k (Finset.mem_range.mp hk)]

/-- **What the candidates stand for** (the tables' layer, a parameter): `W`'s candidate the
witness's polynomial and its fold values at every `t` (the verifier's cells from them are the
row's cells), `Q`'s candidate `h`, `q`, `P`, `q_P` and `S`; and the fixed ones: the setup's polynomials, the ports' `Φ`
(for any public limbs and `γ`), and the identity's claim's constant `c` (`c_3`). `h` is what the claims read,
`h_0 + Z_V h_1` (below `2N`; the prover's second digit `h_1` in `Q`'s slots `1, 5, 9`), and `S` (below `N`) is `Q`'s
slot `12`, which the claims read as `S(t)/Z_V(t)` added to `P(t)`; the honest prover's `h_1` and `S` are zero. -/
structure Model (G : Circuit F) (ω : ℕ → F) (M : Type) where
  setup : SetupPolys G ω
  phi : (ℕ → List F) → F → ℕ → F[X]
  phi_deg : ∀ pub γ k, (phi pub γ k).natDegree < G.N
  phi_eval : ∀ pub γ, ∀ j < G.nP, (phi pub γ (G.port j % G.W)).eval (ω (G.port j)) = G.pubFp γ pub j
  idC : F
  wP : M → F[X]
  wP_deg : ∀ c, (wP c).natDegree < G.N
  hP : M → F[X]
  hP_deg : ∀ c, (hP c).natDegree < 2 * G.N
  qP : M → F[X]
  qP_deg : ∀ c, (qP c).natDegree < 2 * G.N
  pP : M → F[X]
  pP_deg : ∀ c, (pP c).natDegree < G.N
  qPP : M → F[X]
  qPP_deg : ∀ c, (qPP c).natDegree < 2 * G.N
  sP : M → F[X]
  sP_deg : ∀ c, (sP c).natDegree < G.N
  fold : M → F → ℕ → F
  cells_fold : ∀ c t x, x < G.W → cellsOf G.logW ω (fold c t) t x = (wP c).eval (t + ω x)

/-- The verifier's pull denominator at `t`: `α + v_0 + βt`. -/
def dPullAt (v : ℕ → F) (α β t : F) : F := α + v 0 + β * t

/-- The verifier's push denominator at `t`: `α + s + ξ`. -/
def dPushAt (sv ξ α : F) : F := α + sv + ξ

/-- The identity's coefficient of `h(t)`: `c_h = d_pull d_push`. -/
def chAt (v : ℕ → F) (ξ sv α β t : F) : F := dPullAt v α β t * dPushAt sv ξ α

/-- **The pushes' claim's polynomial in `ρ`**: `(1 + ρ) c_q e₂ + ρ e₃`, the errors of `P(t) = s` (`e₂`) and of `P`'s
definition (`e₃`) at the claim's kind coordinate `ρ`. -/
def pushComb (cq e₂ e₃ ρ : F) : F := (1 + ρ) * cq * e₂ + ρ * e₃

/-- **The pushes' claim is a line in `ρ`, nonzero unless both errors are**: at most one root, for `c_q ≠ 0`. -/
theorem card_pushComb_le [Fintype F] {cq e₂ e₃ : F} (hcq : cq ≠ 0) (hne : ¬ (e₂ = 0 ∧ e₃ = 0)) :
    (univ.filter fun ρ => pushComb cq e₂ e₃ ρ = 0).card ≤ 1 := by
  by_cases h : cq * e₂ + e₃ = 0
  · -- then `cq e₂ ≠ 0` and the line is the constant `cq e₂`
    have h2 : cq * e₂ ≠ 0 := by
      intro h0
      apply hne
      have he₂ : e₂ = 0 := (mul_eq_zero.mp h0).resolve_left hcq
      refine ⟨he₂, ?_⟩
      rw [h0, zero_add] at h
      exact h
    rw [Finset.filter_false_of_mem fun ρ _ hρ => h2 (by
      unfold pushComb at hρ
      linear_combination hρ - ρ * h)]
    exact Nat.zero_le _
  · refine (Finset.card_le_card (t := {cq * e₂ / (cq * e₂ + e₃)}) fun ρ hρ => ?_).trans
      (Finset.card_singleton _).le
    rw [Finset.mem_filter] at hρ
    rw [Finset.mem_singleton, eq_div_iff h]
    unfold pushComb at hρ
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination hρ.2 - cq * e₂ * h2

namespace Circuit

variable (G : Circuit F) (ω : ℕ → F)

/-- **The verifier's internal pushes at `t`** from the cells: `P_v(t) = v_0 + Σ_{p internal} I_p(t)·(E_p(v_{k_p ⊕
·}) + v_0)`. -/
noncomputable def pvAt (v : ℕ → F) (γ t : F) : F :=
  v 0 + ∑ p ∈ G.intPairs, (G.ind ω p).eval t *
    ((G.regionRole p.1 p.2).value γ (v 0) (fun c => v (p.2 ^^^ c)) + v 0)

/-- **The verifier's ports' term at `t`** from the cells: `T(t) = Σ_{p port} I_p(t)·(E_p(v_{k_p ⊕ ·}) + Φ_k(t))`. -/
noncomputable def tAt (Φ : ℕ → F[X]) (v : ℕ → F) (γ t : F) : F :=
  ∑ p ∈ G.portPairs, (G.ind ω p).eval t *
    ((G.regionRole p.1 p.2).value γ (v 0) (fun c => v (p.2 ^^^ c)) + (Φ p.2).eval t)

/-- The identity's right side at `t`: `(1 + 1_S)(d_push + d_pull) + T`. -/
noncomputable def rhsAt (Φ : ℕ → F[X]) (v : ℕ → F) (ξ sv α β γ t : F) : F :=
  (1 + (G.holePoly ω).eval t) * (dPushAt sv ξ α + dPullAt v α β t) + G.tAt ω Φ v γ t

/-- **`Q`'s two claims at `t`** (π2v3; the claims' values the verifier's): `t ∉ V_m`, `c_h ≠ 0`, `Y = c_h + c_q ≠ 0`,
**the identity's claim** `e₁ + c ((1 + ρ') c_q e₂ + ρ' e₃) = 0` and **the pushes' claim** `pushComb c_q e₂ e₃ ρ = 0`,
at `ρ' = c_q/Y`, for the errors of the copy identity normalised, `e₁ = (1 + ρ')h(t) + ρ'q(t) + RHS/Y`, of `P(t) = s`,
`e₂ = P(t) + s`, and of `P`'s definition, `e₃ = q_P(t) + (s + P_v(t))/c_q` (`c_q = Z_V(t)`). The identity's claim
weighs `P` and `q_P` too, by the limbs' constant `c` (`c_3 = y_0 y_1/L_0`); `ρ` is drawn after `s`. -/
def QClaim (Φ : ℕ → F[X]) (c : F) (v : ℕ → F) (ξ sv α β γ t ρ ht qt pt qpt : F) : Prop :=
  (G.zV ω).eval t ≠ 0 ∧ chAt v ξ sv α β t ≠ 0 ∧ chAt v ξ sv α β t + (G.zV ω).eval t ≠ 0 ∧
    ((1 + (G.zV ω).eval t / (chAt v ξ sv α β t + (G.zV ω).eval t)) * ht +
        (G.zV ω).eval t / (chAt v ξ sv α β t + (G.zV ω).eval t) * qt +
        G.rhsAt ω Φ v ξ sv α β γ t / (chAt v ξ sv α β t + (G.zV ω).eval t) +
      c * ((1 + (G.zV ω).eval t / (chAt v ξ sv α β t + (G.zV ω).eval t)) * (G.zV ω).eval t * (pt + sv) +
        (G.zV ω).eval t / (chAt v ξ sv α β t + (G.zV ω).eval t) *
          (qpt + (sv + G.pvAt ω v γ t) / (G.zV ω).eval t)) = 0) ∧
    pushComb ((G.zV ω).eval t) (pt + sv) (qpt + (sv + G.pvAt ω v γ t) / (G.zV ω).eval t) ρ = 0

variable {G ω} {n : ℕ}

theorem regionRole_reads_lt (hV : G.Valid) {p : Block × ℕ} (hp : p ∈ G.pairs) {c : ℕ}
    (hc : c ∈ (G.regionRole p.1 p.2).reads) : c < G.W := by
  rcases regionRole_mem hV (mem_pairs.mp hp).1 p.2 with ⟨r, hr, hm⟩ | hf
  · exact hV.reads_lt r hr _ hm c hc
  · rw [hf] at hc; simp [Role.reads] at hc

/-- With the true cells, a pair's formula from the cells is its polynomial at `t`. -/
theorem value_cells_eq (hV : G.Valid) (wP : F[X]) (γ t : F) {v : ℕ → F}
    (hv : ∀ x < G.W, v x = wP.eval (t + ω x)) (hP : Points ω n) {p : Block × ℕ} (hp : p ∈ G.pairs) :
    (G.regionRole p.1 p.2).value γ (v 0) (fun c => v (p.2 ^^^ c)) = (G.formulaPoly ω wP γ p).eval t := by
  have hW : 0 < G.W := Nat.two_pow_pos _
  have hv0 : v 0 = wP.eval t := by rw [hv 0 hW, hP.zero, add_zero]
  unfold formulaPoly
  rw [Role.value_eval]
  refine Role.value_congr _ γ (fun _ => hv0) fun c hc => ?_
  have hk := (mem_pairs.mp hp).2.1
  rw [hv _ (Nat.xor_lt_two_pow hk (regionRole_reads_lt hV hp hc))]
  simp [cellPoly, eval_comp]

/-- **With the true cells, the verifier's internal pushes are `P_v(t)`.** -/
theorem pvAt_eq (hV : G.Valid) (hP : Points ω n) (wP : F[X]) (γ t : F) {v : ℕ → F}
    (hv : ∀ x < G.W, v x = wP.eval (t + ω x)) : G.pvAt ω v γ t = (G.pushPolyV ω wP γ).eval t := by
  have hW : 0 < G.W := Nat.two_pow_pos _
  have hv0 : v 0 = wP.eval t := by rw [hv 0 hW, hP.zero, add_zero]
  unfold pvAt pushPolyV
  simp only [eval_add, eval_mul, eval_finsetSum]
  rw [hv0]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← hv0, value_cells_eq hV wP γ t hv hP (mem_intPairs.mp hp).1, hv0]

/-- **With the true cells, the verifier's ports' term is `T(t)`.** -/
theorem tAt_eq (hV : G.Valid) (hP : Points ω n) (Φ : ℕ → F[X]) (wP : F[X]) (γ t : F) {v : ℕ → F}
    (hv : ∀ x < G.W, v x = wP.eval (t + ω x)) : G.tAt ω Φ v γ t = (G.tPoly ω Φ wP γ).eval t := by
  unfold tAt tPoly
  simp only [eval_add, eval_mul, eval_finsetSum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [value_cells_eq hV wP γ t hv hP (mem_portPairs.mp hp).1]

/-- **With the true values (cells, `ξ`, `s = P(t)`), the multiplied-out copy identity at `t` is `idPoly`'s
value.** -/
theorem idPoly_eval_eq (hV : G.Valid) (hP : Points ω n) (S : SetupPolys G ω) (Φ : ℕ → F[X])
    (wP hP' qP pP : F[X]) (α β γ t ξ sv : F) {v : ℕ → F} (hv : ∀ x < G.W, v x = wP.eval (t + ω x))
    (hξ : ξ = S.κP.eval t + β * S.σP.eval t) (hs : sv = pP.eval t) :
    (G.idPoly ω S Φ wP hP' qP pP α β γ).eval t =
      chAt v ξ sv α β t * hP'.eval t + (G.zV ω).eval t * qP.eval t + G.rhsAt ω Φ v ξ sv α β γ t := by
  have hW : 0 < G.W := Nat.two_pow_pos _
  have hpull : dPullAt v α β t = (dPullP wP α β).eval t := by
    unfold dPullAt dPullP
    rw [hv 0 hW, hP.zero, add_zero]
    simp
  have hpush : dPushAt sv ξ α = (G.dPushP ω S pP α β).eval t := by
    unfold dPushAt dPushP
    simp only [eval_add, eval_mul, eval_C, hξ, hs]
    ring
  unfold idPoly chAt rhsAt
  rw [tAt_eq hV hP Φ wP γ t hv, hpull, hpush]
  simp only [eval_add, eval_mul, eval_one]
  ring

/-- **With the true cells, `P`'s definition at `t` is `P(t) + P_v(t) + c_q q_P(t)`.** -/
theorem defPoly_eval_eq (hV : G.Valid) (hP : Points ω n) (wP pP qPP : F[X]) (γ t : F) {v : ℕ → F}
    (hv : ∀ x < G.W, v x = wP.eval (t + ω x)) :
    (G.defPoly ω wP pP qPP γ).eval t = pP.eval t + G.pvAt ω v γ t + (G.zV ω).eval t * qPP.eval t := by
  unfold defPoly
  rw [pvAt_eq hV hP wP γ t hv]
  simp only [eval_add, eval_mul]
  ring

open Classical in
/-- **`Q`'s claims at the true values, counted in `ρ`**: unless the identities hold at `t`, at most one `ρ` makes
both claims true (for any `s`: a false `s` or a false definition is a nonzero line in `ρ`; with both true, the
identity's claim is the identity at `t`). -/
theorem card_qClaim_le [Fintype F] (hV : G.Valid) (hP : Points ω n) (S : SetupPolys G ω) (Φ : ℕ → F[X])
    (c : F) (wP hP' qP pP qPP : F[X]) (α β γ t ξ sv : F) {v : ℕ → F}
    (hv : ∀ x < G.W, v x = wP.eval (t + ω x)) (hξ : ξ = S.κP.eval t + β * S.σP.eval t)
    (hne : ¬ ((G.idPoly ω S Φ wP hP' qP pP α β γ).eval t = 0 ∧ (G.defPoly ω wP pP qPP γ).eval t = 0)) :
    (univ.filter fun ρ => G.QClaim ω Φ c v ξ sv α β γ t ρ (hP'.eval t) (qP.eval t) (pP.eval t)
      (qPP.eval t)).card ≤ 1 := by
  classical
  by_cases hnd : (G.zV ω).eval t ≠ 0 ∧ chAt v ξ sv α β t ≠ 0 ∧ chAt v ξ sv α β t + (G.zV ω).eval t ≠ 0
  · obtain ⟨hcq, hch, hy⟩ := hnd
    set cq := (G.zV ω).eval t
    set ch := chAt v ξ sv α β t
    set y := ch + cq
    have hrq1 : 1 + cq / y = ch / y := by
      have e : 1 + cq / y = (y + cq) / y := by rw [add_div, div_self hy]
      rw [e]
      congr 1
      show ch + cq + cq = ch
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    by_cases h23 : pP.eval t + sv = 0 ∧ qPP.eval t + (sv + G.pvAt ω v γ t) / cq = 0
    · -- the pushes' relations hold: the identity's claim is the identity at `t`, false
      rw [Finset.filter_false_of_mem (by
        intro ρ _ h
        obtain ⟨-, -, -, hid, -⟩ := h
        rw [show chAt v ξ sv α β t + (G.zV ω).eval t = y from rfl,
          show (G.zV ω).eval t = cq from rfl] at hid
        have hz : c * ((1 + cq / y) * cq * (pP.eval t + sv) +
            cq / y * (qPP.eval t + (sv + G.pvAt ω v γ t) / cq)) = 0 := by
          rw [h23.1, h23.2]; ring
        rw [hz, add_zero] at hid
        have hs : sv = pP.eval t := (CharTwo.add_eq_zero.mp h23.1).symm
        apply hne
        constructor
        · rw [idPoly_eval_eq hV hP S Φ wP hP' qP pP α β γ t ξ sv hv hξ hs]
          rw [hrq1] at hid
          have : (ch * hP'.eval t + cq * qP.eval t + G.rhsAt ω Φ v ξ sv α β γ t) / y = 0 := by
            rw [← hid]; field_simp
          rcases div_eq_zero_iff.mp this with h | h
          · exact h
          · exact absurd h hy
        · rw [defPoly_eval_eq hV hP wP pP qPP γ t hv, ← hs]
          have : (cq * qPP.eval t + (sv + G.pvAt ω v γ t)) / cq = 0 := by
            rw [← h23.2]; field_simp
          rcases div_eq_zero_iff.mp this with h | h
          · rw [← h]; ring
          · exact absurd h hcq)]
      exact Nat.zero_le _
    · refine (Finset.card_le_card fun ρ hρ => ?_).trans (card_pushComb_le hcq h23)
      rw [Finset.mem_filter] at hρ ⊢
      exact ⟨hρ.1, hρ.2.2.2.2.2⟩
  · rw [Finset.filter_false_of_mem (by intro ρ _ h; exact hnd ⟨h.1, h.2.1, h.2.2.1⟩)]
    exact Nat.zero_le _

/-- **`Q`'s claims hold at the true values** (completeness): where the identities hold at `t`, `s = P(t)` and the
three denominators are nonzero, both claims hold at every `ρ`. -/
theorem qClaim_of_eval (hV : G.Valid) (hP : Points ω n) (S : SetupPolys G ω) (Φ : ℕ → F[X])
    (c : F) (wP hP' qP pP qPP : F[X]) (α β γ t ξ sv ρ : F) {v : ℕ → F}
    (hv : ∀ x < G.W, v x = wP.eval (t + ω x)) (hξ : ξ = S.κP.eval t + β * S.σP.eval t) (hs : sv = pP.eval t)
    (hid : (G.idPoly ω S Φ wP hP' qP pP α β γ).eval t = 0) (hdef : (G.defPoly ω wP pP qPP γ).eval t = 0)
    (hcq : (G.zV ω).eval t ≠ 0) (hch : chAt v ξ sv α β t ≠ 0) (hy : chAt v ξ sv α β t + (G.zV ω).eval t ≠ 0) :
    G.QClaim ω Φ c v ξ sv α β γ t ρ (hP'.eval t) (qP.eval t) (pP.eval t) (qPP.eval t) := by
  set cq := (G.zV ω).eval t
  set ch := chAt v ξ sv α β t
  have e2 : pP.eval t + sv = 0 := by rw [hs]; exact CharTwo.add_self_eq_zero _
  have e3 : qPP.eval t + (sv + G.pvAt ω v γ t) / cq = 0 := by
    rw [defPoly_eval_eq hV hP wP pP qPP γ t hv, ← hs] at hdef
    have : qPP.eval t = (sv + G.pvAt ω v γ t) / cq := by
      field_simp
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination hdef - (sv + G.pvAt ω v γ t) * h2
    rw [this]
    exact CharTwo.add_self_eq_zero _
  have hid' := hid
  rw [idPoly_eval_eq hV hP S Φ wP hP' qP pP α β γ t ξ sv hv hξ hs] at hid'
  refine ⟨hcq, hch, hy, ?_, ?_⟩
  · rw [e2, e3]
    have e1 : (1 + cq / (ch + cq)) * hP'.eval t + cq / (ch + cq) * qP.eval t +
        G.rhsAt ω Φ v ξ sv α β γ t / (ch + cq) = (ch * hP'.eval t + cq * qP.eval t + G.rhsAt ω Φ v ξ sv α β γ t) /
          (ch + cq) := by
      field_simp
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination (hP'.eval t) * cq * h2
    rw [e1, hid', zero_div]
    ring
  · unfold pushComb
    rw [e2, e3]
    ring

/-- **`Q`'s claims hold at the true values, with an empty slot `S`** (completeness): `qClaim_of_eval` with `P`'s share
read as `P(t) + S(t)/Z_V(t)`, where `S(t) = 0` (the honest `S` is zero). -/
theorem qClaim_of_eval_sP (hV : G.Valid) (hP : Points ω n) (S : SetupPolys G ω) (Φ : ℕ → F[X])
    (c : F) (wP hP' qP pP qPP sP : F[X]) (α β γ t ξ sv ρ : F) {v : ℕ → F}
    (hv : ∀ x < G.W, v x = wP.eval (t + ω x)) (hξ : ξ = S.κP.eval t + β * S.σP.eval t) (hs : sv = pP.eval t)
    (hid : (G.idPoly ω S Φ wP hP' qP pP α β γ).eval t = 0) (hdef : (G.defPoly ω wP pP qPP γ).eval t = 0)
    (hcq : (G.zV ω).eval t ≠ 0) (hch : chAt v ξ sv α β t ≠ 0) (hy : chAt v ξ sv α β t + (G.zV ω).eval t ≠ 0)
    (hS : sP.eval t = 0) :
    G.QClaim ω Φ c v ξ sv α β γ t ρ (hP'.eval t) (qP.eval t) (pP.eval t + sP.eval t / (G.zV ω).eval t)
      (qPP.eval t) := by
  rw [hS, zero_div, add_zero]
  exact qClaim_of_eval hV hP S Φ c wP hP' qP pP qPP α β γ t ξ sv ρ hv hξ hs hid hdef hcq hch hy

open Classical in
/-- **An empty slot `S ≠ 0` at a random point**: `Z_V·def + S` is a nonzero polynomial (were it zero, `Z_V`, of degree
`N`, would divide `S`, below `N`) of degree at most `4N − 1`, and it vanishes at every `t ∉ V_m` where `P`'s
definition holds with `P`'s share read as `P(t) + S(t)/Z_V(t)`: at most `4N − 1` such `t`. -/
theorem card_defPoly_shift_le [Fintype F] (hV : G.Valid) {wP pP qPP sP : F[X]} (hw : wP.natDegree < G.N)
    (hp : pP.natDegree < G.N) (hqp : qPP.natDegree < 2 * G.N) (hs : sP.natDegree < G.N) (hs0 : sP ≠ 0)
    (γ : F) :
    (univ.filter fun t => (G.zV ω).eval t ≠ 0 ∧
      (G.defPoly ω wP (pP + C (sP.eval t / (G.zV ω).eval t)) qPP γ).eval t = 0).card ≤ 4 * G.N - 1 := by
  have h2 := N_ge_two hV
  set D := G.defPoly ω wP pP qPP γ with hD
  have hne : G.zV ω * D + sP ≠ 0 := by
    intro h0
    have hdvd : G.zV ω ∣ sP := ⟨-D, by linear_combination h0⟩
    have h1 := natDegree_le_of_dvd hdvd hs0
    rw [natDegree_zV] at h1
    omega
  have hdeg : (G.zV ω * D + sP).natDegree ≤ 4 * G.N - 1 := by
    have hDd := natDegree_defPoly_le (ω := ω) hV hw hp hqp γ
    refine natDegree_add_le_of_degree_le ((natDegree_mul_le_of_le (natDegree_zV G ω).le hDd).trans ?_)
      (by omega)
    omega
  refine (Finset.card_le_card fun t ht => ?_).trans ((card_eval_eq_zero_le _ hne).trans hdeg)
  rw [Finset.mem_filter] at ht ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  obtain ⟨-, hz, hd⟩ := ht
  have e : (G.defPoly ω wP (pP + C (sP.eval t / (G.zV ω).eval t)) qPP γ).eval t =
      D.eval t + sP.eval t / (G.zV ω).eval t := by
    rw [hD]
    unfold defPoly
    simp only [eval_add, eval_mul, eval_C]
    ring
  rw [e] at hd
  rw [eval_add, eval_mul]
  calc (G.zV ω).eval t * D.eval t + sP.eval t
      = (G.zV ω).eval t * (D.eval t + sP.eval t / (G.zV ω).eval t) := by field_simp
    _ = 0 := by rw [hd, mul_zero]

end Circuit

/-! ## The states -/

section States

variable {St M : Type} (G : Circuit F) (ω : ℕ → F) (Mo : Model G ω M) (pubOf : St → ℕ → List F)

/-- Round `j` of an opened transcript. -/
def rd (q : Compose.Opened M F) (j : ℕ) : (Option M × List F) × List F := q.getD j ((none, []), [])

theorem rd_append_lt (q l : Compose.Opened M F) (j : ℕ) (h : j < q.length) :
    rd (q ++ l) j = rd q j := by
  simp [rd, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem rd_append_self (q : Compose.Opened M F) (x : (Option M × List F) × List F) :
    rd (q ++ [x]) q.length = x := by
  simp [rd, List.getD_eq_getElem?_getD]

/-- **The relation** of `W`'s candidate: its witness satisfies the circuit for the statement's
public limbs. -/
def Rel (s : St) (c : M) : Prop := G.Satisfies (pubOf s) (fun i => (Mo.wP c).eval (ω i))

/-- **`Σ_V h` is zero.** -/
def SumOK (cQ : M) : Prop := ∑ i ∈ range G.N, (Mo.hP cQ).eval (ω i) = 0

/-- **`P`'s effective polynomial at `t`**: `P + S(t)/Z_V(t)`, the constant shift by which the claims read `Q`'s slot
`12` (`S`) with `P`'s; its value at `t` is the claims' `P(t) + S(t)/Z_V(t)` (`pEff_eval`), and it is `P` for `S = 0`
(`pEff_of_sP`). -/
noncomputable def pEff (cQ : M) (t : F) : F[X] := Mo.pP cQ + C ((Mo.sP cQ).eval t / (G.zV ω).eval t)

theorem pEff_eval (cQ : M) (t : F) :
    (pEff G ω Mo cQ t).eval t = (Mo.pP cQ).eval t + (Mo.sP cQ).eval t / (G.zV ω).eval t := by
  simp [pEff]

theorem pEff_of_sP {cQ : M} (h : Mo.sP cQ = 0) (t : F) : pEff G ω Mo cQ t = Mo.pP cQ := by
  simp [pEff, h]

/-- The copy identity of the candidates. -/
noncomputable def idOf (s : St) (cW cQ : M) (α β γ : F) : F[X] :=
  G.idPoly ω Mo.setup (Mo.phi (pubOf s) γ) (Mo.wP cW) (Mo.hP cQ) (Mo.qP cQ) (Mo.pP cQ) α β γ

/-- `P`'s definition of the candidates. -/
noncomputable def defOf (cW cQ : M) (γ : F) : F[X] := G.defPoly ω (Mo.wP cW) (Mo.pP cQ) (Mo.qPP cQ) γ

/-- The copy identity of the candidates with `P`'s effective polynomial at `t`. -/
noncomputable def idEff (s : St) (cW cQ : M) (α β γ t : F) : F[X] :=
  G.idPoly ω Mo.setup (Mo.phi (pubOf s) γ) (Mo.wP cW) (Mo.hP cQ) (Mo.qP cQ) (pEff G ω Mo cQ t) α β γ

/-- `P`'s definition of the candidates with `P`'s effective polynomial at `t`. -/
noncomputable def defEff (cW cQ : M) (γ t : F) : F[X] := G.defPoly ω (Mo.wP cW) (pEff G ω Mo cQ t) (Mo.qPP cQ) γ

theorem idEff_of_sP {s : St} {cW cQ : M} (h : Mo.sP cQ = 0) (α β γ t : F) :
    idEff G ω Mo pubOf s cW cQ α β γ t = idOf G ω Mo pubOf s cW cQ α β γ := by
  unfold idEff idOf
  rw [pEff_of_sP G ω Mo h]

theorem defEff_of_sP {cW cQ : M} (h : Mo.sP cQ = 0) (γ t : F) :
    defEff G ω Mo cW cQ γ t = defOf G ω Mo cW cQ γ := by
  unfold defEff defOf
  rw [pEff_of_sP G ω Mo h]

/-- `(α, β, γ)` of round `0`'s challenges. -/
def abc (c : List F) : F × F × F := (c.getD 0 0, c.getD 1 0, c.getD 2 0)

/-- **The state after `α, β, γ`.** -/
def S0 (s : St) (cW : M) (c : List F) : Prop :=
  G.CopyOK ω (pubOf s) (fun i => (Mo.wP cW).eval (ω i)) (abc c).1 (abc c).2.1 (abc c).2.2

/-- **The state before `t`**: both identities zero as polynomials, `Σ_V h = 0` (whatever `S`: the copy argument's
state follows on `V_m`, `copyOK_of_idPoly`, and `S ≠ 0` is caught at `t`). -/
def Pre1 (s : St) (cW : M) (c₀ : List F) (cQ : M) : Prop :=
  idOf G ω Mo pubOf s cW cQ (abc c₀).1 (abc c₀).2.1 (abc c₀).2.2 = 0 ∧
    defOf G ω Mo cW cQ (abc c₀).2.2 = 0 ∧ SumOK G ω Mo cQ

/-- **The state after `t`**: `t ∉ V_m`, both identities zero at `t` with `P`'s effective polynomial
`P + S(t)/Z_V(t)`, `Σ_V h = 0`. -/
def Post1 (s : St) (cW : M) (c₀ : List F) (cQ : M) (c₁ : List F) : Prop :=
  (G.zV ω).eval (c₁.getD 0 0) ≠ 0 ∧
    (idEff G ω Mo pubOf s cW cQ (abc c₀).1 (abc c₀).2.1 (abc c₀).2.2 (c₁.getD 0 0)).eval (c₁.getD 0 0) = 0 ∧
    (defEff G ω Mo cW cQ (abc c₀).2.2 (c₁.getD 0 0)).eval (c₁.getD 0 0) = 0 ∧ SumOK G ω Mo cQ

/-- The fold values of round `2`'s message. -/
def foldVals (vals : List F) : ℕ → F := fun k => vals.getD k 0

/-- `ξ` of round `2`'s message. -/
def xiOf (r : ℕ) (vals : List F) : F := vals.getD (2 ^ r) 0

/-- `s` of round `2`'s message. -/
def sOf (r : ℕ) (vals : List F) : F := vals.getD (2 ^ r + 1) 0

/-- **The claims** (the state after `ρ`): `Σ_V h = 0`, the setup's claim at `β`, `Q`'s two claims at `t` (`P`'s share
read as `P(t) + S(t)/Z_V(t)`), `W`'s fold at `ρ`. -/
def Post2 (s : St) (cW : M) (c₀ : List F) (cQ : M) (c₁ vals c₂ : List F) : Prop :=
  SumOK G ω Mo cQ ∧
    xiOf G.logW vals = Mo.setup.κP.eval (c₁.getD 0 0) + (abc c₀).2.1 * Mo.setup.σP.eval (c₁.getD 0 0) ∧
      G.QClaim ω (Mo.phi (pubOf s) (abc c₀).2.2) Mo.idC
        (cellsOf G.logW ω (foldVals vals) (c₁.getD 0 0)) (xiOf G.logW vals) (sOf G.logW vals)
        (abc c₀).1 (abc c₀).2.1 (abc c₀).2.2 (c₁.getD 0 0) (c₂.getD 0 0)
        ((Mo.hP cQ).eval (c₁.getD 0 0)) ((Mo.qP cQ).eval (c₁.getD 0 0))
        ((Mo.pP cQ).eval (c₁.getD 0 0) + (Mo.sP cQ).eval (c₁.getD 0 0) / (G.zV ω).eval (c₁.getD 0 0))
        ((Mo.qPP cQ).eval (c₁.getD 0 0)) ∧
      foldAt G.logW (foldVals vals) (c₂.getD 0 0) =
        foldAt G.logW (Mo.fold cW (c₁.getD 0 0)) (c₂.getD 0 0)

/-- **The state before a round's challenges.** -/
def pre (s : St) (p : Compose.Opened M F) (m : Option M × List F) : Prop :=
  if p.length = 0 then ∃ c, m.1 = some c ∧ Rel G ω Mo pubOf s c
  else if p.length = 1 then
    ∃ cW cQ, (rd p 0).1.1 = some cW ∧ m.1 = some cQ ∧ Pre1 G ω Mo pubOf s cW (rd p 0).2 cQ
  else if p.length = 2 then
    ∃ cW cQ, (rd p 0).1.1 = some cW ∧ (rd p 1).1.1 = some cQ ∧
      Post1 G ω Mo pubOf s cW (rd p 0).2 cQ (rd p 1).2
  else False

/-- **The state after a round's challenges.** -/
def post (s : St) (p : Compose.Opened M F) (m : Option M × List F) (c : List F) : Prop :=
  if p.length = 0 then ∃ cW, m.1 = some cW ∧ S0 G ω Mo pubOf s cW c
  else if p.length = 1 then
    ∃ cW cQ, (rd p 0).1.1 = some cW ∧ m.1 = some cQ ∧ Post1 G ω Mo pubOf s cW (rd p 0).2 cQ c
  else if p.length = 2 then
    ∃ cW cQ, (rd p 0).1.1 = some cW ∧ (rd p 1).1.1 = some cQ ∧
      Post2 G ω Mo pubOf s cW (rd p 0).2 cQ (rd p 1).2 m.2 c
  else False

/-- **The rounds' errors**: `(4N − 1 + Σ_j d_j)/|F|` (the copy argument and the ports), `(4N − 1)/|F|` (the identities
at `t`, `h` below `2N`, and the empty slot `S`), `2^r/|F|` (the fold and the pushes' claim at `ρ`). -/
noncomputable def err [Fintype F] (d : ℕ → ℕ) (j : ℕ) : ℝ≥0∞ :=
  if j = 0 then ((4 * G.N - 1 + ∑ i ∈ range G.nP, d i : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
  else if j = 1 then ((4 * G.N - 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
  else ((2 ^ G.logW : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)

end States

/-! ## The rounds' soundness -/

section Sound

variable {St M : Type} {G : Circuit F} {ω : ℕ → F} (Mo : Model G ω M) (pubOf : St → ℕ → List F)
variable {n : ℕ}

/-- **The next round's state implies this round's after** (`Compose.Piop.pre_post`). -/
theorem pre_post (hV : G.Valid) (hP : Points ω n) (hn : G.logN ≤ n) (s : St)
    (p : Compose.Opened M F) (m : Option M × List F) (c : List F) (m' : Option M × List F)
    (h : pre G ω Mo pubOf s (p ++ [(m, c)]) m') : post G ω Mo pubOf s p m c := by
  unfold pre at h
  unfold post
  rw [List.length_append, List.length_singleton] at h
  by_cases h0 : p.length = 0
  · rw [ite_eq_left h0]
    rw [ite_eq_right (by omega), ite_eq_left (by omega)] at h
    obtain ⟨cW, cQ, hW, -, hpre⟩ := h
    have hp : p = [] := List.eq_nil_of_length_eq_zero h0
    subst hp
    have e : rd ([] ++ [(m, c)] : Compose.Opened M F) 0 = (m, c) := rfl
    rw [e] at hW hpre
    obtain ⟨hid, hdef, hsum⟩ := hpre
    exact ⟨cW, hW, Circuit.copyOK_of_idPoly hV hP hn Mo.setup (pubOf s) (Mo.phi (pubOf s) (abc c).2.2)
      (Mo.wP cW) (Mo.hP cQ) (Mo.qP cQ) (Mo.pP cQ) (Mo.qPP cQ) _ _ _ (Mo.phi_eval _ _) hid hdef hsum⟩
  · rw [ite_eq_right h0]
    by_cases h1 : p.length = 1
    · rw [ite_eq_left h1]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)] at h
      obtain ⟨cW, cQ, hW, hQ, hpost⟩ := h
      rw [rd_append_lt p _ 0 (by omega)] at hW hpost
      have e : rd (p ++ [(m, c)]) 1 = (m, c) := by rw [← h1]; exact rd_append_self p (m, c)
      rw [e] at hQ hpost
      exact ⟨cW, cQ, hW, hQ, hpost⟩
    · rw [ite_eq_right h1]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)] at h
      exact h.elim

variable [Fintype F] [SampleableType F]

/-- **Round `0`'s error**: `(4N − 1 + Σ_j d_j)/|F|` over `α, β, γ` (the copy argument and the ports). -/
theorem sound_zero (hV : G.Valid) (hP : Points ω n) (hn : G.logN + 1 ≤ n) (d : ℕ → ℕ)
    (hbind : ∀ s c, ∀ j < G.nP, G.limbVals (fun i => (Mo.wP c).eval (ω i)) j ≠ pubOf s j →
      (univ.filter fun γ : F => G.push (fun i => (Mo.wP c).eval (ω i)) γ (G.port j) =
        G.pubFp γ (pubOf s) j).card ≤ d j)
    (s : St) (m : Option M × List F) :
    Pr{let c ← Compose.draws F (2 + 1)}[¬ pre G ω Mo pubOf s [] m ∧ post G ω Mo pubOf s [] m c] ≤
      err G d 0 := by
  classical
  have hω : ∀ a < 2 * G.N, ∀ b < 2 * G.N, ω a = ω b → a = b := by
    have h2 : 2 * G.N ≤ 2 ^ n := by
      unfold Circuit.N
      rw [← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) hn
    intro a ha b hb h
    exact hP.inj a (by omega) b (by omega) h
  unfold err
  rw [ite_eq_left rfl]
  refine prEvent_draws_le_of_card 2 _ _ ?_
  by_cases hpre : pre G ω Mo pubOf s [] m
  · rw [Finset.filter_false_of_mem fun v _ h => h.1 hpre]
    exact Nat.zero_le _
  cases hm : m.1 with
  | none =>
    rw [Finset.filter_false_of_mem fun v _ h => by
      have h2 := h.2
      unfold post at h2
      rw [ite_eq_left List.length_nil] at h2
      obtain ⟨cW, hW, -⟩ := h2
      rw [hm] at hW
      simp at hW]
    exact Nat.zero_le _
  | some cW =>
    have hns : ¬ Rel G ω Mo pubOf s cW := fun h' => hpre (by
      unfold pre
      rw [ite_eq_left List.length_nil]
      exact ⟨cW, hm, h'⟩)
    refine (card_fin3_le (fun c => ¬ pre G ω Mo pubOf s [] m ∧ post G ω Mo pubOf s [] m c)
      (fun v => G.CopyOK ω (pubOf s) (fun i => (Mo.wP cW).eval (ω i))
      v.1 v.2.1 v.2.2) fun v hv => ?_).trans
        (Circuit.card_copyOK_le ω hV hω (pubOf s) _ d (hbind s cW) hns)
    have h2 := hv.2
    unfold post at h2
    rw [ite_eq_left List.length_nil] at h2
    obtain ⟨cW', hW', hS⟩ := h2
    rw [hm] at hW'
    cases Option.some.inj hW'
    unfold S0 abc at hS
    rw [getD_ofFn v 0 (by norm_num), getD_ofFn v 1 (by norm_num), getD_ofFn v 2 (by norm_num)] at hS
    exact hS

/-- **Round `1`'s error**: `(4N − 1)/|F|` over `t`: for `S = 0` the identities' degrees (`h` below `2N`); for `S ≠ 0`
the nonzero `Z_V·def + S`, of degree at most `4N − 1`, which `P`'s definition at `t` with `P + S(t)/Z_V(t)` makes
vanish (`Circuit.card_defPoly_shift_le`). -/
theorem sound_one (hV : G.Valid) (d : ℕ → ℕ) (s : St) (p : Compose.Opened M F)
    (hp : p.length = 1) (m : Option M × List F) :
    Pr{let c ← Compose.draws F (0 + 1)}[¬ pre G ω Mo pubOf s p m ∧ post G ω Mo pubOf s p m c] ≤
      err G d 1 := by
  classical
  unfold err
  rw [ite_eq_right (by decide : (1 : ℕ) ≠ 0), ite_eq_left rfl]
  refine prEvent_draws_le_of_card 0 _ _ ?_
  rw [pow_zero, mul_one]
  have hpost : ∀ c, post G ω Mo pubOf s p m c ↔ ∃ cW cQ, (rd p 0).1.1 = some cW ∧
      m.1 = some cQ ∧ Post1 G ω Mo pubOf s cW (rd p 0).2 cQ c := by
    intro c
    unfold post
    rw [ite_eq_right (by omega), ite_eq_left hp]
  by_cases hex : ∃ cW cQ, (rd p 0).1.1 = some cW ∧ m.1 = some cQ
  · obtain ⟨cW, cQ, hW, hQ⟩ := hex
    by_cases hpre : pre G ω Mo pubOf s p m
    · rw [Finset.filter_false_of_mem fun v _ h => h.1 hpre]
      exact Nat.zero_le _
    have hnp : ¬ Pre1 G ω Mo pubOf s cW (rd p 0).2 cQ := fun h => hpre (by
      unfold pre
      rw [ite_eq_right (by omega), ite_eq_left hp]
      exact ⟨cW, cQ, hW, hQ, h⟩)
    set c₀ := (rd p 0).2
    have hpost1 : ∀ v : Fin 1 → F, post G ω Mo pubOf s p m (List.ofFn v) →
        Post1 G ω Mo pubOf s cW c₀ cQ [v 0] := by
      intro v hv
      obtain ⟨cW', cQ', hW', hQ', h1⟩ := (hpost _).mp hv
      rw [hW] at hW'
      rw [hQ] at hQ'
      cases Option.some.inj hW'
      cases Option.some.inj hQ'
      have e : List.ofFn v = [v 0] := by rw [List.ofFn_succ, List.ofFn_zero]
      rw [e] at h1
      exact h1
    by_cases hsum : SumOK G ω Mo cQ
    · by_cases hS : Mo.sP cQ = 0
      · -- `S = 0`: the identities with `P` itself
        have hne : ¬ (idOf G ω Mo pubOf s cW cQ (abc c₀).1 (abc c₀).2.1 (abc c₀).2.2 = 0 ∧
            defOf G ω Mo cW cQ (abc c₀).2.2 = 0) := fun h => hnp ⟨h.1, h.2, hsum⟩
        refine (card_fin1_le (fun c => ¬ pre G ω Mo pubOf s p m ∧ post G ω Mo pubOf s p m c)
          (fun t => (idOf G ω Mo pubOf s cW cQ (abc c₀).1 (abc c₀).2.1 (abc c₀).2.2).eval t = 0 ∧
            (defOf G ω Mo cW cQ (abc c₀).2.2).eval t = 0)
          fun v hv => ?_).trans ?_
        · obtain ⟨-, hev, hdv, -⟩ := hpost1 v hv.2
          rw [List.getD_cons_zero, idEff_of_sP G ω Mo pubOf hS] at hev
          rw [List.getD_cons_zero, defEff_of_sP G ω Mo hS] at hdv
          exact ⟨hev, hdv⟩
        · exact Circuit.card_idPoly_eval_eq_zero_le hV Mo.setup (Mo.phi_deg _ _) (Mo.wP_deg cW) (Mo.hP_deg cQ)
            (Mo.qP_deg cQ) (Mo.pP_deg cQ) (Mo.qPP_deg cQ) _ _ _ hne
      · -- `S ≠ 0`: `Z_V·def + S` vanishes at `t`
        refine (card_fin1_le (fun c => ¬ pre G ω Mo pubOf s p m ∧ post G ω Mo pubOf s p m c)
          (fun t => (G.zV ω).eval t ≠ 0 ∧ (G.defPoly ω (Mo.wP cW)
            (Mo.pP cQ + C ((Mo.sP cQ).eval t / (G.zV ω).eval t)) (Mo.qPP cQ) (abc c₀).2.2).eval t = 0)
          fun v hv => ?_).trans
            (Circuit.card_defPoly_shift_le hV (Mo.wP_deg cW) (Mo.pP_deg cQ) (Mo.qPP_deg cQ) (Mo.sP_deg cQ) hS _)
        obtain ⟨hz, -, hdv, -⟩ := hpost1 v hv.2
        rw [List.getD_cons_zero] at hz hdv
        exact ⟨hz, hdv⟩
    · rw [Finset.filter_false_of_mem fun v _ h => hsum (hpost1 v h.2).2.2.2]
      exact Nat.zero_le _
  · rw [Finset.filter_false_of_mem fun v _ h => hex (by
      obtain ⟨cW, cQ, hW, hQ, -⟩ := (hpost _).mp h.2
      exact ⟨cW, cQ, hW, hQ⟩)]
    exact Nat.zero_le _

/-- **Round `2`'s error**: `2^r/|F|` over `ρ` (`W`'s fold, `2^r − 1`; with the right fold values and `ξ`, `Q`'s
pushes' claim, `1`). -/
theorem sound_two (hV : G.Valid) (hP : Points ω n) (d : ℕ → ℕ) (s : St)
    (p : Compose.Opened M F) (hp : p.length = 2) (m : Option M × List F) :
    Pr{let c ← Compose.draws F (0 + 1)}[¬ pre G ω Mo pubOf s p m ∧ post G ω Mo pubOf s p m c] ≤
      err G d 2 := by
  classical
  unfold err
  rw [ite_eq_right (by decide : (2 : ℕ) ≠ 0), ite_eq_right (by decide : (2 : ℕ) ≠ 1)]
  refine prEvent_draws_le_of_card 0 _ _ ?_
  rw [pow_zero, mul_one]
  have hpost : ∀ c, post G ω Mo pubOf s p m c ↔ ∃ cW cQ, (rd p 0).1.1 = some cW ∧
      (rd p 1).1.1 = some cQ ∧ Post2 G ω Mo pubOf s cW (rd p 0).2 cQ (rd p 1).2 m.2 c := by
    intro c
    unfold post
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hp]
  by_cases hex : ∃ cW cQ, (rd p 0).1.1 = some cW ∧ (rd p 1).1.1 = some cQ
  · obtain ⟨cW, cQ, hW, hQ⟩ := hex
    by_cases hpre : pre G ω Mo pubOf s p m
    · rw [Finset.filter_false_of_mem fun v _ h => h.1 hpre]
      exact Nat.zero_le _
    have hnp : ¬ Post1 G ω Mo pubOf s cW (rd p 0).2 cQ (rd p 1).2 := fun h => hpre (by
      unfold pre
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hp]
      exact ⟨cW, cQ, hW, hQ, h⟩)
    have hclaims : ∀ c, post G ω Mo pubOf s p m c →
        Post2 G ω Mo pubOf s cW (rd p 0).2 cQ (rd p 1).2 m.2 c := by
      intro c h
      obtain ⟨cW', cQ', hW', hQ', h2⟩ := (hpost c).mp h
      rw [hW] at hW'
      rw [hQ] at hQ'
      cases Option.some.inj hW'
      cases Option.some.inj hQ'
      exact h2
    set c₀ := (rd p 0).2
    set t := (rd p 1).2.getD 0 0
    by_cases hfold : ∃ k < 2 ^ G.logW, foldVals m.2 k ≠ Mo.fold cW t k
    · refine (card_fin1_le (fun c => ¬ pre G ω Mo pubOf s p m ∧ post G ω Mo pubOf s p m c)
        (fun ρ => foldAt G.logW (foldVals m.2) ρ =
        foldAt G.logW (Mo.fold cW t) ρ) fun v hv => ?_).trans
          ((card_foldAt_eq_le G.logW hfold).trans (Nat.sub_le _ _))
      have h2 := (hclaims _ hv.2).2.2.2
      rw [getD_ofFn v 0 (by norm_num)] at h2
      exact h2
    · push Not at hfold
      have hv : ∀ x < G.W, cellsOf G.logW ω (foldVals m.2) t x = (Mo.wP cW).eval (t + ω x) := fun x hx => by
        rw [cellsOf_congr G.logW ω hfold _ x, Mo.cells_fold cW _ x hx]
      by_cases hok : SumOK G ω Mo cQ ∧
          xiOf G.logW m.2 = Mo.setup.κP.eval t + (abc c₀).2.1 * Mo.setup.σP.eval t
      · by_cases hz : (G.zV ω).eval t = 0
        · -- `t ∈ V_m`: `Q`'s claims fail
          rw [Finset.filter_false_of_mem fun v _ h => (hclaims _ h.2).2.2.1.1 hz]
          exact Nat.zero_le _
        have hne : ¬ ((idEff G ω Mo pubOf s cW cQ (abc c₀).1 (abc c₀).2.1 (abc c₀).2.2 t).eval t = 0 ∧
            (defEff G ω Mo cW cQ (abc c₀).2.2 t).eval t = 0) := fun h => hnp ⟨hz, h.1, h.2, hok.1⟩
        refine (card_fin1_le (fun c => ¬ pre G ω Mo pubOf s p m ∧ post G ω Mo pubOf s p m c)
          (fun ρ => G.QClaim ω (Mo.phi (pubOf s) (abc c₀).2.2) Mo.idC
            (cellsOf G.logW ω (foldVals m.2) t) (xiOf G.logW m.2) (sOf G.logW m.2)
            (abc c₀).1 (abc c₀).2.1 (abc c₀).2.2 t ρ ((Mo.hP cQ).eval t) ((Mo.qP cQ).eval t)
            ((pEff G ω Mo cQ t).eval t) ((Mo.qPP cQ).eval t)) fun v hv' => ?_).trans
          ((Circuit.card_qClaim_le hV hP Mo.setup _ _ (Mo.wP cW) (Mo.hP cQ) (Mo.qP cQ) (pEff G ω Mo cQ t)
            (Mo.qPP cQ) _ _ _ t _ _ hv hok.2 hne).trans Nat.one_le_two_pow)
        have h2 := (hclaims _ hv'.2).2.2.1
        rw [getD_ofFn v 0 (by norm_num)] at h2
        rw [pEff_eval]
        exact h2
      · rw [Finset.filter_false_of_mem fun v _ h => hok (by
          have h2 := hclaims _ h.2
          exact ⟨h2.1, h2.2.1⟩)]
        exact Nat.zero_le _
  · rw [Finset.filter_false_of_mem fun v _ h => hex (by
      obtain ⟨cW, cQ, hW, hQ, -⟩ := (hpost _).mp h.2
      exact ⟨cW, cQ, hW, hQ⟩)]
    exact Nat.zero_le _

/-- **π2's PIOP in `Compose.Piop`'s form**, for any chain whose rounds are π2's: the states
`pre`, `post`, the errors `err` (round `0` `(4N − 1 + Σ_j d_j)/|F|`, round `1` `(4N − 1)/|F|` (`h` below `2N`,
the empty slot `S`), round `2` `2^r/|F|`), each proved. The hypotheses: a valid circuit, points injective on
`[0, 2N)` (`n ≥ log N + 1`), and the ports' binding `d_j` (`RecPiop.Ports`). -/
noncomputable def piop (K : Compose.ChainSpec F St) (hK : K.rounds = pi2Rounds G.logW)
    (hV : G.Valid) (hP : Points ω n) (hn : G.logN + 1 ≤ n) (d : ℕ → ℕ)
    (hbind : ∀ s c, ∀ j < G.nP, G.limbVals (fun i => (Mo.wP c).eval (ω i)) j ≠ pubOf s j →
      (univ.filter fun γ : F => G.push (fun i => (Mo.wP c).eval (ω i)) γ (G.port j) =
        G.pubFp γ (pubOf s) j).card ≤ d j) :
    Compose.Piop K M where
  pre := pre G ω Mo pubOf
  post := post G ω Mo pubOf
  pre_post := pre_post Mo pubOf hV hP (by omega)
  err := err G d
  sound j s p m hj hp := by
    have hlen : K.rounds.length = 3 := by rw [hK]; rfl
    rw [hlen] at hj
    interval_cases j
    · have hs : (K.spec 0).ns = 2 := by simp [Compose.ChainSpec.spec, hK, pi2Rounds]
      rw [hs, List.eq_nil_of_length_eq_zero hp]
      exact sound_zero Mo pubOf hV hP hn d hbind s m
    · have hs : (K.spec 1).ns = 0 := by simp [Compose.ChainSpec.spec, hK, pi2Rounds]
      rw [hs]
      exact sound_one Mo pubOf hV d s p hp m
    · have hs : (K.spec 2).ns = 0 := by simp [Compose.ChainSpec.spec, hK, pi2Rounds]
      rw [hs]
      exact sound_two Mo pubOf hV hP d s p hp m

end Sound

end RecPiop
