-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The verifier's arithmetic is `formal/RecStatement`'s
-- (`all_ne_zero_iff`), the rounds' claims `formal/RecPiop`'s (`QClaim`, `qClaim_of_eval`, `iPoly`).
import RecCompose.Pi2HonestQ
import RecCompose.Pi2HonestMulX
import UniSound.Piop

/-!
# π2's honest prover: its objects and its bad challenges (π2v4)

* **The honest objects**: `W`'s stack (`honestW`: the witness's basis-`B` coefficients), `Q`'s (`honestQ`: the sixteen
  slots, `H = x h` by `mulX` at `(0, 0)` of each limb, `q`'s digits at `(1, 0)`, `(0, 1)`, `G` zero; `P`, `q_P`'s digits,
  `S` zero at limb code `3`), the verifier's inputs (`honestInputs`: the true fold values at `t`, `ξ = κ(t) + βσ(t)`,
  `s = P(t)`), and the polynomials (`witnessPoly`, `sigmaPoly`, `kappaPoly`, `pushPolyH`, `hxPoly = x h`);
* **`readQ_honest`**, **`qEntry_slot`**: `Q`'s stack read back by slot (`pos + N (b + 4 limb)`);
* **the bad challenges**: `BadCopy` (`α, β`: a non-hole's `d_pull` or `d_push` on `V_m` zero), **`BadT`** (`t`:
  `t ∈ V_m`, `c_h = D(t)`, `Y_1 = (D + x Z_V)(t)`, `Y_2 = (D + x Z_V²)(t)` or `α + P_v(t) + κ(t) + βσ(t)` zero,
  `D = d_pull d_push` the honest polynomial) and **`BadRho`** (`ρ`: `Y_3 = 1 + ρ (1 + Z_V(t))` zero), the nonzero
  values the contract requires (`RecStatement.all_ne_zero_iff`: `w_m`, `c_h`, `Y_1`, `Y_2`, `Y_3`, `α + P_v(t) + ξ`);
* **`iPoly_honest`**: the identity's claim's polynomial `I = D² H + x Z_V D A + x² Z_V³ G + x D R` is zero at the
  honest `H = x h`, `A = q` and `G = 0`, given the old identity `h D + R + q Z_V = 0` (`RecPiop.Circuit.iPoly_X_mul`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters Finset Polynomial

/-! ## The honest objects -/

/-- **The honest `W` stack**: the witness's basis-`B` coefficients, zeros to `W`'s stack (the prover's `wStack`). -/
def honestW (G : RecPiop.Circuit E) (w : ℕ → K) : UniSound.Stk :=
  fun j ↦ (padStack (stackVars G.logN).1 fun i ↦ (wTableB G w).getD i 0).getD j 0

/-- **The honest `Q` stack**: the sixteen slots (`H = x h` by `mulX`, `q`, `G = 0`; `P`, `q_P`, `S = 0`), zeros to
`Q`'s stack (the prover's `qStack`), `Φ` the verifier's at the public scalars `pubs`. -/
def honestQ (G : RecPiop.Circuit E) (S : CoreSpec E) (pubs : List E) (w : ℕ → K) (α β γ : E) : UniSound.Stk :=
  fun j ↦ (padStack (stackVars G.logN).2.1 (qEntry G.logN (mulX (hNovel G w α β))
    (qNovel G w α β γ (phiOn S pubs γ)) (pNovel G w) (qpNovel G w γ))).getD j 0

/-- **The honest inputs** of the verifier's arithmetic: the scalars, the challenges, the true fold values at `t`,
`ξ` from the setup's halves and `s = P(t)` (the prover's `inputs`). -/
def honestInputs (G : RecPiop.Circuit E) (setupStack : Array K) (w : ℕ → K) (scalars : List E)
    (α β γ t ρ : E) : Inputs E :=
  ⟨scalars, α, β, γ, t, foldValues G.logN G.logW (wTableB G w) t, xiOf G.logN setupStack β t,
    sOf G.logN (pNovel G w) t, ρ⟩

/-- **The witness's polynomial** (degree below `N`): its novel coefficients'. -/
noncomputable def witnessPoly (G : RecPiop.Circuit E) (w : ℕ → K) : E[X] :=
  UniKeccakComplete.AlgC.novP G.logN fun j ↦ (UniComplete.novelOfValuesK G.logN (wValues G w)).getD j 0

/-- `σ`'s and `κ`'s polynomials (degree below `N`). -/
noncomputable def sigmaPoly (G : RecPiop.Circuit E) : E[X] :=
  UniKeccakComplete.AlgC.novP G.logN fun j ↦ (UniComplete.novelOfValuesE G.logN (sigmaValues G)).getD j 0

noncomputable def kappaPoly (G : RecPiop.Circuit E) : E[X] :=
  UniKeccakComplete.AlgC.novP G.logN fun j ↦ (UniComplete.novelOfValuesE G.logN (kappaValues G)).getD j 0

/-- **`P`'s polynomial** (degree below `N`): `P`'s novel coefficients'. -/
noncomputable def pushPolyH (G : RecPiop.Circuit E) (w : ℕ → K) : E[X] :=
  UniKeccakComplete.AlgC.novP G.logN fun j ↦ ((pNovel G w).map ofK).getD j 0

/-- **`H = x h`'s polynomial** (degree below `N` when `Σ_V h = 0`): `mulX` of `h`'s novel coefficients'. -/
noncomputable def hxPoly (G : RecPiop.Circuit E) (w : ℕ → K) (α β : E) : E[X] :=
  UniKeccakComplete.AlgC.novP G.logN fun j ↦ (mulX (hNovel G w α β)).getD j 0

/-- **The copy argument's bad challenges**: a non-hole's `d_pull` or `d_push` on `V_m` zero (neither the public limbs
`pub` nor `γ` enter, the ports being out of the copy argument). -/
def BadCopy (G : RecPiop.Circuit E) (w : ℕ → K) (_pub : ℕ → List E) (α β _γ : E) : Prop :=
  (∃ i < G.N, ¬ G.IsHole i ∧ RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i = 0) ∨
    (∃ i < G.N, ¬ G.IsHole i ∧ G.dPushV pi2Omega (RecCircuit.emb w) α β i = 0)

/-- **The honest push denominator** `α + P + κ + β σ`. -/
noncomputable def dPushH (G : RecPiop.Circuit E) (w : ℕ → K) (α β : E) : E[X] :=
  C α + pushPolyH G w + kappaPoly G + C β * sigmaPoly G

/-- **The bad points `t`** (π2v4): `t ∈ V_m` (`w_m(t) = 0`), `c_h = D(t)` zero, `Y_1 = (D + x Z_V)(t)` zero,
`Y_2 = (D + x Z_V²)(t)` zero, or `α + P_v(t) + κ(t) + βσ(t)` zero, `D = d_pull d_push`. -/
def BadT (G : RecPiop.Circuit E) (w : ℕ → K) (α β γ t : E) : Prop :=
  QuotientSecurity.sq^[G.logN] t = 0 ∨
    (RecPiop.dPullP (witnessPoly G w) α β * dPushH G w α β).eval t = 0 ∨
    (RecPiop.dPullP (witnessPoly G w) α β * dPushH G w α β + X * G.zV pi2Omega).eval t = 0 ∨
    (RecPiop.dPullP (witnessPoly G w) α β * dPushH G w α β + X * G.zV pi2Omega ^ 2).eval t = 0 ∨
    (C α + G.pushPolyV pi2Omega (witnessPoly G w) γ + kappaPoly G + C β * sigmaPoly G).eval t = 0

/-- **The bad `ρ`** (π2v4): `Y_3 = 1 + ρ (1 + Z_V(t))` zero, one value of `ρ` unless `Z_V(t) = 1`. -/
def BadRho (G : RecPiop.Circuit E) (t ρ : E) : Prop :=
  1 + ρ + ρ * (G.zV pi2Omega).eval t = 0

/-! ## Facts of the honest objects -/

theorem size_wValues (G : RecPiop.Circuit E) (w : ℕ → K) : (wValues G w).size = 2 ^ G.logN := by
  simp [wValues, RecPiop.Circuit.N]

theorem witnessPoly_omega (G : RecPiop.Circuit E) (w : ℕ → K) (hm : G.logN ≤ 28) {i : ℕ} (hi : i < G.N) :
    (witnessPoly G w).eval (pi2Omega i) = RecCircuit.emb w i := by
  unfold witnessPoly
  rw [novP_valuesK_omega hm _ (size_wValues G w) hi]
  unfold wValues
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [show i < G.N from hi, dite_true, Option.getD_some]
  rfl

theorem sigmaPoly_omega (G : RecPiop.Circuit E) (hm : G.logN ≤ 28) {i : ℕ} (hi : i < G.N) :
    (sigmaPoly G).eval (pi2Omega i) = pi2Omega (G.sigma i) := by
  unfold sigmaPoly
  rw [novP_values_omega hm _ (by simp [sigmaValues, RecPiop.Circuit.N]) hi]
  unfold sigmaValues
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [show i < G.N from hi, dite_true, Option.getD_some]
  rw [pi2Omega_eq]

theorem kappaPoly_omega (G : RecPiop.Circuit E) (hm : G.logN ≤ 28) {i : ℕ} (hi : i < G.N) :
    (kappaPoly G).eval (pi2Omega i) = G.kappa i := by
  unfold kappaPoly
  rw [novP_values_omega hm _ (by simp [kappaValues, RecPiop.Circuit.N]) hi]
  unfold kappaValues
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [show i < G.N from hi, dite_true, Option.getD_some]

theorem hNovel_omega (G : RecPiop.Circuit E) (w : ℕ → K) (α β : E) (hm : G.logN ≤ 28) {i : ℕ} (hi : i < G.N) :
    (UniKeccakComplete.AlgC.novP G.logN fun j ↦ (hNovel G w α β).getD j 0).eval (pi2Omega i) =
      (hValues G w α β).getD i 0 :=
  novP_values_omega hm _ (size_hValues w α β) hi

/-- **`P`'s polynomial takes `P_v + κ`** on `V_m`, for a witness at a circuit over `K`. -/
theorem pushPolyH_omega (G : RecPiop.Circuit E) (hK : KCircuit G) (w : ℕ → K) {pub : ℕ → List E}
    (hw : G.Satisfies pub (RecCircuit.emb w)) (hm : G.logN ≤ 28) {i : ℕ} (hi : i < G.N) :
    (pushPolyH G w).eval (pi2Omega i) = pvValue G w i := by
  unfold pushPolyH
  have e : ((pNovel G w).map ofK) = UniComplete.novelOfValuesK G.logN (pColumn G w) := rfl
  rw [e, novP_valuesK_omega hm _ (size_pColumn w) hi]
  unfold pColumn
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [show i < G.N from hi, dite_true, Option.getD_some]
  exact limb_zero_of_mem (pvValue_mem hK w hw hi)

/-- The honest polynomials are `HonestPolys`. -/
theorem honestPolys (G : RecPiop.Circuit E) (w : ℕ → K) (α β : E) (S : RecPiop.SetupPolys G pi2Omega)
    (hσ : S.σP = sigmaPoly G) (hκ : S.κP = kappaPoly G) :
    HonestPolys G w α β S (witnessPoly G w)
      (UniKeccakComplete.AlgC.novP G.logN fun j ↦ (hNovel G w α β).getD j 0) (pushPolyH G w) :=
  ⟨rfl, hσ, hκ, rfl, rfl⟩

/-! ## The stacks read back -/

/-- **`W`'s stack reads back the honest table.** -/
theorem readW_honest (G : RecPiop.Circuit E) (w : ℕ → K) (i : ℕ) : honestW G w i = (wTableB G w).getD i 0 := by
  unfold honestW
  rw [padStack_getD]
  split_ifs with h
  · rfl
  · have hsz : (wTableB G w).size ≤ 2 ^ (stackVars G.logN).1 := by
      unfold wTableB
      rw [UniKeccakComplete.AlgC.bCoefficients_size, show (wValues G w).size = 2 ^ G.logN by simp [wValues, RecPiop.Circuit.N]]
      exact Nat.pow_le_pow_right (by norm_num) (by simp only [stackVars]; omega)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    rfl

/-- **`Q`'s stack reads back the honest table** below `16 N`. -/
theorem readQ_honest (G : RecPiop.Circuit E) (S : CoreSpec E) (pubs : List E) (w : ℕ → K) (α β γ : E)
    {i : ℕ} (hi : i < 2 ^ (G.logN + 4)) :
    honestQ G S pubs w α β γ i =
      qEntry G.logN (mulX (hNovel G w α β)) (qNovel G w α β γ (phiOn S pubs γ)) (pNovel G w) (qpNovel G w γ) i := by
  unfold honestQ
  have h : i < 2 ^ (stackVars G.logN).2.1 :=
    lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) (by simp only [stackVars]; omega))
  simp only [padStack_getD, h, ↓reduceIte]

theorem slot_lt {m pos b l : ℕ} (hpos : pos < 2 ^ m) (hb : b < 4) (hl : l < 4) :
    pos + 2 ^ m * (b + 4 * l) < 2 ^ (m + 4) := by
  have : 2 ^ (m + 4) = 2 ^ m * 16 := by rw [pow_add]; norm_num
  rw [this]
  nlinarith

/-- **`Q`'s table by slot** (`pos + N (b + 4 limb)`, `b = b_0 + 2 b_1`): `H`'s, `q`'s two digits, `G = 0` at limbs
`0, 1, 2`; `P`, `q_P`'s two digits, `S = 0` at limb code `3`. -/
theorem qEntry_slot (m : ℕ) (hxN qN : Array E) (pN qpN : Array K) {pos b l : ℕ} (hpos : pos < 2 ^ m) (hb : b < 4) :
    qEntry m hxN qN pN qpN (pos + 2 ^ m * (b + 4 * l)) =
      if l < 3 then
        (if b = 0 then limbN (hxN.getD pos 0) l else if b = 1 then limbN (qN.getD pos 0) l
          else if b = 2 then limbN (qN.getD (2 ^ m + pos) 0) l else 0)
      else if l = 3 then
        (if b = 0 then pN.getD pos 0 else if b = 1 then qpN.getD pos 0
          else if b = 2 then qpN.getD (2 ^ m + pos) 0 else 0)
      else 0 := by
  unfold qEntry
  have h1 : (pos + 2 ^ m * (b + 4 * l)) % 2 ^ m = pos := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hpos]
  have h2 : (pos + 2 ^ m * (b + 4 * l)) / 2 ^ m = b + 4 * l := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hpos, zero_add]
  have h3 : (b + 4 * l) % 4 = b := by omega
  have h4 : (b + 4 * l) / 4 = l := by omega
  simp only [h1, h2, h3, h4]

theorem yE_eq : yE = Primitives.F192.Y := rfl

theorem limbN_zero (x : E) : limbN x 0 = x.limb 0 := rfl
theorem limbN_one (x : E) : limbN x 1 = x.limb 1 := rfl
theorem limbN_two (x : E) : limbN x 2 = x.limb 2 := rfl

/-- **An element of `E` from its limbs**: `Σ_l Y^l c_l`. -/
theorem limbs_sum_eq (x : E) : ∑ l ∈ range 3, yE ^ l * ofK (limbN x l) = x := by
  have hk : ∀ a : K, ofK a = Primitives.F192.ofF64 a := fun _ ↦ rfl
  have hl : ∀ i, x.limb i = Primitives.F192.limb x i := fun _ ↦ rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, limbN_zero, limbN_one, limbN_two, hk, hl]
  conv_rhs => rw [← Primitives.F192.ofLimbs_limb x, Primitives.F192.ofLimbs_eq]
  rw [yE_eq]
  ring

/-! ## `H = x h` and the identity's claim -/

/-- **The honest `H` is `x h`** when the copy argument's sum is zero (`Σ_V h = 0`, `novP_mulX`). -/
theorem hxPoly_eq (G : RecPiop.Circuit E) (w : ℕ → K) (α β : E) (hm : G.logN ≤ 28)
    (hs : ∑ i ∈ range (2 ^ G.logN), (hValues G w α β).getD i 0 = 0) :
    hxPoly G w α β = X * UniKeccakComplete.AlgC.novP G.logN fun j ↦ (hNovel G w α β).getD j 0 := by
  unfold hxPoly
  refine novP_mulX _ (by omega) (size_hNovel w α β) ?_
  exact (Finset.sum_congr rfl fun i hi ↦ hNovel_omega G w α β hm (mem_range.mp hi)).trans hs

/-- **The identity's claim's polynomial is zero at the honest `Q`**: `H = x h`, `A = q`, `G = 0`, given the identity
`h D + R + q Z_V = 0`. -/
theorem iPoly_honest (G : RecPiop.Circuit E) (S : RecPiop.SetupPolys G pi2Omega) (Φ : ℕ → E[X]) (wP h qP pP : E[X])
    (α β γ : E) (hid : G.idPoly pi2Omega S Φ wP h qP pP α β γ = 0) :
    G.iPoly pi2Omega S Φ wP (X * h) qP 0 pP α β γ = 0 := by
  rw [RecPiop.Circuit.iPoly_X_mul]
  have hq : G.idPoly pi2Omega S Φ wP h qP pP α β γ = G.idPoly pi2Omega S Φ wP h 0 pP α β γ + qP * G.zV pi2Omega := by
    unfold RecPiop.Circuit.idPoly
    ring
  rw [hq] at hid
  linear_combination X * G.dP pi2Omega S wP pP α β * hid

end RecCompose

/-- info: 'RecCompose.iPoly_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.iPoly_honest

/-- info: 'RecCompose.readW_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.readW_honest
